module Sessions

import RegularTrees
import Data.Fin
import Data.Vect
import Data.Vect.Quantifiers as Q
import System.Concurrency.Raw

total alter : (a -> a) -> Nat -> List a -> Maybe (List a)
alter _ _ [] = Nothing
alter f Z (x :: xs) = Just ((f x) :: xs)
alter f (S k) (x::xs) with (alter f k xs)
  | Just ys = Just (x :: ys)
  | Nothing = Nothing

overwrite : Nat -> a -> List a -> Maybe (List a)
overwrite n x l = alter (const x) n l

data Labels = A | B | C | D

data SType : Vect k Type -> Type where
  SendD    : {v:Vect k Type} -> Fin k -> SType v
  RecvD    : {v:Vect k Type} -> Fin k -> SType v
  One      : SType v
  External : SType v
  Internal : SType v

injective_SendD : (SendD s = SendD t) -> (s = t)
injective_SendD Refl = Refl

injective_RecvD : (RecvD s = RecvD t) -> (s = t)
injective_RecvD Refl = Refl


instance DecEq (SType v) where
  decEq One One = Yes Refl
  decEq External External = Yes Refl
  decEq Internal Internal = Yes Refl
  decEq (SendD i) (SendD j) with (decEq i j)
    decEq (SendD i) (SendD i) | Yes Refl = Yes Refl
    decEq (SendD i) (SendD j) | No ctr = No (ctr . injective_SendD)
  decEq (RecvD i) (RecvD j) with (decEq i j)
    decEq (RecvD i) (RecvD i) | Yes Refl = Yes Refl
    decEq (RecvD i) (RecvD j) | No ctr = No (ctr . injective_RecvD)
  decEq One External = No (\p => case p of Refl impossible)
  decEq One Internal = No (\p => case p of Refl impossible)
  decEq One (SendD _) = No (\p => case p of Refl impossible)
  decEq One (RecvD _) = No (\p => case p of Refl impossible)
  decEq External One = No (\p => case p of Refl impossible)
  decEq External Internal = No (\p => case p of Refl impossible)
  decEq External (SendD _) = No (\p => case p of Refl impossible)
  decEq External (RecvD _) = No (\p => case p of Refl impossible)
  decEq Internal One = No (\p => case p of Refl impossible)
  decEq Internal External = No (\p => case p of Refl impossible)
  decEq Internal (SendD _) = No (\p => case p of Refl impossible)
  decEq Internal (RecvD _) = No (\p => case p of Refl impossible)
  decEq (SendD _) One = No (\p => case p of Refl impossible)
  decEq (SendD _) External = No (\p => case p of Refl impossible)
  decEq (SendD _) Internal = No (\p => case p of Refl impossible)
  decEq (SendD _) (RecvD _) = No (\p => case p of Refl impossible)
  decEq (RecvD _) One = No (\p => case p of Refl impossible)
  decEq (RecvD _) External = No (\p => case p of Refl impossible)
  decEq (RecvD _) Internal = No (\p => case p of Refl impossible)
  decEq (RecvD _) (SendD _) = No (\p => case p of Refl impossible)

STypeArities : {holes:Vect k Type} -> LanguageSpec (SType holes)
STypeArities (SendD _) = 1
STypeArities (RecvD _) = 1
STypeArities One = 0
STypeArities External = 4 -- WARNING Not robust, should be size_of(Labels)
STypeArities Internal = 4 -- WARNING Not robust, should be size_of(Labels)

SessionType : Vect k Type -> Type
SessionType v = RegularTree (STypeArities {holes=v})

sendD : {v:Vect k Type} -> Fin k -> SessionType v -> SessionType v
sendD i s = Connect (SendD i) [s]
recvD : {v:Vect k Type} -> Fin k -> SessionType v -> SessionType v
recvD i s = Connect (RecvD i) [s]
one : SessionType v
one = Connect One []
external : (Labels -> SessionType v) -> SessionType v
external f = Connect External (map f [A,B,C,D])
internal : (Labels -> SessionType v) -> SessionType v
internal f = Connect External (map f [A,B,C,D])

SesEq : SessionType v -> SessionType v -> Type
SesEq s t = RTEq s t

-- TODO Get the decidable type class to work with this
isSesEq : (s:SessionType v) -> (t:SessionType v) -> Dec (SesEq s t)
isSesEq s t = isRTEq s t

SesEnv : (k:Nat) -> (v:Vect m Type) -> Type
SesEnv k v = Vect k (Maybe (SessionType v))

-- TODO Close should enforce that everything is Consumed
-- TODO Forward should ensure that only the forwarded channel is left
data Process : SesEnv k v -> SessionType v -> Type where
  Close : Process env one
  Wait  : (i:Fin k) 
       -> {auto prf:index i env = (Just one)}
       -> Process (replaceAt i Nothing env) s
       -> Process env s
  Forward : {s : SessionType v}
         -> {t:SessionType v}
         -> (i:Fin k) 
         -> {auto jprf:index i env = Just s}
         -> {default (getYes (isSesEq s t)) sprf:SesEq s t}
         -> Process env t
  SendDR : {env:SesEnv k v}
        -> {s:SessionType v}
        -> {t:SessionType v}
        -> index i v 
        -> {auto prf:unfold t = sendD i s} 
        -> Process env s 
        -> Process env t
  SendDL : {env:SesEnv k v}
        -> {s:SessionType v} 
        -> {t:SessionType v}
        -> (i:Fin k)
        -> {auto jprf:index i env = Just (sendD j s)}
        -> (index j v -> Process (replaceAt i (Just s) env) t)
        -> Process env t
  Bind : {env:SesEnv k v}
      -> {s:SessionType v} 
      -> {t:SessionType v}
      -> (Lazy (Process [] s))
      -> Process ((Just s)::env) t
      -> Process env t
  Lift : (Lazy (IO ())) -> Process env s -> Process env s

data Msg : Type where
  MTerm : Msg
  MData : a -> Msg

-- I'm not sure if this is needed, or just needed w/o a progress theorem
data EProc : {v:Vect k Type} -> Type where
  EClose : EProc
  EWait : Nat -> EProc{v=v} -> EProc{v=v}
  EForward : Nat -> EProc
  ESendDR : a -> EProc{v=v} -> EProc{v=v}
  ESendDL : Nat -> (a -> EProc{v=v}) -> EProc{v=v}
  ELift : Lazy (IO ()) -> EProc{v=v} -> EProc{v=v}
  EBind : Lazy (Process{v=v} env s) -> EProc{v=v} -> EProc{v=v}

eraseProc : {v:Vect k Type} -> Process{v=v} env s -> EProc{v=v}
eraseProc Close = EClose
eraseProc (Lift io p) = ELift io (eraseProc p)
eraseProc {v} (Wait n p) = EWait (finToNat n) (eraseProc{v=v} p)
eraseProc (Bind ep cp) = EBind ep (eraseProc cp)
eraseProc (SendDR x p) = ESendDR x (eraseProc p)
eraseProc (SendDL n cont) = ESendDL (finToNat n) (eraseProc . cont)

data Chan : Type -> Type where
  MkChan : List a -> List a -> Chan a

Channels : Type -> Type
Channels a = List (Chan a)

writeSelf : a -> Chan a -> Chan a
writeSelf x (MkChan r w) = MkChan r (w++[x])

readOther : Chan a -> Maybe (Chan a, a)
readOther (MkChan r w) with (w)
  readOther (MkChan r []) | [] = Nothing
  readOther (MkChan r (x::xs)) | _ = Just (MkChan r xs,x)

newChan : Channels a -> (Channels a,Nat)
newChan chs = (chs++[MkChan [] []],length chs)

PState : (v:Vect m Type) -> Type
PState v = (List Nat,Nat,EProc{v=v})

-- TODO Use a state monad or something
-- The types are loose here to try to avoid writting a peservation theorem
step : Channels Msg -> PState v -> IO (Channels Msg,List (PState v))
step chs (env,self,EClose) with (alter (writeSelf MTerm) self chs)
  | Just chs' = return (chs',[])
step chs (env,self,EWait n p) = -- TODO Applicative or something?
  case index' n env of
    Just i => case index' i chs of
      Just ch => case readOther ch of
        Just (ch',MTerm) => case overwrite i ch' chs of
          Just chs' => return (chs',[(env,self,p)])
        Nothing => return (chs,[(env,self,EWait n p)])
step chs (env,self,ELift io p) =
  do io
     return (chs,[(env,self,p)])
step chs (env,self,EBind ep cp) =
  let (chs',i) = newChan chs
  in return (chs',[([],i,eraseProc ep),(env++[i],self,cp)])
step chs (env,self,ESendDR x p) =
  case alter (writeSelf (MData x)) self chs of
       Just chs' => return (chs',[(env,self,p)])
step chs (env,self,ESendDL n cont) =
  case index' n env of
    Just i => case index' i chs of
      Just ch => case readOther ch of
        Just (ch',MData x) => case overwrite i ch' chs of
          Just chs' => return (chs',[(env,self,cont (believe_me x))])
        Nothing => return (chs,[(env,self,(ESendDL n cont))])

-- Is list the best choice here?
interp : Channels Msg -> List (PState v) -> IO ()
interp _ [] = return ()
interp chs (p::ps) =
  do (chs',x) <- step chs p
     interp chs' (ps++x)

interpTop : {v:Vect k Type} -> Process{v=v} [] one -> IO ()
interpTop {v} p =
  let (chs,i) = newChan{a=Msg} []
  in interp {v} chs [([],i,eraseProc p)]

t0 : Process [] one
t0 = Lift (print 45) Close

t1 : Process [Just one] one
t1 = Wait 0 Close

t2 : Process [Just one] one
t2 = Forward {s=one} {t=one} 0

t3 : Process{v=[Int]} [] (Mu (sendD 0 Var))
t3 = SendDR 5 t3

t4 : Process{v=[Int]} [Just (sendD 0 one)] one
t4 = SendDL 0 (\ x => Wait 0 Close)

t5 : Process{v=[Int]} [] (sendD 0 one)
t5 = SendDR 5 Close

t6 : Process{v=[Int]} [] one
t6 = Bind t5 (SendDL 0 (\x => Lift (print x) (Wait 0 Close))) 

t7 : Process{v=[Process [Just one] one]} [] (sendD 0 one)
t7 = SendDR (Close) Close

-- Why is this acceptable but t8 failing?
boom : Vect 1 Type
boom = [Process{v=boom} [] (sendD 0 one)]

-- t8 : Process{v=boom} [] (sendD 0 one)
-- t8 = SendDR t8 Close

t9 : Process [] one
t9 = Bind t0 (Wait 0 Close)

t10' : Process{v=[Int]} [] (sendD 0 one)
t10' = SendDR 97 Close

t10 : Process{v=[Int]} [] one
t10 = Bind t10' (Lift (print "asdf") (SendDL 0 (\x => (Lift (print x) (Wait 0
                Close)))))

main : IO ()
main = interpTop{v=[Int]} t10
