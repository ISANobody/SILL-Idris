module Sessions

import RegularTrees
import Data.Fin
import Data.Vect
import Data.Vect.Quantifiers as Q
import Data.HVect
import System.Concurrency.Raw
import Effects
import Effect.State
import Effect.StdIO

total alter : (a -> a) -> Nat -> List a -> Maybe (List a)
alter _ _ [] = Nothing
alter f Z (x :: xs) = Just ((f x) :: xs)
alter f (S k) (x::xs) with (alter f k xs)
  | Just ys = Just (x :: ys)
  | Nothing = Nothing

overwrite : Nat -> a -> List a -> Maybe (List a)
overwrite n x l = alter (const x) n l

data SType : Vect k Type -> Type where
  SendD    : {v:Vect k Type} -> Fin k -> SType v
  RecvD    : {v:Vect k Type} -> Fin k -> SType v
  One      : SType v
  External : Nat -> SType v
  Internal : Nat -> SType v

injective_SendD : (SendD s = SendD t) -> (s = t)
injective_SendD Refl = Refl

injective_RecvD : (RecvD s = RecvD t) -> (s = t)
injective_RecvD Refl = Refl

injective_External : (External ss = External ts) -> ss = ts
injective_External Refl = Refl

injective_Internal : (Internal ss = Internal ts) -> ss = ts
injective_Internal Refl = Refl

instance DecEq (SType v) where
  decEq One One = Yes Refl
  decEq (External a) (External b) with (decEq a b)
    decEq (External a) (External a) | Yes Refl = Yes Refl
    decEq (External a) (External b) | No ctr = No (ctr . injective_External)
  decEq (Internal a) (Internal b) with (decEq a b)
    decEq (Internal a) (Internal a) | Yes Refl = Yes Refl
    decEq (Internal a) (Internal b) | No ctr = No (ctr . injective_Internal)
  decEq (SendD i) (SendD j) with (decEq i j)
    decEq (SendD i) (SendD i) | Yes Refl = Yes Refl
    decEq (SendD i) (SendD j) | No ctr = No (ctr . injective_SendD)
  decEq (RecvD i) (RecvD j) with (decEq i j)
    decEq (RecvD i) (RecvD i) | Yes Refl = Yes Refl
    decEq (RecvD i) (RecvD j) | No ctr = No (ctr . injective_RecvD)
  decEq One (External _) = No (\p => case p of Refl impossible)
  decEq One (Internal _) = No (\p => case p of Refl impossible)
  decEq One (SendD _) = No (\p => case p of Refl impossible)
  decEq One (RecvD _) = No (\p => case p of Refl impossible)
  decEq (External _) One = No (\p => case p of Refl impossible)
  decEq (External _) (Internal _) = No (\p => case p of Refl impossible)
  decEq (External _) (SendD _) = No (\p => case p of Refl impossible)
  decEq (External _) (RecvD _) = No (\p => case p of Refl impossible)
  decEq (Internal _) One = No (\p => case p of Refl impossible)
  decEq (Internal _) (External _) = No (\p => case p of Refl impossible)
  decEq (Internal _) (SendD _) = No (\p => case p of Refl impossible)
  decEq (Internal _) (RecvD _) = No (\p => case p of Refl impossible)
  decEq (SendD _) One = No (\p => case p of Refl impossible)
  decEq (SendD _) (External _) = No (\p => case p of Refl impossible)
  decEq (SendD _) (Internal _) = No (\p => case p of Refl impossible)
  decEq (SendD _) (RecvD _) = No (\p => case p of Refl impossible)
  decEq (RecvD _) One = No (\p => case p of Refl impossible)
  decEq (RecvD _) (External _) = No (\p => case p of Refl impossible)
  decEq (RecvD _) (Internal _) = No (\p => case p of Refl impossible)
  decEq (RecvD _) (SendD _) = No (\p => case p of Refl impossible)

STypeArities : {holes:Vect k Type} -> LanguageSpec (SType holes)
STypeArities (SendD _) = 1
STypeArities (RecvD _) = 1
STypeArities One = 0
STypeArities (External n) = n
STypeArities (Internal n) = n

SessionType : Vect k Type -> Type
SessionType v = RegularTree (STypeArities {holes=v})

sendD : {v:Vect k Type} -> Fin k -> SessionType v -> SessionType v
sendD i s = Connect (SendD i) [s]
recvD : {v:Vect k Type} -> Fin k -> SessionType v -> SessionType v
recvD i s = Connect (RecvD i) [s]
one : SessionType v
one = Connect One []
external : Vect k (SessionType v) -> SessionType v
external {k} ss = Connect (External k) ss
internal : Vect k (SessionType v) -> SessionType v
internal {k} ss = Connect (Internal k) ss

SesEq : SessionType v -> SessionType v -> Type
SesEq s t = RTEq s t

-- TODO Get the decidable type class to work with this
isSesEq : (s:SessionType v) -> (t:SessionType v) -> Dec (SesEq s t)
isSesEq s t = isRTEq s t

SesEnv : (k:Nat) -> (v:Vect m Type) -> Type
SesEnv k v = Vect k (Maybe (SessionType v))

-- TODO enforce j < k
data SubPerm : Vect j a -> Vect k a -> type where
  Done : SubPerm [] v
  Grab : {v:Vect k a} -> (i:Fin (S k))
      -> SubPerm u v -> SubPerm (x::u) (insertAt i x v)

-- TODO Close should enforce that everything is Consumed
-- TODO Forward should ensure that only the forwarded channel is left
data Process : SesEnv k v -> SessionType v -> Type where
  Close : {k:Nat} -> Process (replicate k Nothing) one
  Wait  : (i:Fin k) 
       -> {auto prf:index i env = (Just one)}
       -> Process (replaceAt i Nothing env) s
       -> Process env s
  Forward : {env:SesEnv k v}
         -> {s : SessionType v}
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
      -> {env':SesEnv j v}
      -> {default Done perm:SubPerm env' env}
      -> (Lazy (Process env' s))
      -> Process (env++[Just s]) t
      -> Process env t
  Lift : ({[STDIO]} Eff ()) -> Process env s -> Process env s
  ExternalR : {env:SesEnv k v}
           -> {t:SessionType v}
           -> {auto prf:unfold t = external{k=n} ss}
           -> (ps:HVect (map (Process env) ss))
           -> Process env t
  ExternalL : {env:SesEnv k v}
           -> {s:SessionType v}
           -> {t:SessionType v}
           -> {ss:Vect n (SessionType v)}
           -> (i:Fin k)
           -> (l:Fin n)
           -> {auto jprf: index i env = Just s}
           -> {auto sprf: unfold s = external ss}
           -> Process (replaceAt i (Just (index l ss)) env) t
           -> Process env t


data Msg : Type where
  MTerm : Msg
  MData : a -> Msg
  MChoice : Nat -> Msg

-- I'm not sure if this is needed, or just needed w/o a progress theorem
data EProc : {v:Vect k Type} -> Type where
  EClose : EProc
  EWait : Nat -> EProc{v=v} -> EProc{v=v}
  EForward : Nat -> EProc
  ESendDR : a -> EProc{v=v} -> EProc{v=v}
  ESendDL : Nat -> (a -> EProc{v=v}) -> EProc{v=v}
  ELift : ({[STDIO]} Eff ()) -> EProc{v=v} -> EProc{v=v}
  EBind : {env:SesEnv k v}
       -> Lazy (Process{v=v} env s) -> Vect k Nat -> EProc{v=v} -> EProc{v=v}
  EExternalR : Vect n (EProc{v=v}) -> EProc{v=v}
  EExternalL : Nat -> Nat -> EProc{v=v} -> EProc{v=v}

hVectMap : HVect (map (\x => {t:Type} -> x -> t) ts) -> HVect ts -> Vect (length ts) a
hVectMap Nil Nil = Nil
hVectMap (f::fs) (x::xs) = (f x) :: (hVectMap fs xs)

erasePerm : {u:Vect k a} -> SubPerm u v -> Vect k Nat
erasePerm Done = []
erasePerm (Grab i p) = (finToNat i) :: erasePerm p

eraseProc : {v:Vect k Type} -> Process{v=v} env s -> EProc{v=v}
eraseAll : {env : SesEnv k v} -> {ss:Vect n (SessionType v)}
        -> HVect (map (Process env) ss)
        -> Vect n (EProc{v=v})

eraseAll {ss=Nil} Nil = Nil
eraseAll {ss=t::ts} (p::ps) = (eraseProc p)::(eraseAll{ss=ts} ps)
eraseAll {ss=Nil} (p::ps) impossible
eraseAll {ss=t::ts} Nil impossible

eraseProc Close = EClose
eraseProc (Lift io p) = ELift io (eraseProc p)
eraseProc {v} (Wait n p) = EWait (finToNat n) (eraseProc{v=v} p)
eraseProc (Bind{perm} ep cp) = EBind ep (erasePerm perm) (eraseProc cp)
eraseProc (SendDR x p) = ESendDR x (eraseProc p)
eraseProc (SendDL n cont) = ESendDL (finToNat n) (eraseProc . cont)
eraseProc (ExternalR ps) = EExternalR (eraseAll ps)
eraseProc (ExternalL i l p) = EExternalL (finToNat i) (finToNat l) (eraseProc p)
eraseProc (Forward i) = EForward (finToNat i)

data Chan : Type -> Type where
  MkChan : List a -> List a -> Chan a
  Indir : Nat -> Chan a

Channels : Type -> Type
Channels a = List (Chan a)

writeSelf : Nat -> a -> { [STATE (Channels a)] } Eff () 
writeSelf n a =
  do chs <- get
     case index' n chs of
          Just (MkChan r w) => case overwrite n (MkChan r (w++[a])) chs of
                                    Just chs' => put chs'

writeOther : Nat -> a -> {[STATE (Channels a)]} Eff ()
writeOther n a =
  do chs <- get
     case index' n chs of
          Just (MkChan r w) => case overwrite n (MkChan (r++[a]) w) chs of
                                    Just chs' => put chs'
          Just (Indir i) => writeOther i a

readSelf : Nat -> { [STATE (Channels a)] } Eff (Maybe a)
readSelf n =
  do chs <- get
     case index' n chs of
          Just (MkChan [] w) => return Nothing
          Just (MkChan (x::xs) w) => case overwrite n (MkChan xs w) chs of
                                          Just chs' => do put chs'
                                                          return (Just x)

readOther : Nat -> {[STATE (Channels a)]} Eff (Maybe a)
readOther n =
  do chs <- get
     case index' n chs of
          Just (MkChan r []) => return Nothing
          Just (MkChan r (x::xs)) => case overwrite n (MkChan r xs) chs of
                                          Just chs' => do put chs'
                                                          return (Just x)
          Just (Indir i) => readOther i

newChan : { [STATE (Channels a)] } Eff Nat
newChan = 
  do chs <- get 
     put (chs++[MkChan [] []])
     return (length chs)

forward : Nat -> Nat -> { [STATE (Channels a)] } Eff ()
forward n m =
  do chs <- get
     case index' m chs of
          Just (Indir i) => forward n i
          Just (MkChan mr mw) => case index' n chs of
            Just (Indir i) => forward i m
            Just (MkChan nr nw) => case overwrite m (Indir n) chs of
              Just chs' => case overwrite n (MkChan (mr++nr) (nw++mw)) chs' of
                Just chs'' => put chs''

PState : (v:Vect m Type) -> Type
PState v = (List Nat,Nat,EProc{v=v})

vindex' : Nat -> Vect k a -> Maybe a
vindex' Z (x::_) = Just x
vindex' (S k) (_::xs) = vindex' k xs
vindex' _ _ = Nothing

remap : List a -> Vect j Nat -> List a
remap v [] = []
remap v (n::ns) = 
  case index' n v of
       Just x => x :: remap v ns

-- TODO Use a state monad or something
-- The types are loose here to try to avoid writting a peservation theorem
step : PState v 
   -> { [STATE (Channels Msg),STDIO] } Eff (List (PState v))
step (env,self,ELift io p) =
  do io
     return [(env,self,p)]
step (env,self,EBind ep cs cp) =
  do i <- newChan
     return [(remap env cs,i,eraseProc ep),(env++[i],self,cp)]
step (env,self,EClose) =
  do writeSelf self MTerm
     return []
step (env,self,ESendDR x p) =
  do writeSelf self (MData x)
     return [(env,self,p)]
step (env,self,EWait n p) = -- TODO Applicative or something?
  case index' n env of
    Just i => do m <- readOther i
                 case m of 
                      Just Mterm => return [(env,self,p)]
                      Nothing => return [(env,self,EWait n p)]
step (env,self,ESendDL n cont) =
  case index' n env of
    Just i => do m <- readOther i
                 case m of
                      Just (MData x) => return [(env,self,cont (believe_me x))]
                      Nothing => return [(env,self,(ESendDL n cont))]
step (env,self,EExternalR ps) =
  do m <- readSelf self
     case m of
       Just (MChoice l) => case vindex' l ps of
         Just p => return [(env,self,p)]
       Nothing => return [(env,self,(EExternalR ps))]
step (env,self,EExternalL c l p) =
  case index' c env of
       Just i => do writeOther i (MChoice l)
                    return [(env,self,p)]
step (env,self,EForward n) =
  case index' n env of
       Just i => do forward i self
                    return []

-- Is list the best choice here?
interp : List (PState v) -> { [STATE (Channels Msg),STDIO] } Eff ()
interp [] = return ()
interp (p::ps) =
  do x <- step p
     interp (ps++x)

-- TODO Seems like this STATE should be hidden
interpTop : {v:Vect k Type} -> Process{v=v} [] one 
         -> { [STATE (Channels Msg),STDIO] } Eff ()
interpTop {v} p =
  do i <- newChan
     interp {v} [([],i,eraseProc p)]

interpTopIO : {v:Vect k Type} -> Process{v=v} [] one -> IO ()
interpTopIO {v} p = run (interpTop {v=v} p)

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
t7 = SendDR (Wait{env=[Just one]} 0 Close) Close

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

-- TODO Is there a better way to do this?
elemToFin : {v:Vect n a} -> Elem t v -> Fin n
elemToFin Here = FZ
elemToFin (There x) with (elemToFin x)
  elemToFin (There x) | y = FS y

SStream : {v:Vect k Type} -> (t:Fin k) -> SessionType v
SStream t = Mu (external [one, sendD t Var])

countUp : Nat -> Process{v=[Nat]} [] (SStream{v=[Nat]} 0)
countUp n = ExternalR [Close,SendDR n (Bind (countUp (S n)) (Forward
                      {s=(SStream{v=[Nat]} 0)} {t=(SStream{v=[Nat]} 0)} 0))]

sfilter : (Nat -> Bool) -> Process [Just (SStream{v=[Nat]} 0)]
                                  (SStream{v=[Nat]} 0)
sfilter p =
  ExternalR [(ExternalL 0 0 (Wait 0 Close))
            ,(ExternalL 0 1 (SendDL 0 (\x =>
             if p x
                then (SendDR x
                     (Bind{perm=Grab 0 Done} (sfilter p) 
                     (Forward{s=(SStream{v=[Nat]} 0)} 
                             {t=(SStream{v=[Nat]} 0)}
                             1)))
                else (Bind{perm=Grab 0 Done} (sfilter p)
                     (ExternalL 1 1 
                     (Forward{s=(sendD{v=[Nat]} 0 (Mu (external [one,sendD 0 Var])))}
                             {t=(sendD{v=[Nat]} 0 (Mu (external [one,sendD 0 Var])))}
                             1))))))]

sieve : Process [Just (SStream{v=[Nat]} 0)] (SStream{v=[Nat]} 0)
sieve =
  ExternalR [(ExternalL 0 0 (Wait 0 Close))
            ,(ExternalL 0 1 
             (SendDL 0 (\x =>
             (SendDR x
             (Bind{perm=(Grab 0 Done)} (sfilter (\n => mod n x /= 0))
             (Bind{perm=(Grab 1 (Done{v=[Just (SStream{v=[Nat]} 0)]}))} sieve 
             (Forward {s=(SStream{v=[Nat]} 0)}{t=(SStream{v=[Nat]} 0)}
                     2)))))))]

primes : Process [] (SStream{v=[Nat]} 0)
primes = Bind (countUp 2)
        (Bind{perm=Grab 0 Done} sieve
        (Forward{s=(SStream{v=[Nat]} 0)}{t=(SStream{v=[Nat]} 0)}
                1))

t11 : Process{v=[Nat]} [] one
t11 = Bind (primes)    (ExternalL 0 1 
                       (SendDL 0 (\n => 
                        Lift (print n) 
                       (ExternalL 0 1
                       (SendDL 0 (\n => 
                        Lift (print n) 
                       (ExternalL 0 1
                       (SendDL 0 (\n => 
                        Lift (print n) 
                       (ExternalL 0 1
                       (SendDL 0 (\n => 
                        Lift (print n) 
                       (ExternalL 0 1
                       (SendDL 0 (\n => 
                        Lift (print n) 
                       (ExternalL 0 0 (Wait 0 Close)))))))))))))))))

main : IO ()
main = run (interpTop{v=[Int]} t10)
