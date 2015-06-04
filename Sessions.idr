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
  SSendD    : {v:Vect k Type} -> Fin k -> SType v
  SRecvD    : {v:Vect k Type} -> Fin k -> SType v
  SOne      : SType v
  SExternal : Nat -> SType v
  SInternal : Nat -> SType v
  SSendC    : SType v
  SRecvC    : SType v

injective_SSendD : (SSendD s = SSendD t) -> (s = t)
injective_SSendD Refl = Refl

injective_SRecvD : (SRecvD s = SRecvD t) -> (s = t)
injective_SRecvD Refl = Refl

injective_SExternal : (SExternal ss = SExternal ts) -> ss = ts
injective_SExternal Refl = Refl

injective_SInternal : (SInternal ss = SInternal ts) -> ss = ts
injective_SInternal Refl = Refl

instance DecEq (SType v) where
  decEq SOne SOne = Yes Refl
  decEq (SExternal a) (SExternal b) with (decEq a b)
    decEq (SExternal a) (SExternal a) | Yes Refl = Yes Refl
    decEq (SExternal a) (SExternal b) | No ctr = No (ctr . injective_SExternal)
  decEq (SInternal a) (SInternal b) with (decEq a b)
    decEq (SInternal a) (SInternal a) | Yes Refl = Yes Refl
    decEq (SInternal a) (SInternal b) | No ctr = No (ctr . injective_SInternal)
  decEq (SSendD i) (SSendD j) with (decEq i j)
    decEq (SSendD i) (SSendD i) | Yes Refl = Yes Refl
    decEq (SSendD i) (SSendD j) | No ctr = No (ctr . injective_SSendD)
  decEq (SRecvD i) (SRecvD j) with (decEq i j)
    decEq (SRecvD i) (SRecvD i) | Yes Refl = Yes Refl
    decEq (SRecvD i) (SRecvD j) | No ctr = No (ctr . injective_SRecvD)
  decEq SSendC SSendC = Yes Refl
  decEq SRecvC SRecvC = Yes Refl
  decEq SOne (SExternal _) = No (\p => case p of Refl impossible)
  decEq SOne (SInternal _) = No (\p => case p of Refl impossible)
  decEq SOne (SSendD _) = No (\p => case p of Refl impossible)
  decEq SOne (SRecvD _) = No (\p => case p of Refl impossible)
  decEq SOne SSendC = No (\p => case p of Refl impossible)
  decEq SOne SRecvC = No (\p => case p of Refl impossible)
  decEq (SExternal _) SOne = No (\p => case p of Refl impossible)
  decEq (SExternal _) (SInternal _) = No (\p => case p of Refl impossible)
  decEq (SExternal _) (SSendD _) = No (\p => case p of Refl impossible)
  decEq (SExternal _) (SRecvD _) = No (\p => case p of Refl impossible)
  decEq (SExternal _) SSendC = No (\p => case p of Refl impossible)
  decEq (SExternal _) SRecvC = No (\p => case p of Refl impossible)
  decEq (SInternal _) SOne = No (\p => case p of Refl impossible)
  decEq (SInternal _) (SExternal _) = No (\p => case p of Refl impossible)
  decEq (SInternal _) (SSendD _) = No (\p => case p of Refl impossible)
  decEq (SInternal _) (SRecvD _) = No (\p => case p of Refl impossible)
  decEq (SInternal _) SSendC = No (\p => case p of Refl impossible)
  decEq (SInternal _) SRecvC = No (\p => case p of Refl impossible)
  decEq (SSendD _) SOne = No (\p => case p of Refl impossible)
  decEq (SSendD _) (SExternal _) = No (\p => case p of Refl impossible)
  decEq (SSendD _) (SInternal _) = No (\p => case p of Refl impossible)
  decEq (SSendD _) (SRecvD _) = No (\p => case p of Refl impossible)
  decEq (SSendD _) SSendC = No (\p => case p of Refl impossible)
  decEq (SSendD _) SRecvC = No (\p => case p of Refl impossible)
  decEq (SRecvD _) SOne = No (\p => case p of Refl impossible)
  decEq (SRecvD _) (SExternal _) = No (\p => case p of Refl impossible)
  decEq (SRecvD _) (SInternal _) = No (\p => case p of Refl impossible)
  decEq (SRecvD _) (SSendD _) = No (\p => case p of Refl impossible)
  decEq (SRecvD _) SSendC = No (\p => case p of Refl impossible)
  decEq (SRecvD _) SRecvC = No (\p => case p of Refl impossible)
  decEq SSendC SOne = No (\p => case p of Refl impossible)
  decEq SSendC (SExternal _) = No (\p => case p of Refl impossible)
  decEq SSendC (SInternal _) = No (\p => case p of Refl impossible)
  decEq SSendC (SSendD _) = No (\p => case p of Refl impossible)
  decEq SSendC SRecvC = No (\p => case p of Refl impossible)
  decEq SSendC (SRecvD _) = No (\p => case p of Refl impossible)
  decEq SRecvC SOne = No (\p => case p of Refl impossible)
  decEq SRecvC (SExternal _) = No (\p => case p of Refl impossible)
  decEq SRecvC (SInternal _) = No (\p => case p of Refl impossible)
  decEq SRecvC (SSendD _) = No (\p => case p of Refl impossible)
  decEq SRecvC SSendC = No (\p => case p of Refl impossible)
  decEq SRecvC (SRecvD _) = No (\p => case p of Refl impossible)

STypeArities : {holes:Vect k Type} -> LanguageSpec (SType holes)
STypeArities (SSendD _) = 1
STypeArities (SRecvD _) = 1
STypeArities SOne = 0
STypeArities (SExternal n) = n
STypeArities (SInternal n) = n
STypeArities SSendC = 2
STypeArities SRecvC = 2

SessionType : Vect k Type -> Type
SessionType v = RegularTree (STypeArities {holes=v})

SendD : {v:Vect k Type} -> Fin k -> SessionType v -> SessionType v
SendD i s = Connect (SSendD i) [s]
RecvD : {v:Vect k Type} -> Fin k -> SessionType v -> SessionType v
RecvD i s = Connect (SRecvD i) [s]
One : SessionType v
One = Connect SOne []
External : Vect k (SessionType v) -> SessionType v
External {k} ss = Connect (SExternal k) ss
Internal : Vect k (SessionType v) -> SessionType v
Internal {k} ss = Connect (SInternal k) ss
SendC : SessionType v -> SessionType v -> SessionType v
SendC s1 s2 = Connect SSendC [s1,s2]
RecvC : SessionType v -> SessionType v -> SessionType v
RecvC s1 s2 = Connect SRecvC [s1,s2]

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
       -> {auto prf:index i env = (Just One)}
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
        -> {auto prf:unfold t = SendD i s} 
        -> Process env s 
        -> Process env t
  SendDL : {env:SesEnv k v}
        -> {s:SessionType v} 
        -> {t:SessionType v}
        -> (i:Fin k)
        -> {auto jprf:index i env = Just (SendD j s)}
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
           -> {auto prf:unfold t = External{k=n} ss}
           -> (ps:HVect (map (Process env) ss))
           -> Process env t
  ExternalL : {env:SesEnv k v}
           -> {s:SessionType v}
           -> {t:SessionType v}
           -> {ss:Vect n (SessionType v)}
           -> (i:Fin k)
           -> (l:Fin n)
           -> {auto jprf: index i env = Just s}
           -> {auto sprf: unfold s = External ss}
           -> Process (replaceAt i (Just (index l ss)) env) t
           -> Process env t
  -- TODO Enforce non-duplication
  SendCR : {env:SesEnv k v}
        -> {t:SessionType v}
        -> {s1:SessionType v}
        -> {s2:SessionType v}
        -> {auto prf:unfold t = SendC s1 s2}
        -> Process env s1
        -> Process env s2
        -> Process env t
  RecvCR : {env:SesEnv k v}
        -> {t:SessionType v}
        -> {s1:SessionType v}
        -> {s2:SessionType v}
        -> {auto prf:unfold t = RecvC s1 s2}
        -> Process (env++[Just s1]) s2
        -> Process env t
  -- TODO Enforce non-duplication
  RecvCL : {env:SesEnv k v}
        -> {t:SessionType v}
        -> {s1:SessionType v}
        -> {s2:SessionType v}
        -> (i:Fin k)
        -> {auto jprf:index i env = Just (RecvC s1 s2)}
        -> Process env s1
        -> Process env s2
        -> Process env t
  InternalR : {env:SesEnv k v}
           -> {t:SessionType v}
           -> {ss:Vect n (SessionType v)}
           -> {auto prf:unfold t = Internal ss}
           -> (i:Fin n)
           -> Process env (index i ss)
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
  ETailBind : {env:SesEnv k v}
       -> Lazy (Process{v=v} env s) -> Vect k Nat -> EProc{v=v}

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
eraseProc (Bind{perm} ep (Forward _)) = ETailBind ep (erasePerm perm)
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
step (env,self,ETailBind ep cs) =
  do i <- newChan
     return [(remap env cs,self,eraseProc ep)]
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
interpTop : {v:Vect k Type} -> Process{v=v} [] One 
         -> { [STATE (Channels Msg),STDIO] } Eff ()
interpTop {v} p =
  do i <- newChan
     interp {v} [([],i,eraseProc p)]

interpTopIO : {v:Vect k Type} -> Process{v=v} [] One -> IO ()
interpTopIO {v} p = run (interpTop {v=v} p)

t0 : Process [] One
t0 = Lift (print 45) Close

t1 : Process [Just One] One
t1 = Wait 0 Close

t2 : Process [Just One] One
t2 = Forward {s=One} {t=One} 0

t3 : Process{v=[Int]} [] (Mu (SendD 0 Var))
t3 = SendDR 5 t3

t4 : Process{v=[Int]} [Just (SendD 0 One)] One
t4 = SendDL 0 (\ x => Wait 0 Close)

t5 : Process{v=[Int]} [] (SendD 0 One)
t5 = SendDR 5 Close

t6 : Process{v=[Int]} [] One
t6 = Bind t5 (SendDL 0 (\x => Lift (print x) (Wait 0 Close))) 

t7 : Process{v=[Process [Just One] One]} [] (SendD 0 One)
t7 = SendDR (Wait{env=[Just One]} 0 Close) Close

-- Why is this acceptable but t8 failing?
boom : Vect 1 Type
boom = [Process{v=boom} [] (SendD 0 One)]

-- t8 : Process{v=boom} [] (sendD 0 One)
-- t8 = SendDR t8 Close

t9 : Process [] One
t9 = Bind t0 (Wait 0 Close)

t10' : Process{v=[Int]} [] (SendD 0 One)
t10' = SendDR 97 Close

t10 : Process{v=[Int]} [] One
t10 = Bind t10' (Lift (print "asdf") (SendDL 0 (\x => (Lift (print x) (Wait 0
                Close)))))

-- TODO Is there a better way to do this?
elemToFin : {v:Vect n a} -> Elem t v -> Fin n
elemToFin Here = FZ
elemToFin (There x) with (elemToFin x)
  elemToFin (There x) | y = FS y

SStream : {v:Vect k Type} -> (t:Fin k) -> SessionType v
SStream t = Mu (External [One, SendD t Var])

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
                     (Forward{s=(SendD{v=[Nat]} 0 (Mu (External [One,SendD 0 Var])))}
                             {t=(SendD{v=[Nat]} 0 (Mu (External [One,SendD 0 Var])))}
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

Queue : SessionType v -> SessionType v
Queue s = Mu (External [RecvC s Var, Internal [One,SendC s Var]])

-- emptyQ : Process [] (Queue s)
-- elemQ : Process [Just s,Just (Queue s)] (Queue s)

{- Doesn't work. I think the parameter s is messing it up?
emptyQ {s} = ExternalR 
               [ (RecvCR
                 (Bind emptyQ
                 (Bind{perm=Grab 1 (Grab 0 Done)} elemQ
                 (Forward{s=Queue s} {t=Queue s} {sprf=believe_me ()} 2))))
               , (InternalR 0
                 (Close)) ] -}

{- Doesn't work. Probably the s parameter again?
elemQ = ExternalR
          [ (RecvCR
            (ExternalL 1 0
            (RecvCL 1 (Forward 0)
            (Bind{perm=Grab 1 (Grab 0 Done)} elemQ
            (Forward 2)))))
          , (InternalR 0
            (SendCR (Forward 0)
            (Forward 1)))]
            -}

t11 : Process{v=[Nat]} [] One
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
