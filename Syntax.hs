{-# LANGUAGE RebindableSyntax, DataKinds #-}
{-# LANGUAGE GADTs, DataKinds, KindSignatures, TypeFamilies, TypeOperators #-}
{-# LANGUAGE TemplateHaskell, QuasiQuotes, PolyKinds, UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables, BangPatterns, Rank2Types #-}
{-# LANGUAGE AllowAmbiguousTypes, FlexibleContexts #-}

import Control.Concurrent
import Control.Concurrent.STM
import Unsafe.Coerce
import Prelude hiding ((>>),(>>=),return,fail)
import qualified Prelude as P
import Data.Singletons
import Data.Singletons.Prelude
import Data.Singletons.TH
import Data.Singletons.Prelude.List
import Data.IORef
import DiQueue

singletons [d|
  data Nat = Z | S Nat deriving (Show,Eq,Ord)
  |]

natToInt :: Nat -> Int
natToInt Z = 0
natToInt (S n) = 1 + (natToInt n)

promote [d|
  maxNat :: Nat -> Nat -> Nat
  maxNat Z n = n
  maxNat n Z = n
  maxNat (S n) (S m) = S (maxNat n m)

  
  inbounds :: Nat -> [a] -> Bool
  inbounds Z [] = False
  inbounds Z _ = True
  inbounds (S k) (_:xs) = inbounds k xs

  index :: Nat -> [a] ->  a
  index Z (x:_) = x
  index (S k) (_:xs) = index k xs

  remove :: Nat -> [a] -> [a]
  remove Z (_:xs) = xs
  remove (S k) (x:xs) = x:(remove k xs)

  update :: Nat -> a -> [a] -> [a]
  update Z x (_:ys) = x:ys
  update (S k) x (y:ys) = y:(update k x ys)

  allNothing :: [Maybe a] -> Bool
  allNothing [] = True
  allNothing (Nothing:xs) = allNothing xs
  allNothing _ = False

  natLen :: [a] -> Nat
  natLen [] = Z
  natLen (_:xs) = S (natLen xs)

  allInbounds :: [Nat] -> [a] -> Bool
  allInbounds [] _ = True
  allInbounds (n:ns) xs = inbounds n xs && allInbounds ns xs

  indJust :: Nat -> [Maybe a] -> Bool
  indJust _ [] = False
  indJust Z _ = True
  indJust (S n) (_:xs) = indJust n xs

  allJusts :: [Nat] -> [Maybe a] -> Bool
  allJusts [] _ = True
  allJusts (n:ns) xs = indJust n xs && allJusts ns xs

  indices :: [Nat] -> [a] -> [a]
  indices [] _ = []
  indices (n:ns) xs = (index n xs) : indices ns xs

  removes :: [Nat] -> [Maybe a] -> [Maybe a]
  removes [] xs = xs
  removes (n:ns) xs = removes ns (update n Nothing xs)

  moreThanOne :: (Eq a) => a -> [a] -> Bool
  moreThanOne _ [] = False
  moreThanOne x (y:ys) = (x == y && elem x ys) || moreThanOne x ys

  noDupsGo :: (Eq a) => [a] -> [a] -> Bool
  noDupsGo [] _ = True
  noDupsGo (x:xs) ys = not (moreThanOne x ys) && noDupsGo xs ys

  noDups :: (Eq a) => [a] -> Bool
  noDups xs = noDupsGo xs xs

  allButNothing :: Nat -> [Maybe a] -> Bool
  allButNothing Z (Just _:xs) = allNothing xs
  allButNothing (S n) (Nothing:xs) = allButNothing n xs

  data Session where
    Mu :: Session -> Session
    Var :: Session
    One :: Session
    SendD :: a -> Session -> Session
    RecvD :: a -> Session -> Session
    SendC :: Session -> Session -> Session
    RecvC :: Session -> Session -> Session
    External :: Session -> Session -> Session
    Internal :: Session -> Session -> Session
    SendShift :: Session -> Session
    RecvShift :: Session -> Session

  contractive :: Session -> Bool
  contractive (Mu Var) = False
  contractive (Mu s) = contractive s
  contractive Var = True
  contractive One = True
  contractive (SendD _ s) = True
  contractive (RecvD _ s) = True
  contractive (SendC s1 s2) = True
  contractive (RecvC s1 s2) = True
  contractive (External s1 s2) = True
  contractive (Internal s1 s2) = True
  contractive (SendShift s) = True
  contractive (RecvShift s) = True

  isPos0 :: Bool -> Session -> Bool
  isPos0 _ (Mu s) = isPos s
  isPos0 p Var = p
  isPos0 p One = True
  isPos0 p (SendD _ _) = True
  isPos0 p (RecvD _ _) = False
  isPos0 p (SendC _ _) = True
  isPos0 p (RecvC _ _) = False
  isPos0 p (External _ _) = False
  isPos0 p (Internal _ _) = True
  isPos0 p (SendShift _) = True
  isPos0 p (RecvShift _) = False

  isPos :: Session -> Bool
  isPos (Mu s) = isPos s
  isPos One = True
  isPos (SendD _ _) = True
  isPos (RecvD _ _) = False
  isPos (SendC _ _) = True
  isPos (RecvC _ _) = False
  isPos (External _ _) = False
  isPos (Internal _ _) = True
  isPos (SendShift _) = True
  isPos (RecvShift _) = False

  polarityWF0 :: Bool -- Are Var's positive?
              -> Bool -- Expected Polarity
              -> Session
	      -> Bool
  polarityWF0 v p Var = v == p
  polarityWF0 _ p (Mu s) = polarityWF0 (isPos s) p s
  polarityWF0 _ True One = True
  polarityWF0 v True (SendD _ s) = polarityWF0 v True s
  polarityWF0 v True (SendC s1 s2) = polarityWF0 v True s1 
                                  && polarityWF0 v True s2
  polarityWF0 v True (Internal s1 s2) = polarityWF0 v True s1 
                                     && polarityWF0 v True s2
  polarityWF0 v True (SendShift s) = polarityWF0 v False s
  polarityWF0 v False (RecvD _ s) = polarityWF0 v False s
  polarityWF0 v False (RecvC s1 s2) = polarityWF0 v True s1 
                                   && polarityWF0 v False s2
  polarityWF0 v False (External s1 s2) = polarityWF0 v False s1 
                                      && polarityWF0 v False s2
  polarityWF0 v False (RecvShift s) = polarityWF0 v True s

  polarityWF :: Session -> Bool
  polarityWF s = polarityWF0 undefined (isPos s) s

  wellformed :: Session -> Bool
  wellformed s = contractive s && polarityWF s

  allWellformed :: [Maybe Session] -> Bool
  allWellformed [] = True
  allWellformed (Nothing:xs) = allWellformed xs
  allWellformed (Just x:xs) = wellformed x && allWellformed xs

  subst :: Session -> Session -> Session
  subst _ One = One
  subst _ (Mu x) = Mu x
  subst x Var = x
  subst x (SendD a s) = SendD a (subst x s)
  subst x (RecvD a s) = RecvD a (subst x s)
  subst x (External s1 s2) = External (subst x s1) (subst x s2)
  subst x (Internal s1 s2) = Internal (subst x s1) (subst x s2)
  subst x (SendShift s) = SendShift (subst x s)
  subst x (RecvShift s) = RecvShift (subst x s)

  unfold :: Session -> Session
  unfold (Mu x) = subst (Mu x) x
  unfold s = s

  data PState where
    Term :: PState
    Running :: [Maybe Session] -> Session -> PState

  |]

-- TODO Add a wellformedness checker that ensures types are
-- 1) Contractive and w/o consecutive Mu's
-- 2) Closed
-- 3) Choices have no duplicates

-- Decides s = t (as regular trees). Assumes that (s,t) \notin hyp
type family RTEq2 (hyp::[(Session,Session)]) (s::Session) (t::Session) :: Bool where
  RTEq2 hyp (Mu x) t = RTEq0 hyp (Unfold (Mu x)) t
  RTEq2 hyp s (Mu y) = RTEq0 hyp s (Unfold (Mu y))
  RTEq2 hyp One One = True
  RTEq2 hyp (SendD a s) (SendD a t) = 
    RTEq0 ('(SendD a s, SendD a t) ': hyp) s t
  RTEq2 hyp (RecvD a s) (RecvD a t) = 
    RTEq0 ('(RecvD a s, RecvD a t) ': hyp) s t
  RTEq2 hyp (SendC s1 s2) (SendC t1 t2) =
    RTEq0 ('((SendC s1 s2),(SendC t1 t2)) ': hyp) s1 t1
    :&&
    RTEq0 ('((SendC s1 s2),(SendC t1 t2)) ': hyp) s2 t2
  RTEq2 hyp (External s1 s2) (External t1 t2) = 
    RTEq0 ('((External s1 s2),(External t1 t2)) ': hyp) s1 t1
    :&&
    RTEq0 ('((External s1 s2),(External t1 t2)) ': hyp) s2 t2
  RTEq2 hyp (Internal s1 s2) (Internal t1 t2) = 
    RTEq0 ('((Internal s1 s2),(Internal t1 t2)) ': hyp) s1 t1
    :&&
    RTEq0 ('((Internal s1 s2),(Internal t1 t2)) ': hyp) s2 t2
  RTEq2 hyp (SendShift s) (SendShift t) = 
    RTEq0 ('(SendShift s, SendShift t) ': hyp) s t
  RTEq2 hyp (RecvShift s) (RecvShift t) = 
    RTEq0 ('(RecvShift s, RecvShift t) ': hyp) s t

-- Decides  whether two session types, s and t, are equal by first searching for
-- assumed equalities in ctx and, if none are found, performing the next
-- non-Assmp step of the circular coinduction. ctx should always be a subset of
-- hyp (this could be strengthed to prefix/suffix).
-- TODO enforce ctx <= hyp
type family RTEq1 (ctx::[(Session,Session)]) (hyp::[(Session,Session)])
   (s::Session) (t::Session) :: Bool where
  RTEq1 '[] hyp s t = RTEq2 hyp s t
  RTEq1 ('(s,t) ': ctx) hyp s t = True
  RTEq1 ('(a,b) ': ctx) hyp s t = RTEq1 ctx hyp s t

-- Decides whether two session types, s and t, are equal given the assumed
-- equalities in hyp. This is a wrapper for RTEq1 that sets up its initial
-- search context.
type family RTEq0 (hyp::[(Session,Session)]) (s::Session) (t::Session) :: Bool 
  where
  RTEq0 hyp s t = RTEq1 hyp hyp s t

-- Type operator that checks that two session types are equal (as regular trees)
-- This works by calling the decision proceedure with its initial arguments
type RTEq s t = RTEq0 '[] s t

-- Computes the local session bounds for a type (i.e., the maximum distance from the
-- current point to the farthest polarity shift).
-- This takes a cache of previously visited nodes to protect against loop
-- and returns Nothing if no bound can be found
type family LocalBounds0 (ctx::[Session]) (loop :: [Session]) (s::Session) 
  :: Maybe Nat where
  LocalBounds0 (s ': ctx) loop s = Nothing
  LocalBounds0 (t ': ctx) loop s = LocalBounds0 ctx loop s
  LocalBounds0 '[] loop s = LocalBounds1 loop s

type family MaybeSucc (m::Maybe Nat) :: Maybe Nat where
  MaybeSucc Nothing = Nothing
  MaybeSucc (Just a) = Just (S a)

-- liftM2 max
type family MaybeMax (m::Maybe Nat) (n::Maybe Nat) :: Maybe Nat where
  MaybeMax Nothing n = Nothing
  MaybeMax m Nothing = Nothing
  MaybeMax (Just m) (Just n) = Just (MaxNat m n)

type family LocalBounds1 (loop :: [Session]) (s::Session) :: Maybe Nat where
  LocalBounds1 loop (Mu s) = LocalBounds1 loop (Unfold (Mu s))
  LocalBounds1 loop One = Just (S Z)
  LocalBounds1 loop (SendShift s) = Just (S Z)
  LocalBounds1 loop (RecvShift s) = Just (S Z)
  LocalBounds1 loop (SendD a s) = 
     MaybeSucc (LocalBounds0 (SendD a s ': loop) (SendD a s ': loop) s)
  LocalBounds1 loop (RecvD a s) = 
     MaybeSucc (LocalBounds0 (RecvD a s ': loop) (RecvD a s ': loop) s)
  LocalBounds1 loop (SendC a s) = 
     MaybeSucc (LocalBounds0 (SendC a s ': loop) (SendC a s ': loop) s)
  LocalBounds1 loop (RecvC a s) = 
     MaybeSucc (LocalBounds0 (RecvC a s ': loop) (RecvC a s ': loop) s)
  LocalBounds1 loop (External s t) = 
     MaybeMax (LocalBounds0 (External s t ': loop) (External s t ': loop) s)
              (LocalBounds0 (External s t ': loop) (External s t ': loop) t)
  LocalBounds1 loop (Internal s t) = 
     MaybeMax (LocalBounds0 (Internal s t ': loop) (Internal s t ': loop) s)
              (LocalBounds0 (Internal s t ': loop) (Internal s t ': loop) t)

type LocalBounds s = LocalBounds0 '[] '[] s


type family PhaseStarts0 (ctx::[Session]) (visited::[Session]) (s::Session) 
  :: [Session] where
  PhaseStarts0 (s ': ctx) visited s = '[]
  PhaseStarts0 (t ': ctx) visited s = PhaseStarts0 ctx visited s
  PhaseStarts0 '[] visited s = PhaseStarts1 visited s

type family PhaseStarts1 (visited::[Session]) (s::Session) :: [Session] where
  PhaseStarts1 visited (Mu s) = PhaseStarts1 visited (Unfold (Mu s))
  PhaseStarts1 visited One = '[]
  PhaseStarts1 visited (SendShift s) = s ': (PhaseStarts0 (SendShift s ': visited)
                                                          (SendShift s ': visited) s)
  PhaseStarts1 visited (RecvShift s) = s ': (PhaseStarts0 (RecvShift s ': visited)
                                                          (RecvShift s ': visited) s)
  PhaseStarts1 visited (SendD a s) = PhaseStarts0 (SendD a s ': visited)
                                                  (SendD a s ': visited) s
  PhaseStarts1 visited (RecvD a s) = PhaseStarts0 (RecvD a s ': visited)
                                                  (RecvD a s ': visited) s
  PhaseStarts1 visited (SendC s t) = PhaseStarts0 (SendC s t ': visited)
                                                  (SendC s t ': visited) t
  PhaseStarts1 visited (RecvC s t) = PhaseStarts0 (RecvC s t ': visited)
                                                  (RecvC s t ': visited) t
  PhaseStarts1 visited (External s t) = PhaseStarts0 (External s t ': visited)
                                                     (External s t ': visited) s
                                    :++ PhaseStarts0 (External s t ': visited)
                                                     (External s t ': visited) t
  PhaseStarts1 visited (Internal s t) = PhaseStarts0 (Internal s t ': visited)
                                                     (Internal s t ': visited) s
                                    :++ PhaseStarts0 (Internal s t ': visited)
                                                     (Internal s t ': visited) t

-- Compute the starts of phases.
type PhaseStarts s = s ': (PhaseStarts1 '[] s)

type family MaybeMaximum (ns::[Maybe Nat]) :: Maybe Nat where
  MaybeMaximum '[ n ] = n
  MaybeMaximum (n ': ns) = MaybeMax n (MaybeMaximum ns)

type family GlobalBounds0 (ss::[Session]) :: [Maybe Nat] where
  GlobalBounds0 '[] = '[]
  GlobalBounds0 (s ': ss) = LocalBounds s ': GlobalBounds0 ss

type GlobalBounds s = MaybeMaximum (GlobalBounds0 (PhaseStarts s))

class IxMonad m where
  return :: a -> m k k a
  (>>=) :: m k1 k2 a -> (a -> m k2 k3 b) -> m k1 k3 b
  (>>) :: m k1 k2 a -> m k2 k3 b -> m k1 k3 b
  fail :: String -> m k1 k2 a

  m >> n = m >>= const n
  fail = error

-- Taken from Coroutine-0.1.0.0

newtype WM m x y a = LiftWM { runWM :: m a }
instance Prelude.Monad m => IxMonad (WM m) where
    return x = LiftWM (P.return x)
    m >>= f  = LiftWM (runWM m P.>>= runWM . f)
    m >> n   = LiftWM (runWM m P.>> runWM n)
    fail s   = LiftWM (P.fail s)

data ExecState = ExecState [IORef (ExtDiQueue Comms)] (IORef (ExtDiQueue Comms))

data IState :: PState -> PState -> * -> * where
  IState :: (ExecState -> IO (a,ExecState)) -> IState env env' a

runIState :: IState env env' a -> (ExecState -> IO (a,ExecState))
runIState (IState f) = f

execIState :: IState (Running env s) Term () -> (ExecState -> IO ())
execIState (IState f) ex = f ex P.>> P.return ()

instance IxMonad IState where
  return a = IState $ \s -> P.return (a,s)
  v >>= f = IState $ \i -> runIState v i P.>>= \(a,m) -> runIState (f a) m

liftIO :: IO a -> IState env env a
liftIO io = IState $ \i -> io P.>>= \a -> P.return (a,i)

-- This should be its own module
data Comms where
  COne :: Comms
  CShift :: Comms
  CData :: a -> Comms
  CChoice :: Bool -> Comms
  CChan :: (ExtDiQueue Comms) -> Comms
  CForward :: (ExtDiQueue Comms) -> Comms

myReadP :: IORef (ExtDiQueue Comms) -> IO Comms
myReadP qr = readIORef qr P.>>= atomically . safeReadP P.>>= \x ->
             case x of
               CForward q' -> atomicWriteIORef qr q' P.>> myReadP qr
               _ -> P.return x

myReadC :: IORef (ExtDiQueue Comms) -> IO Comms
myReadC qr = readIORef qr P.>>= atomically . safeReadC P.>>= \x ->
             case x of
               CForward q' -> atomicWriteIORef qr q' P.>> myReadC qr
               _ -> P.return x

myWriteP :: DiQueue q => IORef (q Comms) -> Comms -> IO ()
myWriteP qr x = readIORef qr P.>>= \q -> atomically (safeWriteP q x)

myWriteC :: DiQueue q => IORef (q Comms) -> Comms -> IO ()
myWriteC qr x = readIORef qr P.>>= \q -> atomically (safeWriteC q x)

myWaitToReadP :: DiQueue q => IORef (q Comms) -> IO ()
myWaitToReadP qr = readIORef qr P.>>= atomically . waitToP

myWaitToReadC :: DiQueue q => IORef (q Comms) -> IO ()
myWaitToReadC qr = readIORef qr P.>>= atomically . waitToC

runtop :: Process '[] One -> IO ()
runtop p = newBDiQueue True 1 P.>>= \q ->
           newIORef (ExtDiQueue q) P.>>= \q1 -> 
           newIORef (ExtDiQueue q) P.>>= \q2 -> 
	   forkIO (execIState p (ExecState [] q1)) P.>>
	   yield P.>>
	   myReadC q2 P.>>= \COne ->
	   putStrLn ("Finished") P.>>
	   P.return ()

wait :: (Inbounds n env ~ True
        ,Index n env ~ Just t
	, Unfold t ~ One)
     => SNat n 
     -> IState (Running env s) 
               (Running (Update n Nothing env) s) ()
wait n = IState $ \(ExecState env self) ->
         myReadC (index (fromSing n) env) P.>>= \COne ->
	 P.return ((),ExecState env self)

close :: (AllNothing env ~ True
         ,Unfold s ~ One)
      => IState (Running env s) Term ()
close = IState $ \(ExecState _ self) ->  
        myWriteP self COne P.>> 
	P.return ((),ExecState [] self)

-- Seems like unsafeCoerce should be unneeded
snatLen :: [a] -> SNat n
snatLen [] = unsafeCoerce SZ
snatLen (_:xs) = unsafeCoerce (SS (unsafeCoerce (natLen xs)))

type family VarArgs (n::Nat) (args1::[a]) (base::b) :: * where
  VarArgs n '[] base = base
  VarArgs n (x ': xs) base = SNat n -> VarArgs (S n) xs base

type Process env s = (AllWellformed env ~ True) => 
   VarArgs Z env (IState (Running env s) Term ())

-- To go with VarArgs we need a way to pass SNats to functions
passargs :: SNat n -> SList l -> (VarArgs n l base) -> base
passargs _ SNil p = p
passargs n (SCons _ xs) p = passargs (SS n) xs (p n)

-- TODO allow for argument channels to vary modulo RTEq
cut :: forall l env s t .
       (NoDups l ~ True
       ,AllInbounds l env ~ True
       ,AllJusts l env ~ True
       ,Wellformed t ~ True
       ,AllWellformed (Indices l env) ~ True
       ,SingI (IsPos t)
       ,SingI (GlobalBounds t))
    => Process (Indices l env) t
    -> SList l
    -> IState (Running env s) 
              (Running ((Removes l env) :++ '[ Just t ]) s)
	      (SNat (NatLen env))
cut p cs = 
  IState $ \(ExecState bigenv self) ->
  (case bounds of
     Nothing -> newUDiQueueE polarity
     Just n -> newBDiQueueE polarity (natToInt n)) P.>>= \q ->
  newIORef q P.>>= \q1 ->
  newIORef q P.>>= \q2 ->
  let newenv = (indices (fromSing cs) bigenv)
  in forkIO (execIState (passargs SZ cs (unsafeCoerce p))
                        (ExecState newenv q1)) P.>>
     yield P.>>
     P.return (snatLen bigenv,ExecState (bigenv++[q2]) self)
  where polarity :: Bool
        polarity = fromSing (sing :: SBool (IsPos t))
        bounds :: Maybe Nat
        bounds = fromSing (sing :: SMaybe (GlobalBounds t))

forward :: forall env n s t.
           (Inbounds n env ~ True
           ,AllButNothing n env ~ True
	   ,Index n env ~ Just t
	   ,RTEq s t ~ True
           ,SingI (IsPos s))
        => SNat n -> IState (Running env s) Term ()
forward n = IState $ \(ExecState env self) ->
     case polarity of
       True -> myWaitToReadC (index (fromSing n) env) P.>>
               readIORef (index (fromSing n) env) P.>>= \q ->
               myWriteP self (CForward q) P.>>
               P.return undefined
       False -> myWaitToReadP self P.>>
                readIORef self P.>>= \q ->
                myWriteC (index (fromSing n) env) (CForward q) P.>>
                P.return undefined
  where polarity :: Bool
        polarity = fromSing (sing :: SBool (IsPos s))


tailcut :: (NoDups l ~ True
           ,AllInbounds l env ~ True
           ,AllJusts l env ~ True
	   ,RTEq s t ~ True
	   ,AllWellformed (Indices l env) ~ True)
        => Process (Indices l env) t
        -> SList l
        -> IState (Running env s) Term () 
tailcut p cs = 
  IState $ \(ExecState bigenv self) ->
  let newenv = (indices (fromSing cs) bigenv)
  in (runIState (passargs SZ cs (unsafeCoerce p))
                        (ExecState newenv self))

recvdr :: (Unfold u ~ (RecvD a t))
       => IState (Running env u) (Running env t) a
recvdr = IState $ \(ExecState env self) ->
         myReadP self P.>>= \(CData x) ->
	 P.return ((unsafeCoerce x),ExecState env self)

recvdl :: (Inbounds n env ~ True
        ,Index n env ~ Just u 
	,Unfold u ~ (SendD a t))
       => SNat n
       -> IState (Running env s) 
                 (Running (Update n (Just t) env) s) a
recvdl n = IState $ \(ExecState env self) ->
           myReadC (index (fromSing n) env) P.>>= \(CData x) ->
	   P.return ((unsafeCoerce x),ExecState env self)

senddr :: (Unfold u ~ (SendD a s))
       => a -> IState (Running env u) (Running env s) ()
senddr x = IState $ \(ExecState env self) ->
           myWriteP self (CData x) P.>>
	   P.return ((),ExecState env self)

senddl :: (Inbounds n env ~ True
          ,Index n env ~ Just u
	  ,Unfold u ~ (RecvD a s))
       => SNat n
       -> a
       -> IState (Running env t) (Running (Update n (Just s) env) t) ()
senddl n x = IState $ \(ExecState env self) ->
             myWriteC (index (fromSing n) env) (CData x) P.>>
	     P.return ((),ExecState env self)

sendcr :: (Inbounds n env ~ True
          ,Index n env ~ Just u
	  ,RTEq u s ~ True)
       => SNat n
       -> IState (Running env (SendC s t))
                 (Running (Update n Nothing env) t)
		 ()
sendcr n = IState $ \(ExecState env self) ->
           readIORef (index (fromSing n) env) P.>>= \q ->
           myWriteP self (CChan q) P.>>
	   P.return ((),ExecState env self)

sendcl :: (Inbounds n env ~ True
          ,Inbounds c env ~ True
	  ,Index n env ~ Just u
	  ,Unfold u ~ (RecvC s1 s2)
	  ,Index c env ~ Just d
	  ,RTEq s1 d ~ True)
       => SNat n
       -> SNat c
       -> IState (Running env t)
                 (Running (Update n (Just s2) (Update n Nothing env)) t)
		 ()
sendcl n c =
  IState $ \(ExecState env self) ->
  readIORef (index (fromSing c) env) P.>>= \q ->
  myWriteC (index (fromSing n) env) (CChan q) P.>>
  P.return ((),ExecState env self)

recvcr :: (Unfold u ~ (RecvC s1 s2))
       => IState (Running env u)
                 (Running (env :++ '[ Just s1]) s2)
		 (SNat (NatLen env))
recvcr = IState $ \(ExecState env self) ->
         myReadP self P.>>= \(CChan c) ->
         newIORef c P.>>= \newc -> 
	 P.return (snatLen env,ExecState (env++[newc]) self)

recvcl :: (Inbounds n env ~ True
          ,Index n env ~ Just u
	  ,Unfold u ~ (SendC s1 s2))
       => SNat n
       -> IState (Running env t)
	         (Running ((Update n (Just s2) env) :++ '[ Just s1 ]) t)
                 (SNat (NatLen env))
recvcl n = IState $ \(ExecState env self) ->
           myReadC (index (fromSing n) env) P.>>= \(CChan c) ->
           newIORef c P.>>= \newc ->
	   P.return (snatLen env,ExecState (env++[newc]) self)

extchoir :: (Unfold u ~ (External s1 s2))
         => IState (Running env s1) t a
         -> IState (Running env s2) t a
	 -> IState (Running env u) t a
extchoir l r = IState $ \(ExecState env self) ->
               myReadP self P.>>= \(CChoice c) ->
	       case c of
	         True -> runIState l (ExecState env self)
		 False -> runIState r (ExecState env self)

extchoil :: (Inbounds n env ~ True
            ,Index n env ~ Just u
	    ,Unfold u ~ (Internal s1 s2))
	  => SNat n
	  -> IState (Running (Update n (Just s1) env) t) k a
	  -> IState (Running (Update n (Just s2) env) t) k a
	  -> IState (Running env t) k a
extchoil n l r = IState $ \(ExecState env self) ->
                 myReadC (index (fromSing n) env) P.>>= \(CChoice c) ->
		 case c of
		   True -> runIState l (ExecState env self)
		   False -> runIState r (ExecState env self)

intchoil1 :: (Inbounds n env ~ True
             ,Index n env ~ Just u
	     ,Unfold u ~ (External s1 s2))
          => SNat n
	  -> IState (Running env t) (Running (Update n (Just s1) env) t) ()
intchoil1 n = IState $ \(ExecState env self) ->
              myWriteC (index (fromSing n) env) (CChoice True) P.>>
	      P.return ((),ExecState env self)

intchoil2 :: (Inbounds n env ~ True
             ,Index n env ~ Just u
	     ,Unfold u ~ (External s1 s2))
          => SNat n
	  -> IState (Running env t) (Running (Update n (Just s2) env) t) ()
intchoil2 n = IState $ \(ExecState env self) ->
              myWriteC (index (fromSing n) env) (CChoice False) P.>>
	      P.return ((),ExecState env self)

intchoir1 :: (Unfold u ~ (Internal s1 s2))
          => IState (Running env u) (Running env s1) ()
intchoir1 = IState $ \(ExecState env self) ->
            myWriteP self (CChoice True) P.>>
	    P.return ((),ExecState env self)

intchoir2 :: (Unfold u ~ (Internal s1 s2))
          => IState (Running env u) (Running env s2) ()
intchoir2 = IState $ \(ExecState env self) ->
            myWriteP self (CChoice False) P.>>
	    P.return ((),ExecState env self)

sendsr :: (Unfold u ~ (SendShift s))
       => IState (Running env u) (Running env s) ()
sendsr = IState $ \(ExecState env self) ->
         myWriteP self CShift P.>>
	 P.return ((),ExecState env self)

sendsl :: (Inbounds n env ~ True
          ,Index n env ~ Just u
	  ,Unfold u ~ RecvShift s)
       => SNat n
       -> IState (Running env t) (Running (Update n (Just s) env) t) ()
sendsl n = IState $ \(ExecState env self) ->
           myWriteC (index (fromSing n) env) CShift P.>>
	   P.return ((),ExecState env self)

recvsr :: (Unfold u ~ (RecvShift s))
       => IState (Running env u) (Running env s) ()
recvsr = IState $ \(ExecState env self) ->
         myReadP self P.>>= \CShift ->
         readIORef self P.>>= atomically . swapDir P.>>
	 P.return ((),ExecState env self)

recvsl :: (Inbounds n env ~ True
          ,Index n env ~ Just u
	  ,Unfold u ~ SendShift s)
       => SNat n
       -> IState (Running env t) (Running (Update n (Just s) env) t) ()
recvsl n = IState $ \(ExecState env self) ->
           let ch = (index (fromSing n) env)
           in myReadC ch P.>>= \CShift ->
              readIORef ch P.>>= atomically . swapDir P.>>
	      P.return ((),ExecState env self)

-- Apparently, using Process is ambiguous here
t0 :: IState (Running '[] One) Term ()
t0 = close

t1 :: Process '[Just One] One
t1 c = do wait c
          close

t2 :: IState (Running '[] One) Term ()
t2 = do c <- cut t0 SNil
        liftIO $ putStrLn ("cut in "++show (fromSing c))
        wait c
        close

t3 :: Process '[Just (SendD Int (SendD Float One))] One
t3 c = do x <- recvdl c
          y <- recvdl c
	  liftIO $ putStrLn ("Got "++show x++" and "++show y)
          wait c
          close

t4 :: Process '[Just (SendD Int (SendD Float One))] One
t4 c = do d <- cut t3 (SCons c SNil)
          liftIO $ putStrLn ("cut in "++show (fromSing d))
          wait d
          close

t5 :: Process '[] (SendD Int (SendD Float One))
t5 = do senddr 3
        senddr 84.72
	close

t6 :: Process '[] One
t6 = do a <- cut t5 SNil
        b <- cut t3 (SCons a SNil)
	wait b
	close

t7 :: Process '[] (SendC (SendD Int (SendD Float One)) One)
t7 = do a <- cut t5 SNil
        sendcr a
	close

t8 :: Process '[] One
t8 = do a <- cut t7 SNil
        b <- recvcl a
	c <- cut t3 (SCons b SNil)
	wait c
	wait a
	close

type Stream a = (Mu (External (RecvShift One) 
                              (RecvShift (SendD a (SendShift Var)))))

printstream :: (Show a) => Nat -> Process '[Just (Stream a)] One
printstream Z c = do intchoil1 c
		     sendsl c
                     wait c
		     close
printstream (S n) c = do intchoil2 c
                         sendsl c
                         x <- recvdl c
			 recvsl c
			 liftIO $ putStrLn ("Got "++show x)
			 b <- cut (printstream n) (SCons c SNil)
			 forward b


countup :: Nat -> Process '[] (Stream Nat)
countup n = extchoir 
              (do recvsr
	          close)
              (do recvsr
	          senddr n
		  sendsr
	          a <- cut (countup (S n)) SNil
	          forward a)

silter :: (a -> Bool) -> Process '[Just (Stream a)] (Stream a)
silter f c = extchoir
               (do recvsr
	           intchoil1 c
		   sendsl c
	           wait c
		   close)
	       (do recvsr
	           intchoil2 c
		   sendsl c
	           x <- recvdl c
		   recvsl c
		   b <- cut (silter f) (SCons c SNil)
		   case f x of
		     True -> do senddr x
				sendsr
		                forward b
		     False -> do intchoil2 b
		                 sendsl b
				 forward b)

natsub :: Nat -> Nat -> Nat
natsub n Z = n
natsub (S n) (S m) = natsub n m

divisible :: Nat -> Nat -> Bool
divisible n Z = True
divisible n m = (n <= m) && (divisible n (natsub m n))
                   
seive :: Process '[Just (Stream Nat)] (Stream Nat)
seive c = extchoir
          (do intchoil1 c
	      sendsl c
	      wait c
	      recvsr
	      close)
	  (do intchoil2 c
	      sendsl c
	      x <- recvdl c
	      recvsl c
	      recvsr
	      senddr x
	      sendsr
	      b <- cut (silter (not . divisible x)) (SCons c SNil)
	      tailcut seive (SCons b SNil))

t9 :: Process '[] One
t9 = do a <- cut (countup (S (S Z))) SNil
        b <- cut seive (SCons a SNil)
        c <- cut (printstream (S (S (S (S (S Z)))))) (SCons b SNil)
	wait c
	close

type Bag a = (Mu (External (RecvD a Var) 
                           (RecvShift (Internal One 
			                        (SendD a (SendShift Var))))))

empty :: Process '[] (Bag Nat)
empty = extchoir
          (do x <- recvdr
	      tailcut (leaf x) SNil)
	  (do recvsr
	      intchoir1
	      close)

leaf :: Nat -> Process '[] (Bag Nat)
leaf x = extchoir
          (do y <- recvdr
	      a <- cut (leaf x) SNil
	      b <- cut (leaf y) SNil
	      tailcut binary (SCons a (SCons b SNil)))
	  (do recvsr
	      intchoir2
	      senddr x
	      sendsr
	      tailcut empty SNil)

-- Invariant (size l == size r || size l + 1 == size r) 
binary :: Process '[Just (Bag Nat), Just (Bag Nat)] (Bag Nat)
binary l r = extchoir
               (do x <- recvdr
	           intchoil1 l
		   senddl l x
		   tailcut binary (SCons r (SCons l SNil)))
               (do intchoil2 r
		   sendsl r
		   extchoil r
		     (do wait r
		         intchoil2 l
			 sendsl l
		         extchoil l
			   (do wait l
			       recvsr
			       intchoir1
			       close)
			   (do x <- recvdl l
			       recvsr
			       intchoir2
			       senddr x
			       sendsr
			       recvsl l
			       forward l))
		     (do x <- recvdl r
		         recvsr
		         intchoir2
			 senddr x
			 sendsr
			 recvsl r
			 tailcut binary (SCons r (SCons l SNil))))

fromList :: [Nat] -> Process '[] (Bag Nat)
fromList [] = empty
fromList xs = do a <- cut empty SNil
                 tailcut (fromListGo xs) (SCons a SNil)

fromListGo :: [Nat] -> Process '[Just (Bag Nat)] (Bag Nat)
fromListGo [] c = forward c
fromListGo (x:xs) c = do intchoil1 c
                         senddl c x
		         tailcut (fromListGo xs) (SCons c SNil)

bagContents :: (Show a) => Process '[Just (Bag a)] One
bagContents c = do intchoil2 c
                   sendsl c
                   extchoil c
		     (do wait c
		         close)
		     (do x <- recvdl c
		         recvsl c
		         liftIO $ putStrLn ("Got "++show x)
			 tailcut bagContents (SCons c SNil))

t10 :: Process '[] One
t10 = do a <- cut (fromList [Z, S Z, S (S Z), S (S (S Z))]) SNil
         tailcut bagContents (SCons a SNil)
