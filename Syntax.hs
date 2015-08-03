{-# LANGUAGE RebindableSyntax, DataKinds #-}
{-# LANGUAGE GADTs, DataKinds, KindSignatures, TypeFamilies, TypeOperators #-}
{-# LANGUAGE TemplateHaskell, QuasiQuotes, PolyKinds, UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables, BangPatterns, Rank2Types #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

import Control.Concurrent
import Unsafe.Coerce
import Prelude hiding ((>>),(>>=),return,fail)
import qualified Prelude as P
import Data.Singletons
import Data.Singletons.Prelude
import Data.Singletons.TH
import Data.Singletons.Prelude.List

singletons [d|
  data Nat = Z | S Nat deriving (Show,Eq,Ord)
  |]

promote [d|
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

  subst :: Session -> Session -> Session
  subst _ One = One
  subst _ (Mu x) = Mu x
  subst x Var = x
  subst x (SendD a s) = SendD a (subst x s)
  subst x (External s1 s2) = External (subst x s1) (subst x s2)
  subst x (Internal s1 s2) = Internal (subst x s1) (subst x s2)

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

-- Helper function that shouldn't need to be defined. This should just be:
-- all2 (RTEq0 ...) cs ds
type family RTEq3 (hyp::[(Session,Session)]) (cs::[Session]) (ds::[Session])
  :: Bool where
  RTEq3 hyp '[] '[] = True
  RTEq3 hyp (x ': xs) (y ': ys) = RTEq0 hyp x y :&& RTEq3 hyp xs ys

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

data ExecState = ExecState [BiChan Comms] (BiChan Comms)

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
  CData :: a -> Comms
  CChoice :: Bool -> Comms
  CChan :: BiChan Comms -> Comms

data RWTag = RTag | WTag

data TaggedChan :: RWTag -> * -> * where
  Recv :: Chan a -> TaggedChan RTag a
  Send :: Chan a -> TaggedChan WTag a

type BiChan a = (TaggedChan RTag a,TaggedChan WTag a)

taggedRead :: BiChan a -> IO a
taggedRead (Recv c,Send _) = readChan c
taggedWrite :: BiChan Comms -> Comms -> IO ()
taggedWrite (Recv _,Send c) x = writeChan c x
taggedNew :: IO (BiChan a)
taggedNew = newChan P.>>= \ch -> P.return (Recv ch,Send ch)

runtop :: Process '[] One -> IO ()
runtop p = taggedNew P.>>= \(ar,aw) ->
           taggedNew P.>>= \(br,bw) ->
	   forkIO (execIState p (ExecState [] (br,aw))) P.>>
	   yield P.>>
	   taggedRead (ar,bw) P.>>= \COne ->
	   putStrLn ("Finished") P.>>
	   P.return ()

wait :: (Inbounds n env ~ True
        ,Index n env ~ Just t
	, Unfold t ~ One)
     => SNat n 
     -> IState (Running env s) 
               (Running (Update n Nothing env) s) ()
wait n = IState $ \(ExecState env self) ->
         taggedRead (index (fromSing n) env) P.>>= \COne ->
	 P.return ((),ExecState env self)

close :: (AllNothing env ~ True
         ,Unfold s ~ One)
      => IState (Running env s) Term ()
close = IState $ \(ExecState _ self) ->  
        taggedWrite self COne P.>> 
	P.return ((),ExecState [] self)

-- Seems like unsafeCoerce should be unneeded
snatLen :: [a] -> SNat n
snatLen [] = unsafeCoerce SZ
snatLen (_:xs) = unsafeCoerce (SS (unsafeCoerce (natLen xs)))

type family VarArgs (n::Nat) (args1::[a]) (base::b) :: * where
  VarArgs n '[] base = base
  VarArgs n (x ': xs) base = SNat n -> VarArgs (S n) xs base

type Process env s = VarArgs Z env (IState (Running env s) Term ())

-- To go with VarArgs we need a way to pass SNats to functions
passargs :: SNat n -> SList l -> (VarArgs n l base) -> base
passargs _ SNil p = p
passargs n (SCons _ xs) p = passargs (SS n) xs (p n)

-- TODO allow for argument channels to vary modulo RTEq
cut :: (NoDups l ~ True
       ,AllInbounds l env ~ True
       ,AllJusts l env ~ True)
    => Process (Indices l env) t
    -> SList l
    -> IState (Running env s) 
              (Running ((Removes l env) :++ '[ Just t ]) s)
	      (SNat (NatLen env))
cut p cs = 
  IState $ \(ExecState bigenv self) ->
  taggedNew P.>>= \(ar,aw) ->
  taggedNew P.>>= \(br,bw) ->
  let newenv = (indices (fromSing cs) bigenv)
  in forkIO (execIState (passargs SZ cs (unsafeCoerce p))
                        (ExecState newenv (br,aw))) P.>>
     yield P.>>
     P.return (snatLen bigenv,ExecState (bigenv++[(ar,bw)]) self)

recvdl :: (Inbounds n env ~ True
        ,Index n env ~ Just u 
	,Unfold u ~ (SendD a t))
       => SNat n
       -> IState (Running env s) 
                 (Running (Update n (Just t) env) s) a
recvdl n = IState $ \(ExecState env self) ->
           taggedRead (index (fromSing n) env) P.>>= \(CData x) ->
	   P.return ((unsafeCoerce x),ExecState env self)

senddr :: (Unfold u ~ (SendD a s))
       => a -> IState (Running env u) (Running env s) ()
senddr x = IState $ \(ExecState env self) ->
           taggedWrite self (CData x) P.>>
	   P.return ((),ExecState env self)

sendcr :: (Inbounds n env ~ True
          ,Index n env ~ Just u
	  ,RTEq u s ~ True)
       => SNat n
       -> IState (Running env (SendC s t))
                 (Running (Update n Nothing env) t)
		 ()
sendcr n = IState $ \(ExecState env self) ->
           taggedWrite self (CChan (index (fromSing n) env)) P.>>
	   P.return ((),ExecState env self)

recvcl :: (Inbounds n env ~ True
          ,Index n env ~ Just u
	  ,Unfold u ~ (SendC s1 s2))
       => SNat n
       -> IState (Running env t)
	         (Running ((Update n (Just s2) env) :++ '[ Just s1 ]) t)
                 (SNat (NatLen env))
recvcl n = IState $ \(ExecState env self) ->
           taggedRead (index (fromSing n) env) P.>>= \(CChan c) ->
	   P.return (snatLen env,ExecState (env++[c]) self)

extchoir :: (Unfold u ~ (External s1 s2))
         => IState (Running env s1) t a
         -> IState (Running env s2) t a
	 -> IState (Running env u) t a
extchoir l r = IState $ \(ExecState env self) ->
               taggedRead self P.>>= \(CChoice c) ->
	       case c of
	         True -> runIState l (ExecState env self)
		 False -> runIState r (ExecState env self)

extchoil1 :: (Inbounds n env ~ True
             ,Index n env ~ Just u
	     ,Unfold u ~ (External s1 s2))
          => SNat n
	  -> IState (Running env t) (Running (Update n (Just s1) env) t) ()
extchoil1 n = IState $ \(ExecState env self) ->
              taggedWrite (index (fromSing n) env) (CChoice True) P.>>
	      P.return ((),ExecState env self)

extchoil2 :: (Inbounds n env ~ True
             ,Index n env ~ Just u
	     ,Unfold u ~ (External s1 s2))
          => SNat n
	  -> IState (Running env t) (Running (Update n (Just s2) env) t) ()
extchoil2 n = IState $ \(ExecState env self) ->
              taggedWrite (index (fromSing n) env) (CChoice False) P.>>
	      P.return ((),ExecState env self)

forward :: (Inbounds n env ~ True
           ,AllButNothing n env ~ True
	   ,Index n env ~ Just t
	   ,RTEq s t ~ True)
        => SNat n -> IState (Running env s) Term ()
forward n = IState $ \(ExecState env self) ->
            let (er,ew) = index (fromSing n) env
            in myThreadId P.>>= \tid1 ->
	       forkIO (zombie tid1 (fst self) ew) P.>>= \tid2 ->
	       zombie tid2 er (snd self) P.>>
	       P.return ((),ExecState env self)
  where zombie :: ThreadId
               -> (TaggedChan RTag Comms)
	       -> (TaggedChan WTag Comms)
	       -> IO ()
	zombie o (Recv r) (Send w) = 
	   readChan r P.>>= \x ->
	   writeChan w x P.>> (
	   case x of
	     COne -> do killThread o P.>> P.return ()
	     _ -> zombie o (Recv r) (Send w))


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

type Stream a = Mu (External One (SendD a Var))

printstream :: (Show a) => Nat -> Process '[Just (Stream a)] One
printstream Z c = do extchoil1 c
                     wait c
		     close
printstream (S n) c = do extchoil2 c
                         x <- recvdl c
			 liftIO $ putStrLn ("Got "++show x)
			 b <- cut (printstream n) (SCons c SNil)
			 forward b


countup :: Nat -> Process '[] (Stream Nat)
countup n = extchoir 
              (close)
              (do senddr n
	          a <- cut (countup (S n)) SNil
	          forward a)

silter :: (a -> Bool) -> Process '[Just (Stream a)] (Stream a)
silter f c = extchoir
               (do extchoil1 c
	           wait c
		   close)
	       (do extchoil2 c
	           x <- recvdl c
		   b <- cut (silter f) (SCons c SNil)
		   case f x of
		     True -> do senddr x
		                forward b
		     False -> do extchoil2 b
				 forward b)

natsub :: Nat -> Nat -> Nat
natsub n Z = n
natsub (S n) (S m) = natsub n m

divisible :: Nat -> Nat -> Bool
divisible n Z = True
divisible n m = (n <= m) && (divisible n (natsub m n))
                   

seive :: Process '[Just (Stream Nat)] (Stream Nat)
seive c = extchoir
          (do extchoil1 c
	      wait c
	      close)
	  (do extchoil2 c
	      x <- recvdl c
	      senddr x
	      b <- cut (silter (not . divisible x)) (SCons c SNil)
	      d <- cut seive (SCons b SNil)
	      forward d)

t9 :: Process '[] One
t9 = do a <- cut (countup (S (S Z))) SNil
        b <- cut seive (SCons a SNil)
        c <- cut (printstream (S (S (S (S (S Z)))))) (SCons b SNil)
	wait c
	close
