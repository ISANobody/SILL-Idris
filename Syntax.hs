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
  data Nat = Z | S Nat deriving (Show,Eq)
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

  data Session where
    One :: Session
    SendD :: a -> Session -> Session
    RecvD :: a -> Session -> Session

  data PState where
    Term :: PState
    Running :: [Maybe Session] -> Session -> PState

  |]

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
  CChoice :: SNat n -> Comms
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
        ,Index n env ~ Just One)
     => SNat n 
     -> IState (Running env s) 
               (Running (Update n Nothing env) s) ()
wait n = IState $ \(ExecState env self) ->
         taggedRead (index (fromSing n) env) P.>>= \COne ->
	 P.return ((),ExecState env self)

close :: (AllNothing env ~ True)
      => IState (Running env One) Term ()
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
        ,Index n env ~ Just (SendD a t))
       => SNat n
       -> IState (Running env s) 
                 (Running (Update n (Just t) env) s) a
recvdl n = IState $ \(ExecState env self) ->
           taggedRead (index (fromSing n) env) P.>>= \(CData x) ->
	   P.return ((unsafeCoerce x),ExecState env self)

senddr :: a -> IState (Running env (SendD a s)) (Running env s) ()
senddr x = IState $ \(ExecState env self) ->
           taggedWrite self (CData x) P.>>
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

