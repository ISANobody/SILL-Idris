{-# LANGUAGE RebindableSyntax, DataKinds #-}
{-# LANGUAGE GADTs, DataKinds, KindSignatures, TypeFamilies, TypeOperators #-}
{-# LANGUAGE TemplateHaskell, QuasiQuotes, PolyKinds, UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables, BangPatterns, Rank2Types #-}

import Unsafe.Coerce
import Prelude hiding ((>>),(>>=),return,fail)
import qualified Prelude as P
import Data.Singletons
import Data.Singletons.Prelude
import Data.Singletons.TH
import Data.Singletons.Prelude.List

singletons [d|
  data Nat = Z | S Nat deriving (Show)
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

  indices :: [Nat] -> [a] -> [a]
  indices [] _ = []
  indices (n:ns) xs = (index n xs) : indices ns xs

  removes :: [Nat] -> [Maybe a] -> [Maybe a]
  removes [] xs = xs
  removes (n:ns) xs = removes ns (update n Nothing xs)

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

data IState :: Maybe [Maybe Nat] -> Maybe [Maybe Nat] -> * -> * where
  IState :: ([Int] -> IO (a,[Int])) -> IState env env' a

runIState :: IState env env' a -> ([Int] -> IO (a,[Int]))
runIState (IState f) = f

instance IxMonad IState where
  return a = IState $ \s -> P.return (a,s)
  v >>= f = IState $ \i -> runIState v i P.>>= \(a,m) -> runIState (f a) m

liftIO :: IO a -> IState env env a
liftIO io = IState $ \i -> io P.>>= \a -> P.return (a,i)

wait :: (Inbounds n env ~ True
        ,Index n env ~ Just Z)
     => SNat n -> IState (Just env) (Just (Update n Nothing env)) ()
wait n = IState $ \i -> putStrLn ("wait "++show (fromSing n)) P.>> P.return ((),i)

close :: (AllNothing env ~ True)
      => IState (Just env) Nothing ()
close = IState $ \i -> putStrLn "close" P.>> P.return ((),i)

type family VarArgs (n::Nat) (args1::[a]) (args2::[a]) :: * where
  VarArgs n '[] env = IState (Just env) Nothing ()
  VarArgs n (x ': xs) env = SNat n -> VarArgs (S n) xs (env :++ '[ x ])

type Process env = VarArgs Z env '[]

-- Seems like unsafeCoerce should be unneeded
snatLen :: [a] -> SNat n
snatLen [] = unsafeCoerce SZ
snatLen (_:xs) = unsafeCoerce (SS (unsafeCoerce (natLen xs)))

-- TODO Check that l has Just x for each binding
-- TODO Check for duplicate bindings
cut :: (AllInbounds l env ~ True)
    => Process (Indices l env)
    -> SList l
    -> IState (Just env) (Just ((Removes l env) :++ '[ Just Z ])) (SNat (NatLen env))
cut p cs = IState $ \i -> putStrLn "cut" P.>> P.return (snatLen i,i)

recv :: (Inbounds n env ~ True
        ,Index n env ~ Just (S i))
     => SNat n -> IState (Just env) (Just (Update n (Just i) env)) String
recv = undefined

-- Apparently, using Process is ambiguous here
t0 :: IState (Just '[]) Nothing ()
t0 = close

t1 :: Process '[Just Z]
t1 c = do wait c
          close

t2 :: IState (Just '[]) Nothing ()
t2 = do c <- cut t0 SNil
        liftIO $ putStrLn ("cut in "++show (fromSing c))
        wait c
        close

t3 :: Process '[Just (S (S Z))]
t3 c = do x <- recv c
          y <- recv c
          wait c
          close

t4 :: Process '[Just (S (S Z))]
t4 c = do d <- cut t3 (SCons SZ SNil)
          liftIO $ putStrLn ("cut in "++show (fromSing d))
          wait d
          close
