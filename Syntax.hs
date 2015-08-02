{-# LANGUAGE RebindableSyntax, DataKinds #-}
{-# LANGUAGE GADTs, DataKinds, KindSignatures, TypeFamilies, TypeOperators #-}
{-# LANGUAGE TemplateHaskell, QuasiQuotes, PolyKinds, UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables, BangPatterns #-}

import Prelude hiding ((>>),(>>=),return)
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
  |]

data IState :: [Maybe Nat] -> [Maybe Nat] -> * -> * where
  IState :: ([Int] -> (a,[Int])) -> IState env env' a

runIState :: IState env env' a -> ([Int] -> (a,[Int]))
runIState (IState f) = f

return :: a -> IState s s a
return a = IState $ \s -> (a, s)

(>>=) :: IState env0 env1 a -> (a -> IState env1 env2 b) -> IState env0 env2 b
v >>= f = IState $ \i -> let (a, m) = runIState v i
                         in runIState (f a) m

(>>) :: IState i m a -> IState m o b -> IState i o b
v >> w = v >>= \_ -> w

wait :: (Inbounds n env ~ True
        ,Index n env ~ Just Z)
     => SNat n -> IState env (Update n Nothing env) ()
wait n = undefined

close :: (AllNothing env ~ True)
      => IState env env ()
close = undefined

cut :: IState '[] env () -> IState env (env :++ '[ Just Z ]) (SNat (NatLen env))
cut = undefined

recv :: (Inbounds n env ~ True
        ,Index n env ~ Just (S i))
     => SNat n -> IState env (Update n (Just i) env) String
recv = undefined

t0 :: IState '[] '[] ()
t0 = close

t1 :: IState '[Just Z] '[Nothing] ()
t1 = do wait SZ
        close

t2 :: IState '[] '[Nothing] ()
t2 = do c <- cut t0
        wait c
        close

t3 :: IState '[Just (S (S Z))] '[Nothing] ()
t3 = do x <- recv SZ
        y <- recv SZ
        wait SZ
        close
