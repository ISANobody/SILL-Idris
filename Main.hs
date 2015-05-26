{-# LANGUAGE GADTs, DataKinds, KindSignatures, TypeFamilies, TypeOperators #-}
{-# LANGUAGE TemplateHaskell, QuasiQuotes, PolyKinds, UndecidableInstances #-}
import Control.Concurrent
import Control.Concurrent.Chan
import Unsafe.Coerce
import Data.Map
import Data.Singletons
import Data.Singletons.TH
import Data.Singletons.Prelude.List

singletons [d|
  data Nat = Z | S Nat
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
  |]

-- Tracking whether this is open or closed makes this type unpromotable
-- Choice is over Nat b/c String is unpromotable
data Session where
  Mu :: Session -> Session
  Var :: Session
  SendD :: a -> Session -> Session
  One :: Session

type family  SynEq (s::Session) (t::Session) :: Bool
type instance SynEq One One = True
type instance SynEq One (SendD b t) = False
type instance SynEq One Var = False
type instance SynEq One (Mu t) = False
type instance SynEq (SendD a s) One = False
type instance SynEq (SendD a s) (SendD a t) = SynEq s t
type instance SynEq (SendD a s) Var = False
type instance SynEq (SendD a s) (Mu t) = False

type family Subst (s::Session) (t::Session) :: Session
type instance Subst x Var = x
type instance Subst x (Mu y) = Mu y
type instance Subst x One = One
type instance Subst x (SendD a s) = (SendD a (Subst x s))

type family Unfold (s::Session) :: Session
type instance Unfold (Mu x) = Subst (Mu x) x
type instance Unfold (SendD a s) = SendD a s
type instance Unfold One = One

-- TODO actually do circular coinduction
type family RTEq (s::Session) (t::Session) :: Bool
type instance RTEq (Mu x) One = RTEq (Unfold (Mu x)) One
type instance RTEq (Mu x) (SendD a s) = RTEq (Unfold (Mu x)) (SendD a s)
type instance RTEq (Mu x) (Mu y) = RTEq (Unfold (Mu x)) (Unfold (Mu y))
type instance RTEq One (Mu y) = RTEq One (Unfold (Mu y))
type instance RTEq One One = True
type instance RTEq (SendD a s) (SendD a t) = RTEq s t

-- Thanks to Mu's we might always have a syntactic mismatch between the declared
-- type of a process's channel and the most natural way to write these types. As
-- a result, we have a lot of (Unfold t ~ s) constraints. The more general 
-- (RTEq t s ~ True) seems to confuse the constraint solver. I believe upcoming
-- injective type families would solve this.
data Process :: [Session] -> Session -> * where
  Close :: (Unfold t ~ One) => Process '[] t
  Wait :: (Inbounds n env ~ True
          ,Unfold (Index n env) ~ One) => SNat n 
	-> Process (Remove n env) s -> Process env s
  SendDR :: (Unfold t ~ SendD a s) => a -> Process env s -> Process env t
  RecvDL :: (Inbounds n env ~ True
            ,Unfold (Index n env) ~ SendD a t) => SNat n
        -> (a -> Process (Update n t env) s) -> Process env s
  Forward :: (RTEq t s ~ True) => Process ('[t]) s
  Bind :: Process '[] t -> Process (t ': env) s -> Process env s
  Lift :: IO () -> Process env s -> Process env s

data Comms where
  COne :: Comms
  CData :: a -> Comms

type MyChan = (Chan Comms,Chan Comms)

interp :: Process '[] One -> IO ()
interp pin = do selfr <- newChan
                selfw <- newChan
	        go [] (selfr,selfw) pin
  where go :: [MyChan] -> (MyChan) -> Process env s -> IO ()
        go env (_,sw) Close = writeChan sw COne
	go env self (Wait n p) = do let (r,w) = index (fromSing n) env
	                            COne <- readChan r
	                            go env self p
        go env (sr,sw) (SendDR x p) = do writeChan sw (CData x)
	                                 go env (sr,sw) p
	go env self (RecvDL n f) = do let (r,w) = index (fromSing n) env
	                              (CData x) <- readChan r
	                              go env self (f (unsafeCoerce x))
	go env self (Bind p1 p2) = do sr <- newChan
	                              sw <- newChan
	                              forkIO (go [] (sr,sw) p1)
	                              go ((sw,sr):env) self p2
        go env self (Lift io p) = do io
	                             go env self p

t1 :: Process '[] (Mu One)
t1 = Close

t1' :: Process '[One] (Mu One)
t1' = Forward

t2 :: Process '[] (SendD Int One)
t2 = SendDR 5 Close

t3 :: Process '[] (SendD Float (SendD Int One))
t3 = SendDR 5 (SendDR 6 Close)

t4 :: Process '[] (SendD Float (SendD Int One))
t4 = SendDR 5.7 (SendDR 8 Close)

t5 :: Process '[SendD Int One] (SendD String One)
t5 = RecvDL SZ (\i -> SendDR (show i) (Wait SZ Close))

t6 :: Process '[] (Mu (SendD String Var))
t6 = SendDR "foo" (Bind t6 Forward)

countup :: Nat -> Process '[] (Mu (SendD Nat Var))
countup n = SendDR n (Bind (countup (S n)) Forward)

main :: IO ()
main = interp (Bind t4 (RecvDL SZ (\f -> RecvDL SZ (\i -> Lift (print f) (Lift (print i) (Wait SZ Close))))))
