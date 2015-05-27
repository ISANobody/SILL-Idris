{-# LANGUAGE GADTs, DataKinds, KindSignatures, TypeFamilies, TypeOperators #-}
{-# LANGUAGE TemplateHaskell, QuasiQuotes, PolyKinds, UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
import Control.Concurrent
import Control.Concurrent.Chan
import Unsafe.Coerce
import Data.Singletons
import Data.Singletons.TH
import Data.Singletons.Prelude.Base
import Data.Singletons.Prelude.List
import Data.Singletons.Prelude.Eq

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

  asmem :: (Eq k) => k -> [(k,v)] -> Bool
  asmem _ [] = False
  asmem x ((k,_):ys) = if x == k then True else asmem x ys

  aslook :: (Eq k) => k -> [(k,v)] -> v
  aslook x ((k,v):ys) = if x == k then v else aslook x ys

  asmap :: (v -> v') -> [(k,v)] -> [(k,v')]
  asmap _ [] = []
  asmap f ((k,v):ys) = (k,f v):(asmap f ys)

  assub :: (Eq k) => [(k,v)] -> [(k,v')] -> Bool
  assub [] _ = True
  assub ((x,_):xs) ys= if asmem x ys then assub xs ys else False
  |]



-- Tracking whether this is open or closed makes this type unpromotable
-- Choice is over Nat b/c String is unpromotable
data Session where
  Mu :: Session -> Session
  Var :: Session
  SendD :: a -> Session -> Session
  One :: Session
  External :: Session -> Session -> Session
  Internal :: Session -> Session -> Session

-- TODO Add a wellformedness checker that ensures types are
-- 1) Contractive and w/o consecutive Mu's
-- 2) Closed
-- 3) Choices have no duplicates

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
type instance Subst x (External s1 s2) = External (Subst x s1) (Subst x s2)

type family Unfold (s::Session) :: Session
type instance Unfold (Mu x) = Subst (Mu x) x
type instance Unfold (SendD a s) = SendD a s
type instance Unfold One = One
type instance Unfold (External s1 s2) = External s1 s2

-- TODO actually do circular coinduction
type family RTEq (s::Session) (t::Session) :: Bool
type instance RTEq (Mu x) One = RTEq (Unfold (Mu x)) One
type instance RTEq (Mu x) (SendD a s) = RTEq (Unfold (Mu x)) (SendD a s)
type instance RTEq (Mu x) (Mu y) = RTEq (Unfold (Mu x)) (Unfold (Mu y))
type instance RTEq One (Mu y) = RTEq One (Unfold (Mu y))
type instance RTEq One One = True
type instance RTEq (SendD a s) (SendD a t) = RTEq s t
type instance RTEq (External s1 s2) (External t1 t2) = RTEq s1 t1 :&& RTEq s2 t2

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
  ExternalR :: (Unfold t ~ External s1 s2)
            => Process env s1 -> Process env s2 -> Process env t
  ExternalL1 :: (Inbounds n env ~ True
                ,Unfold (Index n env) ~ External s1 s2)
            => SNat n -> Process (Update n s1 env) t -> Process env t
  ExternalL2 :: (Inbounds n env ~ True
                ,Unfold (Index n env) ~ External s1 s2)
            => SNat n -> Process (Update n s2 env) t -> Process env t

data Comms where
  COne :: Comms
  CData :: a -> Comms
  CChoice :: Bool -> Comms

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
	go env (sr,sw) (ExternalR p1 p2) = do CChoice b <- readChan sr
	                                      if b
					      then go env (sr,sw) p1
					      else go env (sr,sw) p2
	go env self (ExternalL1 n p) = do let (r,w) = index (fromSing n) env
	                                  writeChan w (CChoice True)
					  go env self p
	go env self (ExternalL2 n p) = do let (r,w) = index (fromSing n) env
	                                  writeChan w (CChoice False)
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

t7 :: IO ()
t7 = interp (Bind t4 (RecvDL SZ (\f -> RecvDL SZ (\i -> Lift (print f) (Lift (print i) (Wait SZ Close))))))

type Stream a = Mu (External One (SendD a Var))

countup :: Nat -> Process '[] (Stream Nat)
countup n = Lift (print n) (ExternalR Close (SendDR n (Bind (countup (S n)) Forward)))

main :: IO ()
main = interp (Bind (countup Z)
		(ExternalL2 SZ (RecvDL SZ (\i -> Lift (print "rec")
		(ExternalL2 SZ (RecvDL SZ (\i -> Lift (print "rec")
		(ExternalL1 SZ (Wait SZ Close)))))))))
