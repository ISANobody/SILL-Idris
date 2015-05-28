{-# LANGUAGE GADTs, DataKinds, KindSignatures, TypeFamilies, TypeOperators #-}
{-# LANGUAGE TemplateHaskell, QuasiQuotes, PolyKinds, UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables, BangPatterns #-}
{-# OPTIONS -Wall -fno-warn-unused-do-bind #-}
import Control.Concurrent
import Control.Concurrent.Chan
import Unsafe.Coerce
import Data.Singletons
import Data.Singletons.TH
import Data.Singletons.Prelude.Base
import Data.Singletons.Prelude.List
import Data.Singletons.Prelude.Eq
import Control.Exception

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
  Internal :: [Session] -> Session

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
  TailBind :: (RTEq t s ~ True) => Process '[] t -> Process '[] s
  Lift :: IO () -> Process env s -> Process env s
  ExternalR :: (Unfold t ~ External s1 s2)
            => Process env s1 -> Process env s2 -> Process env t
  ExternalL1 :: (Inbounds n env ~ True
                ,Unfold (Index n env) ~ External s1 s2)
            => SNat n -> Process (Update n s1 env) t -> Process env t
  ExternalL2 :: (Inbounds n env ~ True
                ,Unfold (Index n env) ~ External s1 s2)
            => SNat n -> Process (Update n s2 env) t -> Process env t
  InternalR :: (Unfold t ~ Internal i)
            => (Map (TyCon1 (Process env)) i) -> Process env t

instance Show (Process env s) where
  show Close = "Close"
  show Forward = "Forward"
  show (Lift _ p) = "Lift ("++show p++")"
  show (Bind p1 p2) = "Bind ("++show p1++") ("++show p2++")"
  show (ExternalR p1 p2) = "External ("++show p1++") ("++show p2++")"
  show (SendDR _ p) = "SendDR ("++show p++")"
  show (RecvDL _ _) = "RecvDL (???)"
  show (Wait _ p) = "Wait ("++show p++")"
  show (ExternalL1 _ p) = "E1 ("++show p++")"
  show (ExternalL2 _ p) = "E2 ("++show p++")"

data Comms where
  COne :: Comms
  CData :: a -> Comms
  CChoice1 :: Comms
  CChoice2 :: Comms

data TaggedChan a = Recv (Chan a) | Send (Chan a)
type MyChan = (TaggedChan Comms,TaggedChan Comms)

taggedRead :: MyChan -> IO Comms
taggedRead (Recv c,Send _) = readChan c
taggedWrite :: MyChan -> Comms -> IO ()
taggedWrite (Recv _,Send c) x = writeChan c x
taggedNew :: IO MyChan
taggedNew = do ch <- newChan
               return (Recv ch,Send ch)


myfin (Left e) = do tid <- myThreadId
                    putStrLn ("finErr "++show tid++" "++show e)
myfin (Right _) = do tid <- myThreadId
                     putStrLn ("fine "++show tid)

interp :: Process '[] One -> IO ()
interp pin = do tid <- myThreadId
                putStrLn ("Starting at "++show tid)
                (r,w) <- taggedNew
                let (r',w') = (Recv undefined,Send undefined)
	        forkFinally (go [] (r',w) pin) myfin
		yield
		COne <- taggedRead (r,w')
		return ()
  where go :: [MyChan] -> (MyChan) -> Process env s -> IO ()
        go [envch] self Forward = 
	   let f (Recv r) (Send w) = do x <- readChan r
	                                writeChan w x
					f (Recv r) (Send w)
	   in do forkFinally (f (fst self) (snd envch)) myfin
	         forkFinally (f (fst envch) (snd self)) myfin
		 return ()
	go _ _ Forward = error "Forward Bug"
        go _ self Close = taggedWrite self COne
	go env self (Wait n p) = do COne <- taggedRead (index (fromSing n) env)
	                            go env self p
        go env self (SendDR x p) = do taggedWrite self (CData x)
	                              go env self p
	go env self (RecvDL n f) = 
	   do (CData x) <- taggedRead (index (fromSing n) env)
	      go env self (f (unsafeCoerce x))
	go env self (Bind p1 p2) = do tid <- myThreadId
	                              putStrLn ("Bind "++show tid)
	                              (ar,aw) <- taggedNew
	                              (br,bw) <- taggedNew
				      putStrLn ("Bind' "++show tid)
	                              forkFinally
				        (do tid' <- myThreadId
				            putStrLn ("From "++show tid
					             ++" to "++show tid')
					    yield
				            go [] (br,aw) p1) myfin
				      putStrLn ("Bind'' "++show tid)
				      yield
	                              go ((ar,bw):env) self p2
	go env self (TailBind p) = go env self p
        go env self (Lift io p) = io >> go env self p
	go env self (ExternalR p1 p2) = do c <- taggedRead self
	                                   case c of
					     CChoice1 -> go env self p1
					     CChoice2 -> go env self p2
	go env self (ExternalL1 n p) = 
	   do taggedWrite (index (fromSing n) env) CChoice1
	      go env self p
	go env self (ExternalL2 n p) = 
	   do taggedWrite (index (fromSing n) env) CChoice2
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
t4 = Bind t3 Forward

t5 :: Process '[SendD Int One] (SendD String One)
t5 = RecvDL SZ (\i -> SendDR (show i) (Wait SZ Close))

t6 :: Process '[] (Mu (SendD String Var))
t6 = SendDR "foo" (Bind t6 Forward)

t7 :: IO ()
t7 = interp (Bind t4 (RecvDL SZ (\f -> RecvDL SZ (\i -> Lift (print f) (Lift (print i) (Wait SZ Close))))))

t8 :: Process '[] (Internal [One,One])
t8 = InternalR [Close,Close]

type Stream a = Mu (External One (SendD a Var))

-- Works
countup :: Nat -> Process '[] (Stream Nat)
countup n = (ExternalR Close (SendDR n (countup (S n))))

-- Fails
countup' :: Nat -> Process '[] (Stream Nat)
countup' n = (ExternalR Close (SendDR n (TailBind (countup' (S n)))))

main :: IO ()
main = interp (Bind (countup' Z)
                (ExternalL2 SZ (RecvDL SZ (\i -> Lift (print i) 
		(ExternalL1 SZ (Wait SZ Close))))))
