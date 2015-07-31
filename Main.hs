{-# LANGUAGE GADTs, DataKinds, KindSignatures, TypeFamilies, TypeOperators #-}
{-# LANGUAGE TemplateHaskell, QuasiQuotes, PolyKinds, UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables, BangPatterns #-}
{-# OPTIONS -Wall -fno-warn-unused-do-bind #-}
import Control.Concurrent
import Control.Concurrent.Chan
import Unsafe.Coerce
import Data.List
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

  update0 :: Nat -> [a] -> a -> [a]
  update0 Z (_:ys) x = x:ys
  update0 (S k) (y:ys) x = y:(update0 k ys x)

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

  all2 :: (a -> b -> Bool) -> [a] -> [b] -> Bool
  all2 f (x:xs) (y:ys) = if f x y 
                         then all2 f xs ys
			 else False

  mapf :: (a -> b -> c) -> b -> [a] -> [c]
  mapf _ _ [] = []
  mapf f z (x:xs) = (f x z):(mapf f z xs)

  mapf0 :: Nat -> [a] -> b -> ([a] -> b -> c) -> [a] -> [c]
  mapf0 n a z f xs = mapf f z (map (update0 n a) xs)
  |]

-- TODO split modules to allow for OverloadedLists here
data HList :: [*] -> * where
  HNil :: HList '[]
  HCons :: a -> (HList ts) -> HList (a ': ts)

hindex :: SNat n -> HList ts -> Index n ts
hindex SZ (HCons x _) = x
hindex (SS k) (HCons _ xs) = hindex k xs

-- Tracking whether this is open or closed makes this type unpromotable
-- Choice is over Nat b/c String is unpromotable
promote [d|
  data Session where
    Mu :: Session -> Session
    Var :: Session
    SendD :: a -> Session -> Session
    One :: Session
    External :: [Session] -> Session
    Internal :: [Session] -> Session
  
  subst :: Session -> Session -> Session
  subst _ One = One
  subst _ (Mu x) = Mu x
  subst x Var = x
  subst x (SendD a s) = SendD a (subst x s)
  subst x (External cs) = External (map (subst x) cs)
  subst x (Internal cs) = Internal (map (subst x) cs)

  unfold :: Session -> Session
  unfold (Mu x) = subst (Mu x) x
  unfold One = One
  unfold Var = Var
  unfold (SendD a s) = SendD a s
  unfold (Internal cs) = (Internal cs)
  unfold (External cs) = (External cs)

  const2 :: a -> b -> c -> a
  const2 x y z = x

  boring :: [a] -> [b] -> Bool
  boring xs ys = all2 (const2 True) xs ys

  truconst :: a -> b -> Bool
  truconst x y = True
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
  RTEq2 hyp (Mu x) One = RTEq0 hyp (Unfold (Mu x)) One
  RTEq2 hyp (Mu x) (SendD a s) = RTEq0 hyp (Unfold (Mu x)) (SendD a s)
  RTEq2 hyp (Mu x) (Mu y) = RTEq0 hyp (Unfold (Mu x)) (Unfold (Mu y))
  RTEq2 hyp One (Mu y) = RTEq0 hyp One (Unfold (Mu y))
  RTEq2 hyp One One = True
  RTEq2 hyp (SendD a s) (SendD a t) = 
    RTEq0 ('(SendD a s, SendD a t) ': hyp) s t
  RTEq2 hyp (External cs) (External ds) = 
    RTEq3 ('((External cs),(External ds)) ': hyp) cs ds
  RTEq2 hyp (Internal cs) (Internal ds) = 
    RTEq3 ('((Internal cs),(Internal ds)) ': hyp) cs ds

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
  ExternalR :: (Unfold t ~ External choices
               ,ps ~ Map (TyCon1 (Process env)) choices)
            => HList ps -> Process env t
  ExternalL :: (Inbounds n env ~ True
               ,Inbounds c choices ~ True
               ,Unfold (Index n env) ~ External choices)
            => SNat n -> SNat c -> Process (Update n (Index c choices) env) t
            -> Process env t
  InternalR :: (Unfold t ~ Internal choices
               ,Inbounds n choices ~ True
	       ,Index n choices ~ s)
            =>  SNat n -> Process env s -> Process env t
  InternalL :: (Inbounds n env ~ True
               ,Unfold (Index n env) ~ Internal choices
	       ,ps ~ (Mapf0 n env s (TyCon2 Process) choices))
            => SNat n -> HList ps -> Process env s

data Comms where
  COne :: Comms
  CData :: a -> Comms
  CChoice :: SNat n -> Comms

data TaggedChan a = Recv (Chan a) | Send (Chan a)
type MyChan = (TaggedChan Comms,TaggedChan Comms)

taggedRead :: MyChan -> IO Comms
taggedRead (Recv c,Send _) = readChan c
taggedWrite :: MyChan -> Comms -> IO ()
taggedWrite (Recv _,Send c) x = writeChan c x
taggedNew :: IO MyChan
taggedNew = do ch <- newChan
               return (Recv ch,Send ch)

interp :: Process '[] One -> IO ()
interp pin = do tid <- myThreadId
                putStrLn ("Starting at "++show tid)
	        (ar,aw) <- taggedNew
	        (br,bw) <- taggedNew
	        forkIO (go [] (br,aw) pin)
		yield
		COne <- taggedRead (ar,bw)
		putStrLn ("Finished")
		return ()
  where go :: [MyChan] -> (MyChan) -> Process env s -> IO ()
        go envch self Forward = 
	   let f o (Recv r) (Send w) = do x <- readChan r
	                                  writeChan w x
					  case x of
					    COne -> do killThread o
					               return ()
					    _ -> f o (Recv r) (Send w)
	   in do tid1 <- myThreadId
	         tid2 <- forkIO (f tid1 (fst self) (snd (head envch)))
	         (f tid2 (fst (head envch)) (snd self))
		 return ()
        go _ self Close = taggedWrite self COne
	go env self (Wait n p) = do COne <- taggedRead (index (fromSing n) env)
	                            go env self p
        go env self (SendDR x p) = do taggedWrite self (CData x)
	                              go env self p
	go env self (RecvDL n f) = 
	   do (CData x) <- taggedRead (index (fromSing n) env)
	      go env self (f (unsafeCoerce x))
	go env self (Bind p1 p2) = do tid <- myThreadId
	                              (ar,aw) <- taggedNew
	                              (br,bw) <- taggedNew
	                              forkIO
				        (do tid' <- myThreadId
					    yield
				            go [] (br,aw) p1)
				      yield
	                              go ((ar,bw):env) self p2
	go env self (TailBind p) = go env self p
        go env self (Lift io p) = io >> go env self p
	go env self (ExternalR ps) = do CChoice n <- taggedRead self
	                                go env self (unsafeCoerce (hindex n ps))
	go env self (ExternalL n k p) = 
	   do taggedWrite (index (fromSing n) env) (CChoice k)
	      go env self p
        go env self (InternalR k p) =  
	   do taggedWrite self (CChoice k)
	      go env self p
	go env self (InternalL n ps) =
	   do CChoice n <- taggedRead (index (fromSing n) env)
	      go env self (unsafeCoerce (hindex n ps))

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
t8 = InternalR SZ Close

type Stream a = Mu (External [One,SendD a Var])
type IStream a = Mu (Internal [One,SendD a Var])

-- Works
countup :: Nat -> Process '[] (Stream Nat)
countup n = (ExternalR (HCons Close (HCons (SendDR n (countup (S n))) HNil)))

countdown :: Nat -> Process '[] (IStream Nat)
countdown Z = InternalR (SS SZ) (SendDR Z (InternalR SZ Close))
countdown (S k) = InternalR (SS SZ) (SendDR (S k) (countdown k))


countup' :: Nat -> Process '[] (Stream Nat)
countup' n = (ExternalR (HCons Close (HCons (SendDR n (TailBind (countup' (S n)))) HNil)))



t9 :: IO ()
t9 = interp (Bind (countup' Z)
                (ExternalL SZ (SS SZ) (RecvDL SZ (\i -> Lift (putStrLn . show $ i) 
                (ExternalL SZ (SS SZ) (RecvDL SZ (\i -> Lift (putStrLn . show $ i) 
		(ExternalL SZ SZ (Wait SZ Close)))))))))

t11 :: IO ()
t11 = interp (Bind (countdown (S (S Z))) go)
   where go :: Process '[IStream Nat] One
         go = (InternalL SZ (HCons (Wait SZ Close) 
                            (HCons (RecvDL SZ (\i -> Lift (putStrLn . show $ i) go)) HNil)))

t10 :: Process '[Internal '[One]] One
t10 = InternalL SZ (HCons (Wait SZ Close) HNil)

main :: IO ()
main = interp (go 0)
  where go n = Lift (putStrLn (show n)) (Bind (go (n+1)) Forward)
