{-# LANGUAGE DataKinds, GADTs, KindSignatures, MonadComprehensions, TupleSections #-}
{-# OPTIONS_GHC -Wall #-}

module DiQueue where
import Control.Concurrent.STM
import Data.Array.IArray
import Data.Array.Base

data Dir = ToC | ToP deriving (Eq, Show)

invertDir :: Dir -> Dir
invertDir ToC = ToP
invertDir ToP = ToC

class DiQueue a where
  safeReadC :: a b -> STM b
  safeReadP :: a b -> STM b
  safeWriteC :: a b -> b -> STM ()
  safeWriteP :: a b -> b -> STM ()
  waitToC :: a b -> STM ()
  waitToP :: a b -> STM ()
  swapDir :: a b -> STM ()

data ExtDiQueue a where
  ExtDiQueue :: DiQueue q => q a -> ExtDiQueue a

instance DiQueue ExtDiQueue where
  safeReadC (ExtDiQueue q) = safeReadC q
  safeReadP (ExtDiQueue q) = safeReadP q
  safeWriteC (ExtDiQueue q) x = safeWriteC q x
  safeWriteP (ExtDiQueue q) x = safeWriteP q x
  waitToC (ExtDiQueue q) = waitToC q
  waitToP (ExtDiQueue q) = waitToP q
  swapDir (ExtDiQueue q) = swapDir q

data UDiQueue a = UDQ { dirU :: TVar Dir
                      , queU :: TQueue a }

-- Wait until the queue is pointing the specified direction and then modify the Chan
withDirU :: Dir -> (TQueue a -> STM b) -> UDiQueue a -> STM b
withDirU d f q = do qd <- readTVar (dirU q)
                    if d == qd 
                    then f (queU q)
                    else retry

-- Bool indicates to start pointing at Client or Provider
newUDiQueue :: Bool -> IO (UDiQueue a)
newUDiQueue b = do q <- newTQueueIO
                   d <- newTVarIO (if b then ToC else ToP)
                   return (UDQ d q)

newUDiQueueE :: Bool -> IO (ExtDiQueue a)
newUDiQueueE b = do q <- newUDiQueue b
                    return (ExtDiQueue q)

instance DiQueue UDiQueue where
  safeReadC = withDirU ToC readTQueue
  safeReadP = withDirU ToP readTQueue
  safeWriteC qr x = withDirU ToP (flip writeTQueue $ x) qr
  safeWriteP qr x = withDirU ToC (flip writeTQueue $ x) qr
  waitToC = withDirU ToC (\_ -> return ())
  waitToP = withDirU ToP (\_ -> return ())
  swapDir qr = modifyTVar' (dirU qr) invertDir

-- This is probably slower than the unbounded implementation but lets us show off type
-- directed optimizations
data BDiQueue a = BDQ { dirB :: TVar Dir
                      , readPos :: TVar Int
                      , writePos :: TVar Int
                      , queB :: Array Int (TMVar a) }

-- Wait until the queue is pointing the specified direction and then modify the Chan
withDirB :: Dir -> (TVar Int -> TVar Int -> Array Int (TMVar a) -> STM b) 
         -> BDiQueue a -> STM b
withDirB d f q = do qd <- readTVar (dirB q)
                    if d == qd 
                    then f (readPos q) (writePos q) (queB q)
                    else retry

-- Bool indicates to start pointing at Client or Provider
newBDiQueue :: Bool -> Int -> IO (BDiQueue a)
newBDiQueue b i = do q <- mapM (\_ -> newEmptyTMVarIO)  [0..i-1]
                     rp <- newTVarIO 0
                     wp <- newTVarIO 0
                     d <- newTVarIO (if b then ToC else ToP)
                     return (BDQ d rp wp (listArray (0,i-1) q))

newBDiQueueE :: Bool -> Int -> IO (ExtDiQueue a)
newBDiQueueE b i = do q <- newBDiQueue b i
                      return (ExtDiQueue q)

instance DiQueue BDiQueue where
  safeReadC = withDirB ToC (\rp _ q -> do i <- readTVar rp
                                          writeTVar rp (i+1)
                                          takeTMVar (unsafeAt q i))
  safeReadP = withDirB ToP (\rp _ q -> do i <- readTVar rp
                                          writeTVar rp (i+1)
                                          takeTMVar (unsafeAt q i))
  safeWriteC qr x = withDirB ToP (\_ wp q -> do i <- readTVar wp
                                                writeTVar wp (i+1)
                                                putTMVar (unsafeAt q i) x) qr
  safeWriteP qr x = withDirB ToC (\_ wp q -> do i <- readTVar wp
                                                writeTVar wp (i+1)
                                                putTMVar (unsafeAt q i) x) qr
  waitToC = withDirB ToC (\_ _ _ -> return ())
  waitToP = withDirB ToP (\_ _ _ -> return ())
  swapDir qr = do modifyTVar' (dirB qr) invertDir
                  writeTVar (readPos qr) 0
                  writeTVar (writePos qr) 0
