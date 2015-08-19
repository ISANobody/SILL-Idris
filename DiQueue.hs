{-# LANGUAGE DataKinds, GADTs, KindSignatures #-}
{-# OPTIONS_GHC -Wall #-}

-- The implementation is via the normal pair of lists where the writing end is locked
module DiQueue where
import Control.Concurrent.STM

-- DiQueues have a direction, represented at the type level by the following type. ToX
-- refers to who can read

data Dir = ToC | ToP deriving (Eq, Show)

invertDir :: Dir -> Dir
invertDir ToC = ToP
invertDir ToP = ToC

data DiQueue a = DQ { dir :: TVar Dir
                    , que :: TQueue a }


-- Wait until the queue is pointing the specified direction and then modify the Chan
withDir :: Dir -> (TQueue a -> STM b) -> DiQueue a -> STM b
withDir d f q = do qd <- readTVar (dir q)
                   if d == qd 
                   then f (que q)
                   else retry

-- Bool indicates to start pointing at Client or Provider
newDiQueue :: Bool -> IO (DiQueue a)
newDiQueue b = do q <- newTQueueIO
                  d <- newTVarIO (if b then ToC else ToP)
                  return (DQ d q)

safeReadC :: DiQueue a -> STM a
safeReadC = withDir ToC readTQueue

safeReadP :: DiQueue a -> STM a
safeReadP = withDir ToP readTQueue

safeWriteC :: DiQueue a -> a -> STM ()
safeWriteC qr x = withDir ToP (flip writeTQueue $ x) qr

safeWriteP :: DiQueue a -> a -> STM ()
safeWriteP qr x = withDir ToC (flip writeTQueue $ x) qr

waitToC :: DiQueue a -> STM ()
waitToC = withDir ToC (\_ -> return ())

waitToP :: DiQueue a -> STM ()
waitToP = withDir ToP (\_ -> return ())

-- TODO Add assertions?
swapDir :: DiQueue a -> STM ()
swapDir qr = modifyTVar' (dir qr) invertDir
