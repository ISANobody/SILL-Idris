{-# LANGUAGE DataKinds, GADTs, KindSignatures #-}
{-# OPTIONS_GHC -Wall #-}

-- The implementation is via the normal pair of lists where the writing end is locked
module DiQueue where
import Control.Concurrent
import Control.Concurrent.STM

-- DiQueues have a direction, represented at the type level by the following type. ToX
-- refers to who can read

data Dir = ToC | ToP

data DiQueueCore a = DQC { dir :: Dir
                         , que :: TChan a }

type DiQueue a = TVar (DiQueueCore a)

-- Bool indicates to start pointing at Client or Provider
newDiQueue :: Bool -> IO (DiQueue a)
newDiQueue d = do q <- newTChanIO
                  if d
                  then newTVarIO (DQC ToC q)
                  else newTVarIO (DQC ToP q)

safeReadC :: DiQueue a -> STM a
safeReadC qr =
 do q <- readTVar qr
    case dir q of
      ToP -> retry
      ToC -> readTChan (que q)

safeReadP :: DiQueue a -> STM a
safeReadP qr =
 do q <- readTVar qr
    case dir q of
      ToC -> retry
      ToP -> readTChan (que q)

safeWriteC :: DiQueue a -> a -> STM ()
safeWriteC qr x = 
  do q <- readTVar qr
     case dir q of
       ToP -> writeTChan (que q) x
       ToC -> retry

safeWriteP :: DiQueue a -> a -> STM ()
safeWriteP qr x = 
  do q <- readTVar qr
     case dir q of
       ToC -> writeTChan (que q) x
       ToP -> retry


waitToC :: DiQueue a -> STM ()
waitToC qr = do q <- readTVar qr
                case dir q of
                  ToC -> return ()
                  ToP -> retry

waitToP :: DiQueue a -> STM ()
waitToP qr = do q <- readTVar qr
                case dir q of
                  ToP -> return ()
                  ToC -> retry

-- TODO Add assertions?
swapDir :: DiQueue a -> STM ()
swapDir qr = modifyTVar qr (\q -> case dir q of
       ToC -> q{dir = ToP}
       ToP -> q{dir = ToC})
