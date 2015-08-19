{-# LANGUAGE DataKinds, GADTs, KindSignatures #-}
{-# OPTIONS_GHC -Wall #-}

-- The implementation is via the normal pair of lists where the writing end is locked
module DiQueue where
import Control.Concurrent
import Data.IORef

-- DiQueues have a direction, represented at the type level by the following type. ToX
-- refers to who can read

data Dir = ToC | ToP

data DiQueueCore a = DQC { dir :: Dir
                         , que :: Chan a }

type DiQueue a = IORef (DiQueueCore a)

-- Bool indicates to start pointing at Client or Provider
newDiQueue :: Bool -> IO (DiQueue a)
newDiQueue d = do q <- newChan
                  if d
                  then newIORef (DQC ToC q)
                  else newIORef (DQC ToP q)

safeReadC :: DiQueue a -> IO a
safeReadC qr =
 do q <- readIORef qr
    case dir q of
      ToP -> yield >> safeReadC qr
      ToC -> readChan (que q)

safeReadP :: DiQueue a -> IO a
safeReadP qr =
 do q <- readIORef qr
    case dir q of
      ToC -> yield >> safeReadP qr
      ToP -> readChan (que q)

safeWriteC :: DiQueue a -> a -> IO ()
safeWriteC qr x = 
  do q <- readIORef qr
     case dir q of
       ToP -> writeChan (que q) x
       ToC -> yield >> safeWriteC qr x

safeWriteP :: DiQueue a -> a -> IO ()
safeWriteP qr x = 
  do q <- readIORef qr
     case dir q of
       ToC -> writeChan (que q) x
       ToP -> yield >> safeWriteP qr x


waitToC :: DiQueue a -> IO ()
waitToC qr = do q <- readIORef qr
                case dir q of
                  ToC -> return ()
                  ToP -> yield >> waitToC qr

waitToP :: DiQueue a -> IO ()
waitToP qr = do q <- readIORef qr
                case dir q of
                  ToP -> return ()
                  ToC -> yield >> waitToP qr

-- TODO Add assertions?
swapDir :: DiQueue a -> IO ()
swapDir qr = atomicModifyIORef' qr (\q -> case dir q of
       ToC -> (q{dir = ToP},())
       ToP -> (q{dir = ToC},()))
