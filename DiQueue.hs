{-# LANGUAGE DataKinds, GADTs, KindSignatures #-}
{-# OPTIONS_GHC -Wall #-}

-- The implementation is via the normal pair of lists where the writing end is locked
module DiQueue where
import Control.Concurrent
import Data.IORef

-- DiQueues have a direction, represented at the type level by the following type. ToX
-- refers to who can read

data DiQueueCore :: * -> * where
  ToC :: IORef [a] -> Chan a -> DiQueueCore a
  ToP :: IORef [a] -> Chan a -> DiQueueCore a

type DiQueue a = IORef (DiQueueCore a)

-- Bool indicates to start pointing at Client or Provider
newDiQueue :: Bool -> IO (DiQueue a)
newDiQueue dir = do h <- newIORef []
                    t <- newChan
                    if dir
                    then newIORef (ToC h t)
                    else newIORef (ToP h t)

safeReadC :: DiQueue a -> IO a
safeReadC qr =
 do q <- readIORef qr
    case q of
      ToP _ _ -> yield >> safeReadC qr
      ToC h t -> do xss <- readIORef h
                    case xss of
                      [] -> readChan t
                      (x:xs) -> do writeIORef h xs
                                   return x

safeReadP :: DiQueue a -> IO a
safeReadP qr =
 do q <- readIORef qr
    case q of
      ToC _ _ -> yield >> safeReadP qr
      ToP h t -> do xss <- readIORef h
                    case xss of
                      [] -> do readChan t
                      (x:xs) -> do writeIORef h xs
                                   return x

safeWriteC :: DiQueue a -> a -> IO ()
safeWriteC qr x = 
  do q <- readIORef qr
     case q of
       ToP _ t -> writeChan t x
       ToC _ _ -> yield >> safeWriteC qr x

safeWriteP :: DiQueue a -> a -> IO ()
safeWriteP qr x = 
  do q <- readIORef qr
     case q of
       ToC _ t -> writeChan t x
       ToP _ _ -> yield >> safeWriteP qr x


waitToC :: DiQueue a -> IO ()
waitToC qr = do q <- readIORef qr
                case q of
                  ToC _ _ -> return ()
                  ToP _ _ -> yield >> waitToC qr

waitToP :: DiQueue a -> IO ()
waitToP qr = do q <- readIORef qr
                case q of
                  ToP _ _ -> return ()
                  ToC _ _ -> yield >> waitToP qr

-- TODO Add assertions?
swapDir :: DiQueue a -> IO ()
swapDir qr = atomicModifyIORef' qr (\q -> case q of
       ToC h t -> (ToP h t,())
       ToP h t -> (ToC h t,()))
