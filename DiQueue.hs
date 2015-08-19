{-# LANGUAGE DataKinds, GADTs, KindSignatures #-}
{-# OPTIONS_GHC -Wall #-}

-- The implementation is via the normal pair of lists where the writing end is locked
module DiQueue where
import Control.Concurrent

-- DiQueues have a direction, represented at the type level by the following type. ToX
-- refers to who can read

data DiQueueCore :: * -> * where
  ToC :: [a] -> DiQueueCore a
  ToP :: [a] -> DiQueueCore a

type DiQueue a = MVar (DiQueueCore a)

-- Bool indicates to start pointing at Client or Provider
newDiQueue :: Bool -> IO (DiQueue a)
newDiQueue dir = if dir
                 then newMVar (ToC [])
                 else newMVar (ToP [])

safeReadC :: DiQueue a -> IO a
safeReadC qr =
 do q <- takeMVar qr
    case q of
      ToP l -> putMVar qr (ToP l) >> yield >> safeReadC qr
      ToC [] -> putMVar qr (ToC []) >> yield >> safeReadC qr
      ToC (x:xs) -> putMVar qr (ToC xs) >> yield >> return x

safeReadP :: DiQueue a -> IO a
safeReadP qr =
 do q <- takeMVar qr
    case q of
      ToC l -> putMVar qr (ToC l) >> yield >> safeReadP qr
      ToP [] -> putMVar qr (ToP []) >> yield >> safeReadP qr
      ToP (x:xs) -> putMVar qr (ToP xs) >> yield >> return x

safeWriteC :: DiQueue a -> a -> IO ()
safeWriteC qr x = 
  do q <- takeMVar qr
     case q of
       ToP l -> putMVar qr (ToP (l++[x]))
       ToC l -> putMVar qr (ToC l) >> yield >> safeWriteC qr x

safeWriteP :: DiQueue a -> a -> IO ()
safeWriteP qr x = 
  do q <- takeMVar qr
     case q of
       ToC l -> putMVar qr (ToC (l++[x]))
       ToP l -> putMVar qr (ToP l) >> yield >> safeWriteP qr x


waitToC :: DiQueue a -> IO ()
waitToC qr = do q <- takeMVar qr
                case q of
                  ToC l -> putMVar qr (ToC l)
                  ToP l -> putMVar qr (ToP l) >> yield >> waitToC qr

waitToP :: DiQueue a -> IO ()
waitToP qr = do q <- takeMVar qr
                case q of
                  ToP l -> putMVar qr (ToP l)
                  ToC l -> putMVar qr (ToC l) >> yield >> waitToP qr

-- TODO get rid of this error checking
swapDir :: DiQueue a -> IO ()
swapDir qr = 
  do q <- takeMVar qr
     case q of
       ToC [] -> putMVar qr (ToP [])
       ToP [] -> putMVar qr (ToC [])
       _ -> error "swapDir of non-empty queue"
