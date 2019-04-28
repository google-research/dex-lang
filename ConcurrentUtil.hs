module ConcurrentUtil (MutMap, readMutMap, writeMutMap, newMutMap, Pipe,
                      pipeReadAll, pipeWriteAll, Packet (..)) where

import Control.Monad
import Control.Concurrent
import Control.Concurrent.MVar
import qualified Data.Map.Strict as M

-- === Channel with EOM token ===

type Pipe a = Chan (Packet a)
data Packet a = Msg a | EOM

pipeWriteAll :: Pipe a -> [a] -> IO ()
pipeWriteAll chan xs = do mapM (writeChan chan . Msg) xs
                          writeChan chan EOM

pipeReadAll :: Pipe a -> IO [a]
pipeReadAll p = do
  next <- readChan p
  case next of EOM -> return []
               Msg x -> liftM (x:) (pipeReadAll p)

-- === mutable map with blocking lookups ===

newtype MutMap k v = MutMap (MVar (M.Map k (MVar v)))

newMutMap :: Ord k => IO (MutMap k v)
newMutMap = liftM MutMap (newMVar mempty)

-- blocks until value available
readMutMap :: Ord k => MutMap k v -> k -> IO v
readMutMap m k = lookupMutMap k m >>= readMVar

lookupMutMap :: Ord k => k -> MutMap k v -> IO (MVar v)
lookupMutMap k (MutMap ptr) = do
  m <- readMVar ptr
  case M.lookup k m of
    Just var -> return var -- this path is an optimization
    Nothing -> do
      var <- newEmptyMVar
      modifyMVar ptr (return . ensureHasKey k var)

ensureHasKey :: Ord k => k -> v -> M.Map k v -> (M.Map k v, v)
ensureHasKey k v m = case M.lookup k m of Just v' -> (m, v')
                                          Nothing -> (M.insert k v m, v)

-- each key should only be written once
writeMutMap :: Ord k => k -> v -> MutMap k v -> IO ()
writeMutMap k v m = lookupMutMap k m >>= flip putMVar v
