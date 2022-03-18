-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module LiveEval (RFragment (..), SetVal(..), watchAndEvalFile) where

import Control.Concurrent (forkIO, readChan, threadDelay)
import Control.Monad.Reader
import Control.Monad.State.Strict
import qualified Data.Map.Strict as M

import Data.Aeson (ToJSON, toJSON, (.=))
import qualified Data.Aeson as A
import System.Directory (getModificationTime)

import Actor
import Parser
import RenderHtml (ToMarkup, pprintHtml)
import Syntax
import TopLevel

type NodeId = Int
data WithId a = WithId { getNodeId :: NodeId
                       , withoutId :: a }
data RFragment = RFragment (SetVal [NodeId])
                           (M.Map NodeId SourceBlock)
                           (M.Map NodeId Result)

-- Start watching and evaluating the given file.  Returns a channel on
-- which one can subscribe to updates to the evaluation state.
watchAndEvalFile :: FilePath -> EvalConfig -> TopStateEx
                 -> IO (PChan (PChan RFragment))
watchAndEvalFile fname opts env = do
  (_, resultsChan) <- spawn logServer
  let cfg = (opts, subChan Publish resultsChan)
  (_, sourceChan) <- spawn $ runDriver cfg env
  forkWatchFile fname sourceChan
  return $ subChan Subscribe resultsChan

-- === executing blocks concurrently ===

type SourceContents = String

type DriverCfg = (EvalConfig, PChan RFragment)
type DriverState = (WithId TopStateEx, CacheState)
type DriverM = ReaderT DriverCfg (StateT DriverState IO)

type EvalCache = M.Map (SourceBlock, WithId TopStateEx) (NodeId, WithId TopStateEx)
data CacheState = CacheState
       { nextBlockId :: NodeId
       , nextStateId :: NodeId
       , evalCache  :: EvalCache }

emptyCache :: CacheState
emptyCache = CacheState 0 1 mempty

runDriver :: DriverCfg -> TopStateEx -> Actor SourceContents
runDriver cfg env self =
  liftM fst $ flip runStateT (WithId 0 env, emptyCache) $ flip runReaderT cfg $
    forever $ (liftIO $ readChan self) >>= evalSource

evalSource :: SourceContents -> DriverM ()
evalSource source = withLocalTopState do
    let UModule _ _ blocks = parseUModule Main source
    (evaluated, remaining) <- tryEvalBlocksCached blocks
    remaining' <- mapM makeNewBlockId remaining
    updateResultList $ map getNodeId $ evaluated ++ remaining'
    mapM_ evalBlock remaining'

tryEvalBlocksCached :: [SourceBlock] -> DriverM ([WithId SourceBlock], [SourceBlock])
tryEvalBlocksCached [] = return ([], [])
tryEvalBlocksCached blocks@(block:rest) = do
  (env, cache) <- get
  case M.lookup (block, env) (evalCache cache) of
    Nothing -> return ([], blocks)
    Just (blockId, env') -> do
      let block' = WithId blockId block
      updateTopState env'
      (evaluated, remaining) <- tryEvalBlocksCached rest
      return (block':evaluated, remaining)

evalBlock :: WithId SourceBlock -> DriverM ()
evalBlock (WithId blockId block) = do
  oldState <- gets fst
  opts <- asks fst
  (result, s) <- liftIO $ evalSourceBlockIO opts (withoutId oldState) block
  resultsChan <- asks snd
  liftIO $ resultsChan `sendPChan` oneResult blockId result
  newState <- makeNewStateId s
  updateTopState newState
  insertCache (block, oldState) (blockId, newState)

-- === DriverM utils ===

updateTopState :: WithId TopStateEx -> DriverM ()
updateTopState s = modify \(_,c) -> (s, c)

makeNewBlockId :: SourceBlock -> DriverM (WithId SourceBlock)
makeNewBlockId block = do
  newId <- gets $ nextBlockId . snd
  modify \(s, cache) -> (s, cache {nextBlockId = newId + 1 })
  resultsChan <- asks snd
  liftIO $ resultsChan `sendPChan` oneSourceBlock newId block
  return $ WithId newId block

makeNewStateId :: TopStateEx -> DriverM (WithId TopStateEx)
makeNewStateId env = do
  newId <- gets $ nextStateId . snd
  modify \(s, cache) -> (s, cache {nextStateId = newId + 1 })
  return $ WithId newId env

insertCache :: (SourceBlock, WithId TopStateEx) -> (NodeId, WithId TopStateEx) -> DriverM ()
insertCache key val = modify \(s, cache) ->
  (s, cache { evalCache = M.insert key val $ evalCache cache })

withLocalTopState :: DriverM a -> DriverM a
withLocalTopState cont = do
  startState <- gets fst
  result <- cont
  updateTopState startState
  return result

-- === utils for sending results ===

updateResultList :: [NodeId] -> DriverM ()
updateResultList ids = do
  resultChan <- asks snd
  liftIO $ resultChan `sendPChan` RFragment (Set ids) mempty mempty

oneResult :: NodeId -> Result -> RFragment
oneResult k r = RFragment mempty mempty (M.singleton k r)

oneSourceBlock :: NodeId -> SourceBlock -> RFragment
oneSourceBlock k b = RFragment mempty (M.singleton k b) mempty

-- === watching files ===

-- A non-Actor source.  Sends file contents to channel whenever file
-- is modified.
forkWatchFile :: FilePath -> PChan String -> IO ()
forkWatchFile fname chan = onmod fname $ sendFileContents fname chan

sendFileContents :: String -> PChan String -> IO ()
sendFileContents fname chan = do
  putStrLn $ fname ++ " updated"
  s <- readFile fname
  sendPChan chan s

onmod :: FilePath -> IO () -> IO ()
onmod fname action = do
  action
  t <- getModificationTime fname
  void $ forkIO $ loop t
  where
    loop t = do
      t' <- getModificationTime fname
      threadDelay 100000
      unless (t == t') action
      loop t'

-- === instances ===

instance Semigroup RFragment where
  (RFragment x y z) <> (RFragment x' y' z') = RFragment (x<>x') (y<>y') (z<>z')

instance Monoid RFragment where
  mempty = RFragment mempty mempty mempty

instance Eq (WithId a) where
  (==) (WithId x _) (WithId y _) = x == y

instance Ord (WithId a) where
  compare (WithId x _) (WithId y _) = compare x y

instance ToJSON a => ToJSON (SetVal a) where
  toJSON (Set x) = A.object ["val" .= toJSON x]
  toJSON NotSet  = A.Null

instance (ToJSON k, ToJSON v) => ToJSON (MonMap k v) where
  toJSON (MonMap m) = toJSON (M.toList m)

instance ToJSON RFragment where
  toJSON (RFragment ids blocks results) = toJSON (ids, contents)
    where contents = MonMap (M.map toHtmlFragment blocks)
                  <> MonMap (M.map toHtmlFragment results)

type TreeAddress = [Int]
type HtmlFragment = [(TreeAddress, String)]

toHtmlFragment :: ToMarkup a => a -> HtmlFragment
toHtmlFragment x = [([], pprintHtml x)]

-- === some handy monoids ===

data SetVal a = Set a | NotSet

instance Semigroup (SetVal a) where
  x <> NotSet = x
  _ <> Set x  = Set x

instance Monoid (SetVal a) where
  mempty = NotSet

newtype MonMap k v = MonMap (M.Map k v)  deriving (Show, Eq)

instance (Ord k, Semigroup v) => Semigroup (MonMap k v) where
  MonMap m <> MonMap m' = MonMap $ M.unionWith (<>) m m'

instance (Ord k, Semigroup v) => Monoid (MonMap k v) where
  mempty = MonMap mempty
