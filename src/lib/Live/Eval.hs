-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module Live.Eval (RFragment (..), SetVal(..), watchAndEvalFile) where

import Control.Concurrent (forkIO, killThread, readChan, threadDelay, ThreadId)
import Control.Monad.Reader
import Control.Monad.State.Strict
import Data.ByteString qualified as BS
import Data.Text (Text)
import Data.Text.Encoding qualified as T
import Data.Map.Strict qualified as M

import Data.Aeson (ToJSON, toJSON, (.=))
import Data.Aeson qualified as A
import Data.Text.Prettyprint.Doc
import System.Directory (getModificationTime)

import ConcreteSyntax
import Actor
import RenderHtml (ToMarkup, pprintHtml)
import TopLevel
import Types.Misc
import Types.Source
import Util (onFst, onSnd)

type NodeId = Int
data WithId a = WithId { getNodeId :: NodeId
                       , withoutId :: a }
                deriving Show

data RFragment = RFragment (SetVal [NodeId])
                           (M.Map NodeId SourceBlock)
                           (M.Map NodeId Result)

-- Start watching and evaluating the given file.  Returns a channel on
-- which one can subscribe to updates to the evaluation state.
--
-- The overall system looks like this:
-- - `forkWatchFile` creates an actor that watches the file for
--   changes and sends `FileChanged` messages to the driver.
-- - `runDriver` creates the main driver actor, which manages
--   the evaluation state and produces rendering fragments.
-- - `logServer` creates an actor that accumulates rendering fragments
--   from the driver and broadcasts them to any subscribed clients.
--
-- `FileChanged` messages from the watch file actor may invalidate the
-- current state.  The driver delegates the actual evaluation to a
-- sub-thread so it can remain responsive.
--
-- `watchAndEvalFile` returns the channel by which a client may
-- subscribe by sending a write-only view of its input channel.
watchAndEvalFile :: FilePath -> EvalConfig -> TopStateEx
                 -> IO (PChan (PChan RFragment))
watchAndEvalFile fname opts env = do
  (_, resultsChan) <- spawn logServer
  let cfg = (opts, subChan Publish resultsChan)
  (_, driverChan) <- spawn $ runDriver cfg env
  forkWatchFile fname $ subChan FileChanged driverChan
  return $ subChan Subscribe resultsChan

-- === executing blocks concurrently ===

type SourceContents = Text

type DriverCfg = (EvalConfig, PChan RFragment)

-- The evaluation-in-progress state is
-- - The (identified) current top-level environment
-- - If a worker is currently running, its ThreadId and the
--   SourceBlock it it working on (necessarily in the current
--   top-level environment)
-- - The list of blocks that remain to be evaluated (if any) after
--   the current worker completes.  If nonempty, there should be
--   a current worker.
-- This is consistent at entry and exit from handling each message,
-- but may be briefly inconsistent while a message is being handled.
type WorkerSpec = Maybe (ThreadId, WithId SourceBlock)
data SourceEvalState = SourceEvalState
  (WithId TopStateEx) WorkerSpec [WithId SourceBlock]

initialEvalState :: TopStateEx -> SourceEvalState
initialEvalState env = (SourceEvalState (WithId 0 env) Nothing [])

newtype DriverM a = DriverM
  { drive :: (ReaderT DriverCfg
              (ReaderT (PChan DriverEvent)
               (StateT (SourceEvalState, CacheState) IO)) a)
  }
  deriving (Functor, Applicative, Monad, MonadIO)

type EvalCache = M.Map (SourceBlock, WithId TopStateEx) (NodeId, WithId TopStateEx)
data CacheState = CacheState
       { nextBlockId :: NodeId
       , nextStateId :: NodeId
       , evalCache  :: EvalCache }

emptyCache :: CacheState
emptyCache = CacheState 0 1 mempty

class (Monad m, MonadIO m) => Driver m where
  askOptions :: m EvalConfig
  askResultsOutput :: m (PChan RFragment)
  askSelf :: m (PChan DriverEvent)
  getTopState :: m (WithId TopStateEx)
  putTopState :: WithId TopStateEx -> m ()
  -- Resets the evaluation state to initial, from the given TopStateEx.
  -- Returns the old top state and the old worker spec, for reuse
  refresh :: TopStateEx -> m (WithId TopStateEx, WorkerSpec)
  -- Get the work chunk we are waiting for, if any
  getWorkingBlock :: m (Maybe (WithId SourceBlock))
  -- Run the action if there is no worker, otherwise don't
  whenNoWorker :: m () -> m ()
  putWorker :: WorkerSpec -> m ()
  -- If a block is pending, remove it from the queue and run the
  -- action on it, otherwise don't.
  popPending :: (WithId SourceBlock -> m ()) -> m ()
  putPending :: [WithId SourceBlock] -> m ()
  newBlockId :: m Int
  newStateId :: m Int
  lookupCache :: SourceBlock
              -> WithId TopStateEx
              -> m (Maybe (NodeId, WithId TopStateEx))
  insertCache :: SourceBlock
              -> WithId TopStateEx
              -> (NodeId, WithId TopStateEx)
              -> m ()

-- The externally visible behavior of the main driver loop:
-- - When the source file changes, send the new set of visible node IDs
--   (`updateResultList`) to the `PChan RFragment`
-- - When a new source block is discovered, assign an ID to it and send
--   the association of that block with that ID (`makeNewBlockId`)
-- - When a source block is successfully evaluated, associate the result
--   with its ID and send that (inside `evalBlock`)

-- Internally, we implement this behavior with a driver thread that
-- forks a worker thread.  Why two threads?  So the driver can notice
-- if a source block in progress has disappeared from the file and
-- kill the worker when that happens.

-- The worker communicates with the driver by sending a "work
-- complete" message.  Note that a worker due to be killed may send a
-- "work complete" message before the driver actually kills it.  If a
-- "file changed" message arrived in the interim, the TopState the
-- worker delivers remains valid to enter into the cache, but should
-- not change the driver's then-current TopState.

-- For this reason, the WorkComplete message contains the ids of the
-- TopStateEx and SourceBlock that the woker evaluated.

data DriverEvent = FileChanged SourceContents
                 | WorkComplete (WithId TopStateEx) (WithId SourceBlock) (Result, TopStateEx)

runDriver :: DriverCfg -> TopStateEx -> Actor DriverEvent
runDriver cfg env self = do
  liftM fst
    $ flip runStateT (initialEvalState env, emptyCache)
    $ flip runReaderT (sendOnly self)
    $ flip runReaderT cfg
    $ drive $ forever $ do
        msg <- liftIO $ readChan self
        case msg of
          (FileChanged source) -> evalSource env source
          (WorkComplete block topState payload) -> processWork block topState payload

-- Start evaluation of the (updated) source file in the given (fresh)
-- evaluation state.  The evaluation state carried in the monad is
-- still the state as of the end of the previous message.
evalSource :: Driver m => TopStateEx -> SourceContents -> m ()
evalSource env source = do
  -- Save the old state from the monad, because we need to kill or
  -- reuse the worker from it.
  (oldTopState, oldWorker) <- refresh env
  let UModule _ _ blocks = parseUModule Main source
  (evaluated, remaining) <- tryEvalBlocksCached blocks
  (reused, remaining') <- tryReuseWorker oldTopState oldWorker remaining
  remaining'' <- mapM makeNewBlockId remaining'
  updateResultList $ map getNodeId $ evaluated ++ reused ++ remaining''
  putPending $ reused ++ remaining''
  maybeLaunchWorker

-- See which blocks already have completed values and reuse those.
tryEvalBlocksCached :: Driver m
                    => [SourceBlock]
                    -> m ([WithId SourceBlock], [SourceBlock])
tryEvalBlocksCached [] = return ([], [])
tryEvalBlocksCached blocks@(block:rest) = do
  env <- getTopState
  res <- lookupCache block env
  case res of
    Nothing -> return ([], blocks)
    Just (blockId, env') -> do
      let block' = WithId blockId block
      putTopState env'
      (evaluated, remaining) <- tryEvalBlocksCached rest
      return (block':evaluated, remaining)

-- See whether the formerly active worker (if any) is still doing
-- something useful given the list of blocks we are waiting to finish;
-- if so reuse it, and if not kill it.
tryReuseWorker :: Driver m
               => WithId TopStateEx
               -> WorkerSpec
               -> [SourceBlock]
               -> m ([WithId SourceBlock], [SourceBlock])
tryReuseWorker _ w [] =
  liftIO (forM_ w (killThread . fst)) >> return ([], [])
tryReuseWorker _ Nothing blocks =
  return ([], blocks)
tryReuseWorker oldEnv w@(Just (_, oldNext)) (next:rest) = do
  curEnv <- getTopState
  if (curEnv == oldEnv) && (withoutId oldNext == next) then do
    -- Reuse the worker
    putWorker w
    return ([oldNext], rest)
  else
    liftIO (forM_ w (killThread . fst)) >> return ([], next:rest)

processWork :: Driver m
            => WithId TopStateEx
            -> WithId SourceBlock
            -> (Result, TopStateEx)
            -> m ()
processWork oldState block answer = do
  -- The computed result is true regardless of whether this is the
  -- worker we are waiting for or not, and therefore safe to cache
  -- outside the `when` clause.  There is a narrow benefit here: if a
  -- worker completes normally while we're processing a FileChanged
  -- message, it can send a sound WorkComplete message before we
  -- actually kill it.  We record that result in case the user edits
  -- back to a state where it can be shown.
  newState <- recordTruth oldState block answer
  curState <- getTopState
  waitingFor <- getWorkingBlock
  when (oldState == curState
        && (fmap withoutId waitingFor == Just (withoutId block))) $ do
    -- We only update our working state if this message is, in fact,
    -- from the worker we are currently waiting for.
    rotateWorkingState newState

-- Record what the worker computed in our cache of truths, and return
-- the updated environment.  This is sound regardless of whether we
-- are waiting for this evaluation or not.
recordTruth :: Driver m
            => WithId TopStateEx
            -> WithId SourceBlock
            -> (Result, TopStateEx)
            -> m (WithId TopStateEx)
recordTruth oldState (WithId blockId block) (result, s) = do
  resultsChan <- askResultsOutput
  liftIO $ resultsChan `sendPChan` oneResult blockId result
  newState <- makeNewStateId s
  insertCache block oldState (blockId, newState)
  return newState

-- Update our current evaluation state assuming the work we were
-- waiting for was just completed with the given new evaluation
-- environment.
rotateWorkingState :: Driver m => WithId TopStateEx -> m ()
rotateWorkingState newState = do
  putTopState newState
  putWorker Nothing  -- Worker finished
  maybeLaunchWorker

-- === DriverM utils ===

-- If we have work to do but no worker doing it, launch such a worker.
maybeLaunchWorker :: (Driver m) => m ()
maybeLaunchWorker = do
  whenNoWorker $ popPending \next -> do
    curState <- getTopState
    opts <- askOptions
    self <- askSelf
    tid <- liftIO $ forkWorker opts curState next self
    putWorker $ Just (tid, next)

forkWorker :: EvalConfig -> WithId TopStateEx -> WithId SourceBlock
           -> PChan DriverEvent -> IO ThreadId
forkWorker opts curState block chan = forkIO $ do
  result <- evalSourceBlockIO opts (withoutId curState) (withoutId block)
  chan `sendPChan` (WorkComplete curState block result)

makeNewBlockId :: Driver m => SourceBlock -> m (WithId SourceBlock)
makeNewBlockId block = do
  newId <- newBlockId
  resultsChan <- askResultsOutput
  liftIO $ resultsChan `sendPChan` oneSourceBlock newId block
  return $ WithId newId block

makeNewStateId :: Driver m => TopStateEx -> m (WithId TopStateEx)
makeNewStateId env = do
  newId <- newStateId
  return $ WithId newId env

-- === utils for sending results ===

updateResultList :: Driver m => [NodeId] -> m ()
updateResultList ids = do
  resultChan <- askResultsOutput
  liftIO $ resultChan `sendPChan` RFragment (Set ids) mempty mempty

oneResult :: NodeId -> Result -> RFragment
oneResult k r = RFragment mempty mempty (M.singleton k r)

oneSourceBlock :: NodeId -> SourceBlock -> RFragment
oneSourceBlock k b = RFragment mempty (M.singleton k b) mempty

-- === watching files ===

-- A non-Actor source.  Sends file contents to channel whenever file
-- is modified.
forkWatchFile :: FilePath -> PChan Text -> IO ()
forkWatchFile fname chan = onmod fname $ sendFileContents fname chan

sendFileContents :: String -> PChan Text -> IO ()
sendFileContents fname chan = do
  putStrLn $ fname ++ " updated"
  s <- T.decodeUtf8 <$> BS.readFile fname
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

instance Driver DriverM where
  askOptions = DriverM $ asks fst
  askResultsOutput = DriverM $ asks snd
  askSelf = DriverM $ lift $ ask
  getTopState = DriverM $ do
    (SourceEvalState s _ _) <- gets fst
    return s

  putTopState s = DriverM $ modify $ onFst \(SourceEvalState _ w blocks)
    -> (SourceEvalState s w blocks)

  refresh env = DriverM $ do
    (SourceEvalState oldState oldWorker _) <- gets fst
    modify $ onFst $ const $ initialEvalState env
    return (oldState, oldWorker)

  getWorkingBlock = DriverM $ do
    (SourceEvalState _ w _) <- gets fst
    return $ (fmap snd) w

  whenNoWorker (DriverM action) = DriverM $ do
    (SourceEvalState _ w _) <- gets fst
    case w of
      (Just _) -> return ()
      Nothing -> action

  putWorker w = DriverM $ modify $ onFst \(SourceEvalState s _ blocks)
    -> (SourceEvalState s w blocks)

  popPending action = do
    (SourceEvalState _ _ curPending) <- DriverM $ gets fst
    case curPending of
      [] -> return ()
      (next:rest) -> do
        DriverM $ modify $ onFst \(SourceEvalState s w _)
          -> (SourceEvalState s w rest)
        action next

  putPending blocks = DriverM $ modify $ onFst \(SourceEvalState s w _)
    -> (SourceEvalState s w blocks)

  lookupCache block env = DriverM $ do
    cache <- gets (evalCache . snd)
    return $ M.lookup (block, env) cache

  newBlockId = DriverM $ do
    newId <- gets $ nextBlockId . snd
    modify $ onSnd \cache -> cache {nextBlockId = newId + 1 }
    return newId

  newStateId = DriverM $ do
    newId <- gets $ nextStateId . snd
    modify $ onSnd \cache -> cache {nextStateId = newId + 1 }
    return newId

  insertCache block env val = DriverM $ modify $ onSnd \cache ->
    cache { evalCache = M.insert (block, env) val $ evalCache cache }

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

instance Pretty SourceEvalState where
  pretty (SourceEvalState env worker pending) =
    "In env ID" <+> pretty (getNodeId env) <> line
    <> "waiting for" <+> pretty (show worker) <+> "to evaluate" <> line
    <> pretty (map prettify pending) where
    prettify (WithId blockId block) = (blockId, block)

instance Pretty DriverEvent where
  pretty (FileChanged contents) = "New file contents" <> line <> pretty contents
  pretty (WorkComplete env (WithId blockId block) (result, _)) =
    "Finished evaluating" <+> pretty (blockId, block)
    <+> "in env with ID" <+> pretty (getNodeId env)
    <+> "got" <+> pretty result

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
