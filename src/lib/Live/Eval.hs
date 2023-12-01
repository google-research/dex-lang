-- Copyright 2023 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE UndecidableInstances #-}

module Live.Eval (
  watchAndEvalFile, EvalServer, EvalUpdate, CellsUpdate, fmapCellsUpdate,
  NodeList (..), NodeListUpdate (..), subscribeIO, nodeListAsUpdate) where

import Control.Concurrent
import Control.Monad
import Control.Monad.State.Strict
import Control.Monad.Writer.Strict
import qualified Data.Map.Strict as M
import Data.Aeson (ToJSON)
import Data.Functor ((<&>))
import Data.Maybe (fromJust)
import Data.Text (Text)
import Prelude hiding (span)
import GHC.Generics

import Actor
import IncState
import Types.Source
import TopLevel
import ConcreteSyntax
import MonadUtil

-- === Top-level interface ===

type EvalServer = StateServer EvalState EvalUpdate
type EvalState  = CellsState  SourceBlock Result
type EvalUpdate = CellsUpdate SourceBlock Result

-- `watchAndEvalFile` returns the channel by which a client may
-- subscribe by sending a write-only view of its input channel.
watchAndEvalFile :: FilePath -> EvalConfig -> TopStateEx -> IO EvalServer
watchAndEvalFile fname opts env = do
  watcher <- launchFileWatcher fname
  parser <- launchCellParser watcher \source -> uModuleSourceBlocks $ parseUModule Main source
  launchDagEvaluator parser env (evalSourceBlockIO' opts)

-- shim to pretend that evalSourceBlockIO streams its results. TODO: make it actually do that.
evalSourceBlockIO'
  :: EvalConfig -> Mailbox Result -> TopStateEx -> SourceBlock -> IO TopStateEx
evalSourceBlockIO' cfg resultChan env block = do
  (result, env') <- evalSourceBlockIO cfg env block
  send resultChan result
  return env'

fmapCellsUpdate :: CellsUpdate i o -> (NodeId -> i -> i') -> (NodeId -> o -> o') -> CellsUpdate i' o'
fmapCellsUpdate (NodeListUpdate t m) fi fo = NodeListUpdate t m' where
  m' = mapUpdateMapWithKey m
         (\k (CellState i s o) -> CellState (fi k i) s (fo k o))
         (\k (CellUpdate  s o) -> CellUpdate         s (fo k o))

-- === DAG diff state ===

-- We intend to make this an arbitrary Dag at some point but for now we just
-- assume that dependence is just given by the top-to-bottom ordering of blocks
-- within the file.

type NodeId = Int

data NodeList a = NodeList
  { orderedNodes :: [NodeId]
  , nodeMap      :: M.Map NodeId a }
  deriving (Show, Generic)

data NodeListUpdate s d = NodeListUpdate
  { orderedNodesUpdate :: TailUpdate NodeId
  , nodeMapUpdate      :: MapUpdate NodeId s d }
  deriving (Show, Generic)

instance IncState s d => Semigroup (NodeListUpdate s d) where
  NodeListUpdate x1 y1 <> NodeListUpdate x2 y2 = NodeListUpdate (x1<>x2) (y1<>y2)

instance IncState s d => Monoid (NodeListUpdate s d) where
  mempty = NodeListUpdate mempty mempty

instance IncState s d => IncState (NodeList s) (NodeListUpdate s d) where
  applyDiff (NodeList m xs) (NodeListUpdate dm dxs) =
    NodeList (applyDiff m dm) (applyDiff xs dxs)

type Dag       a = NodeList (Unchanging a)
type DagUpdate a = NodeListUpdate (Unchanging a) ()

nodeListAsUpdate :: NodeList s -> NodeListUpdate s d
nodeListAsUpdate (NodeList xs m)= NodeListUpdate (TailUpdate 0 xs) (MapUpdate $ fmap Create m)

emptyNodeList :: NodeList a
emptyNodeList = NodeList [] mempty

buildNodeList :: FreshNames NodeId m => [a] -> m (NodeList a)
buildNodeList vals = do
  nodeList <- forM vals \val -> do
    nodeId <- freshName
    return (nodeId, val)
  return $ NodeList (fst <$> nodeList) (M.fromList nodeList)

commonPrefixLength :: Eq a => [a] -> [a] -> Int
commonPrefixLength (x:xs) (y:ys) | x == y = 1 + commonPrefixLength xs ys
commonPrefixLength _ _ = 0

nodeListVals :: NodeList a -> [a]
nodeListVals nodes = orderedNodes nodes <&> \k -> fromJust $ M.lookup k (nodeMap nodes)

computeNodeListUpdate :: (Eq s, FreshNames NodeId m) => NodeList s -> [s] -> m (NodeListUpdate s d)
computeNodeListUpdate nodes newVals = do
  let prefixLength = commonPrefixLength (nodeListVals nodes) newVals
  let oldTail = drop prefixLength $ orderedNodes nodes
  NodeList newTail nodesCreated <- buildNodeList $ drop prefixLength newVals
  let nodeUpdates = fmap Create nodesCreated <> M.fromList (fmap (,Delete) oldTail)
  return $ NodeListUpdate (TailUpdate (length oldTail) newTail) (MapUpdate nodeUpdates)

-- === Cell parser ===

-- This coarsely parses the full file into blocks and forms a DAG (for now a
-- trivial one assuming all top-to-bottom dependencies) of the results.

type CellParser a = StateServer (Dag a) (DagUpdate a)

data CellParserMsg a =
    Subscribe_CP (SubscribeMsg (Dag a) (DagUpdate a))
  | Update_CP (Overwrite Text)
  deriving (Show)

launchCellParser :: (Eq a, MonadIO m) => FileWatcher -> (Text -> [a]) -> m (CellParser a)
launchCellParser fileWatcher parseCells =
  sliceMailbox Subscribe_CP <$> launchActor (cellParserImpl fileWatcher parseCells)

cellParserImpl :: Eq a => FileWatcher -> (Text -> [a]) -> ActorM (CellParserMsg a) ()
cellParserImpl fileWatcher parseCells = runFreshNameT do
  Overwritable initContents <- subscribe Update_CP fileWatcher
  initNodeList <- buildNodeList $ fmap Unchanging $ parseCells initContents
  runIncServerT initNodeList $ messageLoop \case
    Subscribe_CP msg -> handleSubscribeMsg msg
    Update_CP NoChange -> return ()
    Update_CP (OverwriteWith newContents) -> do
      let newCells = fmap Unchanging $ parseCells newContents
      curNodeList <- getl It
      update =<< computeNodeListUpdate curNodeList newCells
      flushDiffs

-- === Dag evaluator ===

-- This is where we track the state of evaluation and decide what we needs to be
-- run and what needs to be killed.

type Evaluator i o = StateServer (CellsState i o) (CellsUpdate i o)
newtype EvaluatorM s i o a =
  EvaluatorM { runEvaluatorM' ::
                 IncServerT (CellsState i o) (CellsUpdate i o)
                   (StateT (EvaluatorState s i o)
                      (ActorM (EvaluatorMsg s i o))) a }
  deriving (Functor, Applicative, Monad, MonadIO,
            Actor (EvaluatorMsg s i o))
deriving instance Monoid o => IncServer (CellsState i o) (CellsUpdate i o) (EvaluatorM s i o)

instance Monoid o => Semigroup (CellUpdate o) where
  CellUpdate s o <> CellUpdate s' o' = CellUpdate (s<>s') (o<>o')

instance Monoid o => Monoid (CellUpdate o) where
  mempty = CellUpdate mempty mempty

instance Monoid o => IncState (CellState i o) (CellUpdate o) where
  applyDiff (CellState source status result) (CellUpdate status' result') =
    CellState source (fromOverwritable (applyDiff (Overwritable status) status')) (result <> result')

instance Monoid o => DefuncState (EvaluatorMUpdate s i o) (EvaluatorM s i o) where
  update = \case
    UpdateDagEU dag     -> EvaluatorM $ update dag
    UpdateCurJob status -> EvaluatorM $ lift $ modify \s -> s { curRunningJob = status }
    UpdateEnvs   envs   -> EvaluatorM $ lift $ modify \s -> s { prevEnvs      = envs}
    AppendEnv env -> do
      envs <- getl PrevEnvs
      update $ UpdateEnvs $ envs ++ [env]
    UpdateCellState nodeId cellUpdate -> update $ UpdateDagEU $ NodeListUpdate mempty $
      MapUpdate $ M.singleton nodeId $ Update cellUpdate

instance Monoid o => LabelReader (EvaluatorMLabel s i o) (EvaluatorM s i o) where
  getl l = case l of
    NodeListEM      -> EvaluatorM $ orderedNodes                <$> getl It
    NodeInfo nodeId -> EvaluatorM $ M.lookup nodeId <$> nodeMap <$> getl It
    PrevEnvs        -> EvaluatorM $ lift $ prevEnvs      <$> get
    CurRunningJob   -> EvaluatorM $ lift $ curRunningJob <$> get
    EvalFun         -> EvaluatorM $ lift $ evalFun       <$> get

data EvaluatorMUpdate s i o =
   UpdateDagEU (NodeListUpdate (CellState i o) (CellUpdate o))
 | UpdateCellState NodeId (CellUpdate o)
 | UpdateCurJob CurJobStatus
 | UpdateEnvs [s]
 | AppendEnv s

data EvaluatorMLabel s i o a where
  NodeListEM    ::           EvaluatorMLabel s i o [NodeId]
  NodeInfo      :: NodeId -> EvaluatorMLabel s i o (Maybe (CellState i o))
  PrevEnvs      ::           EvaluatorMLabel s i o [s]
  CurRunningJob ::           EvaluatorMLabel s i o (CurJobStatus)
  EvalFun       ::           EvaluatorMLabel s i o (EvalFun s i o)

-- `s` is the persistent state (i.e. TopEnvEx the environment)
-- `i` is the type of input cell (e.g. SourceBlock)
-- `o` is the (monoidal) type of updates, e.g. `Result`
type EvalFun s i o = Mailbox o -> s -> i -> IO s
-- It's redundant to have both NodeId and TheadId but it defends against
-- possible GHC reuse of ThreadId (I don't know if that can actually happen)
type JobId = (ThreadId, NodeId)
type CurJobStatus = Maybe (JobId, CellIndex)

data EvaluatorState s i o = EvaluatorState
  { prevEnvs      :: [s]
  , evalFun       :: EvalFun s i o
  , curRunningJob :: CurJobStatus }

data CellStatus = Waiting | Running | Complete deriving (Show, Generic)

data CellState i o = CellState i CellStatus o             deriving (Show, Generic)
data CellUpdate o  = CellUpdate (Overwrite CellStatus) o  deriving (Show, Generic)

type Show3 s i o = (Show s, Show i, Show o)

type CellsState  i o = NodeList       (CellState i o)
type CellsUpdate i o = NodeListUpdate (CellState i o) (CellUpdate o)

type CellIndex = Int -- index in the list of cells, not the NodeId

data JobUpdate o s = PartialJobUpdate o | JobComplete s deriving (Show)

data EvaluatorMsg s i o =
   SourceUpdate (DagUpdate i)
 | JobUpdate JobId (JobUpdate o s)
 | Subscribe_E (SubscribeMsg (CellsState i o) (CellsUpdate i o))
   deriving (Show)

initEvaluatorState :: s -> EvalFun s i o -> EvaluatorState s i o
initEvaluatorState s evalCell = EvaluatorState [s] evalCell Nothing

launchDagEvaluator :: (Show3 s i o, Monoid o, MonadIO m) => CellParser i -> s -> EvalFun s i o -> m (Evaluator i o)
launchDagEvaluator cellParser env evalCell = do
  mailbox <- launchActor do
    let s = initEvaluatorState env evalCell
    void $ flip runStateT s $ runIncServerT emptyNodeList $ runEvaluatorM' $
      dagEvaluatorImpl cellParser
  return $ sliceMailbox Subscribe_E mailbox

dagEvaluatorImpl :: (Show3 s i o, Monoid o) => CellParser i -> EvaluatorM s i o ()
dagEvaluatorImpl cellParser = do
  initDag <- subscribe SourceUpdate cellParser
  processDagUpdate (nodeListAsUpdate initDag) >> flushDiffs
  launchNextJob
  messageLoop \case
    Subscribe_E msg        -> handleSubscribeMsg msg
    SourceUpdate dagUpdate -> do
      processDagUpdate dagUpdate
      flushDiffs
    JobUpdate jobId jobUpdate -> do
      processJobUpdate jobId jobUpdate
      flushDiffs

processJobUpdate :: (Show3 s i o, Monoid o) => JobId -> JobUpdate o s -> EvaluatorM s i o ()
processJobUpdate jobId jobUpdate = do
  getl CurRunningJob >>= \case
    Just (jobId', _) -> when (jobId == jobId') do
      let nodeId = snd jobId
      case jobUpdate of
        JobComplete newEnv -> do
          update $ UpdateCellState nodeId $ CellUpdate (OverwriteWith Complete) mempty
          update $ UpdateCurJob Nothing
          update $ AppendEnv newEnv
          launchNextJob
          flushDiffs
        PartialJobUpdate result -> update $ UpdateCellState nodeId $ CellUpdate NoChange result
    Nothing -> return () -- this job is a zombie

nextCellIndex :: Monoid o => EvaluatorM s i o Int
nextCellIndex = do
  envs <- getl PrevEnvs
  return $ length envs - 1

launchNextJob :: (Show3 s i o, Monoid o) => EvaluatorM s i o ()
launchNextJob = do
  cellIndex <- nextCellIndex
  nodeList <- getl NodeListEM
  when (cellIndex < length nodeList) do -- otherwise we're all done
    curEnv <- (!! cellIndex) <$> getl PrevEnvs
    let nodeId = nodeList !! cellIndex
    launchJob cellIndex nodeId curEnv

launchJob :: (Show3 s i o, Monoid o) => CellIndex -> NodeId -> s -> EvaluatorM s i o ()
launchJob cellIndex nodeId env = do
  jobAction <- getl EvalFun
  CellState source _ _ <- fromJust <$> getl (NodeInfo nodeId)
  mailbox <- selfMailbox id
  update $ UpdateCellState nodeId $ CellUpdate (OverwriteWith Running) mempty
  threadId <- liftIO $ forkIO do
    threadId <- myThreadId
    let jobId = (threadId, nodeId)
    let resultsMailbox = sliceMailbox (JobUpdate jobId . PartialJobUpdate) mailbox
    finalEnv <- jobAction resultsMailbox env source
    send mailbox $ JobUpdate jobId $ JobComplete finalEnv
  let jobId = (threadId, nodeId)
  update $ UpdateCurJob (Just (jobId, cellIndex))

computeNumValidCells :: Monoid o => TailUpdate NodeId -> EvaluatorM s i o Int
computeNumValidCells tailUpdate = do
  let nDropped = numDropped tailUpdate
  nTotal <- length <$> getl NodeListEM
  return $ nTotal - nDropped

processDagUpdate :: (Show3 s i o, Monoid o) => DagUpdate i -> EvaluatorM s i o ()
processDagUpdate (NodeListUpdate tailUpdate mapUpdate) = do
  nValid <- computeNumValidCells tailUpdate
  envs <- getl PrevEnvs
  update $ UpdateEnvs $ take (nValid + 1) envs
  update $ UpdateDagEU $ NodeListUpdate tailUpdate $ mapUpdateMapWithKey mapUpdate
    (\_ (Unchanging i) -> CellState i Waiting mempty)
    (\_ () -> mempty)
  getl CurRunningJob >>= \case
    Nothing -> launchNextJob
    Just ((threadId, _), cellIndex)
      | (cellIndex >= nValid) -> do
          -- Current job is no longer valid. Kill it and restart.
          liftIO $ killThread threadId
          update $ UpdateCurJob Nothing
          launchNextJob
      | otherwise -> return () -- Current job is fine. Let it continue.

-- === instances ===

instance                         ToJSON CellStatus
instance (ToJSON i, ToJSON o) => ToJSON (CellState i o)
instance            ToJSON o  => ToJSON (CellUpdate o)
instance (ToJSON s, ToJSON d) => ToJSON (NodeListUpdate s d)
