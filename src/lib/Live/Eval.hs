-- Copyright 2023 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Live.Eval (
  watchAndEvalFile, ResultsServer, ResultsUpdate, subscribeIO, dagAsUpdate) where

import Control.Concurrent
import Control.Monad
import Control.Monad.State.Strict
import qualified Data.Map.Strict as M
import Data.Aeson (ToJSON, ToJSONKey, toJSON, Value)
import Data.Functor ((<&>))
import Data.Maybe (fromJust)
import Data.Text (Text)
import GHC.Generics

import Actor
import IncState
import Types.Misc
import Types.Source
import TopLevel
import ConcreteSyntax
import RenderHtml (ToMarkup, pprintHtml)
import MonadUtil

-- === Top-level interface ===

-- `watchAndEvalFile` returns the channel by which a client may
-- subscribe by sending a write-only view of its input channel.
watchAndEvalFile :: FilePath -> EvalConfig -> TopStateEx
                 -> IO (Evaluator SourceBlock Result)
watchAndEvalFile fname opts env = do
  watcher <- launchFileWatcher fname
  parser <- launchCellParser watcher \source -> uModuleSourceBlocks $ parseUModule Main source
  launchDagEvaluator parser env (evalSourceBlockIO opts)

type ResultsServer = Evaluator        SourceBlock Result
type ResultsUpdate = EvalStatusUpdate SourceBlock Result

-- === DAG diff state ===

-- We intend to make this an arbitrary Dag at some point but for now we just
-- assume that dependence is just given by the top-to-bottom ordering of blocks
-- within the file.

type NodeId = Int

data NodeList a = NodeList
  { orderedNodes :: [NodeId]
  , nodeMap      :: M.Map NodeId a }
  deriving (Show, Generic)

data NodeListUpdate a = NodeListUpdate
  { orderedNodesUpdate :: TailUpdate NodeId
  , nodeMapUpdate      :: MapUpdate NodeId a }
  deriving (Show, Functor, Generic)

instance Semigroup (NodeListUpdate a) where
  NodeListUpdate x1 y1 <> NodeListUpdate x2 y2 = NodeListUpdate (x1<>x2) (y1<>y2)

instance Monoid (NodeListUpdate a) where
  mempty = NodeListUpdate mempty mempty

instance IncState (NodeList a) (NodeListUpdate a) where
  applyDiff (NodeList m xs) (NodeListUpdate dm dxs) =
    NodeList (applyDiff m dm) (applyDiff xs dxs)

type Dag       = NodeList
type DagUpdate = NodeListUpdate

dagAsUpdate :: Dag a -> DagUpdate a
dagAsUpdate (NodeList xs m)= NodeListUpdate (TailUpdate 0 xs) (MapUpdate $ fmap Create m)

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

computeNodeListUpdate :: (Eq a, FreshNames NodeId m) => NodeList a -> [a] -> m (NodeListUpdate a)
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
  initContents <- subscribe Update_CP fileWatcher
  initNodeList <- buildNodeList $ parseCells initContents
  runIncServerT initNodeList $ messageLoop \case
    Subscribe_CP msg -> handleSubscribeMsg msg
    Update_CP NoChange -> return ()
    Update_CP (OverwriteWith newContents) -> do
      let newCells = parseCells newContents
      curNodeList <- getl It
      update =<< computeNodeListUpdate curNodeList newCells
      flushDiffs

-- === Dag evaluator ===

-- This is where we track the state of evaluation and decide what we needs to be
-- run and what needs to be killed.

type Evaluator i o = StateServer (EvalStatus i o) (EvalStatusUpdate i o)
newtype EvaluatorM s i o a =
  EvaluatorM { runEvaluatorM' ::
                 IncServerT (EvalStatus i o) (EvalStatusUpdate i o)
                   (StateT (EvaluatorState s i o)
                      (ActorM (EvaluatorMsg s i o))) a }
  deriving (Functor, Applicative, Monad, MonadIO,
            Actor (EvaluatorMsg s i o),
            IncServer (EvalStatus i o) (EvalStatusUpdate i o))

instance DefuncState (EvaluatorMUpdate s i o) (EvaluatorM s i o) where
  update = \case
    UpdateDagEU dag     -> EvaluatorM $ update dag
    UpdateCurJob status -> EvaluatorM $ lift $ modify \s -> s { curRunningJob = status }
    UpdateEnvs   envs   -> EvaluatorM $ lift $ modify \s -> s { prevEnvs      = envs}
    AppendEnv env -> do
      envs <- getl PrevEnvs
      update $ UpdateEnvs $ envs ++ [env]
    UpdateJobStatus nodeId status -> do
      NodeState i _ <- fromJust <$> getl (NodeInfo nodeId)
      let newState = NodeState i status
      update $ UpdateDagEU $ NodeListUpdate mempty $ MapUpdate $ M.singleton nodeId (Update newState)

instance LabelReader (EvaluatorMLabel s i o) (EvaluatorM s i o) where
  getl l = case l of
    NodeListEM      -> EvaluatorM $ orderedNodes                <$> getl It
    NodeInfo nodeId -> EvaluatorM $ M.lookup nodeId <$> nodeMap <$> getl It
    PrevEnvs        -> EvaluatorM $ lift $ prevEnvs      <$> get
    CurRunningJob   -> EvaluatorM $ lift $ curRunningJob <$> get
    EvalFun         -> EvaluatorM $ lift $ evalFun       <$> get

data EvaluatorMUpdate s i o =
   UpdateDagEU  (NodeListUpdate (NodeState i o))
 | UpdateJobStatus NodeId (NodeEvalStatus o)
 | UpdateCurJob CurJobStatus
 | UpdateEnvs [s]
 | AppendEnv s

data EvaluatorMLabel s i o a where
  NodeListEM    ::           EvaluatorMLabel s i o [NodeId]
  NodeInfo      :: NodeId -> EvaluatorMLabel s i o (Maybe (NodeState i o))
  PrevEnvs      ::           EvaluatorMLabel s i o [s]
  CurRunningJob ::           EvaluatorMLabel s i o (CurJobStatus)
  EvalFun       ::           EvaluatorMLabel s i o (EvalFun s i o)

-- The envs after each cell evaluated so far
type EvalFun s i o = s -> i -> IO (o, s)
type CurJobStatus = Maybe (ThreadId, NodeId, CellIndex)

data EvaluatorState s i o = EvaluatorState
  { prevEnvs      :: [s]
  , evalFun       :: EvalFun s i o
  , curRunningJob :: CurJobStatus }

data NodeEvalStatus o =
   Waiting
 | Running
 | Complete o
   deriving (Show, Generic)

data NodeState i o = NodeState i (NodeEvalStatus o) deriving (Show, Generic)

type Show3 s i o = (Show s, Show i, Show o)

type EvalStatus       i o = NodeList       (NodeState i o)
type EvalStatusUpdate i o = NodeListUpdate (NodeState i o)

type CellIndex = Int -- index in the list of cells, not the NodeId

data EvaluatorMsg s i o =
   SourceUpdate (DagUpdate i)
 | JobComplete ThreadId s o
 | Subscribe_E (SubscribeMsg (EvalStatus i o) (EvalStatusUpdate i o))
   deriving (Show)

initEvaluatorState :: s -> EvalFun s i o -> EvaluatorState s i o
initEvaluatorState s evalCell = EvaluatorState [s] evalCell Nothing

launchDagEvaluator :: (Show3 s i o, MonadIO m) => CellParser i -> s -> EvalFun s i o -> m (Evaluator i o)
launchDagEvaluator cellParser env evalCell = do
  mailbox <- launchActor do
    let s = initEvaluatorState env evalCell
    void $ flip runStateT s $ runIncServerT emptyNodeList $ runEvaluatorM' $
      dagEvaluatorImpl cellParser
  return $ sliceMailbox Subscribe_E mailbox

dagEvaluatorImpl :: (Show3 s i o) => CellParser i -> EvaluatorM s i o ()
dagEvaluatorImpl cellParser = do
  initDag <- subscribe SourceUpdate cellParser
  processDagUpdate (dagAsUpdate initDag) >> flushDiffs
  launchNextJob
  messageLoop \case
    Subscribe_E msg        -> handleSubscribeMsg msg
    SourceUpdate dagUpdate -> do
      processDagUpdate dagUpdate
      flushDiffs
    JobComplete threadId env result -> do
      processJobComplete threadId env result
      flushDiffs

processJobComplete :: (Show3 s i o) => ThreadId -> s -> o -> EvaluatorM s i o ()
processJobComplete threadId newEnv result = do
  getl CurRunningJob >>= \case
    Just (expectedThreadId, nodeId, _) -> do
      when (threadId == expectedThreadId) do -- otherwise it's a zombie
        update $ UpdateJobStatus nodeId (Complete result)
        update $ UpdateCurJob Nothing
        update $ AppendEnv newEnv
        launchNextJob
    Nothing -> return () -- this job is a zombie

nextJobIndex :: EvaluatorM s i o Int
nextJobIndex = do
  envs <- getl PrevEnvs
  return $ length envs - 1

launchNextJob :: (Show3 s i o) => EvaluatorM s i o ()
launchNextJob = do
  jobIndex <- nextJobIndex
  nodeList <- getl NodeListEM
  when (jobIndex < length nodeList) do -- otherwise we're all done
    curEnv <- (!! jobIndex) <$> getl PrevEnvs
    let nodeId = nodeList !! jobIndex
    launchJob jobIndex nodeId curEnv

launchJob :: (Show3 s i o) => CellIndex -> NodeId -> s -> EvaluatorM s i o ()
launchJob jobIndex nodeId env = do
  jobAction <- getl EvalFun
  NodeState source _ <- fromJust <$> getl (NodeInfo nodeId)
  resultMailbox <- selfMailbox id
  threadId <- liftIO $ forkIO do
    threadId <- myThreadId
    (result, finalEnv) <- jobAction env source
    send resultMailbox $ JobComplete threadId finalEnv result
  update $ UpdateJobStatus nodeId Running
  update $ UpdateCurJob (Just (threadId, nodeId, jobIndex))

computeNumValidCells :: DagUpdate i -> EvaluatorM s i o Int
computeNumValidCells dagUpdate = do
  let nDropped = numDropped $ orderedNodesUpdate dagUpdate
  nTotal <- length <$> getl NodeListEM
  return $ nTotal - nDropped

processDagUpdate :: (Show3 s i o) => DagUpdate i -> EvaluatorM s i o ()
processDagUpdate dagUpdate = do
  nValid <- computeNumValidCells dagUpdate
  envs <- getl PrevEnvs
  update $ UpdateEnvs $ take (nValid + 1) envs
  update $ UpdateDagEU $ fmap (\i -> NodeState i Waiting) dagUpdate
  getl CurRunningJob >>= \case
    Nothing -> launchNextJob
    Just (threadId, _, jobIndex)
      | (jobIndex >= nValid) -> do
          -- Current job is no longer valid. Kill it and restart.
          liftIO $ killThread threadId
          update $ UpdateCurJob Nothing
          launchNextJob
      | otherwise -> return () -- Current job is fine. Let it continue.

-- === instances ===

instance ToJSON a => ToJSON (NodeListUpdate a)
instance (ToJSON a, ToJSONKey k) => ToJSON (MapUpdate k a)
instance ToJSON a => ToJSON (TailUpdate a)
instance ToJSON a => ToJSON (MapEltUpdate a)
instance ToJSON o => ToJSON (NodeEvalStatus o)
instance (ToJSON i, ToJSON o) => ToJSON (NodeState i o)

instance ToJSON SourceBlock where
  toJSON b = toJSON (sbLine b, pprintHtml b)
instance ToJSON Result      where toJSON = toJSONViaHtml

toJSONViaHtml :: ToMarkup a => a -> Value
toJSONViaHtml x = toJSON $ pprintHtml x
