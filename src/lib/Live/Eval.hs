-- Copyright 2023 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE UndecidableInstances #-}

module Live.Eval (
  watchAndEvalFile, EvalServer, CellState (..), CellUpdate (..), CellsState, CellsUpdate,
  NodeList (..), NodeListUpdate (..), subscribeIO,
  CellStatus (..), nodeListAsUpdate, NodeId, evalFileNonInteractive) where

import Control.Concurrent
import Control.Monad
import Control.Monad.State.Strict
import Control.Monad.Writer.Strict
import qualified Data.Map.Strict as M
import Data.Aeson (ToJSON)
import Data.Functor ((<&>))
import Data.Maybe (fromJust)
import Data.Text (Text)
import Data.IORef
import Prelude hiding (span)
import GHC.Generics

import Actor
import IncState
import Types.Source
import TopLevel
import ConcreteSyntax
import MonadUtil
import Util (readFileText)

-- === Top-level interface ===

type EvalServer = StateServer CellsState

-- `watchAndEvalFile` returns the channel by which a client may
-- subscribe by sending a write-only view of its input channel.
watchAndEvalFile :: FilePath -> EvalConfig -> TopStateEx -> IO EvalServer
watchAndEvalFile fname opts env = do
  watcher <- launchFileWatcher fname
  parser <- launchCellParser watcher \source -> uModuleSourceBlocks $ parseUModule Main source
  launchDagEvaluator opts parser env

sourceBlockEvalFun :: EvalConfig -> Mailbox Outputs -> TopStateEx -> SourceBlock -> IO (ExitStatus, TopStateEx)
sourceBlockEvalFun cfg resultChan env block =
  evalSourceBlockIO cfg (send resultChan) env block

-- === Evaluating non-interactively to produce a standalone HTML page ===

evalFileNonInteractive :: FilePath -> EvalConfig -> TopStateEx -> IO CellsState
evalFileNonInteractive fname cfg initEnv = do
  envRef <- newIORef initEnv
  blocks <- parseSourceBlocks <$> readFileText fname
  cellStates <- forM blocks \block -> do
    if isInert block
      then return $ CellState block Inert mempty
      else do
        env <- readIORef envRef
        ((exitStatus, newEnv), outs) <- captureLogs \logger ->
          evalSourceBlockIO cfg logger env block
        writeIORef envRef newEnv
        return $ CellState block (exitStatusAsCellStatus exitStatus) outs
  runFreshNameT $ buildNodeList cellStates


-- === DAG diff state ===

-- We intend to make this an arbitrary Dag at some point but for now we just
-- assume that dependence is just given by the top-to-bottom ordering of blocks
-- within the file.

type NodeId = Int

data NodeList a = NodeList
  { orderedNodes :: [NodeId]
  , nodeMap      :: M.Map NodeId a }
  deriving (Show, Generic, Functor)

data NodeListUpdate s = NodeListUpdate
  { orderedNodesUpdate :: TailUpdate NodeId
  , nodeMapUpdate      :: MapUpdate NodeId s }
  deriving (Generic)

instance IncState s => Semigroup (NodeListUpdate s) where
  NodeListUpdate x1 y1 <> NodeListUpdate x2 y2 = NodeListUpdate (x1<>x2) (y1<>y2)

instance IncState s => Monoid (NodeListUpdate s) where
  mempty = NodeListUpdate mempty mempty

instance IncState s => IncState (NodeList s) where
  type Delta (NodeList s) = NodeListUpdate s
  applyDiff (NodeList m xs) (NodeListUpdate dm dxs) =
    NodeList (applyDiff m dm) (applyDiff xs dxs)

type Dag       a = NodeList (Unchanging a)
type DagUpdate a = NodeListUpdate (Unchanging a)

nodeListAsUpdate :: NodeList s -> NodeListUpdate s
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

computeNodeListUpdate :: (Eq s, FreshNames NodeId m) => NodeList s -> [s] -> m (NodeListUpdate s)
computeNodeListUpdate nodes newVals = do
  let prefixLength = commonPrefixLength (nodeListVals nodes) newVals
  let oldTail = drop prefixLength $ orderedNodes nodes
  NodeList newTail nodesCreated <- buildNodeList $ drop prefixLength newVals
  let nodeUpdates = fmap Create nodesCreated <> M.fromList (fmap (,Delete) oldTail)
  return $ NodeListUpdate (TailUpdate (length oldTail) newTail) (MapUpdate nodeUpdates)

-- === Cell parser ===

-- This coarsely parses the full file into blocks and forms a DAG (for now a
-- trivial one assuming all top-to-bottom dependencies) of the results.

type CellParser = StateServer (Dag SourceBlock)

data CellParserMsg =
    Subscribe_CP (SubscribeMsg (Dag SourceBlock))
  | Update_CP (Overwrite Text)
  deriving (Show)

launchCellParser :: MonadIO m => FileWatcher -> (Text -> [SourceBlock]) -> m CellParser
launchCellParser fileWatcher parseCells =
  sliceMailbox Subscribe_CP <$> launchActor (cellParserImpl fileWatcher parseCells)

cellParserImpl :: FileWatcher -> (Text -> [SourceBlock]) -> ActorM CellParserMsg ()
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

type Evaluator = StateServer CellsState
newtype EvaluatorM a =
  EvaluatorM { runEvaluatorM' ::
                 IncServerT CellsState
                   (StateT EvaluatorState
                      (ActorM EvaluatorMsg)) a }
  deriving (Functor, Applicative, Monad, MonadIO, Actor (EvaluatorMsg))
deriving instance IncServer CellsState EvaluatorM

instance DefuncState EvaluatorMUpdate EvaluatorM where
  update = \case
    UpdateDagEU dag     -> EvaluatorM $ update dag
    UpdateCurJob status -> EvaluatorM $ lift $ modify \s -> s { curRunningJob = status }
    UpdateEnvs   envs   -> EvaluatorM $ lift $ modify \s -> s { prevEnvs      = envs}
    AppendEnv env -> do
      envs <- getl PrevEnvs
      update $ UpdateEnvs $ envs ++ [env]
    UpdateCellState nodeId cellUpdate -> update $ UpdateDagEU $ NodeListUpdate mempty $
      MapUpdate $ M.singleton nodeId $ Update cellUpdate

instance LabelReader EvaluatorMLabel EvaluatorM where
  getl l = case l of
    NodeListEM      -> EvaluatorM $ orderedNodes                <$> getl It
    NodeInfo nodeId -> EvaluatorM $ M.lookup nodeId <$> nodeMap <$> getl It
    PrevEnvs        -> EvaluatorM $ lift $ prevEnvs      <$> get
    CurRunningJob   -> EvaluatorM $ lift $ curRunningJob <$> get
    EvalCfg         -> EvaluatorM $ lift $ evaluatorCfg <$> get

data EvaluatorMUpdate =
   UpdateDagEU (NodeListUpdate CellState)
 | UpdateCellState NodeId CellUpdate
 | UpdateCurJob CurJobStatus
 | UpdateEnvs [TopStateEx]
 | AppendEnv TopStateEx

data EvaluatorMLabel a where
  NodeListEM    ::           EvaluatorMLabel [NodeId]
  NodeInfo      :: NodeId -> EvaluatorMLabel (Maybe CellState)
  PrevEnvs      ::           EvaluatorMLabel [TopStateEx]
  CurRunningJob ::           EvaluatorMLabel (CurJobStatus)
  EvalCfg       ::           EvaluatorMLabel EvalConfig

-- It's redundant to have both NodeId and TheadId but it defends against
-- possible GHC reuse of ThreadId (I don't know if that can actually happen)
type JobId = (ThreadId, NodeId)
type CurJobStatus = Maybe (JobId, CellIndex)

data EvaluatorState = EvaluatorState
  { evaluatorCfg  :: EvalConfig
  , prevEnvs      :: [TopStateEx]
  , curRunningJob :: CurJobStatus }

data CellStatus =
    Waiting
  | Running            -- TODO: split into compiling/running
  | Complete           -- completed without errors
  | CompleteWithErrors
  | Inert              -- doesn't require running at all
    deriving (Show, Generic)

data CellState  = CellState SourceBlock CellStatus Outputs
     deriving (Show, Generic)

data CellUpdate = CellUpdate (Overwrite CellStatus) Outputs deriving (Show, Generic)

type CellsState  = NodeList       CellState
type CellsUpdate = NodeListUpdate CellState

type CellIndex = Int -- index in the list of cells, not the NodeId

data JobUpdate =
    PartialJobUpdate   Outputs
  | JobComplete        (ExitStatus, TopStateEx)
    deriving (Show)

data EvaluatorMsg =
   SourceUpdate (DagUpdate SourceBlock)
 | JobUpdate JobId JobUpdate
 | Subscribe_E (SubscribeMsg CellsState)

initEvaluatorState :: EvalConfig -> TopStateEx -> EvaluatorState
initEvaluatorState cfg s = EvaluatorState cfg [s] Nothing

launchDagEvaluator :: MonadIO m => EvalConfig -> CellParser -> TopStateEx -> m Evaluator
launchDagEvaluator cfg cellParser env = do
  mailbox <- launchActor do
    let s = initEvaluatorState cfg env
    void $ flip runStateT s $ runIncServerT emptyNodeList $ runEvaluatorM' $
      dagEvaluatorImpl cellParser
  return $ sliceMailbox Subscribe_E mailbox

dagEvaluatorImpl :: CellParser -> EvaluatorM ()
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

processJobUpdate :: JobId -> JobUpdate -> EvaluatorM ()
processJobUpdate jobId jobUpdate = do
  getl CurRunningJob >>= \case
    Just (jobId', _) -> when (jobId == jobId') do
      let nodeId = snd jobId
      case jobUpdate of
        JobComplete (exitStatus, newEnv) -> do
          let newStatus = exitStatusAsCellStatus exitStatus
          update $ UpdateCellState nodeId $ CellUpdate (OverwriteWith newStatus) mempty
          update $ UpdateCurJob Nothing
          update $ AppendEnv newEnv
          launchNextJob
          flushDiffs
        PartialJobUpdate result -> update $ UpdateCellState nodeId $ CellUpdate NoChange result
    Nothing -> return () -- this job is a zombie

exitStatusAsCellStatus :: ExitStatus -> CellStatus
exitStatusAsCellStatus = \case
  ExitSuccess -> Complete
  ExitFailure -> CompleteWithErrors

nextCellIndex :: EvaluatorM Int
nextCellIndex = do
  envs <- getl PrevEnvs
  return $ length envs - 1

launchNextJob :: EvaluatorM ()
launchNextJob = do
  cellIndex <- nextCellIndex
  nodeList <- getl NodeListEM
  when (cellIndex < length nodeList) do -- otherwise we're all done
    curEnv <- (!! cellIndex) <$> getl PrevEnvs
    let nodeId = nodeList !! cellIndex
    CellState source _ _ <- fromJust <$> getl (NodeInfo nodeId)
    if isInert source
      then do
        update $ AppendEnv curEnv
        launchNextJob
      else launchJob cellIndex nodeId curEnv

launchJob :: CellIndex -> NodeId -> TopStateEx -> EvaluatorM ()
launchJob cellIndex nodeId env = do
  jobAction <- sourceBlockEvalFun <$> getl EvalCfg
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

computeNumValidCells :: TailUpdate NodeId -> EvaluatorM Int
computeNumValidCells tailUpdate = do
  let nDropped = numDropped tailUpdate
  nTotal <- length <$> getl NodeListEM
  return $ nTotal - nDropped

processDagUpdate :: DagUpdate SourceBlock -> EvaluatorM ()
processDagUpdate (NodeListUpdate tailUpdate mapUpdate) = do
  nValid <- computeNumValidCells tailUpdate
  envs <- getl PrevEnvs
  update $ UpdateEnvs $ take (nValid + 1) envs
  update $ UpdateDagEU $ NodeListUpdate tailUpdate $ mapUpdateMapWithKey mapUpdate
    (\_ (Unchanging source) -> initCellState source)
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

isInert :: SourceBlock -> Bool
isInert sb = case sbContents sb of
  TopDecl _   -> False
  Command _ _ -> False
  DeclareForeign _ _ _ -> False
  DeclareCustomLinearization _ _ _ -> False
  Misc misc -> case misc of
    GetNameType _  -> False
    ImportModule _ -> False
    QueryEnv _     -> False
    ProseBlock _  -> True
    CommentLine   -> True
    EmptyLines    -> True
  UnParseable _ _ -> True

initCellState :: SourceBlock -> CellState
initCellState source = do
  let status = if isInert source
        then Inert
        else Waiting
  CellState source status mempty

-- === ToJSON ===

instance ToJSON CellStatus
instance (IncState s, ToJSON s, ToJSON (Delta s)) => ToJSON (NodeListUpdate s)

-- === IncState and related instance ===

instance Semigroup CellUpdate where
  CellUpdate s o <> CellUpdate s' o' = CellUpdate (s<>s') (o<>o')

instance Monoid CellUpdate where
  mempty = CellUpdate mempty mempty

instance IncState CellState where
  type Delta CellState = CellUpdate
  applyDiff (CellState source status result) (CellUpdate status' result') =
    CellState source (fromOverwritable (applyDiff (Overwritable status) status')) (result <> result')
