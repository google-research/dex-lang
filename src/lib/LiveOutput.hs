-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# OPTIONS_GHC -Wno-orphans #-}

module LiveOutput (runWeb, runTerminal) where

import Control.Concurrent
import Control.Monad
import Control.Monad.Reader
import Control.Monad.State.Strict

import Data.Binary.Builder (fromByteString, Builder)
import Data.List (nub, sort)
import Data.Foldable (toList, fold)
import qualified Data.Map.Strict as M

import Network.Wai
import Network.Wai.Handler.Warp (run)
import Network.HTTP.Types (status200, status404)
import Data.ByteString.Lazy (toStrict)
import Data.Aeson hiding (Result, Null, Value)
import qualified Data.Aeson as A
import System.Console.ANSI
import System.Directory
import System.IO

import Cat
import Syntax
import Actor
import Parser
import Env
import TopLevel hiding (evalSource)
import RenderHtml
import PPrint

type NodeId = Int
data RFragment = RFragment (SetVal [NodeId])
                           (M.Map NodeId SourceBlock)
                           (M.Map NodeId Result)

runWeb :: FilePath -> EvalConfig -> TopEnv -> IO ()
runWeb fname opts env = do
  resultsChan <- watchAndEvalFile fname opts env
  putStrLn "Streaming output to localhost:8000"
  run 8000 $ serveResults $ resultStream resultsChan

runTerminal :: FilePath -> EvalConfig -> TopEnv -> IO ()
runTerminal fname opts env = do
  resultsChan <- watchAndEvalFile fname opts env
  displayResultsTerm resultsChan

watchAndEvalFile :: FilePath -> EvalConfig -> TopEnv -> IO (ReqChan RFragment)
watchAndEvalFile fname opts env = runActor $ do
  (_, resultsChan) <- spawn Trap logServer
  let cfg = ((opts, env), subChan Push resultsChan)
  (_, sourceChan) <- spawn Trap $ runDriver cfg
  liftIO $ watchFile fname sourceChan
  return $ subChan Request resultsChan

-- === executing blocks concurrently ===

type SourceContents = String

type EnvMap = M.Map NodeId (MVar TopEnv)
type DriverCfg = ((EvalConfig, TopEnv), PChan RFragment)
type DriverM = ReaderT DriverCfg
                 (CatT (Dag SourceBlock, EnvMap)
                   (Actor SourceContents))

runDriver :: DriverCfg -> Actor SourceContents ()
runDriver cfg = liftM fst $ flip runCatT mempty $ flip runReaderT cfg $
                  forever $ receive >>= evalSource

evalSource :: SourceContents -> DriverM ()
evalSource source = do
  nodes <- evalCatT $ mapM sourceBlockToDag $ parseProg source
  envMap <- looks snd
  let unevaluatedNodes = filter (not . (`M.member` envMap)) nodes
  mapM_ launchBlockEval unevaluatedNodes
  updateResultList nodes

sourceBlockToDag :: SourceBlock -> CatT (Env NodeId, [NodeId]) DriverM NodeId
sourceBlockToDag block = do
  (varMap, alwaysInScope) <- look
  let parents = sort $ nub $ toList $
                  (boundUVars block <> freeUVars block) `envIntersect` varMap
  n <- lift $ addToBlockDag (block, alwaysInScope <> parents)
  -- TODO: Stop forcing dependencies on all preceding blocks. This will require
  --       an improvement of the analysis above, such that all blocks depend on those
  --       that contain interface instance definitions.
  extend (foldMap ((@>n) . Bind) $ envAsVars $ boundUVars block, [n])
  case sbContents block of
    IncludeSourceFile _ -> extend $ asSnd [n]
    _ -> return ()
  return n

launchBlockEval :: NodeId -> DriverM ()
launchBlockEval n = do
  (block, parents) <- looks $ flip lookupDag n . fst
  envLoc <- newEnvLoc n
  (cfg, resultsChan) <- ask
  resultsChan `send` oneSourceBlock n block
  let chan = subChan (oneResult n) resultsChan
  envMap <- looks snd
  let parentEnvLocs = map (envMap M.!) parents
  void $ liftIO $ forkIO $ blockEval cfg block parentEnvLocs envLoc chan

blockEval :: (EvalConfig, TopEnv) -> SourceBlock
          -> [MVar TopEnv] -> MVar TopEnv -> PChan Result -> IO ()
blockEval (opts, topEnv) block parentLocs loc resultChan = do
  parentEnv <- liftM fold $ mapM readMVar parentLocs
  (env', ans) <- liftIO $ evalSourceBlock opts (topEnv <> parentEnv) block
  putMVar loc (parentEnv <> env')
  sendFromIO resultChan ans

addToBlockDag :: Node SourceBlock -> DriverM NodeId
addToBlockDag node = do
  curDag <- looks fst
  let (n, newDagBit) = addToDag curDag node
  extend $ asFst newDagBit
  return n

newEnvLoc :: NodeId -> DriverM (MVar TopEnv)
newEnvLoc n = do
  v <- liftIO newEmptyMVar
  extend $ asSnd $ M.singleton n v
  return v

updateResultList :: [NodeId] -> DriverM ()
updateResultList ids = do
  resultChan <- asks snd
  resultChan `send` RFragment (Set ids) mempty mempty

oneResult :: NodeId -> Result -> RFragment
oneResult k r = RFragment mempty mempty (M.singleton k r)

oneSourceBlock :: NodeId -> SourceBlock -> RFragment
oneSourceBlock k b = RFragment mempty (M.singleton k b) mempty

-- === serving results via web ===

serveResults :: StreamingBody -> Application
serveResults results request respond = do
  print (pathInfo request)
  case pathInfo request of
    []             -> respondWith "static/index.html" "text/html"
    ["style.css"]  -> respondWith "static/style.css"  "text/css"
    ["plot.js"]    -> respondWith "static/plot.js"    "text/javascript"
    ["dynamic.js"] -> respondWith "static/dynamic.js" "text/javascript"
    ["getnext"]    -> respond $ responseStream status200
                         [ ("Content-Type", "text/event-stream")
                         , ("Cache-Control", "no-cache")] results
    _ -> respond $ responseLBS status404
           [("Content-Type", "text/plain")] "404 - Not Found"
  where
    respondWith fname ctype = respond $ responseFile status200
                               [("Content-Type", ctype)] fname Nothing

resultStream :: ToJSON a => ReqChan a -> StreamingBody
resultStream resultsRequest write flush = runActor $ do
  liftIO $ write (makeBuilder ("start"::String)) >> flush
  subscribe resultsRequest
  forever $ do msg <- receive
               liftIO $ write (makeBuilder msg) >> flush

makeBuilder :: ToJSON a => a -> Builder
makeBuilder = fromByteString . toStrict . wrap . encode
  where wrap s = "data:" <> s <> "\n\n"

instance ToJSON a => ToJSON (SetVal a) where
  toJSON (Set x) = object ["val" .= toJSON x]
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

-- === serving results via terminal ===

type DisplayPos = Int
data KeyboardCommand = ScrollUp | ScrollDown | ResetDisplay

type TermDisplayM = StateT DisplayPos
                      (CatT RFragment
                         (Actor (Either RFragment KeyboardCommand)))

displayResultsTerm :: ReqChan RFragment -> IO ()
displayResultsTerm reqChan =
  void $ runActor $ evalCatT $ flip evalStateT 0 $ do
     c <- myChan
     send reqChan $ subChan Left c
     void $ spawn Trap $ monitorKeyboard $ subChan Right c
     forever termDisplayLoop

termDisplayLoop :: TermDisplayM ()
termDisplayLoop = do
  req <- receive
  case req of
    Left result -> extend result
    Right command -> case command of
      ScrollUp     -> modify (+ 4)
      ScrollDown   -> modify (\p -> max 0 (p - 4))
      ResetDisplay -> put 0
  results <- look
  pos <- get
  case renderResults results of
    Nothing -> return ()
    Just s  -> liftIO $ do
      let cropped = cropTrailingLines pos s
      setCursorPosition 0 0
      clearScreen -- TODO: clean line-by-line instead
      putStr cropped

cropTrailingLines :: Int -> String -> String
cropTrailingLines n s = unlines $ reverse $ drop n $ reverse $ lines s

-- TODO: show incremental results
renderResults :: RFragment -> Maybe String
renderResults (RFragment NotSet _ _) = Nothing
renderResults (RFragment (Set ids) blocks results) =
  liftM fold $ forM ids $ \i -> do
    b <- M.lookup i blocks
    r <- M.lookup i results
    return $ printLitBlock True b r

monitorKeyboard :: PChan KeyboardCommand -> Actor () ()
monitorKeyboard chan = do
  liftIO $ hSetBuffering stdin NoBuffering
  forever $ do
    c <- liftIO getChar
    case c of
      'k' -> send chan ScrollUp
      'j' -> send chan ScrollDown
      'q' -> send chan ResetDisplay
      _   -> return ()

-- === watching files ===

-- sends file contents to channel whenever file is modified
watchFile :: FilePath -> PChan String -> IO ()
watchFile fname chan = onmod fname $ sendFileContents fname chan

sendFileContents :: String -> PChan String -> IO ()
sendFileContents fname chan = do
  putStrLn $ fname ++ " updated"
  s <- readFile fname
  sendFromIO chan s

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

-- === DAG utils ===

-- | A pair of an @a@ and a list of neighbor node ids.
type Node a = (a, [NodeId])

-- | A directed acyclic graph, represented as a bidirectional map from node ids
-- to nodes.
data Dag a = Dag (M.Map NodeId (Node a)) (M.Map (Node a) NodeId)

-- | Adds a node to a DAG, if it does not already exist.
-- Returns the added node id and a DAG representing the added node.
addToDag :: Ord a => Dag a -> Node a -> (NodeId, Dag a)
addToDag (Dag _ m) node =
  case M.lookup node m of
    Just i  -> (i, mempty)
    Nothing -> (i, Dag (M.singleton i node) (M.singleton node i))
      where i = M.size m

lookupDag :: Dag a -> NodeId -> Node a
lookupDag (Dag m _) i = m M.! i

instance Ord a => Semigroup (Dag a) where
  (Dag m1 m2) <> (Dag m1' m2') = Dag (m1' <> m1) (m2' <> m2)

instance Ord a => Monoid (Dag a) where
  mempty = Dag mempty mempty

instance Semigroup RFragment where
  (RFragment x y z) <> (RFragment x' y' z') = RFragment (x<>x') (y<>y') (z<>z')

instance Monoid RFragment where
  mempty = RFragment mempty mempty mempty
