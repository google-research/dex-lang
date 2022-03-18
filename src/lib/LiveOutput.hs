-- Copyright 2022 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module LiveOutput (runWeb, runTerminal) where

import Control.Concurrent
import Control.Monad.Reader
import Control.Monad.State.Strict

import Data.Binary.Builder (fromByteString, Builder)
import Data.Foldable (fold)
import qualified Data.Map.Strict as M

import Network.Wai
import Network.Wai.Handler.Warp (run)
import Network.HTTP.Types (status200, status404)
import Data.Aeson hiding (Result, Null, Value)
import qualified Data.Aeson as A
import Data.ByteString.Lazy (toStrict)

import System.Console.ANSI
import System.Directory
import System.IO

import Paths_dex (getDataFileName)

import Actor
import Cat
import Parser
import PPrint (printLitBlock)
import RenderHtml
import Syntax
import TopLevel

type NodeId = Int
data WithId a = WithId { getNodeId :: NodeId
                       , withoutId :: a }
data RFragment = RFragment (SetVal [NodeId])
                           (M.Map NodeId SourceBlock)
                           (M.Map NodeId Result)

runWeb :: FilePath -> EvalConfig -> TopStateEx -> IO ()
runWeb fname opts env = do
  resultsChan <- watchAndEvalFile fname opts env
  putStrLn "Streaming output to localhost:8000"
  run 8000 $ serveResults resultsChan

runTerminal :: FilePath -> EvalConfig -> TopStateEx -> IO ()
runTerminal fname opts env = do
  resultsChan <- watchAndEvalFile fname opts env
  displayResultsTerm resultsChan

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

-- === serving results via web ===

serveResults :: ToJSON a => PChan (PChan a) -> Application
serveResults resultsSubscribe request respond = do
  print (pathInfo request)
  case pathInfo request of
    []            -> respondWith "static/dynamic.html" "text/html"
    ["style.css"] -> respondWith "static/style.css"  "text/css"
    ["index.js"]  -> respondWith "static/index.js"   "text/javascript"
    ["getnext"]   -> respond $ responseStream status200
                       [ ("Content-Type", "text/event-stream")
                       , ("Cache-Control", "no-cache")]
                       $ resultStream resultsSubscribe
    _ -> respond $ responseLBS status404
           [("Content-Type", "text/plain")] "404 - Not Found"
  where
    respondWith dataFname ctype = do
      fname <- getDataFileName dataFname
      respond $ responseFile status200 [("Content-Type", ctype)] fname Nothing

resultStream :: ToJSON a => PChan (PChan a) -> StreamingBody
resultStream resultsSubscribe write flush = runActor \self -> do
  write (makeBuilder ("start"::String)) >> flush
  resultsSubscribe `sendPChan` (sendOnly self)
  forever $ do msg <- readChan self
               write (makeBuilder msg) >> flush

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

type TermDisplayM = StateT DisplayPos (CatT RFragment IO)

displayResultsTerm :: PChan (PChan RFragment) -> IO ()
displayResultsTerm resultsSubscribe =
  runActor \self -> do
     resultsSubscribe `sendPChan` subChan Left (sendOnly self)
     void $ forkIO $ monitorKeyboard $ subChan Right (sendOnly self)
     evalCatT $ flip evalStateT 0 $ forever $ termDisplayLoop self

termDisplayLoop :: (Chan (Either RFragment KeyboardCommand)) -> TermDisplayM ()
termDisplayLoop self = do
  req <- liftIO $ readChan self
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

-- A non-Actor source.  Sends keyboard command signals as they occur.
monitorKeyboard :: PChan KeyboardCommand -> IO ()
monitorKeyboard chan = do
  hSetBuffering stdin NoBuffering
  forever $ do
    c <- getChar
    case c of
      'k' -> chan `sendPChan` ScrollUp
      'j' -> chan `sendPChan` ScrollDown
      'q' -> chan `sendPChan` ResetDisplay
      _   -> return ()

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

-- === some handy monoids ===

data SetVal a = Set a | NotSet
newtype MonMap k v = MonMap (M.Map k v)  deriving (Show, Eq)

instance Semigroup (SetVal a) where
  x <> NotSet = x
  _ <> Set x  = Set x

instance Monoid (SetVal a) where
  mempty = NotSet

instance (Ord k, Semigroup v) => Semigroup (MonMap k v) where
  MonMap m <> MonMap m' = MonMap $ M.unionWith (<>) m m'

instance (Ord k, Semigroup v) => Monoid (MonMap k v) where
  mempty = MonMap mempty
