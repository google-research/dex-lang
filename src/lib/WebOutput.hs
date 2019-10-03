{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module WebOutput (runWeb) where

import Control.Concurrent
import Control.Monad
import Control.Monad.State.Strict

import Data.Binary.Builder (fromByteString, Builder)
import Data.Monoid ((<>))
import Data.List (nub)
import Data.Foldable (toList)
import Data.Maybe (fromJust)
import qualified Data.Map.Strict as M

import Network.Wai
import Network.Wai.Handler.Warp (run)
import Network.HTTP.Types (status200, status404)
import Data.ByteString.Char8 (pack)
import Data.ByteString.Lazy (toStrict)
import Data.Aeson hiding (Result, Null, Value)
import qualified Data.Aeson as A
import System.INotify
import Data.Void

import Syntax
import Actor
import Pass
import Parser
import Env
import RenderHtml

type FileName = String
type Key = Int

type TreeAddress = [Int]
type HtmlString = String
type HtmlFragment = [(TreeAddress, HtmlString)]
type CellUpdate = HtmlFragment

type ResultSet = (SetVal [Key], MonMap Key CellUpdate)

runWeb :: Monoid env => FileName -> FullPass env -> env -> IO ()
runWeb fname pass env = runActor $ do
  (_, resultsChan) <- spawn Trap logServer
  _ <- spawn Trap $ mainDriver pass env fname (subChan Push resultsChan)
  _ <- spawn Trap $ webServer (subChan Request resultsChan)
  liftIO $ forever (threadDelay maxBound)

webServer :: ReqChan ResultSet -> Actor () ()
webServer resultsRequest = do
  liftIO $ putStrLn "Streaming output to localhost:8000"
  liftIO $ run 8000 app
  where
    app :: Application
    app request respond = do
      putStrLn (show $ pathInfo request)
      case pathInfo request of
        []             -> respondWith "static/index.html" "text/html"
        ["style.css"]  -> respondWith "static/style.css"  "text/css"
        ["plot.js"]    -> respondWith "static/plot.js"    "text/javascript"
        ["dynamic.js"] -> respondWith "static/dynamic.js" "text/javascript"
        ["getnext"]    -> respond $ responseStream status200
                             [ ("Content-Type", "text/event-stream")
                             , ("Cache-Control", "no-cache")] resultStream
        ["favicon.ico"] -> notfound
        path -> error $ "Unexpected request: " ++ (show path)
      where
        respondWith fname ctype = respond $ responseFile status200
                                   [("Content-Type", ctype)] fname Nothing
        notfound = respond $ responseLBS status404
                     [("Content-Type", "text/plain")] "404 - Not Found"

    resultStream :: StreamingBody
    resultStream write flush = runActor $ do
      myChan >>= send resultsRequest
      forever $ do msg <- receive
                   liftIO $ write (makeBuilder msg) >> flush
    makeBuilder :: ToJSON a => a -> Builder
    makeBuilder = fromByteString . toStrict . wrap . encode
      where wrap s = "data:" <> s <> "\n\n"

-- === main driver ===

type DriverM env a = StateT (DriverState env) (Actor DriverMsg) a
type WorkerMap env = M.Map Key (Proc, ReqChan env)
type DeclCache = M.Map (String, [Key]) Key
data DriverMsg = NewProg String
data DriverState env = DriverState
  { freshState :: Int
  , declCache :: DeclCache
  , varMap    :: Env Key
  , workers   :: WorkerMap env
  }

setDeclCache :: (DeclCache -> DeclCache) -> DriverState env -> DriverState env
setDeclCache update state_ = state_ { declCache = update (declCache state_) }

setVarMap :: (Env Key -> Env Key) -> DriverState env -> DriverState env
setVarMap update state_ = state_ { varMap = update (varMap state_) }

setWorkers :: (WorkerMap env -> WorkerMap env) -> DriverState env -> DriverState env
setWorkers update state_ = state_ { workers = update (workers state_) }

initDriverState :: DriverState env
initDriverState = DriverState 0 mempty mempty mempty

mainDriver :: Monoid env => FullPass env -> env -> String
                -> PChan ResultSet -> Actor DriverMsg ()
mainDriver pass env fname resultSetChan = flip evalStateT initDriverState $ do
  chan <- myChan
  liftIO $ inotifyMe fname (subChan NewProg chan)
  forever $ do
    NewProg source <- receive
    modify $ setVarMap (const mempty)
    keys <- mapM processBlock (parseProg source)
    resultSetChan `send` updateOrder keys
  where
    processBlock block = do
      state_ <- get
      let parents = nub $ toList $ freeVars block `envIntersect` varMap state_
      let cacheKey = (sbText block, parents)
      key <- case M.lookup cacheKey (declCache state_) of
        Just key -> return key
        Nothing -> do
          key <- freshKey
          modify $ setDeclCache $ M.insert cacheKey key
          parentChans <- gets $ map (snd . fromJust) . lookupKeys parents . workers
          resultChan key `send` sourceUpdate block
          (p, wChan) <- spawn Trap $
                          worker env (pass block) (resultChan key) parentChans
          modify $ setWorkers $ M.insert key (p, subChan EnvRequest wChan)
          return key
      modify $ setVarMap $ (<> fmap (const key) (lhsVars block))
      return key

    resultChan key = subChan (singletonResult key) resultSetChan

    freshKey :: DriverM env Key
    freshKey = do n <- gets freshState
                  modify $ \s -> s {freshState = n + 1}
                  return n

lookupKeys :: Ord k => [k] -> M.Map k v -> [Maybe v]
lookupKeys ks m = map (flip M.lookup m) ks

data WorkerMsg a = EnvResponse a
                 | JobDone a
                 | EnvRequest (PChan a)

worker :: Monoid env => env -> TopPassM env Void
            -> PChan CellUpdate
            -> [ReqChan env]
            -> Actor (WorkerMsg env) ()
worker initEnv pass resultChan parentChans = do
  selfChan <- myChan
  mapM_ (flip send (subChan EnvResponse selfChan)) parentChans
  envs <- mapM (const (receiveF fResponse)) parentChans
  let env = initEnv <> mconcat envs
  _ <- spawnLink NoTrap $ execPass env pass (subChan JobDone selfChan) resultChan
  env' <- join $ receiveErrF $ \msg -> case msg of
    NormalMsg (JobDone x) -> Just (return x)
    ErrMsg _ s -> Just $ do
      resultChan `send` resultUpdate (Left (Err CompilerErr Nothing s))
      return env
    _ -> Nothing
  forever $ receiveF fReq >>= (`send` env')
  where
    fResponse msg = case msg of EnvResponse x -> Just x; _ -> Nothing
    fReq      msg = case msg of EnvRequest  x -> Just x; _ -> Nothing

execPass :: Monoid env =>
              env -> TopPassM env Void -> PChan env -> PChan CellUpdate -> Actor msg ()
execPass env pass envChan resultChan = do
  ~(Left ans, env') <- liftIO $ runTopPassM env pass
  envChan    `send` (env <> env')
  resultChan `send` resultUpdate ans

-- sends file contents to subscribers whenever file is modified
inotifyMe :: String -> PChan String -> IO ()
inotifyMe fname chan = do
  readSend
  inotify <- initINotify
  void $ addWatch inotify [Modify] (pack fname) (const readSend)
  where readSend = readFile fname >>= sendFromIO chan

-- === rendering ===

singletonResult :: Key -> CellUpdate -> ResultSet
singletonResult k r = (mempty, MonMap (M.singleton k r))

updateOrder :: [Key] -> ResultSet
updateOrder ks = (Set ks, mempty)

sourceUpdate :: SourceBlock -> CellUpdate
sourceUpdate block = [([], renderHtml (sourceBlockHtml block))]

-- TODO: add source to errors upstream so we can render results by themselves
-- without a dummy EvalBlock
resultUpdate :: Result -> CellUpdate
resultUpdate result = [([], renderHtml (resultHtml (EvalBlock undefined result)))]

-- === serialization ===

instance ToJSON a => ToJSON (SetVal a) where
  toJSON (Set x) = object ["val" .= toJSON x]
  toJSON NotSet  = A.Null

instance (ToJSON k, ToJSON v) => ToJSON (MonMap k v) where
  toJSON (MonMap m) = toJSON (M.toList m)
