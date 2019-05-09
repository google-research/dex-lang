{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
module WebOutput (runWeb) where

import Control.Concurrent
import Control.Monad
import Control.Monad.State.Strict

import Data.Binary.Builder (fromByteString, Builder)
import Data.Monoid ((<>))
import Data.List (nub)
import Data.Maybe (catMaybes, fromJust)
import qualified Data.Map.Strict as M

import Network.Wai
import Network.Wai.Handler.Warp (run)
import Network.HTTP.Types (status200)
import Data.ByteString.Char8 (pack)
import Data.ByteString.Lazy (toStrict)
import Data.Aeson hiding (Result, Null)
import qualified Data.Aeson as A
import System.INotify

import Syntax
import Actor
import Pass
import Parser
import PPrint
import Fresh

type FileName = String
type Key = Int
type ResultSet = (SetVal [Key], MonMap Key Result)
type FullPass env = UDecl -> TopPass env ()

runWeb :: Monoid env => FileName -> FullPass env -> env -> IO ()
runWeb fname pass env = runActor $ do
  (_, resultsChan) <- spawn Trap logServer
  spawn Trap $ mainDriver pass env fname (subChan Push resultsChan)
  spawn Trap $ webServer (subChan Request resultsChan)
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
        ["dynamic.js"] -> respondWith "static/dynamic.js" "text/javascript"
        ["getnext"]    -> respond $ responseStream status200
                             [ ("Content-Type", "text/event-stream")
                             , ("Cache-Control", "no-cache")] resultStream
        path -> error $ "Unexpected request: " ++ (show path)
      where
        respondWith fname ctype = respond $ responseFile status200
                                   [("Content-Type", ctype)] fname Nothing

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
data DriverMsg = NewProg String
data DriverState env = DriverState
  { freshState :: Int
  , declCache :: M.Map (String, [Key]) Key
  , varMap    :: M.Map Name Key
  , workers   :: M.Map Key (Proc, ReqChan env)
  }

setDeclCache update state = state { declCache = update (declCache state) }
setVarMap    update state = state { varMap    = update (varMap    state) }
setWorkers   update state = state { workers   = update (workers   state) }

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
    keys <- mapM processDecl (parseProg source)
    resultSetChan `send` updateOrder keys
  where
    processDecl (source, Left e) = do
      key <- freshKey
      resultChan key `send` (resultSource source <> resultErr e)
      return key
    processDecl (source, Right decl) = do
      state <- get
      let parents = nub $ catMaybes $ lookupKeys (freeVars decl) (varMap state)
      key <- case M.lookup (source, parents) (declCache state) of
        Just key -> return key
        Nothing -> do
          key <- freshKey
          modify $ setDeclCache $ M.insert (source, parents) key
          parentChans <- gets $ map (snd . fromJust) . lookupKeys parents . workers
          resultChan key `send` resultSource source
          (p, wChan) <- spawn Trap $
                          worker env (pass decl) (resultChan key) parentChans
          modify $ setWorkers $ M.insert key (p, subChan EnvRequest wChan)
          return key
      modify $ setVarMap $ (<> M.fromList [(v, key) | v <- lhsVars decl])
      return key

    resultChan key = subChan (singletonResult key) resultSetChan

    freshKey :: DriverM env Key
    freshKey = do n <- gets freshState
                  modify $ \s -> s {freshState = n + 1}
                  return n

lookupKeys :: Ord k => [k] -> M.Map k v -> [Maybe v]
lookupKeys ks m = map (flip M.lookup m) ks

singletonResult :: Key -> Result -> ResultSet
singletonResult k r = (mempty, MonMap (M.singleton k r))

updateOrder :: [Key] -> ResultSet
updateOrder ks = (Set ks, mempty)

data WorkerMsg a = EnvResponse a
                 | JobDone a
                 | EnvRequest (PChan a)

worker :: Monoid env => env -> TopPass env ()
            -> PChan Result
            -> [ReqChan env]
            -> Actor (WorkerMsg env) ()
worker initEnv pass resultChan parentChans = do
  selfChan <- myChan
  mapM (flip send (subChan EnvResponse selfChan)) parentChans
  envs <- mapM (const (receiveF fResponse)) parentChans
  let env = initEnv <> mconcat envs
  (pid, _) <- spawnLink NoTrap $
                execPass env pass (subChan JobDone selfChan) resultChan
  env' <- join $ receiveErrF $ \msg -> case msg of
    NormalMsg (JobDone x) -> Just (return x)
    ErrMsg _ s -> Just $ do resultChan `send` resultErr (err CompilerErr s)
                            return env
    _ -> Nothing
  forever $ receiveF fReq >>= (`send` env')
  where
    fResponse msg = case msg of EnvResponse x -> Just x; _ -> Nothing
    fReq      msg = case msg of EnvRequest  x -> Just x; _ -> Nothing

execPass :: Monoid env =>
              env -> TopPass env () -> PChan env -> PChan Result -> Actor msg ()
execPass env pass envChan resultChan = do
  (ans, (env', out)) <- liftIO $ runTopPass env pass
  resultChan `send` resultText out
  envChan    `send` (env <> env')
  -- TODO: consider just throwing IO error and letting the supervisor catch it
  resultChan `send` case ans of Left e   -> resultErr e
                                Right () -> resultComplete

-- sends file contents to subscribers whenever file is modified
inotifyMe :: String -> PChan String -> IO ()
inotifyMe fname chan = do
  readSend
  inotify <- initINotify
  void $ addWatch inotify [Modify] (pack fname) (const readSend)
  where readSend = readFile fname >>= sendFromIO chan

-- === serialization ===

instance ToJSON Result where
  toJSON (Result source status output) = object [ "source" .= toJSON source
                                                , "status" .= toJSON status
                                                , "output" .= toJSON output ]
instance ToJSON a => ToJSON (Nullable a) where
  toJSON (Valid x) = object ["val" .= toJSON x]
  toJSON Null = A.Null

instance ToJSON EvalStatus where
  toJSON Complete   = object ["complete" .= A.Null]
  toJSON (Failed e) = object ["failed"   .= toJSON (pprint e)]

instance ToJSON a => ToJSON (SetVal a) where
  toJSON (Set x) = object ["val" .= toJSON x]
  toJSON NotSet  = A.Null

instance (ToJSON k, ToJSON v) => ToJSON (MonMap k v) where
  toJSON (MonMap m) = toJSON (M.toList m)
