{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
module WebOutput (runWeb) where

import Control.Concurrent.Chan
import Control.Concurrent
import Control.Monad
import Control.Monad.State.Strict

import Data.Function (fix)
import Data.Binary.Builder (fromByteString, Builder)
import Data.IORef
import Data.Monoid ((<>))
import qualified Data.Map.Strict as M

import Network.Wai
import Network.Wai.Handler.Warp (run)
import Network.HTTP.Types (status200)
import Data.ByteString.Char8 (pack)
import Data.ByteString.Lazy (ByteString, toStrict)
import Data.Aeson hiding (Result, Null)
import qualified Data.Aeson as A
import System.INotify

import Syntax
import Actor
import Pass
import Parser
import PPrint

type FileName = String
type Key = Int
type ResultSet = MonMap Key (Nullable Result)

runWeb :: Monoid env => FileName -> Pass env UDecl () -> env -> IO ()
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
        path -> error $ "Unexpected request: " ++ (show $ pathInfo request)
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

data DriverMsg = NewProg String
data DriverState = DriverState
  { foo :: ()
  }

initDriverState :: DriverState
initDriverState = DriverState ()


mainDriver :: Monoid env => Pass env UDecl () -> env -> String
                -> PChan ResultSet -> Actor DriverMsg ()
mainDriver pass env fname resultChan = flip evalStateT initDriverState $ do
  chan <- myChan
  liftIO $ inotifyMe fname (subChan NewProg chan)
  forever $ do
    NewProg source <- receive
    prog <- case parseProg source of
      Left e     -> error "need to handle this case"
      Right prog -> return prog
    let monmap = MonMap $ M.fromList (zip [0..] (map (Valid . resultSource . fst) prog))
    resultChan `send` monmap
    mapM_ spawnWorker (zip [0..] prog)
  where
    singleton k r = MonMap $ M.singleton k (Valid r)
    spawnWorker (k, (_, decl)) =
      spawn NoTrap $ worker env (pass decl) (subChan (singleton k) resultChan) []


data WorkerMsg a = EnvResponse a
                 | JobDone a
                 | EnvRequest (PChan a)

worker :: Monoid env => env -> TopMonadPass env ()
            -> PChan Result
            -> [ReqChan env]
            -> Actor (WorkerMsg env) ()
worker initEnv pass resultChan parentChans = do
  workerChan <- myChan
  mapM (flip send (subChan EnvResponse workerChan)) parentChans
  envs <- mapM (const (receiveF fResponse)) parentChans
  let env = initEnv <> mconcat envs
  (pid, _) <- spawn NoTrap $ do
                (result, env') <- liftIO $ runStateT (evalDecl pass) env
                send resultChan result
                send workerChan (JobDone env')
  -- TODO: handle error messages from worker process
  env' <- receiveF fDone
  forever $ do responseChan <- receiveF fReq
               send responseChan env'
  where
    fResponse msg = case msg of EnvResponse x -> Just x; _ -> Nothing
    fDone     msg = case msg of JobDone     x -> Just x; _ -> Nothing
    fReq      msg = case msg of EnvRequest  x -> Just x; _ -> Nothing

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

instance ToJSON a => ToJSON (SetOnce a) where
  toJSON (Set x) = object ["val" .= toJSON x]
  toJSON NotSet  = A.Null

instance (ToJSON k, ToJSON v) => ToJSON (MonMap k v) where
  toJSON (MonMap m) = toJSON (M.toList m)
