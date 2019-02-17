{-# LANGUAGE OverloadedStrings #-}
module WebOutput (serveOutput, onMod) where

import Control.Concurrent.Chan
import Control.Monad ((>=>))

import Data.Function (fix)
import Data.Binary.Builder (fromByteString)
import Data.IORef

import Network.Wai
import Network.Wai.Handler.Warp (run)
import Network.HTTP.Types (status200)
import Data.ByteString.Char8 (pack)

import System.INotify

type FileName = String

serveOutput :: Chan () -> IORef String -> IO ()
serveOutput ready ref = do
  putStrLn "Streaming output to localhost:8000"
  run 8000 (app ready ref)

onMod :: FileName -> IO (Chan ())
onMod fname = do
  chan <- newChan
  inotify <- initINotify
  addWatch inotify [Modify] (pack fname) (const $ writeChan chan ())
  return chan

app :: Chan () -> IORef String -> Application
app chan ref request respond = do
  putStrLn (show $ pathInfo request)
  case pathInfo request of
    []            -> respond $ responseFile status200
                       [("Content-Type", "text/html")]
                       ("static/index.html") Nothing
    ["style.css"] -> respond $ responseFile status200
                       [("Content-Type", "text/css")]
                       ("static/style.css") Nothing
    ["getnext"]    -> do chan' <- dupChan chan
                         respond $ responseStream status200
                            [ ("Content-Type", "text/event-stream")
                            , ("Cache-Control",  "no-cache")]
                              (streamChan chan' ref)
    path -> error $ "Unexpected request: " ++ (show $ pathInfo request)

streamChan :: Chan () -> IORef String -> StreamingBody
streamChan ready ref write flush = fix $ \loop -> do
  ans <- readIORef ref
  write $ fromByteString $ pack $ makeMessage ans
  flush
  readChan ready
  loop
  where makeMessage :: String -> String
        makeMessage s = concat ["data: " ++ l ++ "\n" | l <- lines s] ++ "\n"
