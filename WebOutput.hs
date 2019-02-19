{-# LANGUAGE OverloadedStrings #-}
module WebOutput (serveOutput, onMod) where

import Control.Concurrent.Chan
import Control.Monad ((>=>))

import Data.Function (fix)
import Data.Binary.Builder (fromByteString)
import Data.IORef
import Data.Monoid ((<>))

import Network.Wai
import Network.Wai.Handler.Warp (run)
import Network.HTTP.Types (status200)
import Data.ByteString.Char8 (pack)
import Data.ByteString.Lazy (ByteString, toStrict)
import Data.Aeson

import Syntax

import System.INotify

type FileName = String

type CellContents = TopDecl ()
type EvalState = IORef [CellContents]
data Message = FreshPage [CellContents]
             | SetContents Int CellContents  -- not used yet

serveOutput :: Chan () -> EvalState -> IO ()
serveOutput ready ref = do
  putStrLn "Streaming output to localhost:8000"
  run 8000 (app ready ref)

onMod :: FileName -> IO (Chan ())
onMod fname = do
  chan <- newChan
  inotify <- initINotify
  addWatch inotify [Modify] (pack fname) (const $ writeChan chan ())
  return chan

app :: Chan () -> EvalState -> Application
app chan ref request respond = do
  putStrLn (show $ pathInfo request)
  case pathInfo request of
    []            -> respond $ responseFile status200
                       [("Content-Type", "text/html")]
                       "static/index.html" Nothing
    ["style.css"] -> respond $ responseFile status200
                       [("Content-Type", "text/css")]
                       "static/style.css" Nothing
    ["dynamic.js"] -> respond $ responseFile status200
                       [("Content-Type", "text/javascript")]
                       "static/dynamic.js" Nothing
    ["getnext"]    -> do chan' <- dupChan chan
                         respond $ responseStream status200
                            [ ("Content-Type", "text/event-stream")
                            , ("Cache-Control",  "no-cache")]
                              (streamChan chan' ref)
    path -> error $ "Unexpected request: " ++ (show $ pathInfo request)

streamChan :: Chan () -> EvalState -> StreamingBody
streamChan ready ref write flush = fix $ \loop -> do
  ans <- readIORef ref
  write $ fromByteString $ toStrict $ makeMessage $ encode (FreshPage ans)
  flush
  readChan ready
  loop

makeMessage :: ByteString -> ByteString
makeMessage s = "data:" <> s <> "\n\n"

instance ToJSON Message where
  toJSON (FreshPage contents) = object ["FreshPage"   .= toJSON contents]
  toJSON (SetContents idx contents) = object ["SetContents" .= object
                                                ["index"    .= toJSON idx,
                                                 "contents" .= toJSON contents]]

instance ToJSON (TopDecl a) where
  toJSON (TopDecl source _ instr) = object [ "source" .= toJSON source
                                           , "instr"  .= toJSON instr ]

instance ToJSON (DeclInstr a) where
  toJSON instr = case instr of
    EvalCmd (Command _ _)   -> object [ "unevaluated" .= toJSON ()  ]
    EvalCmd (CmdResult out) -> object [ "result"      .= toJSON out ]
    EvalCmd (CmdErr e)      -> object [ "error"       .= show e     ]
    _                       -> object [ "source_only" .= toJSON ()  ]

instance ToJSON CommandOutput where
  toJSON (TextOut s) = toJSON s
  toJSON (PlotOut _) = toJSON ("this is a plot" :: String)
