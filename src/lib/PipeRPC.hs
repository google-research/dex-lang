-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module PipeRPC (PipeServer, startPipeServer, callPipeServer, psPop) where

import Control.Concurrent.MVar
import Control.Monad
import Control.Monad.IO.Class
import Data.Aeson
import Data.ByteString.Lazy.Char8 (pack, unpack)
import GHC.IO.Handle.FD
import System.IO
import System.Process

data PipeServer f = PipeServer { _psLock          :: MVar ()
                               , _psSendHandle    :: Handle
                               , _psReceiveHandle :: Handle
                               , psFunctionIndex :: Int}

startPipeServer :: MonadIO m => FilePath -> [String] -> m (PipeServer f)
startPipeServer cmd args = liftIO $ do
  ((clientRead, _), (_, serverWrite)) <- createPipeWithNames
  ((_, serverRead), (clientWrite, _)) <- createPipeWithNames
  void $ createProcess $ proc cmd $ args ++ [serverRead, serverWrite]
  lock <- newMVar ()
  return $ PipeServer lock clientWrite clientRead 0

psPop :: PipeServer (head, tail) -> PipeServer tail
psPop server = server { psFunctionIndex = 1 + psFunctionIndex server }

callPipeServer :: (MonadIO m, ToJSON a, FromJSON b)
               => PipeServer (a -> b, tail) -> a -> m b
callPipeServer (PipeServer lock sendHandle receiveHandle fIdx) arg = liftIO $ do
  void $ takeMVar lock
  let request = unpack $ encode (fIdx, arg)
  hPutStrLn sendHandle request
  response <- hGetLine receiveHandle
  putMVar lock ()
  case eitherDecode (pack response) of
    Right x -> case x of
      Right x' -> return x'
      Left s -> error $ "Error thrown by server:\n" ++ s
    Left s -> error $ s ++ "\nDecoding error. Full response:\n" ++ response

createPipeWithNames :: IO ((Handle, String), (Handle, String))
createPipeWithNames = do
  (r, w) <- createPipe
  hSetBuffering r LineBuffering
  hSetBuffering w LineBuffering
  rName <- unixHandleName r
  wName <- unixHandleName w
  return ((r,rName), (w, wName))

unixHandleName :: Handle -> IO String
unixHandleName h = do
  fd <- handleToFd h
  return $ "/dev/fd/" ++ show fd
