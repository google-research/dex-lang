-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

import Actor
import Control.Monad
import Control.Monad.State
import System.IO
import qualified Data.Map.Strict as M

type Key = String
type Val = String
type StoreID = Int
type ServerMsg = Either Val ClientToServer
type Server a = StateT (M.Map Key (Proc ())) (Actor ServerMsg) a

data ClientToServer = Write Key Val | Read Key

inputDriver :: Proc ServerMsg -> Actor () ()
inputDriver server = do
  command <- liftIO $ getLine
  case words command of
    ["write", s1, s2] -> server `send` (Right (Write s1 s2))
    ["read" , s     ] -> server `send` (Right (Read  s))
    _ -> liftIO $ putStrLn "didn't understand command"
  loop
  where loop = inputDriver server

outputDriver :: Actor String ()
outputDriver = do
  receive $ \_ msg -> liftIO $ putStrLn msg
  outputDriver

serverProc :: Server ()
serverProc = do
  self <- getSelf
  input  <- spawn NoTrap (inputDriver self)
  client <- spawn NoTrap outputDriver
  forever $ mainServerLoop client

storeProc :: Proc ServerMsg -> Val -> Actor () ()
storeProc server val = receive $ \_ _ -> do
  if length val > 5 then error "oops!"
                    else server `send` (Left val) >> loop
  where loop = storeProc server val

mainServerLoop :: Proc String -> Server ()
mainServerLoop client = receiveAny handleMsg handleErr
  where
    handleMsg :: UProc -> ServerMsg -> Server ()
    handleMsg _ msg = case msg of
      Left val -> send client val
      Right req -> case req of
        Write key val -> do
          self <- getSelf
          store <- spawnLink NoTrap (storeProc self val)
          modify $ M.insert key store
        Read key -> do
          ans <- gets (M.lookup key)
          case ans of Nothing -> sorry key
                      Just store -> store `send` ()
    handleErr err = client `send` ("Store " ++ show err ++ " down")
    sorry key     = client `send` ("Store " ++ key ++ " doesn't exist")


main :: IO ()
main = runActor Trap (evalStateT serverProc mempty)
