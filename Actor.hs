{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Actor (Actor, Proc, UProc, CanTrap (..),
              runMainActor, spawn, spawnLink, send,
              receive, receiveAny, getSelf, procId) where

import Control.Monad
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Identity
import Control.Exception
import Data.IORef
import qualified Data.Map.Strict as M

import Control.Concurrent

type ErrMsg = ThreadId
data CanTrap = Trap | NoTrap
data Msg a = ErrMsg ErrMsg | NormalMsg a
data Proc m = Proc CanTrap ThreadId (Chan (Msg m))
data UProc where UProc :: Proc m -> UProc -- hides message type
data ActorConfig m = ActorConfig { selfProc :: Proc m
                                 , links    :: IORef [UProc] }

-- TODO: implement monadstate etc
newtype Actor m a = Actor (ReaderT (ActorConfig m) IO a)
  deriving (Functor, Applicative, Monad, MonadIO)

runMainActor :: CanTrap -> Actor m () -> IO ()
runMainActor canTrap body = do
  linksRef <- newIORef []
  chan <- newChan
  id <- myThreadId
  runActor body (ActorConfig (Proc canTrap id chan) linksRef)

runActor :: Actor m a -> ActorConfig m -> IO a
runActor (Actor m) cfg = runReaderT m cfg

spawnIO :: CanTrap -> [UProc] -> Actor m () -> IO (Proc m)
spawnIO canTrap links body = do
  linksRef <- newIORef links
  chan <- newChan
  id <- forkIO $ do id <- myThreadId
                    runActor body (ActorConfig (Proc canTrap id chan) linksRef)
                      `onException` (readIORef linksRef >>= mapM (cleanup id))
  return $ Proc canTrap id chan

cleanup :: ErrMsg -> UProc -> IO ()
cleanup err (UProc (Proc NoTrap pid _)) = undefined
cleanup err (UProc (Proc Trap  _ chan)) = do
  putStrLn "cleaning up"
  writeChan chan (ErrMsg err)

kill :: UProc -> Actor m ()
kill = undefined

spawn :: CanTrap -> Actor m () -> Actor m' (Proc m)
spawn canTrap body = liftIO $ spawnIO canTrap [] body

spawnLink :: CanTrap -> Actor m () -> Actor m' (Proc m)
spawnLink canTrap body = Actor $ do
  linksPtr <- asks links
  self <- asks selfProc
  liftIO $ do
    links <- readIORef linksPtr
    child <- spawnIO canTrap [UProc self] body
    -- potential bug if we get killed right here, before we've linked the child.
    -- 'mask' from Control.Exception might be a solution
    writeIORef linksPtr (UProc child : links)
    return child

getSelf :: Actor m (Proc m)
getSelf = Actor (asks selfProc)

send :: Proc m -> m -> Actor m' ()
send p x = liftIO $ writeChan (procChan p) (NormalMsg x)

receiveAny :: (m -> Actor m a) -> (ErrMsg -> Actor m a) -> Actor m a
receiveAny f onErr = do
  Proc _ _ chan <- getSelf
  msg <- liftIO $ readChan chan
  case msg of ErrMsg e -> onErr e
              NormalMsg msg -> f msg

receive :: (m -> Actor m a) -> Actor m a
receive f = receiveAny f (\_ -> error "Can't handle error messages here")

-- intend to pair this with receive to filter out messages
ignore :: Actor m a
ignore = undefined

procId :: Proc m -> ThreadId
procId (Proc _ id _) = id

procChan :: Proc m -> Chan (Msg m)
procChan (Proc _ _ chan) = chan
