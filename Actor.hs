{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

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

type ErrMsg = UProc
data CanTrap = Trap | NoTrap
data Msg a = ErrMsg ErrMsg | NormalMsg UProc a
data Proc m = Proc CanTrap ThreadId (Chan (Msg m))
data UProc where UProc :: Proc m -> UProc
data ActorConfig m = ActorConfig { selfProc :: Proc m
                                 , linksPtr :: IORef [UProc] }

-- TODO: implement monadstate etc
newtype Actor m a = Actor (ReaderT (ActorConfig m) IO a)
  deriving (Functor, Applicative, Monad, MonadIO)

class (MonadIO m, Monad m) => MonadActor msg m | m -> msg where
  actorCfg :: m (ActorConfig msg)

instance MonadActor msg (Actor msg) where
  actorCfg = Actor ask

instance MonadActor msg m => MonadActor msg (StateT s m) where
  actorCfg = lift actorCfg


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
                    let self = Proc canTrap id chan
                    runActor body (ActorConfig self linksRef)
                      `onException`
                         (readIORef linksRef >>= mapM (cleanup (UProc self)))
  return $ Proc canTrap id chan

cleanup :: ErrMsg -> UProc -> IO ()
cleanup err (UProc (Proc NoTrap pid _)) = undefined
cleanup err (UProc (Proc Trap  _ chan)) = writeChan chan (ErrMsg err)

kill :: UProc -> Actor m ()
kill = undefined

spawn :: MonadActor msg m => CanTrap -> Actor msg' () -> m (Proc msg')
spawn canTrap body = liftIO $ spawnIO canTrap [] body

spawnLink :: MonadActor msg m => CanTrap -> Actor msg' () -> m (Proc msg')
spawnLink canTrap body = do
  cfg <- actorCfg
  liftIO $ do
    links <- readIORef (linksPtr cfg)
    child <- spawnIO canTrap [UProc (selfProc cfg)] body
    -- potential bug if we get killed right here, before we've linked the child.
    -- 'mask' from Control.Exception might be a solution
    writeIORef (linksPtr cfg) (UProc child : links)
    return child

getSelf :: MonadActor msg m => m (Proc msg)
getSelf = actorCfg >>= return . selfProc

send :: MonadActor msg m => Proc msg' -> msg' -> m ()
send p x = do self <- getSelf
              liftIO $ writeChan (procChan p) (NormalMsg (UProc self) x)

receiveAny :: MonadActor msg m => (UProc -> msg -> m a) -> (ErrMsg -> m a) -> m a
receiveAny f onErr = do
  Proc _ _ chan <- getSelf
  msg <- liftIO $ readChan chan
  case msg of ErrMsg e -> onErr e
              NormalMsg p msg -> f p msg

receive :: MonadActor msg m => (UProc -> msg -> m a) -> m a
receive f = receiveAny f (\_ -> error "Can't handle error messages here")

-- intend to pair this with receive to filter out messages
ignore :: Actor m a
ignore = undefined

procId :: Proc m -> ThreadId
procId (Proc _ id _) = id

procChan :: Proc m -> Chan (Msg m)
procChan (Proc _ _ chan) = chan


instance Show UProc where
  show (UProc (Proc _ pid _)) = show pid

instance Eq UProc where
  UProc (Proc _ pid1 _) == UProc (Proc _ pid2 _) = pid1 == pid2

instance Ord UProc where
  compare (UProc (Proc _ pid1 _)) (UProc (Proc _ pid2 _)) = compare pid1 pid2
