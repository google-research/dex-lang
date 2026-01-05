-- Copyright 2025 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module Proto.Monad where

import Proto.Util
import Proto.Doc

import qualified Data.Map.Strict as M
import Control.Exception
import Control.Monad.Reader

-- === top level monad ===

-- Main monad. Gives access to:
--   * IO
--   * fresh name generation (TODO)
--   * abstracted stdout/stderr, with filtering handled in client code (TODO)
--   * error throwing (formatting to doc and adding source context handled in client code)
--   * some language/pass-specific context

data ProtoTopData = ProtoTopData
  { logAction :: LogAction }
newtype ProtoM r a = ProtoM (ReaderT r (ReaderT ProtoTopData IO) a)
        deriving (Functor, Applicative, Monad, MonadIO)

data ProtoException = ProtoException  deriving Show
instance Exception ProtoException

instance Logger (ProtoM r) where
  applyEdit edit = ProtoM $ lift $ ReaderT \ctx ->
    ctx.logAction edit

throw :: Doc -> ProtoM r a
throw doc = do
  logM $ withLogBlock ErrorBlock doc
  liftIO $ throwIO ProtoException

logM :: Doc -> ProtoM r ()
logM doc = liftDoc doc

captureLog :: ProtoM r a -> ProtoM r (Maybe a, Doc)
captureLog doit = do
  (logAction, readLog) <- makeRecoverableLogAction
  ans <- catchProtoException $ withLogAction logAction doit
  doc <- liftIO $ readLog
  return (ans, doc)

makeRecoverableLogAction :: MonadIO m => m (LogAction, IO Doc)
makeRecoverableLogAction = do
  editsRev <- newStack []
  cleanupEdit <- newStack []
  return (logAction editsRev cleanupEdit, readResult editsRev cleanupEdit)
  where
    logAction editsRev cleanupEdit edit = do
      case edit of
        EnterBlock _ -> push cleanupEdit LeaveBlock
        LeaveBlock -> pop cleanupEdit >> return ()
        _ -> return ()
      push editsRev edit
    readResult editsRev cleanupEdit = do
      edits <- reverse <$> peekAll editsRev
      cleanups <- peekAll cleanupEdit
      return $ editsToDoc $ edits <> cleanups

getCtx :: ProtoM r r
getCtx = ProtoM ask

withCtx :: (r -> r) -> ProtoM r a -> ProtoM r a
withCtx f (ProtoM cont) = ProtoM $ local f cont

withLogAction :: LogAction -> ProtoM r a -> ProtoM r a
withLogAction logger (ProtoM (ReaderT f)) = ProtoM $ ReaderT \c ->
  local (\ctx -> ctx { logAction = logger }) $ f c

catchProtoException :: ProtoM r a -> ProtoM r (Maybe a)
catchProtoException (ProtoM cont) =
  ProtoM $ ReaderT \r -> ReaderT \logger -> do
    catch @ProtoException
      (Just <$> runReaderT (runReaderT cont r) logger)
      (\_ -> return Nothing)

runProtoM :: r -> ProtoM r a -> IO (Maybe a)
runProtoM r (ProtoM m) = do
  logger <- makePlainTextLogAction putStrLn
  catch @ProtoException
    (Just <$> runReaderT (runReaderT m r) (ProtoTopData logger))
    (\_ -> return Nothing)

liftProtoM :: (r -> r') -> ProtoM r' a -> ProtoM r a
liftProtoM f (ProtoM m) = ProtoM $ withReaderT f m

-- === names and environments ===

type Env v = M.Map Name v
type Name = String
