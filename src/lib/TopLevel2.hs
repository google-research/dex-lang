-- Copyright 2020 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE UndecidableInstances #-}

module TopLevel2 (
  EvalConfig (..), TopperM, runTopperM, evalSourceBlockRepl, OptLevel (..),
  LibPath (..), initTopState, ExitStatus (..)) where

import Control.Monad.Writer.Strict  hiding (pass)
import Control.Monad.Reader
import Data.IORef
import qualified Data.Map.Strict as M

import AbstractSyntax
import Err
import Inference
import MonadUtil
import SourceRename
import SourceIdTraversal
import PPrint
import Types.Complicated
import Types.Primitives
import Types.Source hiding (CTopDecl)
import Types.Top2

-- === top-level monad ===

data LibPath = LibDirectory FilePath | LibBuiltinPath

data EvalConfig = EvalConfig
  { libPaths      :: [LibPath]
  , preludeFile   :: Maybe FilePath
  , optLevel      :: OptLevel
  , printBackend  :: PrintBackend }

type LogAction = Outputs -> IO ()
class Monad m => ConfigReader m where
  getConfig :: m EvalConfig

data TopperReaderData = TopperReaderData
  { topperEvalConfig :: EvalConfig
  , topperLogAction  :: LogAction
  , topperTopState   :: IORef TopState }

newtype TopperM a = TopperM
  { runTopperM'
    :: ReaderT TopperReaderData IO a }
    deriving ( Functor, Applicative, Monad, MonadIO, MonadFail
             , Fallible, Catchable, MonadReader TopperReaderData)

runTopperM
  :: EvalConfig -> LogAction -> TopState
  -> TopperM a
  -> IO (a, TopState)
runTopperM cfg logAction initState cont = do
  stateRef <- newIORef initState
  result <- flip runReaderT (TopperReaderData cfg logAction stateRef) $ runTopperM' cont
  finalState <- readIORef stateRef
  return (result, finalState)

initTopState :: IO TopState
initTopState = return $ TopState mempty

-- ======

data ExitStatus = ExitSuccess | ExitFailure  deriving (Show)

evalSourceBlockRepl :: SourceBlock -> TopperM ExitStatus
evalSourceBlockRepl block = do
  maybeErr <- catchErrExcept do
    logTop $ SourceInfo $ SIGroupingInfo $ getGroupingInfo $ sbContents block
    evalSourceBlock' Main block
  case maybeErr of
    Success () -> return ExitSuccess
    Failure e -> do
      logTop $ Error e
      return $ ExitFailure

evalSourceBlock' :: ModuleSourceName -> SourceBlock -> TopperM ()
evalSourceBlock' _ block = case sbContents block of
  TopDecl decl -> parseDecl decl >>= execUDecl
  UnParseable _ s -> throwErr $ ParseErr $ MiscParseErr s
  Misc m -> case m of
    ImportModule _ -> undefined -- importModule moduleName
    ProseBlock _ -> return ()
    CommentLine  -> return ()
    EmptyLines   -> return ()

execUDecl :: UTopDecl -> TopperM ()
execUDecl decl = do
  logPass Parse decl
  renamed <- renameSourceNames decl
  logPass RenamePass renamed
  typedDecl <- checkPass TypePass $ inferTopUDecl renamed
  execCDecl typedDecl

execCDecl :: CTopDecl -> TopperM ()
execCDecl = \case
  CTopLet b rhs -> do
    _ <- evalCExpr rhs  -- TODO: if it's non-data then just return
    case b of
      Nothing -> return ()
      Just b' -> insertTopName b' undefined
  _ -> error "not implemented"

type RuntimeVal = ()

evalCExpr :: CTopExpr -> TopperM RuntimeVal
evalCExpr _ = return ()

checkPass :: Pretty e => PassName -> TopperM e -> TopperM e
checkPass name cont = do
  result <- cont
  logPass name result
  return result

logTop :: TopLogger m => Output -> m ()
logTop x = emitLog $ Outputs [x]

logPass :: Pretty a => PassName -> a -> TopperM ()
logPass passName result = logTop $ PassResult passName $ Just (pprint result)

-- === helpers ===

insertTopName :: SourceName -> TopNameDef -> TopperM ()
insertTopName name val = do
  ref <- asks topperTopState
  topState <- liftIO $ readIORef ref
  liftIO $ writeIORef ref $ topState { topNames = topNames topState <> M.singleton name val }

-- === instances ===

instance ConfigReader TopperM where
  getConfig = TopperM $ asks topperEvalConfig

instance Logger Outputs TopperM where
  emitLog x = do
    logger <- getIOLogAction
    liftIO $ logger x

instance HasIOLogger Outputs TopperM where
  getIOLogAction = TopperM $ asks topperLogAction

instance CanSetIOLogger Outputs TopperM where
  withIOLogAction logger (TopperM m) = TopperM do
    local (\r -> r { topperLogAction = logger }) m
