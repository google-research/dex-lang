-- Copyright 2020 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE UndecidableInstances #-}

module TopLevel2 (
  EvalConfig (..), Topper, TopperM, runTopperM,
  evalSourceBlockRepl, OptLevel (..), LibPath (..),
  evalSourceBlockIO, initTopState, simpOptimizations,
  ExitStatus (..), parseSourceBlocks, captureLogs) where

import Data.Functor
import Data.Maybe (catMaybes)
import Control.Exception (throwIO, catch)
import Control.Monad.Writer.Strict  hiding (pass)
import Control.Monad.State.Strict
import Control.Monad.Reader
import qualified Data.ByteString as BS
import qualified Data.Text as T
import Data.IORef
import Data.Text.Prettyprint.Doc
import Data.Store (encode, decode)
import Data.String (fromString)
import qualified Data.Map.Strict as M
import qualified Data.Set        as S
import Foreign.Ptr
import Foreign.C.String
import GHC.Generics (Generic (..))
import System.FilePath
import System.Directory
import System.IO (stderr, hPutStrLn)
import System.IO.Error (isDoesNotExistError)

import LLVM.Link
import LLVM.Compile
import qualified LLVM.AST

import AbstractSyntax
import ConcreteSyntax
import Err
import MonadUtil
import Paths_dex  (getDataFileName)
import SourceRename
import SourceIdTraversal
import PPrint
import Types.Complicated
import Types.Simple
import Types.Imp
import Types.Primitives
import Types.Source
import Types.Top2
import Util ( Tree (..), File (..), readFileWithHash)

-- === top-level monad ===

data LibPath = LibDirectory FilePath | LibBuiltinPath

data EvalConfig = EvalConfig
  { libPaths      :: [LibPath]
  , preludeFile   :: Maybe FilePath
  , optLevel      :: OptLevel
  , printBackend  :: PrintBackend
  , cfgLogLevel   :: LogLevel }

type LogAction = Outputs -> IO ()
class Monad m => ConfigReader m where
  getConfig :: m EvalConfig

type TopLogger m = (MonadIO m, Logger Outputs m)

class ( Fallible m
      , Logger Outputs m
      , HasIOLogger Outputs m
      , CanSetIOLogger Outputs m
      , Catchable m
      , ConfigReader m
      , MonadIO m ) -- TODO: something more restricted here
      => Topper m

data TopperReaderData = TopperReaderData
  { topperEvalConfig :: EvalConfig
  , topperLogAction  :: LogAction }

newtype TopperM a = TopperM
  { runTopperM'
    :: ReaderT TopperReaderData IO a }
    deriving ( Functor, Applicative, Monad, MonadIO, MonadFail
             , Fallible, Catchable)

runTopperM
  :: EvalConfig -> LogAction -> TopState
  -> TopperM a
  -> IO (a, TopState)
runTopperM = undefined -- opts logger (TopState env rtEnv) cont = undefined
-- runTopperM opts logger (TopState env rtEnv) cont = do
--   Abs frag (LiftE result) <-
--     flip runReaderT (TopperReaderData opts logger rtEnv) $
--       runTopBuilderT env $ runTopperM' do
--         localTopBuilder $ LiftE <$> cont
--   return (result, extendTopEnv env rtEnv frag)

-- extendTopEnv :: Distinct n => Env n -> RuntimeEnv -> TopEnvFrag n l -> TopState
-- extendTopEnv env rtEnv frag = do
--   refreshAbsPure (toScope env) (Abs frag UnitE) \_ frag' UnitE ->
--     TopState (extendOutMap env frag') rtEnv

initTopState :: IO TopState
initTopState = undefined
  -- dyvarStores <- allocateDynamicVarKeyPtrs
  -- return $ TopState emptyOutMap dyvarStores

captureLogs :: (LogAction -> IO a) -> IO (a, Outputs)
captureLogs cont = do
  ref <- newIORef mempty
  ans <- cont \outs -> modifyIORef ref (<>outs)
  finalOuts <- readIORef ref
  return (ans, finalOuts)

-- ======

parseSourceBlocks :: T.Text -> [SourceBlock]
parseSourceBlocks source = uModuleSourceBlocks $ parseUModule Main source

evalSourceBlockIO
  :: EvalConfig -> LogAction -> TopState -> SourceBlock -> IO (ExitStatus, TopState)
evalSourceBlockIO opts logger env block =
  runTopperM opts logger env $ evalSourceBlockRepl block

data ExitStatus = ExitSuccess | ExitFailure  deriving (Show)

-- Module imports have to be handled differently in the repl because we don't
-- know ahead of time which modules will be needed.
evalSourceBlockRepl :: Topper m => SourceBlock -> m ExitStatus
evalSourceBlockRepl block = do
  case sbContents block of
    Misc (ImportModule name) -> do
      -- TODO: clear source map and synth candidates before calling this
      ensureModuleLoaded name
    _ -> return ()
  maybeErr <- evalSourceBlock Main block
  case maybeErr of
    Success () -> return ExitSuccess
    Failure e -> do
      logTop $ Error e
      return $ ExitFailure

-- XXX: This ensures that a module and its transitive dependencies are loaded,
-- (which will require evaluating them if they're not in the cache) but it
-- doesn't bring the names and instances into scope. The modules are "loaded"
-- but not yet "imported".
ensureModuleLoaded :: Topper m => ModuleSourceName -> m ()
ensureModuleLoaded moduleSourceName = undefined
-- ensureModuleLoaded moduleSourceName = do
--   -- TODO: think about where import errors should be handled
--   depsRequired <- findDepsTransitively moduleSourceName
--   forM_ depsRequired \md -> do
--     evaluated <- evalPartiallyParsedUModuleCached md
--     updateTopEnv $ UpdateLoadedModules (umppName md) evaluated
-- {-# SCC ensureModuleLoaded #-}

evalSourceBlock
  :: Topper m => ModuleSourceName -> SourceBlock -> m (Except ())
evalSourceBlock mname block = do
  maybeErr <- catchErrExcept do
    logTop $ SourceInfo $ SIGroupingInfo $ getGroupingInfo $ sbContents block
    evalSourceBlock' mname block
  case (maybeErr, sbContents block) of
    (Failure _, TopDecl decl) -> do
      case parseDecl decl of
        Success decl' -> undefined -- emitSourceMap $ uDeclErrSourceMap (makeTopNameDescription mname block) decl'
        Failure _ -> return ()
    _ -> return ()
  return maybeErr

evalSourceBlock'
  :: Topper m => ModuleSourceName -> SourceBlock -> m ()
evalSourceBlock' mname block = case sbContents block of
  TopDecl decl -> parseDecl decl >>= execUDecl (makeTopNameDescription mname block)
  UnParseable _ s -> throwErr $ ParseErr $ MiscParseErr s
  Misc m -> case m of
    ImportModule moduleName -> undefined -- importModule moduleName
    ProseBlock _ -> return ()
    CommentLine  -> return ()
    EmptyLines   -> return ()
  where
    addTypeAnn :: UExpr n -> UExpr n -> UExpr n
    addTypeAnn e = WithSrcE (srcPos e) . UTypeAnn e
    addShowAny :: UExpr n -> UExpr n
    addShowAny e = WithSrcE (srcPos e) $ UApp (referTo $ WithSrc (srcPos e) "show_any") [e] []
    referTo :: SourceNameW -> UExpr n
    referTo (WithSrc sid name) =  WithSrcE sid $ UVar $ SourceName sid name

-- -- returns a toposorted list of the module's transitive dependencies (including
-- -- the module itself) excluding those provided in the set of already known
-- -- modules.
-- findDepsTransitively
--   :: forall m n. (Topper m, Mut n)
--   => ModuleSourceName -> m n [UModulePartialParse]
-- findDepsTransitively initialModuleName = do
--   alreadyLoaded <- M.keysSet . fromLoadedModules
--     <$> withEnv (envLoadedModules . topEnv)
--   flip evalStateT alreadyLoaded $ execWriterT $ go initialModuleName
--   where
--     go :: ModuleSourceName -> WriterT [UModulePartialParse]
--                                 (StateT (S.Set ModuleSourceName) m) ()
--     go name = do
--       alreadyVisited <- S.member name <$> get
--       unless alreadyVisited do
--         modify $ S.insert name
--         config <- lift $ lift $ getConfig
--         source <- loadModuleSource config name
--         deps <- lift $ lift $ parseUModuleDepsCached name source
--         mapM_ go deps
--         tell [UModulePartialParse name deps source]

-- -- What would it look like to abstract away pattern used here and in
-- -- `evalPartiallyParsedUModuleCached`? We still want case-by-case control over
-- -- keys, eviction policy, etc. Maybe some a type class for caches that implement
-- -- query/extend, with `extend` being where the eviction happens?
-- parseUModuleDepsCached
--   :: (Mut n, TopBuilder m) => ModuleSourceName -> File -> m n [ModuleSourceName]
-- parseUModuleDepsCached Main file = return $ parseUModuleDeps Main file
-- parseUModuleDepsCached name file = do
--   cache <- parsedDeps <$> getCache
--   let req = fHash file
--   case M.lookup name cache of
--     Just (cachedReq, result) | cachedReq == req -> return result
--     _ -> do
--       let result = parseUModuleDeps name file
--       updateTopEnv $ ExtendCache $ mempty { parsedDeps = M.singleton name (req, result) }
--       return result

-- evalPartiallyParsedUModuleCached
--   :: (Topper m, Mut n)
--   => UModulePartialParse -> m n (ModuleName n)
-- evalPartiallyParsedUModuleCached md@(UModulePartialParse name deps source) = do
--   case name of
--     Main -> evalPartiallyParsedUModule md  -- Don't cache main
--     _ -> do
--       LiftE cache <- withEnv $ LiftE . moduleEvaluations . envCache . topEnv
--       -- TODO: we know that these are sufficient to determine the result of
--       -- module evaluation, but maybe we should actually restrict the
--       -- environment we pass to `evalUModule` so that it can't possibly depend
--       -- on anything else.
--       directDeps <- forM deps \dep -> do
--         lookupLoadedModule dep >>= \case
--           Just depVal -> return depVal
--           Nothing -> throwInternal $ pprint dep ++ " isn't loaded"
--       let req = (fHash source, directDeps)
--       case M.lookup name cache of
--         Just (cachedReq, result) | cachedReq == req -> return result
--         _ -> do
--           liftIO $ hPutStrLn stderr $ "Compiling " ++ pprint name
--           result <- evalPartiallyParsedUModule md
--           updateTopEnv $ ExtendCache $ mempty {
--             moduleEvaluations = M.singleton name (req, result) }
--           return result

-- -- Assumes all module dependencies have been loaded already
-- evalPartiallyParsedUModule
--   :: (Topper m, Mut n)
--   => UModulePartialParse -> m n (ModuleName n)
-- evalPartiallyParsedUModule partiallyParsed = do
--   let name = umppName partiallyParsed
--   let uModule = finishUModuleParse partiallyParsed
--   evaluated <- evalUModule uModule
--   emitBinding (getNameHint name) $ ModuleBinding evaluated

-- -- Assumes all module dependencies have been loaded already
-- evalUModule :: (Topper m, Mut n) => UModule -> m n (Module n)
-- evalUModule (UModule name _ blocks) = dropSourceInfoLogging do
--   Abs topFrag UnitE <- localTopBuilder $ mapM_ (evalSourceBlock' name) blocks >> return UnitE
--   TopEnvFrag envFrag moduleEnvFrag otherUpdates <- return topFrag
--   ModuleEnv (ImportStatus directDeps transDeps) sm scs <- return moduleEnvFrag
--   let fragToReEmit = TopEnvFrag envFrag mempty otherUpdates
--   let evaluatedModule = Module name directDeps transDeps sm scs
--   emitEnv $ Abs fragToReEmit evaluatedModule

dropSourceInfoLogging :: Topper m => m a -> m a
dropSourceInfoLogging cont = do
  (ans, Outputs logs) <- captureIOLogs cont
  let logs' = filter isNotSourceInfo logs
  emitLog $ Outputs logs'
  return ans
  where
    isNotSourceInfo = \case
      SourceInfo _ -> False
      _ -> True

-- importModule :: (Mut n, TopBuilder m, Fallible1 m) => ModuleSourceName -> m n ()
-- importModule name = do
--   lookupLoadedModule name >>= \case
--     Nothing -> throwErr $ MiscErr $ ModuleImportErr $ pprint name
--     Just name' -> do
--       Module _ _ transImports' _ _ <- lookupModule name'
--       let importStatus = ImportStatus (S.singleton name')
--             (S.singleton name' <> transImports')
--       emitLocalModuleEnv $ mempty { envImportStatus = importStatus }
-- {-# SCC importModule #-}


-- evalUType :: (Topper m, Mut n) => UType VoidS -> m n (CType n)
-- evalUType ty = do
--   logPass Parse ty
--   renamed <- renameSourceNamesUExpr ty
--   logPass RenamePass renamed
--   checkPass TypePass $ checkTopUType renamed

-- evalUExpr :: (Topper m, Mut n) => UExpr VoidS -> m n (CAtom n)
-- evalUExpr expr = do
--   logPass Parse expr
--   renamed <- renameSourceNamesUExpr expr
--   logPass RenamePass renamed
--   typed <- checkPass TypePass $ inferTopUExpr renamed
--   evalBlock typed

-- whenOpt :: Topper m => a -> (a -> m n a) -> m n a
-- whenOpt x act = getConfig <&> optLevel >>= \case
--   NoOptimize -> return x
--   Optimize   -> act x

-- evalBlock :: (Topper m, Mut n) => TopBlock n -> m n (CAtom n)
-- evalBlock typed@(TopLam _ _ (LamExpr Empty body)) = case body of
--   Atom result -> return result
--   _ -> do
--     simp <- checkPass SimpPass $ simplifyTopBlock typed
--     opt <- simpOptimizations simp
--     dps <- checkPass LowerPass $ dpsPass opt
--     lOpt <- checkPass OptPass $ loweredOptimizations dps
--     cc <- getEntryFunCC
--     impOpt <- checkPass ImpPass $ toImpFunction cc lOpt
--     llvmOpt <- packageLLVMCallable impOpt
--     resultVals <- liftIO $ callEntryFun llvmOpt []
--     TopLam _ destTy _ <- return lOpt
--     resultTy <- return $ assumeConst $ piTypeWithoutDest destTy
--     RepVal _ repVal <- repValFromFlatList resultTy resultVals
--     return $ toAtom $ RepVal (getType body) repVal
-- evalBlock _ = error "not a top block"
-- {-# SCC evalBlock #-}

simpOptimizations :: Topper m => STopLam -> m STopLam
simpOptimizations simp = undefined
-- simpOptimizations simp = do
--   analyzed <- whenOpt simp $ checkPass OccAnalysisPass . analyzeOccurrences
--   inlined <- whenOpt analyzed $ checkPass InlinePass . inlineBindings
--   analyzed2 <- whenOpt inlined $ checkPass OccAnalysisPass . analyzeOccurrences
--   inlined2 <- whenOpt analyzed2 $ checkPass InlinePass . inlineBindings
--   whenOpt inlined2 $ checkPass OptPass . optimize

execUDecl :: Topper m => TopNameDescription -> UTopDecl -> m ()
execUDecl desc decl = undefined
-- execUDecl desc decl = do
--   logPass Parse decl
--   renamed@(Abs renamedDecl sourceMap) <- renameSourceNamesTopUDecl desc decl
--   logPass RenamePass renamed
--   inferenceResult <- checkPass TypePass $ inferTopUDecl renamedDecl sourceMap
--   case inferenceResult of
--     UDeclResultBindName ann block (Abs b sm) -> do
--       result <- evalBlock block
--       case ann of
--         NoInlineLet -> do
--           let fTy = getType result
--           f <- emitBinding (getNameHint b) $ AtomNameBinding $ NoinlineFun fTy result
--           applyRename (b@>f) sm >>= emitSourceMap
--         _ -> do
--           v <- emitTopLet (getNameHint b) ann (Atom result)
--           applyRename (b@>atomVarName v) sm >>= emitSourceMap
--     UDeclResultBindPattern hint block (Abs bs sm) -> do
--       result <- evalBlock block
--       xs <- unpackTelescope bs result
--       vs <- forM xs \x -> emitTopLet hint PlainLet (Atom x)
--       applyRename (bs@@>(atomVarName <$> vs)) sm >>= emitSourceMap
--     UDeclResultDone sourceMap' -> emitSourceMap sourceMap'

getLLVMOptLevel :: EvalConfig -> LLVMOptLevel
getLLVMOptLevel cfg = case optLevel cfg of
  NoOptimize -> OptALittle
  Optimize   -> OptAggressively

checkPass :: (Topper m, Pretty e) => PassName -> m e -> m e
checkPass name cont = do
  result <- cont
  logPass name result
  return result

logTop :: TopLogger m => Output -> m ()
logTop x = emitLog $ Outputs [x]

logDebug :: TopLogger m => m Output -> m ()
logDebug m = getLogLevel >>= \case
  NormalLogLevel -> return ()
  DebugLogLevel -> do
    x <- m
    emitLog $ Outputs [x]

logPass :: Topper m => Pretty a => PassName -> a -> m ()
logPass passName result = do
  getLogLevel >>= \case
    NormalLogLevel -> logTop $ PassResult passName Nothing
    DebugLogLevel  -> logTop $ PassResult passName  $ Just s
      where s = "=== " <> pprint passName <> " ===\n" <> pprint result

-- === instances ===

instance ConfigReader TopperM where
  getConfig = TopperM $ asks topperEvalConfig

instance Topper TopperM

instance Logger Outputs TopperM where
  emitLog x = do
    logger <- getIOLogAction
    liftIO $ logger x
  getLogLevel = cfgLogLevel <$> getConfig

instance HasIOLogger Outputs TopperM where
  getIOLogAction = TopperM $ asks topperLogAction

instance CanSetIOLogger Outputs TopperM where
  withIOLogAction logger (TopperM m) = TopperM do
    local (\r -> r { topperLogAction = logger }) m
