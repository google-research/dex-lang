-- Copyright 2020 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE UndecidableInstances #-}

module TopLevel (
  EvalConfig (..), Topper, TopperM, runTopperM,
  evalSourceBlockRepl, OptLevel (..), TopStateEx (..), LibPath (..),
  evalSourceBlockIO, initTopState, loadCache, storeCache, clearCache,
  ensureModuleLoaded, importModule, printCodegen,
  loadObject, toCFunction, packageLLVMCallable,
  simpOptimizations, loweredOptimizations, compileTopLevelFun,
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
import Builder
import CheckType ( CheckableE (..), checkTypeIs)
#ifdef DEX_DEBUG
import CheckType (checkTypes)
#endif
import Core
import ConcreteSyntax
import CheapReduction
import Err
import IRVariants
import Imp
import ImpToLLVM
import Inference
import Inline
import Lower
import MonadUtil
import MTL1
import Subst
import Name
import OccAnalysis
import Optimize
import Paths_dex  (getDataFileName)
import QueryType
import Runtime
import Serialize (takePtrSnapshot, restorePtrSnapshot)
import Simplify
import SourceRename
import SourceIdTraversal
import PPrint
import Types.Core
import Types.Imp
import Types.Primitives
import Types.Source
import Types.Top
import Util ( Tree (..), File (..), readFileWithHash)
import Vectorize

-- === top-level monad ===

data LibPath = LibDirectory FilePath | LibBuiltinPath

data EvalConfig = EvalConfig
  { backendName   :: Backend
  , libPaths      :: [LibPath]
  , preludeFile   :: Maybe FilePath
  , optLevel      :: OptLevel
  , printBackend  :: PrintBackend
  , cfgLogLevel   :: LogLevel }

type LogAction = Outputs -> IO ()
class Monad m => ConfigReader m where
  getConfig :: m EvalConfig

class Monad m => RuntimeEnvReader m where
  getRuntimeEnv :: m RuntimeEnv

type TopLogger m = (MonadIO m, Logger Outputs m)

class ( forall n. Fallible (m n)
      , forall n. Logger Outputs (m n)
      , forall n. HasIOLogger Outputs (m n)
      , forall n. CanSetIOLogger Outputs (m n)
      , forall n. Catchable (m n)
      , forall n. ConfigReader (m n)
      , forall n. RuntimeEnvReader (m n)
      , forall n. MonadIO (m n)  -- TODO: something more restricted here
      , TopBuilder m )
      => Topper m

data TopperReaderData = TopperReaderData
  { topperEvalConfig :: EvalConfig
  , topperLogAction  :: LogAction
  , topperRuntimeEnv :: RuntimeEnv }

newtype TopperM (n::S) a = TopperM
  { runTopperM'
    :: TopBuilderT (ReaderT TopperReaderData IO) n a }
    deriving ( Functor, Applicative, Monad, MonadIO, MonadFail
             , Fallible, EnvReader, ScopeReader, Catchable)

-- Hides the `n` parameter as an existential
data TopStateEx where
  TopStateEx :: Distinct n => Env n -> RuntimeEnv -> TopStateEx
instance Show TopStateEx where show _ = "TopStateEx"

-- Hides the `n` parameter as an existential
data TopSerializedStateEx where
  TopSerializedStateEx :: Distinct n => SerializedEnv n -> TopSerializedStateEx

runTopperM
  :: EvalConfig -> LogAction -> TopStateEx
  -> (forall n. Mut n => TopperM n a)
  -> IO (a, TopStateEx)
runTopperM opts logger (TopStateEx env rtEnv) cont = do
  Abs frag (LiftE result) <-
    flip runReaderT (TopperReaderData opts logger rtEnv) $
      runTopBuilderT env $ runTopperM' do
        localTopBuilder $ LiftE <$> cont
  return (result, extendTopEnv env rtEnv frag)

extendTopEnv :: Distinct n => Env n -> RuntimeEnv -> TopEnvFrag n l -> TopStateEx
extendTopEnv env rtEnv frag = do
  refreshAbsPure (toScope env) (Abs frag UnitE) \_ frag' UnitE ->
    TopStateEx (extendOutMap env frag') rtEnv

initTopState :: IO TopStateEx
initTopState = do
  dyvarStores <- allocateDynamicVarKeyPtrs
  return $ TopStateEx emptyOutMap dyvarStores

allocateDynamicVarKeyPtrs :: IO DynamicVarKeyPtrs
allocateDynamicVarKeyPtrs = do
  ptr <- createTLSKey
  return [(OutStreamDyvar, castPtr ptr)]

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
  :: EvalConfig -> LogAction -> TopStateEx -> SourceBlock -> IO (ExitStatus, TopStateEx)
evalSourceBlockIO opts logger env block =
  runTopperM opts logger env $ evalSourceBlockRepl block

data ExitStatus = ExitSuccess | ExitFailure  deriving (Show)

-- Module imports have to be handled differently in the repl because we don't
-- know ahead of time which modules will be needed.
evalSourceBlockRepl :: (Topper m, Mut n) => SourceBlock -> m n ExitStatus
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
ensureModuleLoaded :: (Topper m, Mut n) => ModuleSourceName -> m n ()
ensureModuleLoaded moduleSourceName = do
  -- TODO: think about where import errors should be handled
  depsRequired <- findDepsTransitively moduleSourceName
  forM_ depsRequired \md -> do
    evaluated <- evalPartiallyParsedUModuleCached md
    updateTopEnv $ UpdateLoadedModules (umppName md) evaluated
{-# SCC ensureModuleLoaded #-}

evalSourceBlock
  :: (Topper m, Mut n) => ModuleSourceName -> SourceBlock -> m n (Except ())
evalSourceBlock mname block = do
  maybeErr <- catchErrExcept do
    logTop $ SourceInfo $ SIGroupingInfo $ getGroupingInfo $ sbContents block
    evalSourceBlock' mname block
  case (maybeErr, sbContents block) of
    (Failure _, TopDecl decl) -> do
      case parseDecl decl of
        Success decl' -> emitSourceMap $ uDeclErrSourceMap (makeTopNameDescription mname block) decl'
        Failure _ -> return ()
    _ -> return ()
  return maybeErr

evalSourceBlock'
  :: (Topper m, Mut n) => ModuleSourceName -> SourceBlock -> m n ()
evalSourceBlock' mname block = case sbContents block of
  TopDecl decl -> parseDecl decl >>= execUDecl (makeTopNameDescription mname block)
  Command cmd expr' -> do
   expr <- parseExpr expr'
   case cmd of
    -- TODO: we should filter the top-level emissions we produce in this path
    -- we want cache entries but we don't want dead names.
    EvalExpr fmt -> when (mname == Main) case fmt of
      Printed maybeExplicitBackend -> do
        printMode <- case maybeExplicitBackend of
          Just backend -> return backend
          Nothing -> printBackend <$> getConfig
        case printMode of
          PrintHaskell -> do
            val <- evalUExpr expr
            logTop $ TextOut $ pprint val
          PrintCodegen -> do
            stringVal <- evalUExpr $ addShowAny expr
            s <- getDexString stringVal
            logTop $ TextOut s
      RenderHtml -> do
        stringVal <- evalUExpr $ addTypeAnn expr (referTo $ WithSrc (srcPos expr) "String")
        s <- getDexString stringVal
        logTop $ HtmlOut s
    ExportFun _ -> error "not implemented"
    --   f <- evalUModuleVal v m
    --   void $ traverseLiterals f \val -> case val of
    --     PtrLit _ _ -> throw CompilerErr $
    --       "Can't export functions with captured pointers (not implemented)."
    --     _ -> return $ Con $ Lit val
    --   logTop $ ExportedFun name f
    GetType -> do  -- TODO: don't actually evaluate it
      val <- evalUExpr expr
      logTop $ TextOut $ pprintCanonicalized $ getType val
  DeclareForeign fname (WithSrc _ dexName) cTy -> do
    ty <- evalUType =<< parseExpr cTy
    asFFIFunType ty >>= \case
      Nothing -> throwErr $ MiscErr $ MiscMiscErr
        "FFI functions must be n-ary first order functions with the IO effect"
      Just (impFunTy, naryPiTy) -> do
        -- TODO: query linking stuff and check the function is actually available
        let hint = fromString $ pprint dexName
        fTop  <- emitBinding hint $ TopFunBinding $ FFITopFun (pprint $ withoutSrc fname) impFunTy
        vCore <- emitBinding hint $ AtomNameBinding $ FFIFunBound naryPiTy fTop
        let desc = makeTopNameDescription mname block
        emitSourceMap $ SourceMap $
          M.singleton dexName [ModuleVar desc (Just $ UAtomVar vCore)]
  DeclareCustomLinearization fname zeros g -> do
    expr <- parseExpr g
    lookupSourceMap (withoutSrc fname) >>= \case
      Nothing -> throw rootSrcId $ UnboundVarErr $ pprint fname
      Just (UAtomVar fname') -> do
        lookupCustomRules fname' >>= \case
          Nothing -> return ()
          Just _  -> throwErr $ MiscErr $ MiscMiscErr
            $ pprint fname ++ " already has a custom linearization"
        lookupAtomName fname' >>= \case
          NoinlineFun _ _ -> return ()
          _ -> throwErr $ MiscErr $ MiscMiscErr "Custom linearizations only apply to @noinline functions"
        -- We do some special casing to avoid instantiating polymorphic functions.
        impl <- case expr of
          WithSrcE _ (UVar _) ->
            renameSourceNamesUExpr expr >>= \case
              WithSrcE _ (UVar (InternalName _ _ (UAtomVar v))) -> toAtom <$> toAtomVar v
              _ -> error "Expected a variable"
          _ -> evalUExpr expr
        fType <- getType <$> toAtomVar fname'
        (nimplicit, nexplicit, linFunTy) <- liftExceptEnvReaderM $ getLinearizationType zeros fType
        liftEnvReaderT (impl `checkTypeIs` linFunTy) >>= \case
          Failure _ -> do
            let implTy = getType impl
            throwErr $ MiscErr $ MiscMiscErr $ unlines
              [ "Expected the custom linearization to have type:" , "" , pprint linFunTy , ""
              , "but it has type:" , "" , pprint implTy]
          Success () -> return ()
        updateTopEnv $ AddCustomRule fname' $ CustomLinearize nimplicit nexplicit zeros impl
      Just _ -> throwErr $ MiscErr $ MiscMiscErr $ "Custom linearization can only be defined for functions"
  UnParseable _ s -> throwErr $ ParseErr $ MiscParseErr s
  Misc m -> case m of
    GetNameType v -> do
      lookupSourceMap (withoutSrc v) >>= \case
        Nothing -> throw rootSrcId $ UnboundVarErr $ pprint v
        Just uvar -> do
          ty <- getUVarType uvar
          logTop $ TextOut $ pprintCanonicalized ty
    ImportModule moduleName -> importModule moduleName
    QueryEnv query -> void $ runEnvQuery query $> UnitE
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

runEnvQuery :: Topper m => EnvQuery -> m n ()
runEnvQuery query = do
  env <- unsafeGetEnv
  case query of
    DumpSubst -> logTop $ TextOut $ pprint $ env
    InternalNameInfo name ->
      case lookupSubstFragRaw (fromRecSubst $ envDefs $ topEnv env) name of
        Nothing      -> throw rootSrcId $ UnboundVarErr $ pprint name
        Just binding -> logTop $ TextOut $ pprint binding
    SourceNameInfo name -> do
      lookupSourceMap name >>= \case
        Nothing -> throw rootSrcId $ UnboundVarErr $ pprint name
        Just uvar -> do
          logTop $ TextOut $ pprint uvar
          info <- case uvar of
            UAtomVar     v' -> pprint <$> lookupEnv v'
            UTyConVar    v' -> pprint <$> lookupEnv v'
            UDataConVar  v' -> pprint <$> lookupEnv v'
            UClassVar    v' -> pprint <$> lookupEnv v'
            UMethodVar   v' -> pprint <$> lookupEnv v'
            UPunVar v' -> do
              val <- lookupEnv v'
              return $ pprint val ++ "\n(type constructor and data constructor share the same name)"
          logTop $ TextOut $ "Binding:\n" ++ info

-- returns a toposorted list of the module's transitive dependencies (including
-- the module itself) excluding those provided in the set of already known
-- modules.
findDepsTransitively
  :: forall m n. (Topper m, Mut n)
  => ModuleSourceName -> m n [UModulePartialParse]
findDepsTransitively initialModuleName = do
  alreadyLoaded <- M.keysSet . fromLoadedModules
    <$> withEnv (envLoadedModules . topEnv)
  flip evalStateT alreadyLoaded $ execWriterT $ go initialModuleName
  where
    go :: ModuleSourceName -> WriterT [UModulePartialParse]
                                (StateT (S.Set ModuleSourceName) (m n)) ()
    go name = do
      alreadyVisited <- S.member name <$> get
      unless alreadyVisited do
        modify $ S.insert name
        config <- lift $ lift $ getConfig
        source <- loadModuleSource config name
        deps <- lift $ lift $ parseUModuleDepsCached name source
        mapM_ go deps
        tell [UModulePartialParse name deps source]

-- What would it look like to abstract away pattern used here and in
-- `evalPartiallyParsedUModuleCached`? We still want case-by-case control over
-- keys, eviction policy, etc. Maybe some a type class for caches that implement
-- query/extend, with `extend` being where the eviction happens?
parseUModuleDepsCached
  :: (Mut n, TopBuilder m) => ModuleSourceName -> File -> m n [ModuleSourceName]
parseUModuleDepsCached Main file = return $ parseUModuleDeps Main file
parseUModuleDepsCached name file = do
  cache <- parsedDeps <$> getCache
  let req = fHash file
  case M.lookup name cache of
    Just (cachedReq, result) | cachedReq == req -> return result
    _ -> do
      let result = parseUModuleDeps name file
      updateTopEnv $ ExtendCache $ mempty { parsedDeps = M.singleton name (req, result) }
      return result

evalPartiallyParsedUModuleCached
  :: (Topper m, Mut n)
  => UModulePartialParse -> m n (ModuleName n)
evalPartiallyParsedUModuleCached md@(UModulePartialParse name deps source) = do
  case name of
    Main -> evalPartiallyParsedUModule md  -- Don't cache main
    _ -> do
      LiftE cache <- withEnv $ LiftE . moduleEvaluations . envCache . topEnv
      -- TODO: we know that these are sufficient to determine the result of
      -- module evaluation, but maybe we should actually restrict the
      -- environment we pass to `evalUModule` so that it can't possibly depend
      -- on anything else.
      directDeps <- forM deps \dep -> do
        lookupLoadedModule dep >>= \case
          Just depVal -> return depVal
          Nothing -> throwInternal $ pprint dep ++ " isn't loaded"
      let req = (fHash source, directDeps)
      case M.lookup name cache of
        Just (cachedReq, result) | cachedReq == req -> return result
        _ -> do
          liftIO $ hPutStrLn stderr $ "Compiling " ++ pprint name
          result <- evalPartiallyParsedUModule md
          updateTopEnv $ ExtendCache $ mempty {
            moduleEvaluations = M.singleton name (req, result) }
          return result

-- Assumes all module dependencies have been loaded already
evalPartiallyParsedUModule
  :: (Topper m, Mut n)
  => UModulePartialParse -> m n (ModuleName n)
evalPartiallyParsedUModule partiallyParsed = do
  let name = umppName partiallyParsed
  let uModule = finishUModuleParse partiallyParsed
  evaluated <- evalUModule uModule
  emitBinding (getNameHint name) $ ModuleBinding evaluated

-- Assumes all module dependencies have been loaded already
evalUModule :: (Topper m, Mut n) => UModule -> m n (Module n)
evalUModule (UModule name _ blocks) = dropSourceInfoLogging do
  Abs topFrag UnitE <- localTopBuilder $ mapM_ (evalSourceBlock' name) blocks >> return UnitE
  TopEnvFrag envFrag moduleEnvFrag otherUpdates <- return topFrag
  ModuleEnv (ImportStatus directDeps transDeps) sm scs <- return moduleEnvFrag
  let fragToReEmit = TopEnvFrag envFrag mempty otherUpdates
  let evaluatedModule = Module name directDeps transDeps sm scs
  emitEnv $ Abs fragToReEmit evaluatedModule

dropSourceInfoLogging :: Topper m => m n a -> m n a
dropSourceInfoLogging cont = do
  (ans, Outputs logs) <- captureIOLogs cont
  let logs' = filter isNotSourceInfo logs
  emitLog $ Outputs logs'
  return ans
  where
    isNotSourceInfo = \case
      SourceInfo _ -> False
      _ -> True

importModule :: (Mut n, TopBuilder m, Fallible1 m) => ModuleSourceName -> m n ()
importModule name = do
  lookupLoadedModule name >>= \case
    Nothing -> throwErr $ MiscErr $ ModuleImportErr $ pprint name
    Just name' -> do
      Module _ _ transImports' _ _ <- lookupModule name'
      let importStatus = ImportStatus (S.singleton name')
            (S.singleton name' <> transImports')
      emitLocalModuleEnv $ mempty { envImportStatus = importStatus }
{-# SCC importModule #-}

evalUType :: (Topper m, Mut n) => UType VoidS -> m n (CType n)
evalUType ty = do
  logPass Parse ty
  renamed <- renameSourceNamesUExpr ty
  logPass RenamePass renamed
  checkPass TypePass $ checkTopUType renamed

evalUExpr :: (Topper m, Mut n) => UExpr VoidS -> m n (CAtom n)
evalUExpr expr = do
  logPass Parse expr
  renamed <- renameSourceNamesUExpr expr
  logPass RenamePass renamed
  typed <- checkPass TypePass $ inferTopUExpr renamed
  evalBlock typed

whenOpt :: Topper m => a -> (a -> m n a) -> m n a
whenOpt x act = getConfig <&> optLevel >>= \case
  NoOptimize -> return x
  Optimize   -> act x

evalBlock :: (Topper m, Mut n) => TopBlock CoreIR n -> m n (CAtom n)
evalBlock typed = do
  SimplifiedTopLam simp recon <- checkPass SimpPass $ simplifyTopBlock typed
  opt <- simpOptimizations simp
  simpResult <- case opt of
    TopLam _ _ (LamExpr Empty (Atom result)) -> return result
    _ -> do
      lowered <- checkPass LowerPass $ lowerFullySequential True opt
      lOpt <- checkPass OptPass $ loweredOptimizations lowered
      cc <- getEntryFunCC
      impOpt <- checkPass ImpPass $ toImpFunction cc lOpt
      llvmOpt <- packageLLVMCallable impOpt
      resultVals <- liftIO $ callEntryFun llvmOpt []
      TopLam _ destTy _ <- return lOpt
      EffTy _ resultTy <- return $ assumeConst $ piTypeWithoutDest destTy
      repValAtom =<< repValFromFlatList resultTy resultVals
  applyReconTop recon simpResult
{-# SCC evalBlock #-}

simpOptimizations :: Topper m => STopLam n -> m n (STopLam n)
simpOptimizations simp = do
  analyzed <- whenOpt simp $ checkPass OccAnalysisPass . analyzeOccurrences
  inlined <- whenOpt analyzed $ checkPass InlinePass . inlineBindings
  analyzed2 <- whenOpt inlined $ checkPass OccAnalysisPass . analyzeOccurrences
  inlined2 <- whenOpt analyzed2 $ checkPass InlinePass . inlineBindings
  whenOpt inlined2 $ checkPass OptPass . optimize

loweredOptimizations :: Topper m => STopLam n -> m n (STopLam n)
loweredOptimizations lowered = do
  lopt <- whenOpt lowered $ checkPass LowerOptPass .
    (dceTop >=> hoistLoopInvariant)
  whenOpt lopt \lo -> do
    (vo, errs) <- vectorizeLoops 64 lo
    logTop $ TextOut $ pprint errs
    checkPass VectPass $ return vo

loweredOptimizationsNoDest :: Topper m => STopLam n -> m n (STopLam n)
loweredOptimizationsNoDest lowered = do
  lopt <- whenOpt lowered $ checkPass LowerOptPass .
    (dceTop >=> hoistLoopInvariant)
  -- TODO Add a NoDest entry point for vectorization and add it here
  return lopt

evalSpecializations :: (Topper m, Mut n) => [TopFunName n] -> m n ()
evalSpecializations fs = do
  fSimps <- toposortAnnVars <$> catMaybes <$> forM fs \f -> lookupTopFun f >>= \case
    DexTopFun _ simp Waiting -> return $ Just (f, simp)
    _ -> return Nothing
  forM_ fSimps \(f, simp) -> do
    -- Prevents infinite loop in case compiling `v` ends up requiring `v`
    -- (even without recursion in Dex itself this is possible via the
    -- specialization cache)
    updateTopEnv $ UpdateTopFunEvalStatus f Running
    imp <- compileTopLevelFun StandardCC simp
    objName <- toCFunction (getNameHint f) imp >>= emitObjFile
    void $ loadObject objName
    updateTopEnv $ UpdateTopFunEvalStatus f (Finished $ TopFunLowerings objName)

evalDictSpecializations :: (Topper m, Mut n) => [SpecDictName n] -> m n ()
evalDictSpecializations ds = do
  -- TODO Do we have to do these in order, like evalSpecializations, or are they
  -- independent enough not to need it?
  -- TODO Do we need to gate the status of these, too?
  forM_ ds \dName -> do
    SpecializedDict _ (Just fs) <- lookupSpecDict dName
    fs' <- forM fs \lam -> do
      opt <- simpOptimizations lam
      lowered <- checkPass LowerPass $ lowerFullySequential False opt
      loweredOptimizationsNoDest lowered
    updateTopEnv $ LowerDictSpecialization dName fs'
  return ()

execUDecl
  :: (Topper m, Mut n) => TopNameDescription -> UTopDecl VoidS VoidS -> m n ()
execUDecl desc decl = do
  logPass Parse decl
  renamed@(Abs renamedDecl sourceMap) <- renameSourceNamesTopUDecl desc decl
  logPass RenamePass renamed
  inferenceResult <- checkPass TypePass $ inferTopUDecl renamedDecl sourceMap
  case inferenceResult of
    UDeclResultBindName ann block (Abs b sm) -> do
      result <- evalBlock block
      case ann of
        NoInlineLet -> do
          let fTy = getType result
          f <- emitBinding (getNameHint b) $ AtomNameBinding $ NoinlineFun fTy result
          applyRename (b@>f) sm >>= emitSourceMap
        _ -> do
          v <- emitTopLet (getNameHint b) ann (Atom result)
          applyRename (b@>atomVarName v) sm >>= emitSourceMap
    UDeclResultBindPattern hint block (Abs bs sm) -> do
      result <- evalBlock block
      xs <- unpackTelescope bs result
      vs <- forM xs \x -> emitTopLet hint PlainLet (Atom x)
      applyRename (bs@@>(atomVarName <$> vs)) sm >>= emitSourceMap
    UDeclResultDone sourceMap' -> emitSourceMap sourceMap'

compileTopLevelFun :: (Topper m, Mut n)
  => CallingConvention -> STopLam n -> m n (ImpFunction n)
compileTopLevelFun cc fSimp = do
  fOpt <- simpOptimizations fSimp
  fLower <- checkPass LowerPass $ lowerFullySequential True fOpt
  flOpt <- loweredOptimizations fLower
  checkPass ImpPass $ toImpFunction cc flOpt

printCodegen :: (Topper m, Mut n) => CAtom n -> m n String
printCodegen x = do
  block <- liftBuilder $ buildBlock $ emit $ ShowAny $ sink x
  (topBlock, _) <- asTopBlock block
  getDexString =<< evalBlock topBlock

loadObject :: (Topper m, Mut n) => FunObjCodeName n -> m n NativeFunction
loadObject fname =
  lookupLoadedObject fname >>= \case
    Just p -> return p
    Nothing -> do
      f <- lookupFunObjCode fname >>= loadObjectContent
      updateTopEnv $ UpdateLoadedObjects fname f
      return f

loadObjectContent :: (Topper m, Mut n) => CFunction n -> m n NativeFunction
loadObjectContent CFunction{objectCode, linkerNames} = do
  (LinktimeNames funNames ptrNames) <- return linkerNames
  funVals <- forM funNames \name -> nativeFunPtr <$> loadObject name
  ptrVals <- forM ptrNames \name -> snd <$> lookupPtrName name
  dyvarStores <- getRuntimeEnv
  liftIO $ linkFunObjCode objectCode dyvarStores $ LinktimeVals funVals ptrVals

linkFunObjCode
  :: FunObjCode -> DynamicVarKeyPtrs -> LinktimeVals -> IO NativeFunction
linkFunObjCode objCode dyvarStores (LinktimeVals funVals ptrVals) = do
  let (WithCNameInterface code mainFunName reqFuns reqPtrs dtors) = objCode
  let linkMap =   zip reqFuns (map castFunPtrToPtr funVals)
               <> zip reqPtrs ptrVals
               <> dynamicVarLinkMap dyvarStores
  l <- createLinker
  addExplicitLinkMap l linkMap
  addObjectFile l code
  ptr <- getFunctionPointer l mainFunName
  dtorPtrs <- mapM (getFunctionPointer l) dtors
  let destructor :: IO () = do
        mapM_ callDtor dtorPtrs
        destroyLinker l
  return $ NativeFunction ptr destructor

toCFunction :: (Topper m, Mut n) => NameHint -> ImpFunction n -> m n (CFunction n)
toCFunction nameHint impFun = do
  logger <- getIOLogger
  (closedImpFun, reqFuns, reqPtrNames) <- abstractLinktimeObjects impFun
  obj <- impToLLVM logger nameHint closedImpFun >>= compileToObjCode
  reqObjNames <- mapM funNameToObj reqFuns
  return $ CFunction nameHint obj (LinktimeNames reqObjNames reqPtrNames)

getLLVMOptLevel :: EvalConfig -> LLVMOptLevel
getLLVMOptLevel cfg = case optLevel cfg of
  NoOptimize -> OptALittle
  Optimize   -> OptAggressively

getEntryFunCC :: Topper m => m n CallingConvention
getEntryFunCC = getConfig <&> backendName <&> \case
    LLVMCUDA -> EntryFunCC CUDARequired
    _        -> EntryFunCC CUDANotRequired

packageLLVMCallable :: forall n m. (Topper m, Mut n)
  => ImpFunction n -> m n LLVMCallable
packageLLVMCallable impFun = do
  nativeFun <- toCFunction "main" impFun >>= loadObjectContent
  logger <- getIOLogger
  let IFunType _ _ resultTypes = impFunType impFun
  return LLVMCallable{..}

compileToObjCode :: Topper m => WithCNameInterface LLVM.AST.Module -> m n FunObjCode
compileToObjCode astWithNames = forM astWithNames \ast -> do
  logger <- getIOLogger
  opt <- getLLVMOptLevel <$> getConfig
  liftIO $ compileLLVM logger opt ast (cniMainFunName astWithNames)

funNameToObj
  :: (EnvReader m, Fallible1 m) => ImpFunName n -> m n (FunObjCodeName n)
funNameToObj v = do
  lookupEnv v >>= \case
    TopFunBinding (DexTopFun _ _ (Finished impl)) -> return $ topFunObjCode impl
    b -> error $ "couldn't find object cache entry for " ++ pprint v ++ "\ngot:\n" ++ pprint b

checkPass :: (Topper m, Pretty (e n), CheckableE r e)
          => PassName -> m n (e n) -> m n (e n)
checkPass name cont = do
  result <- cont
  logPass name result
#ifdef DEX_DEBUG
  logDebug $ return $ MiscLog $ "Running checks"
  checkTypes result
  logDebug $ return $ MiscLog $ "Checks passed"
#else
  logDebug $ return $ MiscLog $ "Checks skipped (not a debug build)"
#endif
  return result

logTop :: TopLogger m => Output -> m ()
logTop x = emitLog $ Outputs [x]

logDebug :: TopLogger m => m Output -> m ()
logDebug m = getLogLevel >>= \case
  NormalLogLevel -> return ()
  DebugLogLevel -> do
    x <- m
    emitLog $ Outputs [x]

logPass :: Topper m => Pretty a => PassName -> a -> m n ()
logPass passName result = do
  getLogLevel >>= \case
    NormalLogLevel -> logTop $ PassResult passName Nothing
    DebugLogLevel  -> logTop $ PassResult passName  $ Just s
      where s = "=== " <> pprint passName <> " ===\n" <> pprint result

loadModuleSource
  :: (MonadIO m, Fallible m) => EvalConfig -> ModuleSourceName -> m File
loadModuleSource config moduleName = do
  fullPath <- case moduleName of
    OrdinaryModule moduleName' -> findFullPath $ pprint moduleName' ++ ".dx"
    Prelude -> case preludeFile config of
      Nothing -> findFullPath "prelude.dx"
      Just path -> return path
    Main -> error "shouldn't be trying to load the source for main"
  readFileWithHash fullPath
  where
    findFullPath :: (MonadIO m, Fallible m) => String -> m FilePath
    findFullPath fname = do
      fsPaths <- liftIO $ traverse resolveBuiltinPath $ libPaths config
      liftIO (findFile fsPaths fname) >>= \case
        Just fpath -> return fpath
        Nothing    -> throwErr $ MiscErr $ CantFindModuleSource $ pprint moduleName
    resolveBuiltinPath = \case
      LibBuiltinPath   -> liftIO $ getDataFileName "lib"
      LibDirectory dir -> return dir
{-# SCC loadModuleSource #-}

getDexString :: (MonadIO1 m, EnvReader m, Fallible1 m) => Val CoreIR n -> m n String
getDexString val = do
  -- TODO: use a `ByteString` instead of `String`
  Stuck _ (LiftSimp _ (RepValAtom (RepVal _ tree))) <- return val
  Branch [Leaf (IIdxRepVal n), Leaf (IPtrVar ptrName _)] <- return tree
  PtrBinding (CPU, Scalar Word8Type) (PtrLitVal ptr) <- lookupEnv ptrName
  liftIO $ peekCStringLen (castPtr ptr, fromIntegral n)

-- === saving cache to disk ===

-- None of this is safe in the presence of multiple processes trying to interact
-- with the cache. But we plan to fix that by using an actual database.

loadCache :: MonadIO m => m TopStateEx
loadCache = liftIO do
  cachePath <- getCachePath
  cacheExists <- doesFileExist cachePath
  if cacheExists
    then do
      decoded <- decode <$> BS.readFile cachePath
      case decoded of
        Right result -> fromSerializedEnv result
        _            -> removeFile cachePath >> initTopState
    else initTopState
{-# SCC loadCache #-}

storeCache :: MonadIO m => TopStateEx -> m ()
storeCache env = liftIO do
  cachePath <- getCachePath
  createDirectoryIfMissing True =<< getCacheDir
  TopSerializedStateEx sEnv <- toSerializedEnv env
  BS.writeFile cachePath $ encode sEnv

snapshotPtrs :: MonadIO m => RecSubst Binding n -> m (RecSubst Binding n)
snapshotPtrs bindings = RecSubst <$> traverseSubstFrag
  (\case
      PtrBinding ty p -> liftIO $ PtrBinding ty <$> takePtrSnapshot ty p
      b -> return b)
  (fromRecSubst bindings)

traverseBindingsTopStateEx
  :: Monad m => TopStateEx
  -> (forall c n. Binding c n -> m (Binding c n)) -> m TopStateEx
traverseBindingsTopStateEx (TopStateEx (Env tenv menv) dyvars) f = do
  defs <- traverseSubstFrag f $ fromRecSubst $ envDefs tenv
  return $ TopStateEx (Env (tenv {envDefs = RecSubst defs}) menv) dyvars

fromSerializedEnv :: forall n m. MonadIO m => SerializedEnv n -> m TopStateEx
fromSerializedEnv (SerializedEnv defs rules cache) = do
  Distinct <- return (fabricateDistinctEvidence :: DistinctEvidence n)
  dyvarStores <- liftIO allocateDynamicVarKeyPtrs
  let topEnv = Env (TopEnv defs rules cache mempty mempty) mempty
  restorePtrSnapshots $ TopStateEx topEnv dyvarStores

toSerializedEnv :: MonadIO m => TopStateEx -> m TopSerializedStateEx
toSerializedEnv (TopStateEx (Env (TopEnv (RecSubst defs) (CustomRules rules) cache _ _) _) _) = do
  collectGarbage (RecSubstFrag defs) (PairE (CustomRules rules) cache)
    \defsFrag'@(RecSubstFrag defs') (PairE (CustomRules rules') cache') -> do
      let liveNames = toNameSet $ toScopeFrag defsFrag'
      let rules'' = CustomRules
           $ M.filterWithKey (\k _ -> k `isInNameSet` liveNames) rules'
      defs'' <- snapshotPtrs (RecSubst defs')
      return $ TopSerializedStateEx $ SerializedEnv defs'' rules'' cache'

getCacheDir :: MonadIO m => m FilePath
getCacheDir = liftIO $ getXdgDirectory XdgCache "dex"

getCachePath :: MonadIO m => m FilePath
getCachePath = liftIO do
  cacheDir <- getCacheDir
  return $ cacheDir </> "dex.cache"

clearCache :: MonadIO m => m ()
clearCache = liftIO do
  cachePath <- getCachePath
  removeFile cachePath `catch` \e -> unless (isDoesNotExistError e) (throwIO e)

restorePtrSnapshots :: MonadIO m => TopStateEx -> m TopStateEx
restorePtrSnapshots s = traverseBindingsTopStateEx s \case
  PtrBinding ty p  -> liftIO $ PtrBinding ty <$> restorePtrSnapshot p
  b -> return b

-- === instances ===

instance RuntimeEnvReader (TopperM n) where
  getRuntimeEnv = TopperM $ asks topperRuntimeEnv

instance ConfigReader (TopperM n) where
  getConfig = TopperM $ asks topperEvalConfig

instance (Monad1 m, ConfigReader (m n)) => ConfigReader (StateT1 s m n) where
  getConfig = lift11 getConfig

instance Topper TopperM

instance TopBuilder TopperM where
  emitBinding = emitBindingDefault
  emitEnv (Abs frag result) = do
    result' `PairE` ListE fNames `PairE` ListE dictNames <- TopperM $ emitEnv $
      Abs frag $ result `PairE` ListE (boundNamesList frag) `PairE` ListE (boundNamesList frag)
    evalSpecializations fNames
    evalDictSpecializations dictNames
    return result'
  emitNamelessEnv env = TopperM $ emitNamelessEnv env
  localTopBuilder cont = TopperM $ localTopBuilder $ runTopperM' cont

instance Logger Outputs (TopperM n) where
  emitLog x = do
    logger <- getIOLogAction
    liftIO $ logger x
  getLogLevel = cfgLogLevel <$> getConfig

instance HasIOLogger Outputs (TopperM n) where
  getIOLogAction = TopperM $ asks topperLogAction

instance CanSetIOLogger Outputs (TopperM n) where
  withIOLogAction logger (TopperM m) = TopperM do
    local (\r -> r { topperLogAction = logger }) m

instance Generic TopStateEx where
  type Rep TopStateEx = Rep (Env UnsafeS, RuntimeEnv)
  from (TopStateEx env rtEnv) = from ((unsafeCoerceE env :: Env UnsafeS), rtEnv)
  to rep = do
    case fabricateDistinctEvidence :: DistinctEvidence UnsafeS of
      Distinct -> uncurry TopStateEx (to rep :: (Env UnsafeS, RuntimeEnv))

getLinearizationType :: SymbolicZeros -> CType n -> EnvReaderT Except n (Int, Int, CType n)
getLinearizationType zeros = \case
  TyCon (Pi (CorePiType ExplicitApp expls bs (EffTy Pure resultTy))) -> do
    (numIs, numEs) <- getNumImplicits expls
    refreshAbs (Abs bs resultTy) \bs' resultTy' -> do
      PairB _ bsE <- return $ splitNestAt numIs bs'
      let explicitArgTys = nestToList (\b -> sink $ binderType b) bsE
      argTanTys <- forM explicitArgTys \t -> maybeTangentType t >>= \case
        Just tty -> case zeros of
          InstantiateZeros -> return tty
          SymbolicZeros    -> symbolicTangentTy tty
        Nothing  -> throwErr $ MiscErr $ MiscMiscErr $ "No tangent type for: " ++ pprint t
      resultTanTy <- maybeTangentType resultTy' >>= \case
        Just rtt -> return rtt
        Nothing  -> throwErr $ MiscErr $ MiscMiscErr $ "No tangent type for: " ++ pprint resultTy'
      let tanFunTy = toType $ Pi $ nonDepPiType argTanTys Pure resultTanTy
      let fullTy = CorePiType ExplicitApp expls bs' $ EffTy Pure (PairTy resultTy' tanFunTy)
      return (numIs, numEs, toType $ Pi fullTy)
  _ -> throwErr $ MiscErr $ MiscMiscErr $ "Can't define a custom linearization for implicit or impure functions"
  where
    getNumImplicits :: Fallible m => [Explicitness] -> m (Int, Int)
    getNumImplicits = \case
      [] -> return (0, 0)
      expl:expls -> do
        (ni, ne) <- getNumImplicits expls
        case expl of
          Inferred _ _ -> return (ni + 1, ne)
          Explicit -> case ni of
            0 -> return (0, ne + 1)
            _ -> throwErr $ MiscErr $ MiscMiscErr "All implicit args must precede implicit args"
