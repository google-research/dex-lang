-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleContexts #-}

module TopLevel (evalSourceBlock, evalDecl, evalSource, evalFile,
                 EvalConfig (..), Backend (..)) where

import Control.Monad.State.Strict
import Control.Monad.Reader
import Control.Monad.Except hiding (Except)
import Data.Text.Prettyprint.Doc
import Data.List (partition)
import Data.Time.Clock (getCurrentTime, diffUTCTime)

import Syntax
import Cat
import Env
import Embed
import Type
import Inference
import Simplify
import Serialize
import Imp
import JIT
import Logging
import LLVMExec
import PPrint
import Parser
import Util (highlightRegion)
import Optimize

data EvalConfig = EvalConfig
  { backendName :: Backend
  , preludeFile :: FilePath
  , logFile     :: Maybe FilePath
  , logService  :: Logger [Output] }

type TopPassM a = ReaderT EvalConfig IO a

evalDecl :: EvalConfig -> SourceBlock -> StateT TopEnv IO Result
evalDecl opts block = do
  env <- get
  (env', ans) <- liftIO $ evalSourceBlock opts env $ block
  put $ env <> env'
  return ans

evalFile :: EvalConfig -> FilePath -> StateT TopEnv IO [(SourceBlock, Result)]
evalFile opts fname = do
  evalSource opts =<< (liftIO $ readFile fname)

evalSource :: EvalConfig -> FilePath -> StateT TopEnv IO [(SourceBlock, Result)]
evalSource opts source = do
  let sourceBlocks = parseProg source
  results <- mapM (evalDecl opts) sourceBlocks
  return $ zip sourceBlocks results

-- TODO: handle errors due to upstream modules failing
evalSourceBlock :: EvalConfig -> TopEnv -> SourceBlock -> IO (TopEnv, Result)
evalSourceBlock opts env block = do
  (ans, outs) <- runTopPassM opts $ withCompileTime $ evalSourceBlockM env block
  let (logOuts, requiredOuts) = partition isLogInfo outs
  let outs' = requiredOuts ++ processLogs (sbLogLevel block) logOuts
  case ans of
    Left err   -> return (mempty, Result outs' (Left (addCtx block err)))
    Right env' -> return (env'  , Result outs' (Right ()))

runTopPassM :: EvalConfig -> TopPassM a -> IO (Except a, [Output])
runTopPassM opts m = runLogger (logFile opts) $ \logger ->
  runExceptT $ catchIOExcept $ runReaderT m $ opts {logService = logger}

evalSourceBlockM :: TopEnv -> SourceBlock -> TopPassM TopEnv
evalSourceBlockM env block = case sbContents block of
  RunModule m -> evalUModule env m
  Command cmd (v, m) -> mempty <$ case cmd of
    EvalExpr fmt -> do
      val <- evalUModuleVal env v m
      case fmt of
        Printed -> do
          s <- liftIO $ pprintVal val
          logTop $ TextOut s
        Heatmap color -> return mempty -- logTop $ valToHeatmap color val
        Scatter       -> return mempty -- logTop $ valToScatter val
    GetType -> do  -- TODO: don't actually evaluate it
      val <- evalUModuleVal env v m
      logTop $ TextOut $ pprint $ getType val
  GetNameType v -> case envLookup env (v:>()) of
    Just (ty, _) -> logTop (TextOut $ pprint ty) >> return mempty
    _            -> liftEitherIO $ throw UnboundVarErr $ pprint v
  IncludeSourceFile fname -> do
    source <- liftIO $ readFile fname
    evalSourceBlocks env $ parseProg source
  UnParseable _ s -> liftEitherIO $ throw ParseErr s
  _               -> return mempty

processLogs :: LogLevel -> [Output] -> [Output]
processLogs logLevel logs = case logLevel of
  LogAll -> logs
  LogNothing -> []
  LogPasses passes -> flip filter logs $ \l -> case l of
                        PassInfo pass _ | pass `elem` passes -> True
                                        | otherwise          -> False
                        _ -> False
  PrintEvalTime -> [BenchResult "" compileTime runTime]
    where (compileTime, runTime) = timesFromLogs logs
  PrintBench benchName -> [BenchResult benchName compileTime runTime]
    where (compileTime, runTime) = timesFromLogs logs

timesFromLogs :: [Output] -> (Double, Double)
timesFromLogs logs = (totalTime - evalTime, evalTime)
  where
    evalTime  = case [tEval | EvalTime tEval <- logs] of
                  []  -> 0.0
                  [t] -> t
                  _   -> error "Expect at most one result"
    totalTime = case [tTotal | TotalTime tTotal <- logs] of
                  []  -> 0.0
                  [t] -> t
                  _   -> error "Expect at most one result"

isLogInfo :: Output -> Bool
isLogInfo out = case out of
  PassInfo _ _ -> True
  MiscLog  _   -> True
  EvalTime _   -> True
  TotalTime _  -> True
  _ -> False

evalSourceBlocks :: TopEnv -> [SourceBlock] -> TopPassM TopEnv
evalSourceBlocks env blocks = catFoldM evalSourceBlockM env blocks

evalUModuleVal :: TopEnv -> Name -> UModule -> TopPassM Val
evalUModuleVal env v m = do
  env' <- evalUModule env m
  return $ lookupBindings (env <> env') (v:>())

lookupBindings :: Scope -> VarP ann -> Atom
lookupBindings scope v = reduceAtom scope x
  where (_, LetBound PlainLet (Atom x)) = scope ! v

-- TODO: extract only the relevant part of the env we can check for module-level
-- unbound vars and upstream errors here. This should catch all unbound variable
-- errors, but there could still be internal shadowing errors.
evalUModule :: TopEnv -> UModule -> TopPassM TopEnv
evalUModule env untyped = do
  -- TODO: it's handy to log the env, but we need to filter out just the
  --       relevant part (transitive closure of free vars)
  logPass Parse untyped
  typed <- liftEitherIO $ inferModule env untyped
  checkPass TypePass typed
  synthed <- liftEitherIO $ synthModule env typed
  -- TODO: check that the type of module exports doesn't change from here on
  checkPass SynthPass synthed
  evalModule env synthed

evalModule :: TopEnv -> Module -> TopPassM TopEnv
evalModule bindings normalized = do
  let defunctionalized = simplifyModule bindings normalized
  checkPass SimpPass defunctionalized
  let optimized = optimizeModule defunctionalized
  checkPass OptimPass optimized
  evaluated <- evalSimplified optimized evalBackend
  checkPass ResultPass evaluated
  Module Evaluated Empty newBindings <- return evaluated
  return newBindings

evalBackend :: Block -> TopPassM Atom
evalBackend block = do
  backend <- asks backendName
  logger  <- asks logService
  let (impModule, args, reconAtom) = toImpModule backend block
  checkPass ImpPass impModule
  llvmModule <- liftIO $ impToLLVM logger impModule
  resultVals <- liftM (map (Con . Lit)) $ liftIO $ callLLVM logger llvmModule args
  return $ applyNaryAbs reconAtom resultVals

withCompileTime :: TopPassM a -> TopPassM a
withCompileTime m = do
  t1 <- liftIO $ getCurrentTime
  ans <- m
  t2 <- liftIO $ getCurrentTime
  logTop $ TotalTime $ realToFrac $ t2 `diffUTCTime` t1
  return ans

checkPass :: (Pretty a, Checkable a) => PassName -> a -> TopPassM ()
checkPass name x = do
  logPass name x
  liftEitherIO $ checkValid x
  logTop $ MiscLog $ pprint name ++ " checks passed"

logPass :: Pretty a => PassName -> a -> TopPassM ()
logPass passName x = logTop $ PassInfo passName $ pprint x

addCtx :: SourceBlock -> Err -> Err
addCtx block err@(Err e src s) = case src of
  Nothing -> err
  Just (start, stop) ->
    Err e Nothing $ s ++ "\n\n" ++ ctx
    where n = sbOffset block
          ctx = highlightRegion (start - n, stop - n) (sbText block)

logTop :: Output -> TopPassM ()
logTop x = do
  logger <- asks logService
  logThis logger [x]
