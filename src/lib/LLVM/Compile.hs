-- Copyright 2022 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module LLVM.Compile
  ( compileLLVM, runPasses, standardCompilationPipeline
  , LLVMOptLevel (..)) where

#ifdef DEX_DEBUG
import qualified LLVM.Analysis as L
#endif
import qualified LLVM.AST as L
import qualified LLVM.AST.Global as GL
import qualified LLVM.Module as Mod
import qualified LLVM.Internal.Module as Mod
#if MIN_VERSION_llvm_hs(15,0,0)
import qualified LLVM.Passes as P
#else
import qualified LLVM.PassManager as P
import qualified LLVM.Transforms as P
#endif
import qualified LLVM.Target as T
import qualified LLVM.Shims
import LLVM.Context
import qualified Data.ByteString       as BS
import qualified Data.ByteString.Char8 as B
import System.IO.Unsafe

import Control.Monad

import Logging
import PPrint ()
import Paths_dex  (getDataFileName)
import Types.Misc
-- The only reason this module depends on Types.Source is that we pass in the logger,
-- in order to optionally print out the IRs. LLVM mutates its IRs in-place, so
-- we can't just expose a functional API for each stage without taking a
-- performance hit. But maybe the performance hit isn't so bad?
import Types.Source


data LLVMOptLevel = OptALittle       -- -O1
                  | OptAggressively  -- -O3, incl. auto vectorization
  deriving Show

compileLLVM :: PassLogger -> LLVMOptLevel -> L.Module -> String -> IO BS.ByteString
compileLLVM logger opt ast exportName = do
  tm <- LLVM.Shims.newDefaultHostTargetMachine
  withContext \c -> do
    Mod.withModuleFromAST c ast \m -> do
      standardCompilationPipeline opt
        logger
        [exportName] tm m
      Mod.moduleObject tm m

-- === LLVM passes ===

runDefaultPasses :: LLVMOptLevel -> T.TargetMachine -> Mod.Module -> IO ()
runDefaultPasses opt t m = do
#if MIN_VERSION_llvm_hs(15,0,0)
  -- TODO: Modify llvm-hs to request vectorization
  P.runPasses (P.PassSetSpec [P.CuratedPassSet lvl] (Just t)) m
  where lvl = case opt of OptALittle -> 1; OptAggressively -> 3
#else
  P.withPassManager defaultPasses \pm -> void $ P.runPassManager pm m
  case extraPasses of
    [] -> return ()
    _  -> runPasses extraPasses (Just t) m
  where
    defaultPasses = case opt of
      OptALittle ->
        P.defaultCuratedPassSetSpec {P.optLevel = Just 1, P.targetMachine = Just t}
      OptAggressively ->
        P.defaultCuratedPassSetSpec
          { P.optLevel = Just 3
          , P.loopVectorize = Just True
          , P.superwordLevelParallelismVectorize = Just True
          , P.targetMachine = Just t }
    extraPasses = []
#endif

#if MIN_VERSION_llvm_hs(15,0,0)
runPasses :: [P.ModulePass] -> Maybe T.TargetMachine -> Mod.Module -> IO ()
runPasses passes mt m = P.runPasses (P.PassSetSpec passes mt) m
#else
runPasses :: [P.Pass] -> Maybe T.TargetMachine -> Mod.Module -> IO ()
runPasses passes mt m = do
  dl <- case mt of
         Just t  -> Just <$> T.getTargetMachineDataLayout t
         Nothing -> return Nothing
  let passSpec = P.PassSetSpec passes dl Nothing mt
  P.withPassManager passSpec \pm -> void $ P.runPassManager pm m
#endif

standardCompilationPipeline :: LLVMOptLevel -> PassLogger -> [String] -> T.TargetMachine -> Mod.Module -> IO ()
standardCompilationPipeline opt logger exports tm m = do
  -- TODO: this means we build a copy of dexrt for every function. Is that
  -- really necessary?
  linkDexrt m
  internalize exports m
  {-# SCC showLLVM   #-} logPass JitPass $ showModule m
#ifdef DEX_DEBUG
  {-# SCC verifyLLVM #-} L.verify m
#endif
  {-# SCC runPasses  #-} runDefaultPasses opt tm m
  {-# SCC showOptimizedLLVM #-} logPass LLVMOpt $ showModule m
  {-# SCC showAssembly      #-} logPass AsmPass $ showAsm tm m
  where
    logPass :: PassName -> IO String -> IO ()
    logPass passName cont = logFiltered logger passName $ cont >>= \s -> return [PassInfo passName s]
{-# SCC standardCompilationPipeline #-}

internalize :: [String] -> Mod.Module -> IO ()
internalize names m = runPasses [P.InternalizeFunctions names, P.GlobalDeadCodeElimination] Nothing m

-- === dex runtime ===

{-# NOINLINE dexrtAST #-}
dexrtAST :: L.Module
dexrtAST = unsafePerformIO $ do
  dexrtBC <- B.readFile =<< getDataFileName "src/lib/dexrt.bc"
  withContext \ctx -> do
    Mod.withModuleFromBitcode ctx (("dexrt.c" :: String), dexrtBC) \m ->
      stripFunctionAnnotations <$> Mod.moduleAST m
  where
    -- We strip the function annotations for dexrt functions, because clang
    -- usually assumes that it's compiling for some generic CPU instead of the
    -- target that we select here. That creates a lot of confusion, making
    -- optimizations much less effective.
    stripFunctionAnnotations ast =
      ast { L.moduleDefinitions = stripDef <$> L.moduleDefinitions ast }
    stripDef def@(L.GlobalDefinition f@L.Function{..}) = case basicBlocks of
      [] -> def
      _  -> L.GlobalDefinition $ f { GL.functionAttributes = [] }
    stripDef def = def

linkDexrt :: Mod.Module -> IO ()
linkDexrt m = do
  ctx <- Mod.moduleContext m
  dataLayout <- Mod.getDataLayout =<< Mod.readModule m
  targetTriple <- Mod.getTargetTriple =<< Mod.readModule m
  let dexrtTargetAST = dexrtAST { L.moduleDataLayout = dataLayout
                                , L.moduleTargetTriple = targetTriple }
  Mod.withModuleFromAST ctx dexrtTargetAST \dexrtm -> do
    Mod.linkModules m dexrtm
    runPasses [P.AlwaysInline True] Nothing m

-- === printing ===

showModule :: Mod.Module -> IO String
showModule m = B.unpack <$> Mod.moduleLLVMAssembly m

showAsm :: T.TargetMachine -> Mod.Module -> IO String
showAsm t m' = do
  ctx <- Mod.moduleContext m'
  -- Uncomment this to dump assembly to a file that can be linked to a C benchmark suite:
  -- withModuleClone ctx m' \m -> Mod.writeObjectToFile t (Mod.File "asm.o") m
  withModuleClone ctx m' \m -> B.unpack <$> Mod.moduleTargetAssembly t m

withModuleClone :: Context -> Mod.Module -> (Mod.Module -> IO a) -> IO a
withModuleClone ctx m f = do
  -- It would be better to go through bitcode, but apparently that doesn't work...
  bc <- Mod.moduleLLVMAssembly m
  Mod.withModuleFromLLVMAssembly ctx (("<string>" :: String), bc) f
