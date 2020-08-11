-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE RecordWildCards #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module LLVMExec (LLVMFunction (..), LLVMKernel (..),
                 callLLVM, compilePTX) where

import qualified LLVM.Analysis as L
import qualified LLVM.AST as L
import qualified LLVM.AST.Global as L
import qualified LLVM.AST.AddrSpace as L
import qualified LLVM.AST.Constant as C
import qualified LLVM.AST.FunctionAttribute as FA
import qualified LLVM.Relocation as R
import qualified LLVM.CodeModel as CM
import qualified LLVM.CodeGenOpt as CGO
import qualified LLVM.Module as Mod
import qualified LLVM.PassManager as P
import qualified LLVM.Transforms as P
import qualified LLVM.Target as T
import qualified LLVM.Linking as Linking
import qualified LLVM.OrcJIT as JIT
import LLVM.Internal.OrcJIT.CompileLayer as JIT
import LLVM.Context
import Data.Time.Clock (getCurrentTime, diffUTCTime)
import System.IO.Unsafe
import System.Directory (listDirectory)

import Foreign.Marshal.Alloc
import Foreign.Ptr
import Foreign.Storable hiding (alignment)
import Control.Monad
import Control.Exception hiding (throw)
import Data.ByteString.Char8 (unpack)
import Data.IORef
import Data.FileEmbed
import qualified Data.ByteString as BS
import qualified Data.Map as M

import Logging
import Syntax
import JIT (LLVMFunction (..), LLVMKernel (..), ptxTargetTriple, ptxDataLayout)

type ExitCode = Int

foreign import ccall "dynamic"
  callFunPtr :: FunPtr (Ptr () -> IO ExitCode) -> Ptr () -> IO ExitCode

compilePTX :: Logger [Output] -> LLVMKernel -> IO PTXKernel
compilePTX logger (LLVMKernel ast) = do
  T.initializeAllTargets
  withContext $ \ctx ->
    Mod.withModuleFromAST ctx ast $ \m -> do
      withGPUTargetMachine "sm_60" $ \tm -> do
        linkLibdevice ctx        m
        linkDexrt     ctx        m
        internalize   ["kernel"] m
        compileModule logger tm  m
        PTXKernel . unpack <$> Mod.moduleTargetAssembly tm m

callLLVM :: Logger [Output] -> LLVMFunction -> [Ptr ()] -> IO [Ptr ()]
callLLVM logger (LLVMFunction numOutputs ast) inArrays = do
  argsPtr <- mallocBytes $ (numOutputs + numInputs) * ptrSize
  forM_ (zip [numOutputs..] inArrays) $ \(i, p) -> do
    poke (argsPtr `plusPtr` (i * ptrSize)) p
  exitCode <- evalLLVM logger ast argsPtr
  case exitCode of
    0 -> do
      outputPtrs <- forM [0..numOutputs - 1] $ \i -> peek (argsPtr `plusPtr` (i * ptrSize))
      free argsPtr
      return outputPtrs
    _ -> throwIO $ Err RuntimeErr Nothing ""
  where
    numInputs = length inArrays
    ptrSize = 8 -- TODO: Get this from LLVM instead of hardcoding!

evalLLVM :: Logger [Output] -> L.Module -> Ptr () -> IO ExitCode
evalLLVM logger ast argPtr = do
  resolvers <- newIORef M.empty
  withContext $ \c -> do
    void $ Linking.loadLibraryPermanently Nothing
    Mod.withModuleFromAST c ast $ \m ->
      -- XXX: We need to use the large code model for macOS, because the libC functions
      --      are loaded very far away from the JITed code. This does not prevent the
      --      runtime linker from attempting to shove their offsets into 32-bit values
      --      which cannot represent them, leading to segfaults that are very fun to debug.
      --      It would be good to find a better solution, because larger code models might
      --      hurt performance if we were to end up doing a lot of function calls.
      -- TODO: Consider changing the linking layer, as suggested in:
      --       http://llvm.1065342.n5.nabble.com/llvm-dev-ORC-JIT-Weekly-5-td135203.html
      T.withHostTargetMachine R.PIC CM.Large CGO.Aggressive $ \tm -> do
        linkDexrt     c            m
        internalize   ["entryFun"] m
        compileModule logger tm    m
        JIT.withExecutionSession $ \exe ->
          JIT.withObjectLinkingLayer exe (\k -> (M.! k) <$> readIORef resolvers) $ \linkLayer ->
            JIT.withIRCompileLayer linkLayer tm $ \compileLayer -> do
              JIT.withModuleKey exe $ \moduleKey ->
                JIT.withSymbolResolver exe (makeResolver compileLayer) $ \resolver -> do
                  modifyIORef resolvers (M.insert moduleKey resolver)
                  JIT.withModule compileLayer moduleKey m $ do
                    entryFunSymbol <- JIT.mangleSymbol compileLayer "entryFun"
                    Right (JIT.JITSymbol f _) <- JIT.findSymbol compileLayer entryFunSymbol False
                    t1 <- getCurrentTime
                    exitCode <- callFunPtr (castPtrToFunPtr (wordPtrToPtr f)) argPtr
                    t2 <- getCurrentTime
                    logThis logger [EvalTime $ realToFrac $ t2 `diffUTCTime` t1]
                    return exitCode
  where
    makeResolver :: JIT.IRCompileLayer JIT.ObjectLinkingLayer -> JIT.SymbolResolver
    makeResolver cl = JIT.SymbolResolver $ \sym -> do
      rsym <- JIT.findSymbol cl sym False
      -- We look up functions like malloc in the current process
      -- TODO: Use JITDylibs to avoid inlining addresses as constants:
      -- https://releases.llvm.org/9.0.0/docs/ORCv2.html#how-to-add-process-and-library-symbols-to-the-jitdylibs
      case rsym of
        Right _ -> return rsym
        Left  _ -> do
          ptr <- Linking.getSymbolAddressInProcess sym
          if ptr == 0
            then error $ "Missing symbol: " ++ show sym
            else return $ Right $ externSym ptr
    externSym ptr =
      JIT.JITSymbol { JIT.jitSymbolAddress = ptr
                    , JIT.jitSymbolFlags = JIT.defaultJITSymbolFlags { JIT.jitSymbolExported = True, JIT.jitSymbolAbsolute = True }
                    }

compileModule :: Logger [Output] -> T.TargetMachine -> Mod.Module -> IO ()
compileModule logger tm m = do
  showModule          m >>= logPass logger JitPass
  L.verify            m
  runDefaultPasses tm m
  showModule          m >>= logPass logger LLVMOpt
  showAsm          tm m >>= logPass logger AsmPass

logPass :: Logger [Output] -> PassName -> String -> IO ()
logPass logger passName s = logThis logger [PassInfo passName s]

showModule :: Mod.Module -> IO String
showModule m = unpack <$> Mod.moduleLLVMAssembly m

runDefaultPasses :: T.TargetMachine -> Mod.Module -> IO ()
runDefaultPasses t m = do
  P.withPassManager defaultPasses $ \pm -> void $ P.runPassManager pm m
  -- We are highly dependent on LLVM when it comes to some optimizations such as
  -- turning a sequence of scalar stores into a vector store, so we execute some
  -- extra passes to make sure they get simplified correctly.
  runPasses extraPasses (Just t) m
  P.withPassManager defaultPasses $ \pm -> void $ P.runPassManager pm m
  where
    defaultPasses = P.defaultCuratedPassSetSpec {P.optLevel = Just 3}
    extraPasses = [ P.SuperwordLevelParallelismVectorize
                  , P.FunctionInlining 0 ]


runPasses :: [P.Pass] -> Maybe T.TargetMachine -> Mod.Module -> IO ()
runPasses passes mt m = do
  dl <- case mt of
         Just t  -> Just <$> T.getTargetMachineDataLayout t
         Nothing -> return Nothing
  let passSpec = P.PassSetSpec passes dl Nothing mt
  P.withPassManager passSpec $ \pm -> void $ P.runPassManager pm m

showAsm :: T.TargetMachine -> Mod.Module -> IO String
showAsm t m = do
  -- Uncomment this to dump assembly to a file that can be linked to a C benchmark suite:
  -- Mod.writeObjectToFile t (Mod.File "asm.o") m
  liftM unpack $ Mod.moduleTargetAssembly t m

internalize :: [String] -> Mod.Module -> IO ()
internalize names m = runPasses [P.InternalizeFunctions names, P.GlobalDeadCodeElimination] Nothing m

instance Show LLVMKernel where
  show (LLVMKernel ast) = unsafePerformIO $ withContext $ \c -> Mod.withModuleFromAST c ast showModule

withGPUTargetMachine :: BS.ByteString -> (T.TargetMachine -> IO a) -> IO a
withGPUTargetMachine computeCapability next = do
  (tripleTarget, _) <- T.lookupTarget Nothing ptxTargetTriple
  T.withTargetOptions $ \topt ->
    T.withTargetMachine
      tripleTarget
      ptxTargetTriple
      computeCapability
      (M.singleton (T.CPUFeature "ptx64") True)
      topt
      R.Default
      CM.Default
      CGO.Aggressive
      next

-- === dex runtime ===

dexrtBC :: BS.ByteString
dexrtBC = $(embedFile "src/lib/dexrt.bc")

linkDexrt :: Context -> Mod.Module -> IO ()
linkDexrt ctx m = do
  Mod.withModuleFromBitcode ctx (("dexrt.c" :: String), dexrtBC) $ \dexrtm -> do
    Mod.linkModules m dexrtm
    runPasses [P.AlwaysInline True] Nothing m

-- === libdevice support ===

{-# NOINLINE libdevice #-}
libdevice :: L.Module
libdevice = unsafePerformIO $ do
  withContext $ \ctx -> do
    let libdeviceDirectory = "/usr/local/cuda/nvvm/libdevice"
    [libdeviceFileName] <- listDirectory libdeviceDirectory
    let libdevicePath = libdeviceDirectory ++ "/" ++ libdeviceFileName
    libdeviceBC <- BS.readFile libdevicePath
    m <- Mod.withModuleFromBitcode ctx (libdevicePath, libdeviceBC) Mod.moduleAST
    -- Override the data layout and target triple to avoid warnings when linking
    return $ m { L.moduleDataLayout = Just ptxDataLayout
               , L.moduleTargetTriple = Just ptxTargetTriple }

linkLibdevice :: Context -> Mod.Module -> IO ()
linkLibdevice ctx m =
  Mod.withModuleFromAST ctx zeroNVVMReflect $ \reflectm ->
    Mod.withModuleFromAST ctx libdevice $ \ldm -> do
      Mod.linkModules m ldm
      Mod.linkModules m reflectm
      runPasses [P.AlwaysInline True] Nothing m

-- llvm-hs does not expose the NVVM reflect pass, so we have to eliminate all calls to
-- __nvvm_reflect by ourselves. Since we aren't really interested in setting any reflection
-- flags to a value other than 0 for now, we eliminate the function by linking with this
-- trivial module and forcing the definition to get inlined.
zeroNVVMReflect :: L.Module
zeroNVVMReflect =
  L.Module { L.moduleName = "zero-nvvm-reflect"
           , L.moduleSourceFileName = ""
           , L.moduleDataLayout = Just ptxDataLayout
           , L.moduleTargetTriple = Just ptxTargetTriple
           , L.moduleDefinitions =
               [ L.GlobalDefinition $ L.functionDefaults
                   { L.name = "__nvvm_reflect"
                   , L.returnType = L.IntegerType 32
                   , L.parameters =
                       ([ L.Parameter (L.PointerType (L.IntegerType 8) (L.AddrSpace 0)) "name" [] ], False)
                   , L.functionAttributes = [ Right FA.AlwaysInline ]
                   , L.basicBlocks = [
                       L.BasicBlock "entry" [] $ L.Do $ L.Ret (Just $ L.ConstantOperand $ C.Int 32 0) []
                     ]
                   }
               ]
           }
