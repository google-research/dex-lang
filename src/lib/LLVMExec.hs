-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE OverloadedStrings #-}

module LLVMExec (LLVMFunction (..), LLVMKernel (..),
                 callLLVM, compilePTX, linking_hack) where

import qualified LLVM.Analysis as L
import qualified LLVM.AST as L
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

import Foreign.Marshal.Alloc
import Foreign.Ptr
import Foreign.Storable
import Control.Monad
import Data.ByteString.Char8 (unpack)
import Data.IORef
import qualified Data.Map as M

import Logging
import Syntax

-- This forces the linker to link libdex.so. TODO: something better
foreign import ccall "threefry2x32"  linking_hack :: Int -> Int -> Int

foreign import ccall "dynamic"
  callFunPtr :: FunPtr (Ptr () -> IO ()) -> Ptr () -> IO ()

type NumOutputs   = Int
data LLVMFunction = LLVMFunction NumOutputs L.Module
data LLVMKernel   = LLVMKernel L.Module

compilePTX :: Logger [Output] -> LLVMKernel -> IO PTXKernel
compilePTX logger (LLVMKernel ast) = do
  T.initializeAllTargets
  withContext $ \c ->
    Mod.withModuleFromAST c ast $ \m -> do
      (tripleTarget, _) <- T.lookupTarget Nothing ptxTargetTriple
      T.withTargetOptions $ \topt ->
        T.withTargetMachine
          tripleTarget
          ptxTargetTriple
          "sm_60"
          (M.singleton (T.CPUFeature "ptx64") True)
          topt
          R.Default
          CM.Default
          CGO.Aggressive $ \tm -> do
            compileModule logger tm m
            PTXKernel . unpack <$> Mod.moduleTargetAssembly tm m
  where
    ptxTargetTriple = "nvptx64-nvidia-cuda"

callLLVM :: Logger [Output] -> LLVMFunction -> [Ptr ()] -> IO [Ptr ()]
callLLVM logger (LLVMFunction numOutputs ast) inArrays = do
  argsPtr <- mallocBytes $ (numOutputs + numInputs) * ptrSize
  forM_ (zip [numOutputs..] inArrays) $ \(i, p) -> do
    poke (argsPtr `plusPtr` (i * ptrSize)) p
  evalLLVM logger ast argsPtr
  outputPtrs <- forM [0..numOutputs - 1] $ \i -> peek (argsPtr `plusPtr` (i * ptrSize))
  free argsPtr
  return outputPtrs
  where
    numInputs = length inArrays
    ptrSize = 8 -- TODO: Get this from LLVM instead of hardcoding!

evalLLVM :: Logger [Output] -> L.Module -> Ptr () -> IO ()
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
        compileModule logger tm m
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
                    callFunPtr (castPtrToFunPtr (wordPtrToPtr f)) argPtr
                    t2 <- getCurrentTime
                    logThis logger [EvalTime $ realToFrac $ t2 `diffUTCTime` t1]
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
  showModule    m >>= logPass logger JitPass
  L.verify      m
  runPasses  tm m
  showModule    m >>= logPass logger LLVMOpt
  showAsm    tm m >>= logPass logger AsmPass

logPass :: Logger [Output] -> PassName -> String -> IO ()
logPass logger passName s = logThis logger [PassInfo passName s]

showModule :: Mod.Module -> IO String
showModule m = unpack <$> Mod.moduleLLVMAssembly m

runPasses :: T.TargetMachine -> Mod.Module -> IO ()
runPasses t m = do
  P.withPassManager passes $ \pm -> void $ P.runPassManager pm m
  -- We are highly dependent on LLVM when it comes to some optimizations such as
  -- turning a sequence of scalar stores into a vector store, so we execute some
  -- extra passes to make sure they get simplified correctly.
  dl <- T.getTargetMachineDataLayout t
  let slp = P.PassSetSpec extraPasses (Just dl) Nothing (Just t)
  P.withPassManager slp $ \pm -> void $ P.runPassManager pm m
  P.withPassManager passes $ \pm -> void $ P.runPassManager pm m
  where
    extraPasses = [ P.SuperwordLevelParallelismVectorize ]

showAsm :: T.TargetMachine -> Mod.Module -> IO String
showAsm t m = do
  -- Uncomment this to dump assembly to a file that can be linked to a C benchmark suite:
  -- Mod.writeObjectToFile t (Mod.File "asm.o") m
  liftM unpack $ Mod.moduleTargetAssembly t m

passes :: P.PassSetSpec
passes = P.defaultCuratedPassSetSpec {P.optLevel = Just 3}

instance Show LLVMKernel where
  show (LLVMKernel ast) = unsafePerformIO $ withContext $ \c -> Mod.withModuleFromAST c ast showModule
