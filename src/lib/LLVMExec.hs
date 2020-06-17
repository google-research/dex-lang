-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE OverloadedStrings #-}

module LLVMExec (LLVMFunction (..), showLLVM, evalLLVM, callLLVM,
                 linking_hack) where

import qualified LLVM.Analysis as L
import qualified LLVM.AST as L
import qualified LLVM.Module as Mod
import qualified LLVM.PassManager as P
import qualified LLVM.ExecutionEngine as EE
import qualified LLVM.Target as T
import LLVM.Context
import Data.Time.Clock (getCurrentTime, diffUTCTime)

import Foreign.Marshal.Alloc
import Foreign.Ptr
import Foreign.Storable
import Control.Exception
import Control.Monad
import Data.ByteString.Char8 (unpack)
import Data.Maybe (fromMaybe)

import Logging
import Syntax

-- This forces the linker to link libdex.so. TODO: something better
foreign import ccall "threefry2x32"  linking_hack :: Int -> Int -> Int

foreign import ccall "dynamic"
  callFunPtr :: FunPtr (Ptr () -> IO ()) -> Ptr () -> IO ()

-- First element holds the number of outputs
data LLVMFunction = LLVMFunction Int L.Module

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
  T.initializeAllTargets
  withContext $ \c ->
    Mod.withModuleFromAST c ast $ \m -> do
      showModule m >>= logPass logger JitPass
      L.verify m
      runPasses m
      showModule m >>= logPass logger LLVMOpt
      showAsm    m >>= logPass logger AsmPass
      jit c $ \ee -> do
        EE.withModuleInEngine ee m $ \eee -> do
          f <- liftM (fromMaybe (error "failed to fetch function")) $
                 EE.getFunction eee (L.Name "entryFun")
          t1 <- getCurrentTime
          callFunPtr (castFunPtr f :: FunPtr (Ptr () -> IO ())) argPtr
          t2 <- getCurrentTime
          logPass logger LLVMEval $ show (t2 `diffUTCTime` t1)

jit :: Context -> (EE.MCJIT -> IO a) -> IO a
jit c = EE.withMCJIT c (Just 3) Nothing Nothing Nothing

logPass :: Logger [Output] -> PassName -> String -> IO ()
logPass logger passName s = logThis logger [PassInfo passName s]

runPasses :: Mod.Module -> IO ()
runPasses m = P.withPassManager passes $ \pm -> void $ P.runPassManager pm m

showLLVM :: L.Module -> IO String
showLLVM m = do
  T.initializeAllTargets
  withContext $ \c ->
    Mod.withModuleFromAST c m $ \m' -> do
      verifyErr <- verifyAndRecover m'
      prePass <- showModule m'
      runPasses m'
      postPass <- showModule m'
      return $ verifyErr ++ "Input LLVM:\n\n" ++ prePass
            ++ "\nAfter passes:\n\n" ++ postPass

showModule :: Mod.Module -> IO String
showModule m = liftM unpack $ Mod.moduleLLVMAssembly m

verifyAndRecover :: Mod.Module -> IO String
verifyAndRecover m =
  (L.verify m >> return  "") `catch`
    (\e -> return ("\nVerification error:\n" ++ show (e::SomeException) ++ "\n"))

showAsm :: Mod.Module -> IO String
showAsm m = T.withHostTargetMachineDefault $ \t ->
              liftM unpack $ Mod.moduleTargetAssembly t m

passes :: P.PassSetSpec
passes = P.defaultCuratedPassSetSpec {P.optLevel = Just 3}
