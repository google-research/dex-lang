-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE OverloadedStrings #-}

module LLVMExec (showLLVM, evalJit) where

import qualified LLVM.Analysis as L
import qualified LLVM.AST as L
import qualified LLVM.Module as Mod
import qualified LLVM.PassManager as P
import qualified LLVM.ExecutionEngine as EE
import qualified LLVM.Target as T
import LLVM.Context
import Data.Time.Clock (getCurrentTime, diffUTCTime)

import Foreign.Ptr
import Control.Exception
import Control.Monad
import Data.ByteString.Char8 (unpack)
import Data.Maybe (fromMaybe)

import Syntax

foreign import ccall "dynamic"
  haskFun :: FunPtr (IO ()) -> IO ()

evalJit :: L.Module -> IO [Output]
evalJit ast = do
  T.initializeAllTargets
  withContext $ \c ->
    Mod.withModuleFromAST c ast $ \m -> do
      L.verify m
      preOpt <- showModule m
      runPasses m
      postOpt <- showModule m
      asm <- showAsm m
      jit c $ \ee -> do
        EE.withModuleInEngine ee m $ \eee -> do
          f <- liftM (fromMaybe (error "failed to fetch function")) $
                 EE.getFunction eee (L.Name "thefun")
          t1 <- getCurrentTime
          runJitted f
          t2 <- getCurrentTime
          return [ PassInfo JitPass "" preOpt
                 , PassInfo LLVMOpt "" postOpt
                 , PassInfo AsmPass "" asm
                 , PassInfo LLVMEval "" (show (t2 `diffUTCTime` t1))]

jit :: Context -> (EE.MCJIT -> IO a) -> IO a
jit c = EE.withMCJIT c (Just 3) Nothing Nothing Nothing

runJitted :: FunPtr a -> IO ()
runJitted fn = haskFun (castFunPtr fn :: FunPtr (IO ()))

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
