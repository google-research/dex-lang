-- Copyright 2020 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE RecordWildCards #-}

module Dex.Foreign.JIT (
  JIT, NativeFunction,
  dexCreateJIT, dexDestroyJIT,
  dexCompile, dexUnload
  ) where

import Control.Monad.State.Strict

import Foreign.Ptr

import Data.IORef
import qualified Data.Map.Strict as M

import LLVM.Target (TargetMachine)
import qualified LLVM.Relocation as R
import qualified LLVM.CodeModel as CM
import qualified LLVM.CodeGenOpt as CGO
import qualified LLVM.JIT
import qualified LLVM.Shims

import Logging
import LLVMExec
import JIT
import Syntax  hiding (sizeOf)
import TopLevel

import Dex.Foreign.Util
import Dex.Foreign.Context

data JIT = ForeignJIT { jit :: LLVM.JIT.JIT
                      , jitTargetMachine :: TargetMachine
                      , funcToModuleRef :: IORef (M.Map (Ptr NativeFunction) LLVM.JIT.NativeModule)
                      }


dexCreateJIT :: IO (Ptr JIT)
dexCreateJIT = do
  jitTargetMachine <- LLVM.Shims.newHostTargetMachine R.PIC CM.Large CGO.Aggressive
  jit <- LLVM.JIT.createJIT jitTargetMachine
  funcToModuleRef <- newIORef mempty
  toStablePtr ForeignJIT{..}

dexDestroyJIT :: Ptr JIT -> IO ()
dexDestroyJIT jitPtr = do
  ForeignJIT{..} <- fromStablePtr jitPtr
  funcToModule <- readIORef funcToModuleRef
  forM_ (M.toList funcToModule) $ \(_, m) -> LLVM.JIT.unloadNativeModule m
  LLVM.JIT.destroyJIT jit
  LLVM.Shims.disposeTargetMachine jitTargetMachine

data NativeFunction

dexCompile :: Ptr JIT -> Ptr Context -> Ptr Atom -> IO (Ptr NativeFunction)
dexCompile jitPtr ctxPtr funcAtomPtr = do
  ForeignJIT{..} <- fromStablePtr jitPtr
  Context _ env <- fromStablePtr ctxPtr
  funcAtom <- fromStablePtr funcAtomPtr
  let impMod = prepareFunctionForExport env "userFunc" funcAtom
  nativeModule <- execLogger Nothing $ \logger -> do
    llvmAST <- impToLLVM logger impMod
    LLVM.JIT.compileModule jit llvmAST
        (standardCompilationPipeline logger ["userFunc"] jitTargetMachine)
  funcPtr <- castFunPtrToPtr <$> LLVM.JIT.getFunctionPtr nativeModule "userFunc"
  modifyIORef funcToModuleRef $ M.insert funcPtr nativeModule
  return $ funcPtr

dexUnload :: Ptr JIT -> Ptr NativeFunction  -> IO ()
dexUnload jitPtr funcPtr = do
  ForeignJIT{..} <- fromStablePtr jitPtr
  funcToModule <- readIORef funcToModuleRef
  LLVM.JIT.unloadNativeModule $ funcToModule M.! funcPtr
  modifyIORef funcToModuleRef $ M.delete funcPtr
