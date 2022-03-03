-- Copyright 2020 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Dex.Foreign.JIT (
  JIT, NativeFunction, ClosedExportedSignature,
  dexCreateJIT, dexDestroyJIT,
  dexGetFunctionSignature, dexFreeFunctionSignature,
  dexCompile, dexUnload
  ) where

import Control.Monad.State.Strict

import Foreign.Ptr
import Foreign.C.String
import Foreign.Storable
import Foreign.Marshal.Alloc

import Data.IORef
import Data.Functor
import qualified Data.Map.Strict as M

import LLVM.Target (TargetMachine)
import qualified LLVM.Relocation as R
import qualified LLVM.CodeModel as CM
import qualified LLVM.CodeGenOpt as CGO
import qualified LLVM.JIT
import qualified LLVM.Shims

import Name
import Logging
import Builder
import LLVMExec
import TopLevel
import JIT
import Export
import Syntax  hiding (sizeOf)

import Dex.Foreign.Util
import Dex.Foreign.Context

type ClosedExportedSignature = ExportedSignature 'VoidS
data NativeFunction =
  NativeFunction { nativeModule    :: LLVM.JIT.NativeModule
                 , nativeSignature :: ExportedSignature 'VoidS }
type NativeFunctionAddr = Ptr NativeFunction

data JIT = ForeignJIT { jit :: LLVM.JIT.JIT
                      , jitTargetMachine :: TargetMachine
                      , addrTableRef :: IORef (M.Map NativeFunctionAddr NativeFunction)
                      }

instance Storable (ExportedSignature 'VoidS) where
  sizeOf _ = 3 * sizeOf (undefined :: Ptr ())
  alignment _ = alignment (undefined :: Ptr ())
  peek _ = error "peek not implemented for ExportedSignature"
  poke addr sig = do
    let strAddr = castPtr @(ExportedSignature 'VoidS) @CString addr
    let (arg, res, ccall) = exportedSignatureDesc sig
    pokeElemOff strAddr 0 =<< newCString arg
    pokeElemOff strAddr 1 =<< newCString res
    pokeElemOff strAddr 2 =<< newCString ccall

dexCreateJIT :: IO (Ptr JIT)
dexCreateJIT = do
  jitTargetMachine <- LLVM.Shims.newHostTargetMachine R.PIC CM.Large CGO.Aggressive
  jit <- LLVM.JIT.createJIT jitTargetMachine
  addrTableRef <- newIORef mempty
  toStablePtr ForeignJIT{..}

dexDestroyJIT :: Ptr JIT -> IO ()
dexDestroyJIT jitPtr = do
  ForeignJIT{..} <- fromStablePtr jitPtr
  addrTable <- readIORef addrTableRef
  forM_ (M.toList addrTable) $ \(_, m) -> LLVM.JIT.unloadNativeModule $ nativeModule m
  LLVM.JIT.destroyJIT jit
  LLVM.Shims.disposeTargetMachine jitTargetMachine

dexCompile :: Ptr JIT -> Ptr Context -> Ptr AtomEx -> IO NativeFunctionAddr
dexCompile jitPtr ctxPtr funcAtomPtr = catchErrors $ do
  ForeignJIT{..} <- fromStablePtr jitPtr
  Context evalConfig initEnv <- fromStablePtr ctxPtr
  AtomEx funcAtom <- fromStablePtr funcAtomPtr
  fst <$> runTopperM evalConfig initEnv do
    -- TODO: Check if atom is compatible with context! Use module name?
    (impFunc, nativeSignature) <- prepareFunctionForExport (unsafeCoerceE funcAtom)
    (_, llvmAST) <- impToLLVM "userFunc" impFunc
    logger <- getLogger
    objFileNames <- getAllRequiredObjectFiles
    objFiles <- forM objFileNames \objFileName -> do
      ObjectFileBinding (ObjectFile bytes _ _) <- lookupEnv objFileName
      return bytes
    liftIO do
      nativeModule <- LLVM.JIT.compileModule jit objFiles llvmAST
          (standardCompilationPipeline logger ["userFunc"] jitTargetMachine)
      funcPtr <- castFunPtrToPtr <$> LLVM.JIT.getFunctionPtr nativeModule "userFunc"
      modifyIORef addrTableRef $ M.insert funcPtr NativeFunction{..}
      return $ funcPtr

dexGetFunctionSignature :: Ptr JIT -> NativeFunctionAddr -> IO (Ptr (ExportedSignature 'VoidS))
dexGetFunctionSignature jitPtr funcPtr = do
  ForeignJIT{..} <- fromStablePtr jitPtr
  addrTable <- readIORef addrTableRef
  case M.lookup funcPtr addrTable of
    Nothing -> setError "Invalid function address" $> nullPtr
    Just NativeFunction{..} -> putOnHeap nativeSignature

dexFreeFunctionSignature :: Ptr (ExportedSignature 'VoidS) -> IO ()
dexFreeFunctionSignature sigPtr = do
  let strPtr = castPtr @(ExportedSignature 'VoidS) @CString sigPtr
  free =<< peekElemOff strPtr 0
  free =<< peekElemOff strPtr 1
  free =<< peekElemOff strPtr 2
  free sigPtr

dexUnload :: Ptr JIT -> NativeFunctionAddr -> IO ()
dexUnload jitPtr funcPtr = do
  ForeignJIT{..} <- fromStablePtr jitPtr
  addrTable <- readIORef addrTableRef
  LLVM.JIT.unloadNativeModule $ nativeModule $ addrTable M.! funcPtr
  modifyIORef addrTableRef $ M.delete funcPtr
