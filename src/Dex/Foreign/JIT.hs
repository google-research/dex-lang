-- Copyright 2020 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# OPTIONS_GHC -Wno-orphans #-}

module Dex.Foreign.JIT (
  NativeFunction, ClosedExportedSignature,
  ExportNativeFunction (..), ExportNativeFunctionAddr,
  dexGetFunctionSignature, dexFreeFunctionSignature,
  dexCompile, dexUnload
  ) where

import Control.Concurrent.MVar
import Control.Monad.State.Strict

import Foreign.Ptr
import Foreign.C.String
import Foreign.C.Types
import Foreign.Storable
import Foreign.Marshal.Alloc

import Data.Functor
import qualified Data.Map.Strict as M

import Export
import Name
import Types.Core

import Dex.Foreign.Util
import Dex.Foreign.Context

dexCompile :: Ptr Context -> CInt -> Ptr AtomEx -> IO ExportNativeFunctionAddr
dexCompile ctxPtr ccInt funcAtomPtr = catchErrors do
  AtomEx funcAtom <- fromStablePtr funcAtomPtr
  let cc = intAsCC ccInt
  runTopperMFromContext ctxPtr do
    -- TODO: Check if atom is compatible with context! Use module name?
    func <- prepareFunctionForExport cc (unsafeCoerceE funcAtom)
    liftIO $ emitExport ctxPtr func

dexGetFunctionSignature :: Ptr Context -> ExportNativeFunctionAddr -> IO (Ptr (ExportedSignature 'VoidS))
dexGetFunctionSignature ctxPtr funcPtr = do
  Context _ _ ptrTabMVar <- fromStablePtr ctxPtr
  addrTable <- readMVar ptrTabMVar
  case M.lookup funcPtr addrTable of
    Nothing -> setError "Invalid function address" $> nullPtr
    Just ExportNativeFunction{..} -> putOnHeap nativeSignature

dexFreeFunctionSignature :: Ptr (ExportedSignature 'VoidS) -> IO ()
dexFreeFunctionSignature sigPtr = do
  let strPtr = castPtr @(ExportedSignature 'VoidS) @CString sigPtr
  free =<< peekElemOff strPtr 0
  free =<< peekElemOff strPtr 1
  free =<< peekElemOff strPtr 2
  free sigPtr

dexUnload :: Ptr Context -> ExportNativeFunctionAddr -> IO ()
dexUnload ctxPtr funcPtr = do
  f <- popFromNativeFunctionTable ctxPtr funcPtr
  nativeFunTeardown $ nativeFunction f
