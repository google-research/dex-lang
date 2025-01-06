-- Copyright 2025 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module LLVMFFI (LLVMContext, initializeLLVM, compileLLVM, getFunctionPtr,
                callEntryFun) where

import Data.Int
import Util (BString)

foreign import ccall "doit_cpp"  doit_cpp    :: Int64  -> IO Int64

type FunctionPtr = ()
type LLVMContext = ()
type DataPtr = ()
type DataListPtr = ()

initializeLLVM :: IO LLVMContext
initializeLLVM = return undefined

compileLLVM :: LLVMContext -> BString  -> IO ()
compileLLVM _ _ = return undefined

getFunctionPtr :: LLVMContext -> BString -> IO FunctionPtr
getFunctionPtr _ _ = return undefined

callEntryFun :: FunctionPtr -> [DataPtr] -> IO DataPtr
callEntryFun _ _ = return undefined
