-- Copyright 2025 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module LLVMFFI (LLVMContext, initializeLLVM, compileLLVM, getFunctionPtr,
                callEntryFun) where

import Control.Monad
import qualified Data.ByteString as BS
import Foreign.Ptr
import qualified Types.LLVM as L
import Data.Int
import PPrint

foreign import ccall "initialize_jit" initialize_jit :: IO Int
foreign import ccall "add_to_jit" add_to_jit :: Ptr () -> Int64 -> IO Int
foreign import ccall "get_function_ptr" get_function_ptr :: Ptr () -> Int64 -> IO (Ptr ())
foreign import ccall "call_function_ptr" call_function_ptr :: Ptr () -> IO (Ptr ())

type LLVMContext = ()
type FunctionPtr = Ptr ()
type DataPtr = Ptr ()
type DataListPtr = Ptr ()

initializeLLVM :: IO LLVMContext
initializeLLVM = initialize_jit >> return ()

compileLLVM :: LLVMContext -> L.Module  -> IO ()
compileLLVM _ f = do
  BS.useAsCStringLen (pprint f) \(ptr, n) ->
    void $ add_to_jit (castPtr ptr) (fromIntegral n)

getFunctionPtr :: LLVMContext -> L.Name -> IO FunctionPtr
getFunctionPtr _ fname = do
  BS.useAsCStringLen fname.val \(ptr, n) ->
    castPtr <$> get_function_ptr(castPtr ptr) (fromIntegral n)

callEntryFun :: FunctionPtr -> [DataPtr] -> IO ()
callEntryFun fPtr [] = do
  call_function_ptr fPtr
  return ()
