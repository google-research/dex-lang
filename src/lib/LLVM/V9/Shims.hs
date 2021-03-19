-- Copyright 2020 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module LLVM.V9.Shims (
  SymbolResolver (..), newSymbolResolver, disposeSymbolResolver,
  ) where

import Foreign.C.String
import Foreign.Ptr

import qualified LLVM.Internal.OrcJIT as OrcJIT
import qualified LLVM.Internal.FFI.OrcJIT as OrcJIT.FFI

import LLVM.Internal.Coding (encodeM, decodeM)

-- llvm-hs doesn't expose any way to manage the symbol resolvers in a non-bracketed way

type FFIResolver = CString -> Ptr OrcJIT.FFI.JITSymbol -> IO ()
foreign import ccall "wrapper" wrapFFIResolver :: FFIResolver -> IO (FunPtr FFIResolver)
data SymbolResolver = SymbolResolver (FunPtr FFIResolver) (Ptr OrcJIT.FFI.SymbolResolver)

-- | Create a `FFI.SymbolResolver` that can be used with the JIT.
newSymbolResolver :: OrcJIT.ExecutionSession -> OrcJIT.SymbolResolver -> IO SymbolResolver
newSymbolResolver (OrcJIT.ExecutionSession session) (OrcJIT.SymbolResolver resolverFn) = do
  ffiResolverPtr <- wrapFFIResolver \sym res -> do
    f <- encodeM =<< resolverFn =<< decodeM sym
    f res
  lambdaResolver <- OrcJIT.FFI.createLambdaResolver session ffiResolverPtr
  return $ SymbolResolver ffiResolverPtr lambdaResolver

disposeSymbolResolver :: SymbolResolver -> IO ()
disposeSymbolResolver (SymbolResolver wrapper resolver) = do
  OrcJIT.FFI.disposeSymbolResolver resolver
  freeHaskellFunPtr wrapper
