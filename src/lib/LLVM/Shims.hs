-- Copyright 2020 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module LLVM.Shims (
  SymbolResolver (..), newSymbolResolver, disposeSymbolResolver,
  newTargetMachine, newHostTargetMachine, disposeTargetMachine,
  ) where

import qualified Data.Map as M
import Foreign.C.String
import Foreign.Ptr
import qualified Data.ByteString.Char8 as BS
import qualified Data.ByteString.Short as SBS

import qualified LLVM.Internal.OrcJIT as OrcJIT
import qualified LLVM.Internal.FFI.OrcJIT as OrcJIT.FFI

import qualified LLVM.Relocation as R
import qualified LLVM.CodeModel as CM
import qualified LLVM.CodeGenOpt as CGO
import qualified LLVM.Internal.Target as Target
import qualified LLVM.Internal.FFI.Target as Target.FFI
import LLVM.Prelude (ShortByteString, ByteString)
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

-- llvm-hs doesn't expose any way to manage target machines in a non-bracketed way

newTargetMachine :: Target.Target
                 -> ShortByteString
                 -> ByteString
                 -> M.Map Target.CPUFeature Bool
                 -> Target.TargetOptions
                 -> R.Model
                 -> CM.Model
                 -> CGO.Level
                 -> IO Target.TargetMachine
newTargetMachine (Target.Target targetFFI) triple cpu features
                 (Target.TargetOptions targetOptFFI)
                 relocModel codeModel cgoLevel = do
  SBS.useAsCString triple \tripleFFI -> do
    BS.useAsCString cpu \cpuFFI -> do
      let featuresStr = BS.intercalate "," $ fmap encodeFeature $ M.toList features
      BS.useAsCString featuresStr \featuresFFI -> do
        relocModelFFI <- encodeM relocModel
        codeModelFFI <- encodeM codeModel
        cgoLevelFFI <- encodeM cgoLevel
        Target.TargetMachine <$> Target.FFI.createTargetMachine
                targetFFI tripleFFI cpuFFI featuresFFI
                targetOptFFI relocModelFFI codeModelFFI cgoLevelFFI
  where encodeFeature (Target.CPUFeature f, on) = (if on then "+" else "-") <> f

newHostTargetMachine :: R.Model -> CM.Model -> CGO.Level -> IO Target.TargetMachine
newHostTargetMachine relocModel codeModel cgoLevel = do
  Target.initializeAllTargets
  triple <- Target.getProcessTargetTriple
  (target, _) <- Target.lookupTarget Nothing triple
  cpu <- Target.getHostCPUName
  features <- Target.getHostCPUFeatures
  Target.withTargetOptions \targetOptions ->
    newTargetMachine target triple cpu features targetOptions relocModel codeModel cgoLevel

disposeTargetMachine :: Target.TargetMachine -> IO ()
disposeTargetMachine (Target.TargetMachine tmFFI) = Target.FFI.disposeTargetMachine tmFFI
