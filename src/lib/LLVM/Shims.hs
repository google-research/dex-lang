-- Copyright 2021 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module LLVM.Shims (
  newTargetMachine, newHostTargetMachine, disposeTargetMachine,
  newDefaultHostTargetMachine
  ) where

import qualified Data.Map as M
import qualified Data.ByteString.Char8 as BS
import qualified Data.ByteString.Short as SBS

import qualified LLVM.Relocation as R
import qualified LLVM.CodeModel as CM
import qualified LLVM.CodeGenOpt as CGO
import qualified LLVM.Internal.Target as Target
import qualified LLVM.Internal.FFI.Target as Target.FFI
import LLVM.Prelude (ShortByteString, ByteString)
import LLVM.Internal.Coding (encodeM)

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

-- XXX: We need to use the large code model for macOS, because the libC functions
--      are loaded very far away from the JITed code. This does not prevent the
--      runtime linker from attempting to shove their offsets into 32-bit values
--      which cannot represent them, leading to segfaults that are very fun to debug.
--      It would be good to find a better solution, because larger code models might
--      hurt performance if we were to end up doing a lot of function calls.
-- TODO: Consider changing the linking layer, as suggested in:
--       http://llvm.1065342.n5.nabble.com/llvm-dev-ORC-JIT-Weekly-5-td135203.html
newDefaultHostTargetMachine :: IO Target.TargetMachine
newDefaultHostTargetMachine = LLVM.Shims.newHostTargetMachine R.PIC cm CGO.Aggressive
  where
#if darwin_HOST_OS
    cm = CM.Small
#else
    cm = CM.Large
#endif

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
