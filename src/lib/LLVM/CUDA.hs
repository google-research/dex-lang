-- Copyright 2022 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module LLVM.CUDA (
  LLVMKernel (..), compileCUDAKernel, ptxTargetTriple, ptxDataLayout) where

import qualified LLVM.AST as L
import qualified LLVM.AST.Global as L
import qualified LLVM.AST.Global as GL
import qualified LLVM.AST.AddrSpace as L
import qualified LLVM.AST.Constant as C
import qualified LLVM.AST.DataLayout as L
import qualified LLVM.AST.FunctionAttribute as FA
import qualified LLVM.Relocation as R
import qualified LLVM.CodeModel as CM
import qualified LLVM.CodeGenOpt as CGO
import qualified LLVM.Module as Mod
#if MIN_VERSION_llvm_hs(15,0,0)
import qualified LLVM.Passes as P
#else
import qualified LLVM.Transforms as P
#endif
import qualified LLVM.Target as T
import LLVM.Context
import System.IO
import System.IO.Unsafe
import System.IO.Temp
import System.Directory (listDirectory)
import System.Process
import qualified System.Environment as E
import System.Exit

import Data.ByteString.Short (ShortByteString)
import qualified Data.ByteString.Char8 as B
import qualified Data.Map as M
import qualified Data.Set as S

import LLVM.Compile
import Types.Imp
import Types.Source


data LLVMKernel = LLVMKernel L.Module

cudaPath :: IO String
cudaPath = maybe "/usr/local/cuda" id <$> E.lookupEnv "CUDA_PATH"

compileCUDAKernel :: PassLogger -> LLVMKernel -> String -> IO CUDAKernel
compileCUDAKernel logger (LLVMKernel ast) arch = undefined
  T.initializeAllTargets
  withContext \ctx ->
    Mod.withModuleFromAST ctx ast \m -> do
      withGPUTargetMachine (B.pack arch) \tm -> do
        linkLibdevice m
        standardCompilationPipeline OptAggressively logger ["kernel"] tm m
        ptx <- Mod.moduleTargetAssembly tm m
        usePTXAS <- maybe False (=="1") <$> E.lookupEnv "DEX_USE_PTXAS"
        if usePTXAS
          then do
            ptxasPath <- (++"/bin/ptxas") <$> cudaPath
            withSystemTempFile "kernel.ptx" \ptxPath ptxH -> do
              B.hPut ptxH ptx
              hClose ptxH
              withSystemTempFile "kernel.sass" \sassPath sassH -> do
                let cmd = proc ptxasPath [ptxPath, "-o", sassPath, "-arch=" ++ arch, "-O3"]
                withCreateProcess cmd \_ _ _ ptxas -> do
                  code <- waitForProcess ptxas
                  case code of
                    ExitSuccess   -> return ()
                    ExitFailure _ -> error "ptxas invocation failed"
                -- TODO: B.readFile might be faster, but withSystemTempFile seems to lock the file...
                CUDAKernel <$> B.hGetContents sassH
          else return $ CUDAKernel ptx
{-# SCC compileCUDAKernel #-}

{-# NOINLINE libdevice #-}
libdevice :: L.Module
libdevice = unsafePerformIO $ do
  withContext \ctx -> do
    libdeviceDirectory <- (flip (++) $ "/nvvm/libdevice") <$> cudaPath
    [libdeviceFileName] <- listDirectory libdeviceDirectory
    let libdevicePath = libdeviceDirectory ++ "/" ++ libdeviceFileName
    libdeviceBC <- B.readFile libdevicePath
    m <- Mod.withModuleFromBitcode ctx (libdevicePath, libdeviceBC) Mod.moduleAST
    -- Override the data layout and target triple to avoid warnings when linking
    return $ m { L.moduleDataLayout = Just ptxDataLayout
               , L.moduleTargetTriple = Just ptxTargetTriple }

linkLibdevice :: Mod.Module -> IO ()
linkLibdevice m = do
  ctx <- Mod.moduleContext m
  Mod.withModuleFromAST ctx zeroNVVMReflect \reflectm ->
    Mod.withModuleFromAST ctx libdevice \ldm -> do
      Mod.linkModules m ldm
      Mod.linkModules m reflectm
      runPasses [P.AlwaysInline True] Nothing m

-- llvm-hs does not expose the NVVM reflect pass, so we have to eliminate all calls to
-- __nvvm_reflect by ourselves. Since we aren't really interested in setting any reflection
-- flags to a value other than 0 for now, we eliminate the function by linking with this
-- trivial module and forcing the definition to get inlined.
zeroNVVMReflect :: L.Module
zeroNVVMReflect =
  L.Module { L.moduleName = "zero-nvvm-reflect"
           , L.moduleSourceFileName = ""
           , L.moduleDataLayout = Just ptxDataLayout
           , L.moduleTargetTriple = Just ptxTargetTriple
           , L.moduleDefinitions =
               [ L.GlobalDefinition $ L.functionDefaults
                   { L.name = "__nvvm_reflect"
                   , L.returnType = L.IntegerType 32
                   , L.parameters =
                       ([ L.Parameter i8p "name" [] ], False)
                   , GL.functionAttributes = [ Right FA.AlwaysInline ]
                   , L.basicBlocks = [
                       L.BasicBlock "entry" [] $ L.Do $ L.Ret (Just $ L.ConstantOperand $ C.Int 32 0) []
                     ]
                   }
               ]
           }
  where
#if MIN_VERSION_llvm_hs(15,0,0)
    i8p = L.PointerType (L.AddrSpace 0)
#else
    i8p = L.PointerType (L.IntegerType 8) (L.AddrSpace 0)
#endif

ptxTargetTriple :: ShortByteString
ptxTargetTriple = "nvptx64-nvidia-cuda"

ptxDataLayout :: L.DataLayout
ptxDataLayout = (L.defaultDataLayout L.LittleEndian)
    { L.endianness     = L.LittleEndian
    , L.pointerLayouts = M.fromList [(L.AddrSpace 0, (64, L.AlignmentInfo 64 64))]
    , L.typeLayouts    = M.fromList $
        [ ((L.IntegerAlign, 1), L.AlignmentInfo 8 8) ] ++
        [ ((L.IntegerAlign, w), L.AlignmentInfo w w) | w <- [8, 16, 32, 64] ] ++
        [ ((L.FloatAlign,   w), L.AlignmentInfo w w) | w <- [32, 64] ] ++
        [ ((L.VectorAlign,  w), L.AlignmentInfo w w) | w <- [16, 32, 64, 128] ]
    , L.nativeSizes    = Just $ S.fromList [16, 32, 64]
    }

-- === supported target machines ===

withGPUTargetMachine :: B.ByteString -> (T.TargetMachine -> IO a) -> IO a
withGPUTargetMachine computeCapability next = do
  (tripleTarget, _) <- T.lookupTarget Nothing ptxTargetTriple
  T.withTargetOptions \topt ->
    T.withTargetMachine
      tripleTarget
      ptxTargetTriple
      computeCapability
      (M.singleton (T.CPUFeature "ptx64") True)
      topt
      R.Default
      CM.Default
      CGO.Aggressive
      next
