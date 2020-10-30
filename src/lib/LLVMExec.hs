-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE RecordWildCards #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module LLVMExec (LLVMKernel (..), ptxDataLayout, ptxTargetTriple,
                 callLLVM, benchLLVM, exportLLVM,
                 compileCUDAKernel, loadLitVal) where

import qualified LLVM.Analysis as L
import qualified LLVM.AST as L
import qualified LLVM.AST.Global as L
import qualified LLVM.AST.AddrSpace as L
import qualified LLVM.AST.Constant as C
import qualified LLVM.AST.DataLayout as L
import qualified LLVM.AST.FunctionAttribute as FA
import qualified LLVM.Relocation as R
import qualified LLVM.CodeModel as CM
import qualified LLVM.CodeGenOpt as CGO
import qualified LLVM.Module as Mod
import qualified LLVM.Internal.Module as Mod
import qualified LLVM.PassManager as P
import qualified LLVM.Transforms as P
import qualified LLVM.Target as T
import qualified LLVM.Linking as Linking
import qualified LLVM.OrcJIT as JIT
import LLVM.Internal.OrcJIT.CompileLayer as JIT
import LLVM.Context
import Data.Time.Clock (getCurrentTime, diffUTCTime)
import System.IO
import System.IO.Unsafe
import System.IO.Temp
import System.Directory (listDirectory)
import System.Process
import System.Environment
import System.Exit

import Foreign.Marshal.Alloc
import Foreign.Ptr
import Foreign.Storable hiding (alignment)
import Control.Monad
import Control.Exception hiding (throw)
import Data.ByteString.Short (ShortByteString)
import qualified Data.ByteString.Short as SBS
import Data.ByteString.Char8 (unpack, pack)
import Data.List (sortBy)
import Data.String
import Data.IORef
import qualified Data.ByteString.Char8 as B
import qualified Data.Map as M
import qualified Data.Set as S

import Logging
import Syntax
import Resources
import CUDA (synchronizeCUDA)

foreign import ccall "dynamic"
  callFunPtr :: DexExecutable -> Ptr () -> Ptr () -> IO DexExitCode

foreign import ccall "dynamic"
  callDtor :: FunPtr (IO ()) -> IO ()

type DexExecutable = FunPtr (Ptr () -> Ptr () -> IO DexExitCode)
type DexExitCode = Int

data LLVMKernel = LLVMKernel L.Module

compileCUDAKernel :: Logger [Output] -> LLVMKernel -> IO CUDAKernel
compileCUDAKernel logger (LLVMKernel ast) = do
  T.initializeAllTargets
  withContext $ \ctx ->
    Mod.withModuleFromAST ctx ast $ \m -> do
      withGPUTargetMachine (pack arch) $ \tm -> do
        linkLibdevice ctx           m
        linkDexrt     ctx           m
        internalize   ["kernel"]    m
        compileModule ctx logger tm m
        ptx <- Mod.moduleTargetAssembly tm m
        usePTXAS <- maybe False (=="1") <$> lookupEnv "DEX_USE_PTXAS"
        if usePTXAS
          then do
            withSystemTempFile "kernel.ptx" $ \ptxPath ptxH -> do
              B.hPut ptxH ptx
              hClose ptxH
              withSystemTempFile "kernel.sass" $ \sassPath sassH -> do
                let cmd = proc ptxasPath [ptxPath, "-o", sassPath, "-arch=" ++ arch, "-O3"]
                withCreateProcess cmd $ \_ _ _ ptxas -> do
                  code <- waitForProcess ptxas
                  case code of
                    ExitSuccess   -> return ()
                    ExitFailure _ -> error "ptxas invocation failed"
                -- TODO: B.readFile might be faster, but withSystemTempFile seems to lock the file...
                CUDAKernel <$> B.hGetContents sassH
          else return $ CUDAKernel ptx
  where
    ptxasPath = "/usr/local/cuda/bin/ptxas"
    arch = "sm_60"

checkedCallFunPtr :: Bool -> Ptr () -> Ptr () -> DexExecutable -> IO Double
checkedCallFunPtr sync argsPtr resultPtr fPtr = do
  t1 <- getCurrentTime
  exitCode <- callFunPtr fPtr argsPtr resultPtr
  when sync $ synchronizeCUDA
  t2 <- getCurrentTime
  unless (exitCode == 0) $ throwIO $ Err RuntimeErr Nothing ""
  return $ t2 `secondsSince` t1
  where
    secondsSince end start = realToFrac $ end `diffUTCTime` start

callLLVM :: Logger [Output] -> L.Module -> String -> [LitVal] -> [BaseType] -> IO [LitVal]
callLLVM logger ast fname args resultTypes = do
  allocaBytes (length args * cellSize) $ \argsPtr ->
    allocaBytes (length resultTypes * cellSize) $ \resultPtr -> do
      storeLitVals argsPtr args
      evalTime <- compileFunc logger ast fname $ checkedCallFunPtr False argsPtr resultPtr
      logThis logger [EvalTime evalTime Nothing]
      loadLitVals resultPtr resultTypes

benchLLVM :: Logger [Output] -> L.Module -> String -> [LitVal] -> [BaseType] -> IO [LitVal]
benchLLVM logger ast fname args resultTypes = do
  allocaBytes (length args * cellSize) $ \argsPtr ->
    allocaBytes (length resultTypes * cellSize) $ \resultPtr -> do
      storeLitVals argsPtr args
      compileFunc logger ast fname $ \fPtr -> do
        -- First warmup iteration, which we also use to get the results
        void $ checkedCallFunPtr True argsPtr resultPtr fPtr
        results <- loadLitVals resultPtr resultTypes
        let run = do
              time <- checkedCallFunPtr True argsPtr resultPtr fPtr
              _benchResults <- loadLitVals resultPtr resultTypes
              -- TODO: Free results!
              return time
        exampleDuration <- run
        let timeBudget = 2 -- seconds
        let benchRuns = (ceiling $ timeBudget / exampleDuration) :: Int
        times <- forM [1..benchRuns] $ const run
        let avgTime = sum times / (fromIntegral benchRuns)
        logThis logger [EvalTime avgTime (Just benchRuns)]
        return results

exportLLVM :: FilePath -> [(L.Module, [String])] -> IO ()
exportLLVM objFile modules = do
  withContext $ \c -> do
    void $ Linking.loadLibraryPermanently Nothing
    withHostTargetMachine $ \tm ->
      withBrackets (fmap (toLLVM c tm) modules) $ \mods -> do
        Mod.withModuleFromAST c L.defaultModule $ \exportMod -> do
          void $ foldM linkModules exportMod mods
          linkDexrt c exportMod
          internalize allExports exportMod
          Mod.writeObjectToFile tm (Mod.File objFile) exportMod
  where
    allExports = foldMap snd modules

    toLLVM :: Context -> T.TargetMachine -> (L.Module, [String]) -> (Mod.Module -> IO a) -> IO a
    toLLVM c tm (ast, exports) cont = do
      Mod.withModuleFromAST c ast $ \m -> do
        internalize exports m
        execLogger Nothing $ \logger -> compileModule c logger tm m
        cont m

    linkModules a b = a <$ Mod.linkModules a b

    withBrackets :: [(a -> IO b) -> IO b] -> ([a] -> IO b) -> IO b
    withBrackets brackets f = go brackets []
      where
        go (h:t) args = h $ \arg -> go t (arg:args)
        go []    args = f args

compileFunc :: Logger [Output] -> L.Module -> String -> (DexExecutable -> IO a) -> IO a
compileFunc logger ast name f = do
  resolvers <- newIORef M.empty
  withContext $ \c -> do
    void $ Linking.loadLibraryPermanently Nothing
    Mod.withModuleFromAST c ast $ \m -> do
      withHostTargetMachine $ \tm -> do
        linkDexrt     c            m
        let exports = name : dtorNames
        internalize   exports      m
        compileModule c logger tm  m
        JIT.withExecutionSession $ \exe ->
          JIT.withObjectLinkingLayer exe (\k -> (M.! k) <$> readIORef resolvers) $ \linkLayer ->
            JIT.withIRCompileLayer linkLayer tm $ \compileLayer -> do
              JIT.withModuleKey exe $ \moduleKey ->
                JIT.withSymbolResolver exe (makeResolver compileLayer) $ \resolver -> do
                  modifyIORef resolvers (M.insert moduleKey resolver)
                  JIT.withModule compileLayer moduleKey m $ do
                    entryFunSymbol <- JIT.mangleSymbol compileLayer (fromString name)
                    Right (JIT.JITSymbol funAddr _) <- JIT.findSymbol compileLayer entryFunSymbol False
                    res <- f $ castPtrToFunPtr $ wordPtrToPtr funAddr
                    forM_ dtorNames $ \dtorName -> do
                      dtorSymbol <- JIT.mangleSymbol compileLayer (fromString dtorName)
                      Right (JIT.JITSymbol dtorAddr _) <- JIT.findSymbol compileLayer dtorSymbol False
                      callDtor $ castPtrToFunPtr $ wordPtrToPtr dtorAddr
                    return res
  where
    makeResolver :: JIT.IRCompileLayer JIT.ObjectLinkingLayer -> JIT.SymbolResolver
    makeResolver cl = JIT.SymbolResolver $ \sym -> do
      rsym <- JIT.findSymbol cl sym False
      -- We look up functions like malloc in the current process
      -- TODO: Use JITDylibs to avoid inlining addresses as constants:
      -- https://releases.llvm.org/9.0.0/docs/ORCv2.html#how-to-add-process-and-library-symbols-to-the-jitdylibs
      case rsym of
        Right _ -> return rsym
        Left  _ -> do
          ptr <- Linking.getSymbolAddressInProcess sym
          if ptr == 0
            then error $ "Missing symbol: " ++ show sym
            else return $ Right $ externSym ptr
    externSym ptr =
      JIT.JITSymbol { JIT.jitSymbolAddress = ptr
                    , JIT.jitSymbolFlags = JIT.defaultJITSymbolFlags { JIT.jitSymbolExported = True, JIT.jitSymbolAbsolute = True }
                    }
    -- Unfortunately the JIT layers we use here don't handle the destructors properly,
    -- so we have to find and call them ourselves.
    dtorNames = do
      let dtorStructs = flip foldMap (L.moduleDefinitions ast) $ \case
            L.GlobalDefinition
              L.GlobalVariable{name="llvm.global_dtors",
                               initializer=Just (C.Array _ elems),
                               ..} -> elems
            _ -> []
      -- Sort in the order of decreasing priority!
      fmap snd $ sortBy (flip compare) $ flip fmap dtorStructs $
        \(C.Struct _ _ [C.Int _ n, C.GlobalReference _ (L.Name dname), _]) ->
          (n, unpack $ SBS.fromShort dname)

compileModule :: Context -> Logger [Output] -> T.TargetMachine -> Mod.Module -> IO ()
compileModule ctx logger tm m = do
  showModule          m >>= logPass logger JitPass
  L.verify            m
  runDefaultPasses tm m
  showModule          m >>= logPass logger LLVMOpt
  showAsm      ctx tm m >>= logPass logger AsmPass

withModuleClone :: Context -> Mod.Module -> (Mod.Module -> IO a) -> IO a
withModuleClone ctx m f = do
  -- It would be better to go through bitcode, but apparently that doesn't work...
  bc <- Mod.moduleLLVMAssembly m
  Mod.withModuleFromLLVMAssembly ctx (("<string>" :: String), bc) f

logPass :: Logger [Output] -> PassName -> String -> IO ()
logPass logger passName s = logThis logger [PassInfo passName s]

showModule :: Mod.Module -> IO String
showModule m = unpack <$> Mod.moduleLLVMAssembly m

runDefaultPasses :: T.TargetMachine -> Mod.Module -> IO ()
runDefaultPasses t m = do
  P.withPassManager defaultPasses $ \pm -> void $ P.runPassManager pm m
  -- We are highly dependent on LLVM when it comes to some optimizations such as
  -- turning a sequence of scalar stores into a vector store, so we execute some
  -- extra passes to make sure they get simplified correctly.
  runPasses extraPasses (Just t) m
  P.withPassManager defaultPasses $ \pm -> void $ P.runPassManager pm m
  where
    defaultPasses = P.defaultCuratedPassSetSpec {P.optLevel = Just 3}
    extraPasses = [ P.SuperwordLevelParallelismVectorize
                  , P.FunctionInlining 0 ]

runPasses :: [P.Pass] -> Maybe T.TargetMachine -> Mod.Module -> IO ()
runPasses passes mt m = do
  dl <- case mt of
         Just t  -> Just <$> T.getTargetMachineDataLayout t
         Nothing -> return Nothing
  let passSpec = P.PassSetSpec passes dl Nothing mt
  P.withPassManager passSpec $ \pm -> void $ P.runPassManager pm m

showAsm :: Context -> T.TargetMachine -> Mod.Module -> IO String
showAsm ctx t m' = do
  -- Uncomment this to dump assembly to a file that can be linked to a C benchmark suite:
  -- withModuleClone ctx m' $ \m -> Mod.writeObjectToFile t (Mod.File "asm.o") m
  withModuleClone ctx m' $ \m -> unpack <$> Mod.moduleTargetAssembly t m

internalize :: [String] -> Mod.Module -> IO ()
internalize names m = runPasses [P.InternalizeFunctions names, P.GlobalDeadCodeElimination] Nothing m

instance Show LLVMKernel where
  show (LLVMKernel ast) = unsafePerformIO $ withContext $ \c -> Mod.withModuleFromAST c ast showModule

-- XXX: We need to use the large code model for macOS, because the libC functions
--      are loaded very far away from the JITed code. This does not prevent the
--      runtime linker from attempting to shove their offsets into 32-bit values
--      which cannot represent them, leading to segfaults that are very fun to debug.
--      It would be good to find a better solution, because larger code models might
--      hurt performance if we were to end up doing a lot of function calls.
-- TODO: Consider changing the linking layer, as suggested in:
--       http://llvm.1065342.n5.nabble.com/llvm-dev-ORC-JIT-Weekly-5-td135203.html
withHostTargetMachine :: (T.TargetMachine -> IO a) -> IO a
withHostTargetMachine f =
  T.withHostTargetMachine R.PIC CM.Large CGO.Aggressive f

withGPUTargetMachine :: B.ByteString -> (T.TargetMachine -> IO a) -> IO a
withGPUTargetMachine computeCapability next = do
  (tripleTarget, _) <- T.lookupTarget Nothing ptxTargetTriple
  T.withTargetOptions $ \topt ->
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

-- === serializing scalars ===

loadLitVals :: Ptr () -> [BaseType] -> IO [LitVal]
loadLitVals p types = zipWithM loadLitVal (ptrArray p) types

storeLitVals :: Ptr () -> [LitVal] -> IO ()
storeLitVals p xs = zipWithM_ storeLitVal (ptrArray p) xs

loadLitVal :: Ptr () -> BaseType -> IO LitVal
loadLitVal ptr (Scalar ty) = case ty of
  Int64Type   -> Int64Lit   <$> peek (castPtr ptr)
  Int32Type   -> Int32Lit   <$> peek (castPtr ptr)
  Int8Type    -> Int8Lit    <$> peek (castPtr ptr)
  Float64Type -> Float64Lit <$> peek (castPtr ptr)
  Float32Type -> Float32Lit <$> peek (castPtr ptr)
loadLitVal ptr (PtrType t) = PtrLit t <$> peek (castPtr ptr)
loadLitVal _ _ = error "not implemented"

storeLitVal :: Ptr () -> LitVal -> IO ()
storeLitVal ptr val = case val of
  Int64Lit   x -> poke (castPtr ptr) x
  Int32Lit   x -> poke (castPtr ptr) x
  Int8Lit    x -> poke (castPtr ptr) x
  Float64Lit x -> poke (castPtr ptr) x
  Float32Lit x -> poke (castPtr ptr) x
  PtrLit _   x -> poke (castPtr ptr) x
  _ -> error "not implemented"

cellSize :: Int
cellSize = 8

ptrArray :: Ptr () -> [Ptr ()]
ptrArray p = map (\i -> p `plusPtr` (i * cellSize)) [0..]

-- === dex runtime ===

dexrtAST :: L.Module
dexrtAST = unsafePerformIO $ do
  withContext $ \ctx -> do
    Mod.withModuleFromBitcode ctx (("dexrt.c" :: String), dexrtBC) $ \m ->
      stripFunctionAnnotations <$> Mod.moduleAST m
  where
    -- We strip the function annotations for dexrt functions, because clang
    -- usually assumes that it's compiling for some generic CPU instead of the
    -- target that we select here. That creates a lot of confusion, making
    -- optimizations much less effective.
    stripFunctionAnnotations ast =
      ast { L.moduleDefinitions = stripDef <$> L.moduleDefinitions ast }
    stripDef def@(L.GlobalDefinition f@L.Function{..}) = case basicBlocks of
      [] -> def
      _  -> L.GlobalDefinition $ f { L.functionAttributes = [] }
    stripDef def = def

linkDexrt :: Context -> Mod.Module -> IO ()
linkDexrt ctx m = do
  dataLayout <- Mod.getDataLayout =<< Mod.readModule m
  targetTriple <- Mod.getTargetTriple =<< Mod.readModule m
  let dexrtTargetAST = dexrtAST { L.moduleDataLayout = dataLayout
                                , L.moduleTargetTriple = targetTriple }
  Mod.withModuleFromAST ctx dexrtTargetAST $ \dexrtm -> do
    Mod.linkModules m dexrtm
    runPasses [P.AlwaysInline True] Nothing m


-- === libdevice support ===

{-# NOINLINE libdevice #-}
libdevice :: L.Module
libdevice = unsafePerformIO $ do
  withContext $ \ctx -> do
    let libdeviceDirectory = "/usr/local/cuda/nvvm/libdevice"
    [libdeviceFileName] <- listDirectory libdeviceDirectory
    let libdevicePath = libdeviceDirectory ++ "/" ++ libdeviceFileName
    libdeviceBC <- B.readFile libdevicePath
    m <- Mod.withModuleFromBitcode ctx (libdevicePath, libdeviceBC) Mod.moduleAST
    -- Override the data layout and target triple to avoid warnings when linking
    return $ m { L.moduleDataLayout = Just ptxDataLayout
               , L.moduleTargetTriple = Just ptxTargetTriple }

linkLibdevice :: Context -> Mod.Module -> IO ()
linkLibdevice ctx m =
  Mod.withModuleFromAST ctx zeroNVVMReflect $ \reflectm ->
    Mod.withModuleFromAST ctx libdevice $ \ldm -> do
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
                       ([ L.Parameter (L.PointerType (L.IntegerType 8) (L.AddrSpace 0)) "name" [] ], False)
                   , L.functionAttributes = [ Right FA.AlwaysInline ]
                   , L.basicBlocks = [
                       L.BasicBlock "entry" [] $ L.Do $ L.Ret (Just $ L.ConstantOperand $ C.Int 32 0) []
                     ]
                   }
               ]
           }

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
