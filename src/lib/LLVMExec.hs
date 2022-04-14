-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE DuplicateRecordFields #-}

module LLVMExec (LLVMKernel (..), ptxDataLayout, ptxTargetTriple,
                 compileAndEval, compileAndBench, exportObjectFile,
                 exportObjectFileVal,
                 standardCompilationPipeline,
                 compileCUDAKernel,
                 storeLitVals, loadLitVals, allocaCells, loadLitVal) where

#ifdef DEX_DEBUG
import qualified LLVM.Analysis as L
#endif
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
import LLVM.Context
import Data.Int
import GHC.IO.FD
import GHC.IO.Handle.FD
import System.IO
import System.IO.Unsafe
import System.IO.Temp
import System.Directory (listDirectory)
import System.Process
import qualified System.Environment as E
import System.Exit

import Foreign.Marshal.Alloc
import Foreign.Ptr
import Foreign.C.Types (CInt (..))
import Foreign.Storable hiding (alignment)
import Control.Monad.IO.Class
import Control.Monad
import Control.Concurrent
import Control.Exception hiding (throw)
import Data.ByteString.Short (ShortByteString)
import Data.ByteString.Char8 (unpack, pack)
import qualified Data.ByteString.Char8 as B
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Control.Exception as E

import Paths_dex  (getDataFileName)
import Err
import Logging
import Syntax
import CUDA (synchronizeCUDA)
import LLVM.JIT
import Util (measureSeconds)
import PPrint ()

-- === One-shot evaluation ===

foreign import ccall "dynamic"
  callFunPtr :: DexExecutable -> Int32 -> Ptr () -> Ptr () -> IO DexExitCode

type DexExecutable = FunPtr (Int32 -> Ptr () -> Ptr () -> IO DexExitCode)
type DexExitCode = Int

compileAndEval :: FilteredLogger PassName [Output] -> [ObjectFile n] -> L.Module -> String
               -> [LitVal] -> [BaseType] -> IO [LitVal]
compileAndEval logger objFiles ast fname args resultTypes = do
  withPipeToLogger logger \fd ->
    allocaCells (length args) \argsPtr ->
      allocaCells (length resultTypes) \resultPtr -> do
        storeLitVals argsPtr args
        evalTime <- compileOneOff logger objFiles ast fname $
          checkedCallFunPtr fd argsPtr resultPtr
        logSkippingFilter logger [EvalTime evalTime Nothing]
        loadLitVals resultPtr resultTypes
{-# SCC compileAndEval #-}

compileAndBench :: Bool -> FilteredLogger PassName [Output] -> [ObjectFile n] -> L.Module -> String
                -> [LitVal] -> [BaseType] -> IO [LitVal]
compileAndBench shouldSyncCUDA logger objFiles ast fname args resultTypes = do
  withPipeToLogger logger \fd ->
    allocaCells (length args) \argsPtr ->
      allocaCells (length resultTypes) \resultPtr -> do
        storeLitVals argsPtr args
        compileOneOff logger objFiles ast fname \fPtr -> do
          ((avgTime, benchRuns, results), totalTime) <- measureSeconds $ do
            -- First warmup iteration, which we also use to get the results
            void $ checkedCallFunPtr fd argsPtr resultPtr fPtr
            results <- loadLitVals resultPtr resultTypes
            let run = do
                  let (CInt fd') = fdFD fd
                  exitCode <- callFunPtr fPtr fd' argsPtr resultPtr
                  unless (exitCode == 0) $ throw RuntimeErr ""
                  freeLitVals resultPtr resultTypes
            let sync = when shouldSyncCUDA $ synchronizeCUDA
            exampleDuration <- snd <$> measureSeconds (run >> sync)
            let timeBudget = 2 -- seconds
            let benchRuns = (ceiling $ timeBudget / exampleDuration) :: Int
            sync
            totalTime <- liftM snd $ measureSeconds $ do
              forM_ [1..benchRuns] $ const run
              sync
            let avgTime = totalTime / (fromIntegral benchRuns)
            return (avgTime, benchRuns, results)
          logSkippingFilter logger [EvalTime avgTime (Just (benchRuns, totalTime))]
          return results
{-# SCC compileAndBench #-}

withPipeToLogger :: FilteredLogger PassName [Output] -> (FD -> IO a) -> IO a
withPipeToLogger logger writeAction = do
  result <- snd <$> withPipe
    (\h -> readStream h \s -> logSkippingFilter logger [TextOut s])
    (\h -> handleToFd h >>= writeAction)
  case result of
    Left e -> E.throw e
    Right ans -> return ans

checkedCallFunPtr :: FD -> Ptr () -> Ptr () -> DexExecutable -> IO Double
checkedCallFunPtr fd argsPtr resultPtr fPtr = do
  let (CInt fd') = fdFD fd
  (exitCode, duration) <- measureSeconds $ do
    exitCode <- callFunPtr fPtr fd' argsPtr resultPtr
    return exitCode
  unless (exitCode == 0) $ throw RuntimeErr ""
  return duration
{-# SCC checkedCallFunPtr #-}

compileOneOff :: FilteredLogger PassName [Output] -> [ObjectFile n] -> L.Module -> String -> (DexExecutable -> IO a) -> IO a
compileOneOff logger objFiles ast name f = do
  withHostTargetMachine \tm ->
    withJIT tm \jit -> do
      let pipeline = standardCompilationPipeline logger [name] tm
      let objFileContents = [s | ObjectFile s _ _ <- objFiles]
      withNativeModule jit objFileContents ast pipeline \compiled ->
        f =<< getFunctionPtr compiled name

standardCompilationPipeline :: FilteredLogger PassName [Output] -> [String] -> T.TargetMachine -> Mod.Module -> IO ()
standardCompilationPipeline logger exports tm m = do
  linkDexrt m
  internalize exports m
  {-# SCC showLLVM   #-} logPass JitPass $ showModule m
#ifdef DEX_DEBUG
  {-# SCC verifyLLVM #-} L.verify m
#endif
  {-# SCC runPasses  #-} runDefaultPasses tm m
  {-# SCC showOptimizedLLVM #-} logPass LLVMOpt $ showModule m
  {-# SCC showAssembly      #-} logPass AsmPass $ showAsm tm m
  where
    logPass :: PassName -> IO String -> IO ()
    logPass passName cont = logFiltered logger passName $ cont >>= \s -> return [PassInfo passName s]
{-# SCC standardCompilationPipeline #-}


-- === object file export ===

exportObjectFileVal :: [ObjectFileName n] -> L.Module -> String -> IO (ObjectFile n)
exportObjectFileVal deps m fname = do
  contents <- exportObjectFile [(m, [fname])] Mod.moduleObject
  return $ ObjectFile contents [fname] deps
{-# SCC exportObjectFileVal #-}

-- Each module comes with a list of exported functions
exportObjectFile :: [(L.Module, [String])] -> (T.TargetMachine -> Mod.Module -> IO a) -> IO a
exportObjectFile modules exportFn = do
  withContext \c -> do
    withHostTargetMachine \tm ->
      withBrackets (fmap (toLLVM c) modules) \mods -> do
        Mod.withModuleFromAST c L.defaultModule \exportMod -> do
          void $ foldM linkModules exportMod mods
          execLogger Nothing \logger ->
            standardCompilationPipeline
              (FilteredLogger (const False) logger)
              allExports tm exportMod
          exportFn tm exportMod
  where
    allExports = foldMap snd modules

    toLLVM :: Context -> (L.Module, [String]) -> (Mod.Module -> IO a) -> IO a
    toLLVM c (ast, exports) cont = do
      Mod.withModuleFromAST c ast \m -> internalize exports m >> cont m

    linkModules a b = a <$ Mod.linkModules a b

    withBrackets :: [(a -> IO b) -> IO b] -> ([a] -> IO b) -> IO b
    withBrackets brackets f = go brackets []
      where
        go (h:t) args = h \arg -> go t (arg:args)
        go []    args = f args
{-# SCC exportObjectFile #-}


-- === LLVM passes ===

runDefaultPasses :: T.TargetMachine -> Mod.Module -> IO ()
runDefaultPasses t m = do
  P.withPassManager defaultPasses \pm -> void $ P.runPassManager pm m
  case extraPasses of
    [] -> return ()
    _  -> runPasses extraPasses (Just t) m
  where
    defaultPasses = P.defaultCuratedPassSetSpec {P.optLevel = Just 1}
    extraPasses = []

runPasses :: [P.Pass] -> Maybe T.TargetMachine -> Mod.Module -> IO ()
runPasses passes mt m = do
  dl <- case mt of
         Just t  -> Just <$> T.getTargetMachineDataLayout t
         Nothing -> return Nothing
  let passSpec = P.PassSetSpec passes dl Nothing mt
  P.withPassManager passSpec \pm -> void $ P.runPassManager pm m

internalize :: [String] -> Mod.Module -> IO ()
internalize names m = runPasses [P.InternalizeFunctions names, P.GlobalDeadCodeElimination] Nothing m


-- === supported target machines ===

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


-- === printing ===

showModule :: Mod.Module -> IO String
showModule m = unpack <$> Mod.moduleLLVMAssembly m

showAsm :: T.TargetMachine -> Mod.Module -> IO String
showAsm t m' = do
  ctx <- Mod.moduleContext m'
  -- Uncomment this to dump assembly to a file that can be linked to a C benchmark suite:
  -- withModuleClone ctx m' \m -> Mod.writeObjectToFile t (Mod.File "asm.o") m
  withModuleClone ctx m' \m -> unpack <$> Mod.moduleTargetAssembly t m

withModuleClone :: Context -> Mod.Module -> (Mod.Module -> IO a) -> IO a
withModuleClone ctx m f = do
  -- It would be better to go through bitcode, but apparently that doesn't work...
  bc <- Mod.moduleLLVMAssembly m
  Mod.withModuleFromLLVMAssembly ctx (("<string>" :: String), bc) f


-- === serializing scalars ===

loadLitVals :: MonadIO m => Ptr () -> [BaseType] -> m [LitVal]
loadLitVals p types = zipWithM loadLitVal (ptrArray p) types

freeLitVals :: MonadIO m => Ptr () -> [BaseType] -> m ()
freeLitVals p types = zipWithM_ freeLitVal (ptrArray p) types

storeLitVals :: MonadIO m => Ptr () -> [LitVal] -> m ()
storeLitVals p xs = zipWithM_ storeLitVal (ptrArray p) xs

loadLitVal :: MonadIO m => Ptr () -> BaseType -> m LitVal
loadLitVal ptr (Scalar ty) = liftIO case ty of
  Int64Type   -> Int64Lit   <$> peek (castPtr ptr)
  Int32Type   -> Int32Lit   <$> peek (castPtr ptr)
  Word8Type   -> Word8Lit   <$> peek (castPtr ptr)
  Word32Type  -> Word32Lit  <$> peek (castPtr ptr)
  Word64Type  -> Word64Lit  <$> peek (castPtr ptr)
  Float64Type -> Float64Lit <$> peek (castPtr ptr)
  Float32Type -> Float32Lit <$> peek (castPtr ptr)
loadLitVal ptrPtr (PtrType t) = do
  ptr <- liftIO $ peek $ castPtr ptrPtr
  return $ PtrLit $ PtrLitVal t ptr
loadLitVal _ _ = error "not implemented"

storeLitVal :: MonadIO m => Ptr () -> LitVal -> m ()
storeLitVal ptr val = liftIO case val of
  Int64Lit   x -> poke (castPtr ptr) x
  Int32Lit   x -> poke (castPtr ptr) x
  Word8Lit   x -> poke (castPtr ptr) x
  Float64Lit x -> poke (castPtr ptr) x
  Float32Lit x -> poke (castPtr ptr) x
  PtrLit (PtrLitVal _ x) -> poke (castPtr ptr) x
  _ -> error "not implemented"

foreign import ccall "free_dex"
  free_cpu :: Ptr () -> IO ()
#ifdef DEX_CUDA
foreign import ccall "dex_cuMemFree"
  free_gpu :: Ptr () -> IO ()
#else
free_gpu :: Ptr () -> IO ()
free_gpu = error "Compiled without GPU support!"
#endif

freeLitVal :: MonadIO m => Ptr () -> BaseType -> m ()
freeLitVal litValPtr ty = case ty of
  Scalar  _ -> return ()
  PtrType (Heap CPU, Scalar _) -> liftIO $ free_cpu =<< loadPtr
  PtrType (Heap GPU, Scalar _) -> liftIO $ free_gpu =<< loadPtr
  -- TODO: Handle pointers to pointers
  _ -> error "not implemented"
  where loadPtr = peek (castPtr litValPtr)

cellSize :: Int
cellSize = 8

ptrArray :: Ptr () -> [Ptr ()]
ptrArray p = map (\i -> p `plusPtr` (i * cellSize)) [0..]

allocaCells :: MonadIO m => Int -> (Ptr () -> IO a) -> m a
allocaCells n cont = liftIO $ allocaBytes (n * cellSize) cont


-- === dex runtime ===

{-# NOINLINE dexrtAST #-}
dexrtAST :: L.Module
dexrtAST = unsafePerformIO $ do
  dexrtBC <- B.readFile =<< getDataFileName "src/lib/dexrt.bc"
  withContext \ctx -> do
    Mod.withModuleFromBitcode ctx (("dexrt.c" :: String), dexrtBC) \m ->
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

linkDexrt :: Mod.Module -> IO ()
linkDexrt m = do
  ctx <- Mod.moduleContext m
  dataLayout <- Mod.getDataLayout =<< Mod.readModule m
  targetTriple <- Mod.getTargetTriple =<< Mod.readModule m
  let dexrtTargetAST = dexrtAST { L.moduleDataLayout = dataLayout
                                , L.moduleTargetTriple = targetTriple }
  Mod.withModuleFromAST ctx dexrtTargetAST \dexrtm -> do
    Mod.linkModules m dexrtm
    runPasses [P.AlwaysInline True] Nothing m


-- === CUDA support ===

data LLVMKernel = LLVMKernel L.Module

cudaPath :: IO String
cudaPath = maybe "/usr/local/cuda" id <$> E.lookupEnv "CUDA_PATH"

compileCUDAKernel :: FilteredLogger PassName [Output] -> LLVMKernel -> String -> IO CUDAKernel
compileCUDAKernel logger (LLVMKernel ast) arch = do
  T.initializeAllTargets
  withContext \ctx ->
    Mod.withModuleFromAST ctx ast \m -> do
      withGPUTargetMachine (pack arch) \tm -> do
        linkLibdevice m
        standardCompilationPipeline logger ["kernel"] tm m
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

-- ==== unix pipe utilities ===

type IOExcept a = Either SomeException a

withPipe :: (Handle -> IO a) -> (Handle -> IO b) -> IO (IOExcept a, IOExcept b)
withPipe readAction writeAction = do
  (readHandle, writeHandle) <- createPipe
  waitForReader <- forkWithResult $ readAction  readHandle
  waitForWriter <- forkWithResult $ writeAction writeHandle
  y <- waitForWriter `finally` hClose writeHandle
  x <- waitForReader `finally` hClose readHandle
  return (x, y)

forkWithResult :: IO a -> IO (IO (IOExcept a))
forkWithResult action = do
  resultMVar <- newEmptyMVar
  void $ forkIO $ catch (do result <- action
                            putMVar resultMVar $ Right result)
                        (\e -> putMVar resultMVar $ Left (e::SomeException))
  return $ takeMVar resultMVar

readStream :: Handle -> (String -> IO ()) -> IO ()
readStream h action = go
  where
    go :: IO ()
    go = do
      eof <- hIsEOF h
      unless eof $ hGetLine h >>= action >> go
