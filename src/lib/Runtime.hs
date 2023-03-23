-- Copyright 2022 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module Runtime
  ( loadLitVal
  , LLVMCallable (..), callEntryFun, callDtor, BenchRequirement (..)
  , createTLSKey, PThreadKey) where

import Data.Int
import GHC.IO.FD
import GHC.IO.Handle.FD
import System.IO
import System.Process

import Foreign.Marshal.Alloc
import Foreign.Ptr
import Foreign.C.Types (CInt (..))
import Foreign.Storable hiding (alignment)
import Control.Monad.IO.Class
import Control.Monad
import Control.Concurrent
import Control.Exception hiding (throw)
import qualified Control.Exception as E
import qualified System.Environment as E

import Err
import Logging
import Util (measureSeconds)
import PPrint ()
import CUDA (synchronizeCUDA)

import Types.Core hiding (DexDestructor)
import Types.Primitives
import Types.Misc

-- === One-shot evaluation ===

foreign import ccall "dynamic"
  callFunPtr :: DexExecutable -> Int32 -> Ptr () -> Ptr () -> IO DexExitCode

foreign import ccall "dynamic"
  callDtor :: DexDestructor -> IO ()

type DexDestructor = FunPtr (IO ())
type DexExecutable = FunPtr (Int32 -> Ptr () -> Ptr () -> IO DexExitCode)
type DexExitCode = Int


data BenchRequirement =
    NoBench
  | DoBench Bool -- True means "must sync CUDA"

data LLVMCallable = LLVMCallable
  { nativeFun :: NativeFunction
  , benchRequired :: BenchRequirement
  , logger :: PassLogger
  , resultTypes :: [BaseType]
  }

-- The NativeFunction needs to have been compiled with EntryFunCC.
callEntryFun :: LLVMCallable -> [LitVal] -> IO [LitVal]
callEntryFun LLVMCallable{nativeFun, benchRequired, logger, resultTypes} args = do
  withPipeToLogger logger \fd ->
    allocaCells (length args) \argsPtr ->
      allocaCells (length resultTypes) \resultPtr -> do
        storeLitVals argsPtr args
        let fPtr = castFunPtr $ nativeFunPtr nativeFun
        evalTime <- checkedCallFunPtr fd argsPtr resultPtr fPtr
        results <- loadLitVals resultPtr resultTypes
        case benchRequired of
          NoBench -> logSkippingFilter logger [EvalTime evalTime Nothing]
          DoBench shouldSyncCUDA -> do
            let sync = when shouldSyncCUDA $ synchronizeCUDA
            (avgTime, benchRuns, totalTime) <- runBench do
              let (CInt fd') = fdFD fd
              exitCode <- callFunPtr fPtr fd' argsPtr resultPtr
              unless (exitCode == 0) $ throw RuntimeErr ""
              freeLitVals resultPtr resultTypes
              sync
            logSkippingFilter logger [EvalTime avgTime (Just (benchRuns, totalTime + evalTime))]
        return results

checkedCallFunPtr :: FD -> Ptr () -> Ptr () -> DexExecutable -> IO Double
checkedCallFunPtr fd argsPtr resultPtr fPtr = do
  let (CInt fd') = fdFD fd
  (exitCode, duration) <- measureSeconds $ do
    exitCode <- callFunPtr fPtr fd' argsPtr resultPtr
    return exitCode
  unless (exitCode == 0) $ throw RuntimeErr ""
  return duration
{-# SCC checkedCallFunPtr #-}

withPipeToLogger :: PassLogger -> (FD -> IO a) -> IO a
withPipeToLogger logger writeAction = do
  result <- snd <$> withPipe
    (\h -> readStream h \s -> logSkippingFilter logger [TextOut s])
    (\h -> handleToFd h >>= writeAction)
  case result of
    Left e -> E.throw e
    Right ans -> return ans

runBench :: IO () -> IO (Double, Int, Double)
runBench run = do
  exampleDuration <- snd <$> measureSeconds run
  test_mode <- (Just "t" ==) <$> E.lookupEnv "DEX_TEST_MODE"
  let timeBudget = (2 - exampleDuration) `max` 0 -- seconds
  let benchRuns = if test_mode
        then 0
        else (ceiling $ timeBudget / exampleDuration) :: Int
  totalTime' <- liftM snd $ measureSeconds $ do
    forM_ [1..benchRuns] $ const run
  let totalTime = totalTime' + exampleDuration
      avgTime = totalTime / (fromIntegral $ benchRuns + 1)

  return (avgTime, benchRuns + 1, totalTime)

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
  PtrLit t <$> if ptr == nullPtr
    then return NullPtr
    else return $ PtrLitVal ptr
loadLitVal _ (Vector _ _) = error "Vector loads not implemented"

storeLitVal :: MonadIO m => Ptr () -> LitVal -> m ()
storeLitVal ptr val = liftIO case val of
  Int64Lit   x -> poke (castPtr ptr) x
  Int32Lit   x -> poke (castPtr ptr) x
  Word8Lit   x -> poke (castPtr ptr) x
  Word32Lit  x -> poke (castPtr ptr) x
  Word64Lit  x -> poke (castPtr ptr) x
  Float64Lit x -> poke (castPtr ptr) x
  Float32Lit x -> poke (castPtr ptr) x
  PtrLit _ (PtrLitVal x) -> poke (castPtr ptr) x
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
  PtrType (CPU, Scalar _) -> liftIO $ free_cpu =<< loadPtr
  PtrType (GPU, Scalar _) -> liftIO $ free_gpu =<< loadPtr
  -- TODO: Handle pointers to pointers
  _ -> error "not implemented"
  where loadPtr = peek (castPtr litValPtr)

cellSize :: Int
cellSize = 8

ptrArray :: Ptr () -> [Ptr ()]
ptrArray p = map (\i -> p `plusPtr` (i * cellSize)) [0..]

allocaCells :: MonadIO m => Int -> (Ptr () -> IO a) -> m a
allocaCells n cont = liftIO $ allocaBytes (n * cellSize) cont

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

-- ==== thread-local storage ===

-- We use TLS to implement some dynamically scoped variables, like the file
-- descriptor for the current output stream. We create the key here and we
-- generate code for `pthread_setspecific` at entry functions and
-- `pthread_getspecific` at use sites.

data PThreadKey

foreign import ccall "dex_pthread_key_create"
  pthreadKeyCreate :: IO (Ptr PThreadKey)

createTLSKey :: IO (Ptr (Ptr ()))
createTLSKey = castPtr <$> pthreadKeyCreate
