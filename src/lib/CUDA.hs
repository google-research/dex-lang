
module CUDA (hasCUDA, loadCUDAArray, synchronizeCUDA, getCudaArchitecture) where

import Data.Int
import Foreign.Ptr
#ifdef DEX_CUDA
import Foreign.C
#else
#endif

hasCUDA :: Bool

#ifdef DEX_CUDA
hasCUDA = True

foreign import ccall "dex_cuMemcpyDtoH"    cuMemcpyDToH    :: Int64 -> Ptr () -> Ptr () -> IO ()
foreign import ccall "dex_synchronizeCUDA" synchronizeCUDA :: IO ()
foreign import ccall "dex_ensure_has_cuda_context" ensureHasCUDAContext :: IO ()
foreign import ccall "dex_get_cuda_architecture" dex_getCudaArchitecture :: Int -> CString -> IO ()

getCudaArchitecture :: Int -> IO String
getCudaArchitecture dev =
  withCString "sm_00" $ \cs ->
      dex_getCudaArchitecture dev cs >> peekCString cs
#else
hasCUDA = False

cuMemcpyDToH :: Int64 -> Ptr () -> Ptr () -> IO ()
cuMemcpyDToH = error "Dex built without CUDA support"

synchronizeCUDA :: IO ()
synchronizeCUDA = return ()

ensureHasCUDAContext :: IO ()
ensureHasCUDAContext = return ()

getCudaArchitecture :: Int -> IO String
getCudaArchitecture _ = error "Dex built without CUDA support"
#endif

loadCUDAArray :: Ptr () -> Ptr () -> Int -> IO ()
loadCUDAArray hostPtr devicePtr bytes = do
  ensureHasCUDAContext
  cuMemcpyDToH (fromIntegral bytes) devicePtr hostPtr
