
module CUDA (hasCUDA, loadCUDAArray) where

import Data.Int
import Foreign.Ptr

hasCUDA :: Bool

#ifdef DEX_CUDA
foreign import ccall "load_cuda_array"  loadCUDAArrayImpl :: Ptr () -> Ptr () -> Int64 -> IO ()

hasCUDA = True
#else
loadCUDAArrayImpl :: Ptr () -> Ptr () -> Int64 -> IO ()
loadCUDAArrayImpl _ _ = error "Dex built without CUDA support"

hasCUDA = False
#endif

loadCUDAArray :: Ptr () -> Ptr () -> Int -> IO ()
loadCUDAArray hostPtr devicePtr bytes = loadCUDAArrayImpl hostPtr devicePtr (fromIntegral bytes)
