
module CUDA (hasCUDA, loadCUDAArray) where

import Data.Int
import Foreign.Ptr

hasCUDA :: Bool

#ifdef DEX_CUDA
foreign import ccall "load_cuda_array"  loadCUDAArrayImpl :: Ptr () -> Int64 -> IO (Ptr ())

hasCUDA = True
#else
loadCUDAArrayImpl :: Ptr () -> Int64 -> IO (Ptr ())
loadCUDAArrayImpl _ _ = error "Dex built without CUDA support"

hasCUDA = False
#endif

loadCUDAArray :: Ptr () -> Int -> IO (Ptr ())
loadCUDAArray ptr bytes = loadCUDAArrayImpl ptr (fromIntegral bytes)
