
module CUDA (hasCUDA, loadCUDAArray, synchronizeCUDA) where

import Data.Int
import Foreign.Ptr

hasCUDA :: Bool

#ifdef DEX_CUDA
hasCUDA = True

foreign import ccall "dex_cuMemcpyDtoH"    cuMemcpyDToH    :: Int64 -> Ptr () -> Ptr () -> IO ()
foreign import ccall "dex_synchronizeCUDA" synchronizeCUDA :: IO ()
#else
hasCUDA = False

cuMemcpyDToH :: Int64 -> Ptr () -> Ptr () -> IO ()
cuMemcpyDToH = error "Dex built without CUDA support"

synchronizeCUDA :: IO ()
synchronizeCUDA = return ()
#endif

loadCUDAArray :: Ptr () -> Ptr () -> Int -> IO ()
loadCUDAArray hostPtr devicePtr bytes = cuMemcpyDToH (fromIntegral bytes) devicePtr hostPtr
