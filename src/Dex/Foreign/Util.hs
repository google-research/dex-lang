-- Copyright 2020 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module Dex.Foreign.Util (fromStablePtr, toStablePtr, putOnHeap, setError, catchErrors) where

import Data.Int
import Data.Functor

import Foreign.Ptr
import Foreign.StablePtr
import Foreign.Storable
import Foreign.C.String
import Foreign.Marshal.Alloc

import Err

fromStablePtr :: Ptr a -> IO a
fromStablePtr = deRefStablePtr . castPtrToStablePtr . castPtr

toStablePtr :: a -> IO (Ptr a)
toStablePtr x = castPtr . castStablePtrToPtr <$> newStablePtr x

putOnHeap :: Storable a => a -> IO (Ptr a)
putOnHeap x = do
  ptr <- malloc
  poke ptr x
  return ptr

catchErrors :: IO (Ptr a) -> IO (Ptr a)
catchErrors m = catchIOExcept m >>= \case
  Success ans -> return ans
  Failure err -> setError (pprint err) $> nullPtr

foreign import ccall "_internal_dexSetError" internalSetErrorPtr :: CString -> Int64 -> IO ()

setError :: String -> IO ()
setError msg = withCStringLen msg $ \(ptr, len) ->
  internalSetErrorPtr ptr (fromIntegral len)
