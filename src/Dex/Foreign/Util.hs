-- Copyright 2020 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module Dex.Foreign.Util (fromStablePtr, toStablePtr, putOnHeap) where

import Foreign.Ptr
import Foreign.StablePtr
import Foreign.Storable
import Foreign.Marshal.Alloc

fromStablePtr :: Ptr a -> IO a
fromStablePtr = deRefStablePtr . castPtrToStablePtr . castPtr

toStablePtr :: a -> IO (Ptr a)
toStablePtr x = castPtr . castStablePtrToPtr <$> newStablePtr x

putOnHeap :: Storable a => a -> IO (Ptr a)
putOnHeap x = do
  ptr <- malloc
  poke ptr x
  return ptr
