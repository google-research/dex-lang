-- Copyright 2020 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module Dex.Foreign.Util (fromStablePtr, toStablePtr) where

import Foreign.StablePtr
import Foreign.Ptr

fromStablePtr :: Ptr a -> IO a
fromStablePtr = deRefStablePtr . castPtrToStablePtr . castPtr

toStablePtr :: a -> IO (Ptr a)
toStablePtr x = castPtr . castStablePtrToPtr <$> newStablePtr x
