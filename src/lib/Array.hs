-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module Array (allocateArray, loadScalar, storeScalar, subArray) where

import Control.Monad
import Foreign.Marshal.Alloc
import Foreign.Ptr
import Foreign.Storable  hiding (sizeOf)

import Syntax

sizeOf :: BaseType -> Int
sizeOf _ = 8

subArray :: Int -> Array -> Array
subArray i (Array (_:shape) b ptr) = Array shape b ptr'
  where ptr' = ptr `plusPtr` (i * product shape * sizeOf b)
subArray _ (Array [] _ _) = error "Can't get subarray of rank-0 array"

-- TODO: free
allocateArray :: BaseType -> [Int] -> IO Array
allocateArray b shape = do
  ptr <- mallocBytes $ product shape * sizeOf b
  return $ Array shape b ptr

loadScalar :: Array -> IO LitVal
loadScalar (Array [] b ptr) = case b of
  IntType  -> liftM IntLit  $ peek (castPtr ptr)
  RealType -> liftM RealLit $ peek (castPtr ptr)
  BoolType -> do
    x <- peek (castPtr ptr :: Ptr Int)
    return $ BoolLit $ case x of 0 -> False
                                 _ -> True
  _ -> error "Not implemented"
loadScalar _ = error "Array must be rank-0"

storeScalar :: Array -> LitVal -> IO ()
storeScalar (Array [] _ ptr) val = case val of
  IntLit  x -> poke (castPtr ptr) x
  RealLit x -> poke (castPtr ptr) x
  BoolLit x -> case x of False -> poke ptr' 0
                         True  -> poke ptr' 1
    where ptr' = castPtr ptr :: Ptr Int
  _ -> error "Not implemented"
storeScalar _ _ = error "Array must be rank-0"
