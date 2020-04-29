-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module Array (allocateArray, loadScalar, storeScalar, allocStoreArray,
              subArray, subArrayVal, loadArray, storeArray) where

import Control.Monad
import Foreign.Marshal.Alloc
import Foreign.Ptr
import Foreign.Storable  hiding (sizeOf)

import Syntax

sizeOf :: BaseType -> Int
sizeOf _ = 8

loadArray :: Array -> IO ArrayLitVal
loadArray arr@(Array shape b _) = do
  xs <- case shape of
          [] -> liftM (:[]) $ loadScalar arr
          (n:_) -> liftM concat $ forM [0..(n-1)] $ \i -> do
                     (ArrayLitVal _ _ xs) <- loadArray $ subArray i arr
                     return xs
  return $ ArrayLitVal shape b xs

allocStoreArray :: ArrayLitVal -> IO Array
allocStoreArray arr@(ArrayLitVal shape b _) = do
  arrayRef <- allocateArray b shape
  storeArray arrayRef arr
  return arrayRef

storeArray :: Array -> ArrayLitVal -> IO ()
storeArray ref (ArrayLitVal [] _ ~[x]) = storeScalar ref x
storeArray ref arr@(ArrayLitVal (n:_) _ _) = forM_ [0..(n-1)] $ \i -> do
  storeArray (subArray i ref) (subArrayVal i arr)

subArrayVal :: Int -> ArrayLitVal -> ArrayLitVal
subArrayVal i (ArrayLitVal (_:shape) b xs) =
  ArrayLitVal shape b $ take size $ drop offset xs
  where
    size = product shape
    offset = i * size
subArrayVal _ (ArrayLitVal [] _ _) = error "Can't get subarray of rank-0 array"

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
