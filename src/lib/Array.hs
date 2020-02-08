-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module Array (allocateArray, storeArray, loadArray, allocAndStoreArray,
              subArray, subArrayRef, readScalar, vecRefInfo, scalarArray,
              newArrayRef) where

import Control.Monad
import Foreign.Ptr
import Foreign.Marshal.Array

import Syntax

subArray :: Int -> Array -> Array
subArray i (Array (_:shape) vec) = Array shape sliced
  where
    subArraySize = product shape
    start = i * subArraySize
    stop  = start + subArraySize
    sliced = case vec of
      IntVec  xs -> IntVec  (slice start stop xs)
      RealVec xs -> RealVec (slice start stop xs)
      BoolVec xs -> BoolVec (slice start stop xs)
subArray _ (Array [] _) = error "Can't get subarray of rank-0 array"

-- This is just here to avoid and import cycle: TODO: organize better
subArrayRef :: Int -> ArrayRef -> ArrayRef
subArrayRef i (Array (_:shape) (_,ref)) = Array shape (newSize, ref')
  where
    newSize = product shape
    offset = i * newSize
    ref' = case ref of
     IntVecRef  ptr -> IntVecRef  $ advancePtr ptr offset
     RealVecRef ptr -> RealVecRef $ advancePtr ptr offset
     BoolVecRef ptr -> BoolVecRef $ advancePtr ptr offset
subArrayRef _ (Array [] _) = error "Can't get subarray of rank-0 array"

slice :: Int -> Int -> [a] -> [a]
slice start stop xs = take (stop - start) $ drop start xs

-- TODO: free
allocateArray :: BaseType -> [Int] -> IO ArrayRef
allocateArray b shape = do
  ptr <- case b of
    IntType  -> liftM IntVecRef  $ mallocArray size
    RealType -> liftM RealVecRef $ mallocArray size
    BoolType -> liftM BoolVecRef $ mallocArray size
    StrType  -> error "Not implemented"
  return $ Array shape (size, ptr)
  where size = product shape

allocAndStoreArray :: Array -> IO ArrayRef
allocAndStoreArray array@(Array shape vec) = do
  arrayRef <- allocateArray b shape
  storeArray arrayRef array
  return arrayRef
  where (_, b) = vecInfo vec

storeArray :: ArrayRef -> Array -> IO ()
storeArray (Array _ (_, ref)) (Array _ vec) = case (ref, vec) of
  (IntVecRef  ptr, IntVec  xs) -> pokeArray ptr xs
  (RealVecRef ptr, RealVec xs) -> pokeArray ptr xs
  (BoolVecRef ptr, BoolVec xs) -> pokeArray ptr xs
  _ -> error "Mismatched types"

loadArray :: ArrayRef -> IO Array
loadArray (Array shape (size, ref)) = case ref of
  IntVecRef  ptr -> liftM (Array shape . IntVec ) $ peekArray size ptr
  RealVecRef ptr -> liftM (Array shape . RealVec) $ peekArray size ptr
  BoolVecRef ptr -> liftM (Array shape . BoolVec) $ peekArray size ptr

readScalar :: Array -> LitVal
readScalar (Array [] vec) = case vec of
  IntVec  [x] -> IntLit  x
  RealVec [x] -> RealLit x
  BoolVec [x] -> BoolLit $ case x of 0 -> False
                                     _ -> True
  _ -> error "Not a singleton list"
readScalar _ = error "Array must be rank-0"

scalarArray :: LitVal -> Array
scalarArray val = case val of
  IntLit  x -> Array [] (IntVec  [x])
  RealLit x -> Array [] (RealVec [x])
  BoolLit False -> Array [] (BoolVec [0])
  BoolLit True  -> Array [] (BoolVec [1])
  _ -> error "Not implemented"

vecRefInfo :: VecRef -> (Int, BaseType, Ptr ())
vecRefInfo (size, x) = case x of
  IntVecRef  ptr -> (size, IntType , castPtr ptr)
  RealVecRef ptr -> (size, RealType, castPtr ptr)
  BoolVecRef ptr -> (size, BoolType, castPtr ptr)

vecInfo :: Vec -> (Int, BaseType)
vecInfo vec = case vec of
  IntVec  xs -> (length xs, IntType)
  RealVec xs -> (length xs, RealType)
  BoolVec xs -> (length xs, BoolType)

newArrayRef :: Ptr () -> (BaseType, [Int]) -> ArrayRef
newArrayRef ptr (b, shape) = Array shape $ case b of
  IntType  -> (size, IntVecRef  $ castPtr ptr)
  RealType -> (size, RealVecRef $ castPtr ptr)
  BoolType -> (size, BoolVecRef $ castPtr ptr)
  StrType  -> error "Not implemented"
  where size = product shape
