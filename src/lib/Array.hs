-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}

module Array (
  BaseType (..), LitVal (..), ArrayType, Array (..), ArrayRef (..),
  Vec (..), subArray, scalarFromArray, arrayFromScalar,
  loadArray, storeArray, subArrayRef, newArrayRef, storeArrayNew) where

import Control.Monad
import Control.Monad.Primitive (PrimState)
import Data.Text.Prettyprint.Doc
import qualified Data.Vector.Unboxed as V
import Foreign.Marshal.Alloc
import Foreign.Marshal.Array
import Foreign.Ptr
import Foreign.Storable  hiding (sizeOf)
import GHC.Generics

data Array    = Array    ArrayType Vec     deriving (Show, Eq, Generic)
data ArrayRef = ArrayRef ArrayType (Ptr ())  deriving (Show, Eq, Generic)

data LitVal = IntLit  Int
            | RealLit Double
            | BoolLit Bool
            | StrLit  String
              deriving (Show, Eq, Generic)

data Vec = IntVec    (V.Vector Int)
         | DoubleVec (V.Vector Double)
           deriving (Show, Eq, Generic)

data VecRef = IntVecRef    (V.MVector (PrimState IO) Int)
            | DoubleVecRef (V.MVector (PrimState IO) Double)
              deriving (Generic)

data BaseType = IntType | BoolType | RealType | StrType
                deriving (Show, Eq, Generic)

type ArrayType = ([Int], BaseType)

sizeOf :: BaseType -> Int
sizeOf _ = 8

subArray :: Int -> Array -> Array
subArray i (Array ((_:shape), b) vec) = Array (shape, b) vec'
  where size = product shape
        offset = i * size
        vec' = case vec of
                 IntVec    xs -> IntVec    $ V.slice offset size xs
                 DoubleVec xs -> DoubleVec $ V.slice offset size xs
subArray _ _ = error "Can't get subarray of rank-0 array"

scalarFromArray :: Array -> LitVal
scalarFromArray (Array ([], b) vec) = case b of
  IntType  -> IntLit  $ xs V.! 0       where IntVec    xs = vec
  BoolType -> BoolLit $ xs V.! 0 /= 0  where IntVec    xs = vec
  RealType -> RealLit $ xs V.! 0       where DoubleVec xs = vec
  _ -> error "Not implemented"
scalarFromArray x = error $ "Not a rank-zero array: " ++ show x

arrayFromScalar :: LitVal -> Array
arrayFromScalar val = case val of
  IntLit  x -> Array ([], IntType ) $ IntVec $ V.fromList [x]
  BoolLit x -> Array ([], BoolType) $ IntVec $ V.fromList [x']
    where x' = case x of False -> 0
                         True  -> 1
  RealLit x -> Array ([], RealType) $ DoubleVec $ V.fromList [x]
  _ -> error "Not implemented"

loadArray :: ArrayRef -> IO Array
loadArray (ArrayRef ty@(shape,b) ptr) = liftM (Array ty) $ case b of
  IntType  -> liftM IntVec    $ peekVec size $ castPtr ptr
  BoolType -> liftM IntVec    $ peekVec size $ castPtr ptr
  RealType -> liftM DoubleVec $ peekVec size $ castPtr ptr
  _ -> error "Not implemented"
  where size = product shape

storeArray :: ArrayRef -> Array -> IO ()
storeArray (ArrayRef _ ptr) (Array _ vec) = case vec of
  IntVec    v -> pokeVec (castPtr ptr) v
  DoubleVec v -> pokeVec (castPtr ptr) v

peekVec :: (V.Unbox a, Storable a) => Int -> Ptr a -> IO (V.Vector a)
peekVec size ptr = V.generateM size $ \i -> peek (ptr `advancePtr` i)

pokeVec :: (V.Unbox a, Storable a) => Ptr a -> V.Vector a -> IO ()
pokeVec ptr v = forM_ [0..(V.length v - 1)] $ \i -> do
  x <- V.indexM v i
  poke (ptr `advancePtr` i) x

subArrayRef :: Int -> ArrayRef -> ArrayRef
subArrayRef i (ArrayRef ty@((_:shape), b) ptr) = ArrayRef ty ptr'
  where ptr' = ptr `advancePtr` (i * product shape * sizeOf b)
subArrayRef _ _ = error "Can't get subarray of rank-0 array"

-- TODO: free
newArrayRef :: ArrayType -> IO ArrayRef
newArrayRef ty@(shape, b) = do
  ptr <- mallocBytes $ product shape * sizeOf b
  return $ ArrayRef ty ptr

storeArrayNew :: Array -> IO ArrayRef
storeArrayNew arr@(Array ty _) = do
  ref <- newArrayRef ty
  storeArray ref arr
  return ref

instance Pretty Array where
  pretty (Array _ _) = "<<TODO: array printing>>"
