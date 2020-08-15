-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE RankNTypes #-}

module Array (
  BaseType (..), ScalarBaseType (..), LitVal (..), ArrayType, Array (..), ArrayRef (..),
  Vec (..), scalarFromArray, arrayFromScalar, arrayOffset, arrayHead, arrayConcat,
  loadArray, storeArray, sizeOf, arrayType, unsafeWithArrayPointer, vectorWidth) where

import Control.Monad
import qualified Data.Vector.Storable as V
import Data.Maybe (fromJust)
import Data.Store (Store)
import Foreign.Marshal.Array
import Foreign.Ptr
import Foreign.Storable  hiding (sizeOf)
import GHC.Generics
import Data.Int

data Array    = Array    BaseType  Vec       deriving (Show, Eq, Generic)
data ArrayRef = ArrayRef ArrayType (Ptr ())  deriving (Show, Eq, Generic)

data LitVal = Int64Lit   Int64
            | Int32Lit   Int32
            | Int8Lit    Int8
            | Float64Lit Double
            | Float32Lit Float
            | VecLit     [LitVal]  -- Only one level of nesting allowed!
              deriving (Show, Eq, Generic)

data Vec = Int64Vec   (V.Vector Int64)
         | Int32Vec   (V.Vector Int32)
         | Int8Vec    (V.Vector Int8)
         | Float64Vec (V.Vector Double)
         | Float32Vec (V.Vector Float)
           deriving (Show, Eq, Generic)

data ScalarBaseType = Int64Type | Int32Type | Int8Type | Float64Type | Float32Type
                      deriving (Show, Eq, Generic)
data BaseType = Scalar ScalarBaseType
              | Vector ScalarBaseType
                deriving (Show, Eq, Generic)

type ArrayType = (Int, BaseType)

vectorWidth :: Int
vectorWidth = 4

arrayLength :: Array -> Int
arrayLength arr@(Array b _) = applyVec arr V.length `div` vecEntriesFor b

arrayType :: Array -> ArrayType
arrayType arr@(Array b _) = (arrayLength arr, b)

vecEntriesFor :: BaseType -> Int
vecEntriesFor t = case t of
  Scalar _ -> 1
  Vector _ -> vectorWidth

sizeOf :: BaseType -> Int
sizeOf t = case t of
  Scalar Int64Type   -> 8
  Scalar Int32Type   -> 4
  Scalar Int8Type    -> 1
  Scalar Float64Type -> 8
  Scalar Float32Type -> 4
  Vector st          -> vectorWidth * sizeOf (Scalar st)

scalarFromArray :: Array -> Maybe LitVal
scalarFromArray arr@(Array b vec) = case arrayLength arr of
    1 -> Just $ case b of
      Scalar _ -> scalarFromVec vec
      Vector _ -> VecLit $ fmap (\i -> scalarFromVec $ modifyVec vec (V.drop i)) [0..vectorWidth - 1]
    _ -> Nothing
  where
    scalarFromVec :: Vec -> LitVal
    scalarFromVec v = case v of
      Int64Vec   xs -> Int64Lit   $ xs V.! 0
      Int32Vec   xs -> Int32Lit   $ xs V.! 0
      Int8Vec    xs -> Int8Lit    $ xs V.! 0
      Float64Vec xs -> Float64Lit $ xs V.! 0
      Float32Vec xs -> Float32Lit $ xs V.! 0

arrayOffset :: Array -> Int -> Array
arrayOffset (Array b vec) off = Array b $ modifyVec vec $ V.drop (off * vecEntriesFor b)

arrayHead :: Array -> LitVal
arrayHead (Array b vec) = fromJust $ scalarFromArray $ Array b $ modifyVec vec $ V.slice 0 (vecEntriesFor b)

arrayFromScalar :: LitVal -> Array
arrayFromScalar val = case val of
  Int64Lit   x -> Array (Scalar Int64Type  ) $ Int64Vec   $ V.fromList [x]
  Int32Lit   x -> Array (Scalar Int32Type  ) $ Int32Vec   $ V.fromList [x]
  Int8Lit    x -> Array (Scalar Int8Type   ) $ Int8Vec    $ V.fromList [x]
  Float64Lit x -> Array (Scalar Float64Type) $ Float64Vec $ V.fromList [x]
  Float32Lit x -> Array (Scalar Float32Type) $ Float32Vec $ V.fromList [x]
  _ -> error "Not implemented"

arrayConcat :: [Array] -> Array
arrayConcat arrs = Array b $ choose i64v i32v i8v fp64v fp32v
  where
    (Array b _) = head arrs

    i64v  = [v | (Array _ (Int64Vec   v)) <- arrs]
    i32v  = [v | (Array _ (Int32Vec   v)) <- arrs]
    i8v   = [v | (Array _ (Int8Vec    v)) <- arrs]
    fp64v = [v | (Array _ (Float64Vec v)) <- arrs]
    fp32v = [v | (Array _ (Float32Vec v)) <- arrs]

    choose l [] [] [] [] = Int64Vec   $ V.concat l
    choose [] l [] [] [] = Int32Vec   $ V.concat l
    choose [] [] l [] [] = Int8Vec    $ V.concat l
    choose [] [] [] l [] = Float64Vec $ V.concat l
    choose [] [] [] [] l = Float32Vec $ V.concat l
    choose _  _  _  _  _ = error "Can't concatenate heterogenous vectors!"

loadArray :: ArrayRef -> IO Array
loadArray (ArrayRef (size, b) ptr) = Array b <$> case b of
    Scalar sb -> loadVec sb 1
    Vector sb -> loadVec sb vectorWidth
  where
    loadVec :: ScalarBaseType -> Int -> IO Vec
    loadVec sb width = case sb of
      Int64Type   -> liftM Int64Vec   $ peekVec (size * width) $ castPtr ptr
      Int32Type   -> liftM Int32Vec   $ peekVec (size * width) $ castPtr ptr
      Int8Type    -> liftM Int8Vec    $ peekVec (size * width) $ castPtr ptr
      Float64Type -> liftM Float64Vec $ peekVec (size * width) $ castPtr ptr
      Float32Type -> liftM Float32Vec $ peekVec (size * width) $ castPtr ptr

storeArray :: ArrayRef -> Array -> IO ()
storeArray (ArrayRef _ ptr) arr = applyVec arr (pokeVec (castPtr ptr))

peekVec :: Storable a => Int -> Ptr a -> IO (V.Vector a)
peekVec size ptr = V.generateM size $ \i -> peek (ptr `advancePtr` i)

pokeVec :: Storable a => Ptr a -> V.Vector a -> IO ()
pokeVec ptr v = forM_ [0..(V.length v - 1)] $ \i -> do
  x <- V.indexM v i
  poke (ptr `advancePtr` i) x

unsafeWithArrayPointer :: Array -> (Ptr () -> IO a) -> IO a
unsafeWithArrayPointer arr f = applyVec arr (\v -> V.unsafeWith v (f. castPtr))

modifyVec :: Vec -> (forall a. Storable a => V.Vector a -> V.Vector a) -> Vec
modifyVec vec f = case vec of
  Int64Vec   v -> Int64Vec   $ f v
  Int32Vec   v -> Int32Vec   $ f v
  Int8Vec    v -> Int8Vec    $ f v
  Float64Vec v -> Float64Vec $ f v
  Float32Vec v -> Float32Vec $ f v

applyVec :: Array -> (forall a. Storable a => V.Vector a -> b) -> b
applyVec (Array _ vec) f = case vec of
  Int64Vec   v -> f v
  Int32Vec   v -> f v
  Int8Vec    v -> f v
  Float64Vec v -> f v
  Float32Vec v -> f v

instance Store Array
instance Store Vec
instance Store BaseType
instance Store ScalarBaseType
instance Store LitVal
