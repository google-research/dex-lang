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
import Data.Word
import Foreign.Marshal.Array
import Foreign.Ptr
import Foreign.Storable  hiding (sizeOf)
import GHC.Generics

data Array    = Array    BaseType  Vec       deriving (Show, Eq, Generic)
data ArrayRef = ArrayRef ArrayType (Ptr ())  deriving (Show, Eq, Generic)

data LitVal = IntLit  Int
            | CharLit Char
            | RealLit Double
            | BoolLit Bool
            | StrLit  String
            | VecLit [LitVal]  -- Only one level of nesting allowed!
              deriving (Show, Eq, Generic)

data Vec = CharVec   (V.Vector Word8)
         | IntVec    (V.Vector Int)
         | BoolVec   (V.Vector Int)
         | RealVec   (V.Vector Double)
           deriving (Show, Eq, Generic)

data ScalarBaseType = IntType | BoolType | RealType | StrType | CharType
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
sizeOf t = vecEntriesFor t * 8

scalarFromArray :: Array -> Maybe LitVal
scalarFromArray arr@(Array b vec) = case arrayLength arr of
    1 -> Just $ case b of
      Scalar _ -> scalarFromVec vec
      Vector _ -> VecLit $ fmap (\i -> scalarFromVec $ modifyVec vec (V.drop i)) [0..vectorWidth - 1]
    _ -> Nothing
  where
    scalarFromVec :: Vec -> LitVal
    scalarFromVec v = case v of
      CharVec   xs -> CharLit $ toEnum $ fromIntegral $ xs V.! 0
      IntVec    xs -> IntLit  $ xs V.! 0
      BoolVec   xs -> BoolLit $ xs V.! 0 /= 0
      RealVec   xs -> RealLit $ xs V.! 0

arrayOffset :: Array -> Int -> Array
arrayOffset (Array b vec) off = Array b $ modifyVec vec $ V.drop (off * vecEntriesFor b)

arrayHead :: Array -> LitVal
arrayHead (Array b vec) = fromJust $ scalarFromArray $ Array b $ modifyVec vec $ V.slice 0 (vecEntriesFor b)

arrayFromScalar :: LitVal -> Array
arrayFromScalar val = case val of
  IntLit  x -> Array (Scalar IntType)  $ IntVec $ V.fromList [x]
  BoolLit x -> Array (Scalar BoolType) $ BoolVec $ V.fromList [x']
    where x' = case x of False -> 0
                         True  -> 1
  RealLit x -> Array (Scalar RealType) $ RealVec $ V.fromList [x]
  _ -> error "Not implemented"

arrayConcat :: [Array] -> Array
arrayConcat arrs = Array b $ choose intVecs boolVecs doubleVecs
  where
    (Array b _) = head arrs

    intVecs    = [v | (Array _ (IntVec v )) <- arrs]
    boolVecs   = [v | (Array _ (BoolVec v)) <- arrs]
    doubleVecs = [v | (Array _ (RealVec v)) <- arrs]

    choose l [] [] = IntVec  $ V.concat l
    choose [] l [] = BoolVec $ V.concat l
    choose [] [] l = RealVec $ V.concat l
    choose _  _  _ = error "Can't concatenate heterogenous vectors!"

loadArray :: ArrayRef -> IO Array
loadArray (ArrayRef (size, b) ptr) = Array b <$> case b of
    Scalar sb -> loadVec sb 1
    Vector sb -> loadVec sb vectorWidth
  where
    loadVec :: ScalarBaseType -> Int -> IO Vec
    loadVec sb width = case sb of
      CharType -> liftM CharVec $ peekVec (size * width) $ castPtr ptr
      IntType  -> liftM IntVec  $ peekVec (size * width) $ castPtr ptr
      BoolType -> liftM BoolVec $ peekVec (size * width) $ castPtr ptr
      RealType -> liftM RealVec $ peekVec (size * width) $ castPtr ptr
      StrType  -> error "Not implemented"

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
  CharVec v -> CharVec $ f v
  IntVec  v -> IntVec  $ f v
  BoolVec v -> BoolVec $ f v
  RealVec v -> RealVec $ f v

applyVec :: Array -> (forall a. Storable a => V.Vector a -> b) -> b
applyVec (Array _ vec) f = case vec of
  CharVec v -> f v
  IntVec  v -> f v
  BoolVec v -> f v
  RealVec v -> f v

instance Store Array
instance Store Vec
instance Store BaseType
instance Store ScalarBaseType
instance Store LitVal
