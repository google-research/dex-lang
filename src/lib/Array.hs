-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE RankNTypes #-}

module Array (
  BaseType (..), LitVal (..), ArrayType, Array (..), ArrayRef (..),
  Vec (..), scalarFromArray, arrayFromScalar, arrayOffset, arrayHead, arrayConcat,
  loadArray, storeArray, sizeOf, arrayType, unsafeWithArrayPointer) where

import Control.Monad
import qualified Data.Vector.Storable as V
import Data.Maybe (fromJust)
import Foreign.Marshal.Array
import Foreign.Ptr
import Foreign.Storable  hiding (sizeOf)
import Data.Coerce
import GHC.Generics

newtype Array = Array    Vec                 deriving (Show, Eq, Generic)
data ArrayRef = ArrayRef ArrayType (Ptr ())  deriving (Show, Eq, Generic)

data LitVal = IntLit  Int
            | RealLit Double
            | BoolLit Bool
            | StrLit  String
              deriving (Show, Eq, Generic)

data Vec = IntVec    (V.Vector Int)
         | BoolVec   (V.Vector Int)
         | DoubleVec (V.Vector Double)
           deriving (Show, Eq, Generic)

data BaseType = IntType | BoolType | RealType | StrType
                deriving (Show, Eq, Generic)

type ArrayType = (Int, BaseType)

arrayType :: Array -> ArrayType
arrayType (Array (IntVec v))    = (V.length v, IntType)
arrayType (Array (BoolVec v))   = (V.length v, BoolType)
arrayType (Array (DoubleVec v)) = (V.length v, RealType)

sizeOf :: BaseType -> Int
sizeOf _ = 8

scalarFromArray :: Array -> Maybe LitVal
scalarFromArray arr@(Array vec) = case size of
    1 -> Just $ case b of
      IntType  -> IntLit  $ xs V.! 0       where IntVec    xs = vec
      BoolType -> BoolLit $ xs V.! 0 /= 0  where BoolVec   xs = vec
      RealType -> RealLit $ xs V.! 0       where DoubleVec xs = vec
      _ -> error "Not implemented"
    _ -> Nothing
  where
    (size, b) = arrayType arr

arrayOffset :: Array -> Int -> Array
arrayOffset arr off = modifyVec arr (V.drop off)

arrayHead :: Array -> LitVal
arrayHead arr = fromJust $ scalarFromArray $ modifyVec arr (V.slice 0 1)

arrayFromScalar :: LitVal -> Array
arrayFromScalar val = case val of
  IntLit  x -> Array $ IntVec $ V.fromList [x]
  BoolLit x -> Array $ IntVec $ V.fromList [x']
    where x' = case x of False -> 0
                         True  -> 1
  RealLit x -> Array $ DoubleVec $ V.fromList [x]
  _ -> error "Not implemented"

arrayConcat :: [Array] -> Array
arrayConcat arrs = Array $ choose intVecs boolVecs doubleVecs
  where
    intVecs    = [v | IntVec v    <- coerce arrs]
    boolVecs   = [v | BoolVec v   <- coerce arrs]
    doubleVecs = [v | DoubleVec v <- coerce arrs]

    choose l [] [] = IntVec    $ V.concat l
    choose [] l [] = BoolVec   $ V.concat l
    choose [] [] l = DoubleVec $ V.concat l
    choose _  _  _ = error "Can't concatenate heterogenous vectors!"

loadArray :: ArrayRef -> IO Array
loadArray (ArrayRef (size, b) ptr) = Array <$> case b of
  IntType  -> liftM IntVec    $ peekVec size $ castPtr ptr
  BoolType -> liftM BoolVec   $ peekVec size $ castPtr ptr
  RealType -> liftM DoubleVec $ peekVec size $ castPtr ptr
  _ -> error "Not implemented"

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

modifyVec :: Array -> (forall a. Storable a => V.Vector a -> V.Vector a) -> Array
modifyVec (Array vec) f = case vec of
  IntVec v    -> Array $ IntVec    $ f v
  BoolVec v   -> Array $ BoolVec   $ f v
  DoubleVec v -> Array $ DoubleVec $ f v

applyVec :: Array -> (forall a. Storable a => V.Vector a -> b) -> b
applyVec (Array vec) f = case vec of
  IntVec v    -> f v
  BoolVec v   -> f v
  DoubleVec v -> f v
