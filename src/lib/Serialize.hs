-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Serialize (serializeVal, restructureVal, subArray, readScalar,
                  allocateArray, storeArray, loadArray, vecRefInfo,
                  printLitBlock) where

import Control.Monad
import Foreign.Ptr
import Foreign.Marshal.Array
import Data.Foldable
import Data.Text.Prettyprint.Doc

import Type
import Syntax
import Util
import PPrint

serializeVal :: Val -> IO FlatValRef
serializeVal val = do
  let ty = getType val
  vecRefs <- mapM (uncurry allocateArray) $ flattenType ty
  let flatValRef = FlatVal ty vecRefs
  writeVal flatValRef $ stripSrcAnnot  val
  return flatValRef

writeVal :: FlatValRef -> Val -> IO ()
writeVal (FlatVal (BaseType _) [ref]) (Lit x) = storeArray ref $ scalarArray x
writeVal fv val = error $ "Unexpected flatval/val: " ++ pprint (fv, show val)

restructureVal :: FlatVal -> Val
restructureVal (FlatVal ty arrays) = case ty of
  BaseType _  -> Lit      $ readScalar array  where [array] = arrays
  RecType k r -> RecCon k $ fst $ traverseFun restructureValPartial r arrays
  TabType (IdxSetLit n) a -> TabCon ty $
    [restructureVal $ FlatVal a $ map (subArray i) arrays | i <- [0..n-1]]
  IdxSetLit n -> IdxLit n i  where [array] = arrays
                                   IntLit i = readScalar array
  _ -> error $ "Unexpected type: " ++ show ty

restructureValPartial :: Type -> [Array] -> (Val, [Array])
restructureValPartial ty xsRest = (restructureVal (FlatVal ty xs), rest)
  where (xs, rest) = splitAt (length (flattenType ty)) xsRest

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

flattenType :: Type -> [(BaseType, [Int])]
flattenType ty = case ty of
  BaseType b  -> [(b, [])]
  RecType _ r -> concat $ map flattenType $ toList r
  TabType (IdxSetLit n) a -> [(b, n:shape) | (b, shape) <- flattenType a]
  _ -> error $ "Unexpected type: " ++ show ty

-- These Pretty instances are here for circular import reasons
-- TODO: refactor. Pretty-printing shouldn't do complicated restructuring anyway

instance Pretty Output where
  pretty (ValOut Printed val) = pretty (restructureVal val)
  pretty (ValOut _ _) = "<graphical output>"
  pretty (TextOut s) = pretty s
  pretty NoOutput = ""

instance Pretty SourceBlock where
  pretty block = pretty (sbText block)

instance Pretty Result' where
  pretty r = case r of
    Left err -> pretty err
    Right NoOutput -> mempty
    Right out -> pretty out

instance Pretty Result where
  pretty (Result r) = pretty r

printLitBlock :: SourceBlock -> Result -> String
printLitBlock block result = pprint block ++ resultStr
  where
    resultStr = unlines $ map addPrefix $ lines $ pprint result
    addPrefix :: String -> String
    addPrefix s = case s of "" -> ">"
                            _  -> "> " ++ s
