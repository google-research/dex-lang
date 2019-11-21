-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Generators where

import GHC.Float
import Control.Monad
import Test.QuickCheck
import qualified Data.Map.Strict as M

import Record
import Env
import Syntax

arb :: Arbitrary a => Gen a
arb = arbitrary

smaller :: Int -> Gen a -> Gen a
smaller n m = scale (\size -> size `div` n) m  -- TODO: use ceil div instead?

oneOfFiltered :: [(Bool, Gen a)] -> Gen a
oneOfFiltered gens = oneof $ map snd $ filter fst gens

oneOrTwo :: Arbitrary a => Gen [a]
oneOrTwo = do n::Int <- elements [1, 2]
              mapM (const arbitrary) [1..n]

zeroToTwo :: Arbitrary a => Gen [a]
zeroToTwo = do n::Int <- elements [0, 1, 2]
               mapM (const arbitrary) [1..n]

liftS2 :: (Arbitrary a, Arbitrary b) => (a -> b -> c) -> a -> b -> [c]
liftS2 f x y = [f x' y' | (x', y') <- shrink (x, y)]

liftS :: Arbitrary a => (a -> b) -> a -> [b]
liftS f x = map f (shrink x)

instance Arbitrary Lin where
  arbitrary = elements [NonLin, Lin]

instance Arbitrary ProdKind where
  arbitrary = elements [Cart] -- TODO: handle tensor product

instance Arbitrary Name where
  arbitrary = liftM2 Name (elements ["x", "y"]) (elements [0, 1])
  shrink _ = []

instance Arbitrary Type where
  arbitrary = arbType 0
  shrink = genericShrink

arbType :: Int -> Gen Type
arbType numBinders = do
  n <- getSize
  let nonLeaf = n>0
  oneOfFiltered
    [ (True, liftM BaseType arb)
    , (True, liftM TypeVar arbTypeName)
    , (nonLeaf, liftM3 ArrType arb (smaller 2 arb) (smaller 2 arb))
    , (nonLeaf, liftM2 TabType (smaller 2 arb) (smaller 2 arb))
    , (nonLeaf, liftM (RecType Cart) arb)
    -- TODO: add explicit quantification to concrete syntax
    -- , (True, liftM (Forall [TyKind]) (arbType (numBinders + 1)))
    , (True, liftM Exists (arbType (numBinders + 1)))
    , (numBinders > 0, liftM BoundTVar (elements [0..numBinders-1]))]
    --     | IdxSetLit IdxSetVal

instance Arbitrary BaseType where
  arbitrary = elements [IntType, BoolType, RealType]  -- TODO: StrType
  shrink = genericShrink

instance Arbitrary a => Arbitrary (RecTree a) where
  arbitrary = frequency [ (2, liftM RecLeaf arb)
                        , (1, liftM RecTree arb) ]
  shrink = genericShrink

-- Note: empty tuples but no singletons
instance Arbitrary a => Arbitrary (Record a) where
  arbitrary = liftM Tup $ frequency
    [ (1, return [])
    , (2, sequence $ replicate 2 (smaller 2 arb)) ]
  shrink = genericShrink

instance Arbitrary b => Arbitrary (BinderP b) where
  arbitrary = liftM2 (:>) arb arb
  shrink = genericShrink

instance Arbitrary expr => Arbitrary (Command expr) where
  arbitrary = liftM2 Command arb arb
  shrink = genericShrink

instance Arbitrary b => Arbitrary (TopDeclP b) where
  arbitrary = liftM TopDecl arb
  shrink = genericShrink

instance Arbitrary CmdName where
  arbitrary = elements [GetType, EvalExpr Printed]

instance Arbitrary b => Arbitrary (DeclP b) where
  arbitrary = frequency
    [ (4, liftM2 LetMono arb arb)
    , (1, liftM2 TAlias arbTypeName arb)
    , (1, liftM3 Unpack arb arbTypeName arb)]
  shrink decl = case decl of
    LetMono p e  -> liftS2 LetMono p e
    LetPoly _ _  -> error "Not implemented"
    Unpack _ _ _ -> error "Not implemented"
    TAlias v ty -> liftS2 TAlias v ty

instance Arbitrary b => Arbitrary (ExprP b) where
  arbitrary = oneof
    [ liftM Lit arb
    , liftM (flip Var []) arb
    , liftM3 PrimOp arb (return []) oneOrTwo  -- TODO: explicit type args
    , liftM2 Decl (smaller 2 arb) (smaller 2 arb)
    ]
  shrink = genericShrink
  -- TODO: the rest

allBuiltins :: [Builtin]
allBuiltins = M.elems builtinNames

instance Arbitrary Builtin where
  arbitrary = elements allBuiltins

instance Arbitrary LitVal where
  arbitrary = oneof
    [ liftM IntLit  arb
    , liftM (RealLit . roundTripDouble) arb
    , liftM BoolLit arb ]
  shrink = genericShrink
  -- TODO: StrLit

roundTripDouble :: Double -> Double
roundTripDouble x = read (show (double2Float x))

instance Arbitrary Ann where
  arbitrary = oneof [return NoAnn, liftM Ann arb]
  shrink = genericShrink

arbTypeName :: Gen Name
arbTypeName = liftM2 Name (elements ["A", "B"]) (elements [0, 1])
