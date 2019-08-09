module Generators where

import Control.Monad
import Test.QuickCheck

import Record
import Env
import Syntax

arb :: Arbitrary a => Gen a
arb = arbitrary

smaller :: Int -> Gen a -> Gen a
smaller n m = scale (\size -> size `div` n) m  -- TODO: use ceil div instead?



instance Arbitrary Name where
  arbitrary = liftM2 Name (elements ["x", "y"]) (elements [0, 1])

instance Arbitrary Type where
  arbitrary = oneof
    [ liftM BaseType arb ]
  -- TODO: the rest

instance Arbitrary BaseType where
  arbitrary = elements [IntType, BoolType, RealType]  -- TODO: StrType

instance Arbitrary a => Arbitrary (RecTree a) where
  arbitrary = frequency [ (2, liftM RecLeaf arb)
                        , (1, liftM RecTree arb) ]

-- Note: empty tuples but no singletons
instance Arbitrary a => Arbitrary (Record a) where
  arbitrary = liftM Tup $ frequency
    [ (1, return [])
    , (2, sequence $ replicate 2 (smaller 2 arb)) ]
  -- TODO: generate named records too

instance Arbitrary b => Arbitrary (BinderP b) where
  arbitrary = liftM2 (:>) arb arb

instance Arbitrary b => Arbitrary (TopDeclP b) where
  arbitrary = liftM TopDecl arb
  -- TODO: commands

instance Arbitrary b => Arbitrary (DeclP b) where
  arbitrary = frequency
    [ (4, liftM2 Let arb arb)
    , (1, liftM2 TAlias arb arb)
    , (1, liftM3 Unpack arb arb arb)]

instance Arbitrary b => Arbitrary (ExprP b) where
  arbitrary = oneof
    [ liftM Var arbitrary ]
  -- TODO: the rest

instance Arbitrary Ann where
  arbitrary = oneof [return NoAnn, liftM Ann arb]

