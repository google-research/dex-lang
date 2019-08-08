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

instance Arbitrary UBinder where
  arbitrary = undefined

instance Arbitrary UTopDecl where
  arbitrary = liftM UTopDecl arb
  -- TODO: commands

instance Arbitrary UDecl where
  arbitrary = frequency
    [ (4, liftM2 ULet arb arb)
    , (1, liftM2 UTAlias arb arb)
    , (1, liftM3 UUnpack arb arb arb)]

instance Arbitrary UExpr where
  arbitrary = oneof
    [ liftM UVar arbitrary ]
  -- TODO: the rest
