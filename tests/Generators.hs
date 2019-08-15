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

oneOfFiltered :: [(Bool, Gen a)] -> Gen a
oneOfFiltered gens = oneof $ map snd $ filter fst gens

instance Arbitrary Name where
  arbitrary = liftM2 Name (elements ["x", "y"]) (elements [0, 1])

instance Arbitrary Type where
  arbitrary = arbType 0

arbType :: Int -> Gen Type
arbType numBinders = do
  n <- getSize
  let nonLeaf = n>0
  oneOfFiltered
    [ (True, liftM BaseType arb)
    , (True, liftM TypeVar arbTypeName)
    , (nonLeaf, liftM2 ArrType (smaller 2 arb) (smaller 2 arb))
    , (nonLeaf, liftM2 TabType (smaller 2 arb) (smaller 2 arb))
    , (nonLeaf, liftM RecType arb)
    -- TODO: add explicit quantification to concrete syntax
    -- , (True, liftM (Forall [TyKind]) (arbType (numBinders + 1)))
    -- , (True, liftM Exists (arbType (numBinders + 1)))
    , (numBinders > 0, liftM BoundTVar (elements [0..numBinders-1]))]
    --     | IdxSetLit IdxSetVal

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
    , (1, liftM2 TAlias arbTypeName arb)
    , (1, liftM3 Unpack arb arbTypeName arb)]

instance Arbitrary b => Arbitrary (ExprP b) where
  arbitrary = oneof
    [ liftM Var arbitrary ]
  -- TODO: the rest

instance Arbitrary Ann where
  arbitrary = oneof [return NoAnn, liftM Ann arb]

arbTypeName :: Gen Name
arbTypeName = liftM2 Name (elements ["A", "B"]) (elements [0, 1])
