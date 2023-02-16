-- Copyright 2022 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# OPTIONS_GHC -Wno-orphans #-}

module ConstantCastingSpec (spec) where

import Control.Monad
import Test.Hspec
import Test.Hspec.QuickCheck
import Test.QuickCheck

import Builder
import Core
import Imp (repValFromFlatList)
import Lower
import Name
import Optimize
import QueryType (getDestBlockType)
import TopLevel
import Types.Core
import Types.Imp
import Types.Primitives
import Types.Source
import Util

castOp :: ScalarBaseType -> LitVal -> PrimOp (SAtom VoidS)
castOp ty x = MiscOp $ CastOp (BaseTy (Scalar ty)) (Con (Lit x))

exprToBlock :: EnvReader m => SExpr n -> m n (SBlock n)
exprToBlock expr = do
  liftBuilder $ buildBlock $ do
    v <- emit $ sink expr
    return $ Var v

evalBlock :: (Topper m, Mut n) => SBlock n -> m n (SRepVal n)
evalBlock block = do
  NullaryDestLamExpr lowered <- lowerFullySequential $ NullaryLamExpr block
  imp <- asImpFunction lowered
  resultVals <- evalLLVM imp
  resultTy <- getDestBlockType lowered
  repValFromFlatList resultTy resultVals

evalClosedExpr :: SExpr VoidS -> IO LitVal
evalClosedExpr expr = do
  let cfg = EvalConfig LLVM [LibBuiltinPath] Nothing Nothing Nothing NoOptimize PrintCodegen
  env <- initTopState
  fst <$> runTopperM cfg env do
    block <- exprToBlock $ unsafeCoerceE expr
    RepVal _ (Leaf (ILit ans)) <- evalBlock block
    return ans

instance Arbitrary LitVal where
  arbitrary = oneof
    [ Int64Lit   <$> arbitrary
    , Int32Lit   <$> arbitrary
    , Word8Lit   <$> arbitrary
    , Word32Lit  <$> arbitrary
    , Word64Lit  <$> arbitrary
    , Float64Lit <$> arbitrary
    , Float32Lit <$> arbitrary
    ]

spec :: Spec
spec = do
  describe "constant-folding casts" do
    let constant_folding_and_runtime_casts_agree ty = 
          \(x::LitVal) -> case foldCast ty x of
              Nothing -> return ()
              Just folded -> do
                let op = castOp ty x
                evaled <- evalClosedExpr $ PrimOp op
                -- The failure message will list `evaled` as "expected" and `folded` as "got"
                folded `shouldBe` evaled
    forM_ [Int64Type, Int32Type, Word8Type, Word32Type, Word64Type, Float64Type, Float32Type] \ty ->
      -- TODO: We'd really like to run 10,000 or 1,000,000 examples here, but
      -- status quo is that each one runs through the LLVM compile-and-run
      -- pipeline separately, and is thus incredibly slow.  Taking 50 as a
      -- compromise between test suite speed and test coverage.
      -- I ran this offline with 10,000 before checking in, and it passed.
      modifyMaxSuccess (const 50) $ prop ("agrees with runtime when casting to " ++ show ty) $ constant_folding_and_runtime_casts_agree ty
    it "agrees with runtime on rounding mode" $
      -- These values are chosen to tickle the difference between different
      -- rounding modes when rounding to float32, and specifically between
      -- breaking ties to even, to zero, or to +infinity when rounding to
      -- nearest.
      --
      -- Specifically, these are 32-bit integers that are large enough not to be
      -- exactly representable in 32-bit floating-point, whose low-order bits go
      -- through every configuration that rounding behavior is sensitive to
      -- (i.e., nearest float is larger, nearest float is smaller, exactly
      -- between two floats with the previous bit being even, or odd).
      forM_ [ Word32Lit 0x3000000
            , Word32Lit 0x3000001
            , Word32Lit 0x3000002
            , Word32Lit 0x3000003
            , Word32Lit 0x3000004
            , Word32Lit 0x3000005
            , Word32Lit 0x3000006
            , Word32Lit 0x3000007
            , Word32Lit 0x3000008
            , Word32Lit 0x3000009
            , Word32Lit 0x300000A
            , Word32Lit 0x300000B
            , Word32Lit 0x300000C
            , Word32Lit 0x300000D
            , Word32Lit 0x300000E
            ] \val ->
                constant_folding_and_runtime_casts_agree Float32Type val
