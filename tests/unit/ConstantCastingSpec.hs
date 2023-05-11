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
import Name
import Optimize
import Runtime
import IRVariants
import TopLevel
import Types.Core
import Types.Imp
import Types.Primitives
import Types.Source

castOp :: ScalarBaseType -> (SAtom n) -> PrimOp SimpIR n
castOp ty x = MiscOp $ CastOp (BaseTy (Scalar ty)) x

castLam :: EnvExtender m => ScalarBaseType -> ScalarBaseType -> m n (SLam n)
castLam fromTy toTy = do
  withFreshBinder noHint (BaseTy (Scalar fromTy)) \x -> do
    body <- exprToBlock $ PrimOp $ castOp toTy $ Var $ binderName x
    return $ LamExpr (Nest x Empty) body

exprToBlock :: EnvReader m => SExpr n -> m n (SBlock n)
exprToBlock expr = do
  liftBuilder $ buildBlock $ do
    v <- emit $ sink expr
    return $ Var v

compile :: (Topper m, Mut n)
  => ScalarBaseType -> ScalarBaseType -> m n LLVMCallable
compile fromTy toTy = do
  sLam <- liftEnvReaderM $ castLam fromTy toTy
  compileTopLevelFun (EntryFunCC CUDANotRequired) sLam >>= packageLLVMCallable

arbLitVal :: ScalarBaseType -> Gen LitVal
arbLitVal ty = case ty of
  Int64Type   -> Int64Lit   <$> arbitrary
  Int32Type   -> Int32Lit   <$> arbitrary
  Word64Type  -> Word64Lit  <$> arbitrary
  Word32Type  -> Word32Lit  <$> arbitrary
  Word8Type   -> Word8Lit   <$> arbitrary
  Float64Type -> Float64Lit <$> arbitrary
  Float32Type -> Float32Lit <$> arbitrary

constant_folding_and_runtime_casts_agree :: LLVMCallable
  -> ScalarBaseType -> LitVal -> IO ()
constant_folding_and_runtime_casts_agree llvmFunc toTy lit =
  case foldCast toTy lit of
    Nothing -> return ()
    Just folded -> do
      ~[evaled] <- callEntryFun llvmFunc [lit]
      -- The failure message will list `evaled` as "expected" and `folded` as "got"
      folded `shouldBe` evaled

spec :: Spec
spec = do
  let cfg = EvalConfig LLVM [LibBuiltinPath] Nothing Nothing Nothing Optimize PrintCodegen
  -- or just initTopState, to always compile the prelude during unit tests?
  init_env <- runIO loadCache
  describe "constant-folding casts" do
    forM_ [ Int64Type, Int32Type, Word8Type, Word32Type
          , Word64Type, Float64Type, Float32Type] \fromTy ->
      forM_ [ Int64Type, Int32Type, Word8Type, Word32Type
            , Word64Type, Float64Type, Float32Type] \toTy -> do
        llvmFunc <- runIO $ fst <$> runTopperM cfg init_env (compile fromTy toTy)
        -- TODO: We'd really like to run 10,000 or 1,000,000 examples here, but
        -- taking 500 as a compromise between test suite speed and test
        -- coverage.
        -- I ran this offline with 10,000 before checking in, and it passed.
        modifyMaxSuccess (const 500)
          $ prop ("agrees with runtime when casting from "
                  ++ show fromTy ++ " to " ++ show toTy)
          $ forAll (arbLitVal fromTy)
          $ \lit -> constant_folding_and_runtime_casts_agree llvmFunc toTy lit
    llvm_w32_f32 <- runIO $ fst <$> runTopperM cfg init_env
      (compile Word32Type Float32Type)
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
                constant_folding_and_runtime_casts_agree llvm_w32_f32 Float32Type val
    llvm_w64_f64 <- runIO $ fst <$> runTopperM cfg init_env
      (compile Word64Type Float64Type)
    it "rounds to nearest even" $
      -- This particular literal was found by QuickCheck as a counter-example
      -- where a previous version of `foldCast.fixUlp` did not round to nearest
      -- even correctly.
      constant_folding_and_runtime_casts_agree llvm_w64_f64 Float64Type $
        Word64Lit 10633092062366456832
