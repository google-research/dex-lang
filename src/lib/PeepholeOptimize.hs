-- Copyright 2023 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module PeepholeOptimize (PeepholeOpt (..), peepholeExpr) where

import Data.Word
import Data.Bits
import Data.List
import Data.Bits.Floating
import GHC.Float

import Types.Core
import Types.Primitives
import Name
import IRVariants
import qualified Types.OpNames as P

peepholeExpr :: Expr r n -> Expr r n
peepholeExpr e = case peephole e of
  Just x  -> Atom x
  Nothing -> e
{-# INLINE peepholeExpr #-}

-- === Peephole optimization = undefined

-- These are context-free (no env!) optimizations of expressions and ops that
-- are worth doing unconditionally. Builder calls this automatically in `emit`.

class ToExpr e r => PeepholeOpt (e::E) (r::IR) | e -> r where
  peephole :: e n -> Maybe (Atom r n)

instance PeepholeOpt (Expr r) r where
  peephole = \case
    Atom x -> Just x
    PrimOp op -> peephole op
    Project _ i x  -> case x of
      Con con -> Just case con of
        ProdCon xs             -> xs !! i
        DepPair l _ _ | i == 0 -> l
        DepPair _ r _ | i == 1 -> r
        _ -> error "not a product"
      Stuck _ _ -> Nothing
    Unwrap _ x -> case x of
      Con con -> Just case con of
        NewtypeCon _ x' -> x'
        _ -> error "not a newtype"
      Stuck _ _  -> Nothing
    App    _ _ _ -> Nothing
    TabApp _ _ _ -> Nothing
    Case _ _ _   -> Nothing
    TopApp _ _ _ -> Nothing
    Block _ _    -> Nothing
    TabCon _ _ _ -> Nothing
    ApplyMethod _ _ _ _ -> Nothing
  {-# INLINE peephole #-}

instance PeepholeOpt (PrimOp r) r where
  peephole = \case
    MiscOp op -> peephole op
    BinOp op l r -> peepholeBinOp op l r
    _ -> Nothing
  {-# INLINE peephole #-}

peepholeBinOp :: P.BinOp -> Atom r n -> Atom r n -> Maybe (Atom r n)
peepholeBinOp op x y = case op of
  IAdd -> case (x, y) of
    (Con (Lit x'), y') | getIntLit x' == 0 -> Just y'
    (x', Con (Lit y')) | getIntLit y' == 0 -> Just x'
    (Con (Lit x'), Con (Lit y'))           -> Just $ Con $ Lit $ applyIntBinOp (+) x' y'
    _ -> Nothing
  ISub -> case (x, y) of
    (x', Con (Lit y')) | getIntLit y' == 0 -> Just x'
    (Con (Lit x'), Con (Lit y'))           -> Just $ Con $ Lit $ applyIntBinOp (-) x' y'
    _ -> Nothing
  IMul -> case (x, y) of
    (Con (Lit x'), y') | getIntLit x' == 1 -> Just y'
    (x', Con (Lit y')) | getIntLit y' == 1 -> Just x'
    (Con (Lit x'), Con (Lit y'))           -> Just $ Con $ Lit $ applyIntBinOp (*) x' y'
    _ -> Nothing
  IDiv -> case (x, y) of
    (x', Con (Lit y')) | getIntLit y' == 1 -> Just x'
    _ -> Nothing
  ICmp cop -> case (x, y) of
    (Con (Lit x'), Con (Lit y')) -> Just $ Con $ Lit $ applyIntCmpOp (cmp cop) x' y'
    _ -> Nothing
  FAdd -> case (x, y) of
    (Con (Lit x'), y') | getFloatLit x' == 0 -> Just y'
    (x', Con (Lit y')) | getFloatLit y' == 0 -> Just x'
    (Con (Lit x'), Con (Lit y'))           -> Just $ Con $ Lit $ applyFloatBinOp (+) x' y'
    _ -> Nothing
  FSub -> case (x, y) of
    (x', Con (Lit y')) | getFloatLit y' == 0 -> Just x'
    (Con (Lit x'), Con (Lit y'))           -> Just $ Con $ Lit $ applyFloatBinOp (-) x' y'
    _ -> Nothing
  FMul -> case (x, y) of
    (Con (Lit x'), y') | getFloatLit x' == 1 -> Just y'
    (x', Con (Lit y')) | getFloatLit y' == 1 -> Just x'
    (Con (Lit x'), Con (Lit y'))             -> Just $ Con $ Lit $ applyFloatBinOp (*) x' y'
    _ -> Nothing
  FDiv -> case (x, y) of
    (x', Con (Lit y')) | getFloatLit y' == 1 -> Just x'
    _ -> Nothing
  FCmp cop -> case (x, y) of
    (Con (Lit x'), Con (Lit y')) -> Just $ Con $ Lit $ applyFloatCmpOp (cmp cop) x' y'
    _ -> Nothing
  BOr -> case (x, y) of
    (Con (Lit (Word8Lit x')), Con (Lit (Word8Lit y'))) -> Just $ Con $ Lit $ Word8Lit $ x' .|. y'
    _ -> Nothing
  BAnd -> case (x, y) of
    (Con (Lit (Word8Lit lv)), Con (Lit (Word8Lit rv))) -> Just $ Con $ Lit $ Word8Lit $ lv .&. rv
    _ -> Nothing
  BXor -> Nothing -- TODO
  BShL -> Nothing -- TODO
  BShR -> Nothing -- TODO
  IRem -> Nothing -- TODO
  FPow -> Nothing -- TODO
{-# INLINE peepholeBinOp #-}

instance PeepholeOpt (MiscOp r) r where
  peephole = \case
    CastOp (TyCon (BaseType (Scalar sTy))) (Con (Lit l)) -> case foldCast sTy l of
      Just l' -> Just $ Con $ Lit l'
      Nothing -> Nothing
    ToEnum ty (Con (Lit (Word8Lit tag))) -> case ty of
      TyCon (SumType cases) -> Just $ Con $ SumCon cases (fromIntegral tag) UnitVal
      _ -> error "Ill typed ToEnum"
    SumTag (Con (SumCon _ tag _)) -> Just $ Con $ Lit $ Word8Lit $ fromIntegral tag
    Select p x y -> case p of
      Con (Lit (Word8Lit p')) -> Just if p' /= 0 then x else y
      _ -> Nothing
    _ -> Nothing

foldCast :: ScalarBaseType -> LitVal -> Maybe LitVal
foldCast sTy l = case sTy of
  -- TODO: Check that the casts relating to floating-point agree with the
  -- runtime behavior.  The runtime is given by the `ICastOp` case in
  -- ImpToLLVM.hs.  We should make sure that the Haskell functions here
  -- produce bitwise identical results to those instructions, by adjusting
  -- either this or that as called for.
  -- TODO: Also implement casts that may have unrepresentable results, i.e.,
  -- casting floating-point numbers to smaller floating-point numbers or to
  -- fixed-point.  Both of these necessarily have a much smaller dynamic range.
  Int32Type -> case l of
    Int32Lit  _  -> Just l
    Int64Lit  i  -> Just $ Int32Lit  $ fromIntegral i
    Word8Lit  i  -> Just $ Int32Lit  $ fromIntegral i
    Word32Lit i  -> Just $ Int32Lit  $ fromIntegral i
    Word64Lit i  -> Just $ Int32Lit  $ fromIntegral i
    Float32Lit _ -> Nothing
    Float64Lit _ -> Nothing
    PtrLit   _ _ -> Nothing
  Int64Type -> case l of
    Int32Lit  i  -> Just $ Int64Lit  $ fromIntegral i
    Int64Lit  _  -> Just l
    Word8Lit  i  -> Just $ Int64Lit  $ fromIntegral i
    Word32Lit i  -> Just $ Int64Lit  $ fromIntegral i
    Word64Lit i  -> Just $ Int64Lit  $ fromIntegral i
    Float32Lit _ -> Nothing
    Float64Lit _ -> Nothing
    PtrLit   _ _ -> Nothing
  Word8Type -> case l of
    Int32Lit  i  -> Just $ Word8Lit  $ fromIntegral i
    Int64Lit  i  -> Just $ Word8Lit  $ fromIntegral i
    Word8Lit  _  -> Just l
    Word32Lit i  -> Just $ Word8Lit  $ fromIntegral i
    Word64Lit i  -> Just $ Word8Lit  $ fromIntegral i
    Float32Lit _ -> Nothing
    Float64Lit _ -> Nothing
    PtrLit   _ _ -> Nothing
  Word32Type -> case l of
    Int32Lit  i  -> Just $ Word32Lit $ fromIntegral i
    Int64Lit  i  -> Just $ Word32Lit $ fromIntegral i
    Word8Lit  i  -> Just $ Word32Lit $ fromIntegral i
    Word32Lit _  -> Just l
    Word64Lit i  -> Just $ Word32Lit $ fromIntegral i
    Float32Lit _ -> Nothing
    Float64Lit _ -> Nothing
    PtrLit   _ _ -> Nothing
  Word64Type -> case l of
    Int32Lit  i  -> Just $ Word64Lit $ fromIntegral (fromIntegral i :: Word32)
    Int64Lit  i  -> Just $ Word64Lit $ fromIntegral i
    Word8Lit  i  -> Just $ Word64Lit $ fromIntegral i
    Word32Lit i  -> Just $ Word64Lit $ fromIntegral i
    Word64Lit _  -> Just l
    Float32Lit _ -> Nothing
    Float64Lit _ -> Nothing
    PtrLit   _ _ -> Nothing
  Float32Type -> case l of
    Int32Lit  i  -> Just $ Float32Lit $ fixUlp i $ fromIntegral i
    Int64Lit  i  -> Just $ Float32Lit $ fixUlp i $ fromIntegral i
    Word8Lit  i  -> Just $ Float32Lit $ fromIntegral i
    Word32Lit i  -> Just $ Float32Lit $ fixUlp i $ fromIntegral i
    Word64Lit i  -> Just $ Float32Lit $ fixUlp i $ fromIntegral i
    Float32Lit _ -> Just l
    Float64Lit _ -> Nothing
    PtrLit   _ _ -> Nothing
  Float64Type -> case l of
    Int32Lit  i  -> Just $ Float64Lit $ fromIntegral i
    Int64Lit  i  -> Just $ Float64Lit $ fixUlp i $ fromIntegral i
    Word8Lit  i  -> Just $ Float64Lit $ fromIntegral i
    Word32Lit i  -> Just $ Float64Lit $ fromIntegral i
    Word64Lit i  -> Just $ Float64Lit $ fixUlp i $ fromIntegral i
    Float32Lit f -> Just $ Float64Lit $ float2Double f
    Float64Lit _ -> Just l
    PtrLit   _ _ -> Nothing
  where
    -- When casting an integer type to a floating-point type of lower precision
    -- (e.g., int32 to float32), GHC between 7.8.3 and 9.2.2 (exclusive) rounds
    -- toward zero, instead of rounding to nearest even like everybody else.
    -- See https://gitlab.haskell.org/ghc/ghc/-/issues/17231.
    --
    -- We patch this by manually checking the two adjacent floats to the
    -- candidate answer, and using one of those if the reverse cast is closer
    -- to the original input.
    --
    -- This rounds to nearest.  We round to nearest *even* by considering the
    -- candidates in decreasing order of the number of trailing zeros they
    -- exhibit when cast back to the original integer type.
    fixUlp :: forall a b w. (Num a, Integral a, FiniteBits a, RealFrac b, FloatingBits b w)
      => a -> b -> b
    fixUlp orig candidate = res where
      res = closest $ sortBy moreLowBits [candidate, candidatem1, candidatep1]
      candidatem1 = nextDown candidate
      candidatep1 = nextUp candidate
      closest = minimumBy (\ca cb -> err ca `compare` err cb)
      err cand = absdiff orig (round cand)
      absdiff a b = if a >= b then a - b else b - a
      moreLowBits a b =
        compare (0 - countTrailingZeros (round @b @a a))
                (0 - countTrailingZeros (round @b @a b))

-- === Helpers for function evaluation over fixed-width types ===

applyIntBinOp :: (forall a. (Num a, Integral a) => a -> a -> a) -> LitVal -> LitVal -> LitVal
applyIntBinOp f x y = case (x, y) of
  (Int64Lit  x', Int64Lit  y') -> Int64Lit  $ f x' y'
  (Int32Lit  x', Int32Lit  y') -> Int32Lit  $ f x' y'
  (Word8Lit  x', Word8Lit  y') -> Word8Lit  $ f x' y'
  (Word32Lit x', Word32Lit y') -> Word32Lit $ f x' y'
  (Word64Lit x', Word64Lit y') -> Word64Lit $ f x' y'
  _ -> error "Expected integer atoms"

applyIntCmpOp :: (forall a. (Eq a, Ord a) => a -> a -> Bool) -> LitVal -> LitVal -> LitVal
applyIntCmpOp f x y = boolLit case (x, y) of
  (Int64Lit  x', Int64Lit  y') -> f x' y'
  (Int32Lit  x', Int32Lit  y') -> f x' y'
  (Word8Lit  x', Word8Lit  y') -> f x' y'
  (Word32Lit x', Word32Lit y') -> f x' y'
  (Word64Lit x', Word64Lit y') -> f x' y'
  _ -> error "Expected integer atoms"

applyFloatBinOp :: (forall a. (Num a, Fractional a) => a -> a -> a) -> LitVal -> LitVal -> LitVal
applyFloatBinOp f x y = case (x, y) of
  (Float64Lit x', Float64Lit y') -> Float64Lit $ f x' y'
  (Float32Lit x', Float32Lit y') -> Float32Lit $ f x' y'
  _ -> error "Expected float atoms"

applyFloatCmpOp :: (forall a. (Eq a, Ord a) => a -> a -> Bool) -> LitVal -> LitVal -> LitVal
applyFloatCmpOp f x y = boolLit case (x, y) of
  (Float64Lit x', Float64Lit y') -> f x' y'
  (Float32Lit x', Float32Lit y') -> f x' y'
  _ -> error "Expected float atoms"

boolLit :: Bool -> LitVal
boolLit x = Word8Lit $ fromIntegral $ fromEnum x

cmp :: Ord a => CmpOp -> a -> a -> Bool
cmp = \case
  Less         -> (<)
  Greater      -> (>)
  Equal        -> (==)
  LessEqual    -> (<=)
  GreaterEqual -> (>=)
