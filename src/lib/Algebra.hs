-- Copyright 2020 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleContexts #-}

module Algebra (offsetToE, elemCountE, applyIdxs,
                showPolyC, showSumPolyC) where

-- TODO: remove
import Inference

import Prelude hiding (lookup, sum, pi)
import Control.Monad
import qualified Data.Foldable as F
import Data.Ratio
import Data.Map.Strict hiding (foldl, map)
import Data.Text.Prettyprint.Doc
import Data.List (intersperse)
import Data.Tuple (swap)
import Data.Coerce

import Name
import Syntax
import PPrint
import Builder ( MonadBuilder, iadd, imul, idiv, clampPositive, ptrOffset
               , indexToIntE, indexSetSizeE )

-- MVar is like Var, but it additionally defines Ord. The invariant here is that the variables
-- should never be shadowing, and so it is sufficient to only use the name for equality and
-- order checks, as name equality should imply type equality.
newtype MVar n = MVar (Var n) deriving Show

-- Set of monomials, each multiplied by a constant.
type Constant         = Rational
type PolynomialP mono = Map mono Constant

-- Set of variables, each with its power.
-- Note that some variables appearing in monomials will be index set variables, which
-- we identify with their ordinals.
type Monomial   n     = Map (MVar n) Int
type Polynomial n     = PolynomialP (Monomial n)

-- Clamp represents the expression max(poly, 0).
newtype Clamp n       = Clamp (Polynomial n)           deriving (Show, Eq, Ord)
-- TODO: Make clamps a map of powers!
-- A product of a number of clamps and a monomial.
data ClampMonomial   n = ClampMonomial [Clamp n] (Monomial n) deriving (Show, Eq, Ord)
type ClampPolynomial n = PolynomialP (ClampMonomial n)

-- Polynomials that use the special singleton sumVar inside, with the type of sumVar
-- given by Var bundled in this ADT.
data SumPolynomial      n = SumPolynomial (Polynomial n) (Var n)           deriving (Show)
data SumClampPolynomial n = SumClampPolynomial (ClampPolynomial n) (Var n) deriving (Show)

applyIdxs :: MonadBuilder n m => Atom n -> IndexStructure n l -> m (Atom n)
applyIdxs ptr Empty = return ptr
-- applyIdxs ptr idxs@(Nest ~(Bind i) rest) = do
--   ordinal <- indexToIntE $ Var i
--   offset <- offsetToE idxs ordinal
--   ptr' <- ptrOffset ptr offset
--   applyIdxs ptr' rest

offsetToE :: MonadBuilder n m => IndexStructure n l -> Atom n -> m (Atom n)
offsetToE idxs i = evalSumClampPolynomial (offsets idxs) i

elemCountE :: MonadBuilder n m => IndexStructure n l -> m (Atom n)
elemCountE idxs = case idxs of
  Empty    -> return $ IdxRepVal 1
  Nest b _ -> offsetToE idxs =<< indexSetSizeE (binderType b)

elemCount :: IndexStructure n l -> ClampPolynomial n
elemCount idxs = case idxs of
  Empty -> liftC $ poly [(1, mono [])]
  Nest b _ -> (offsets idxs) `psubstSumVar` (indexSetSize $ binderType b)

offsets :: IndexStructure n l -> SumClampPolynomial n
offsets = undefined
-- offsets idxs = case idxs of
--   -- TODO: not sure about `fromBind` here`
--   Nest b body -> sumC (fromBind "_" b) $ elemCount body
--   _ -> error $ "Not a non-empty index structure " ++ pprint idxs

indexSetSize :: Type n -> ClampPolynomial n
indexSetSize (TC con) = case con of
  UnitType              -> liftC $ toPolynomial $ IdxRepVal 1
  IntRange low high     -> clamp $ toPolynomial high `sub` toPolynomial low
  IndexRange n low high -> case (low, high) of
    -- When one bound is left unspecified, the size expressions are guaranteed
    -- to be non-negative, so we don't have to clamp them.
    (Unlimited, _) -> liftC $ high' -- `sub` 0
    (_, Unlimited) -> (indexSetSize n) `sub` (liftC low')
    -- When both bounds are specified, we may have to clamp to avoid negative terms
    _              -> clamp $ high' `sub` low'
    where
      add1 = add (poly [(1, mono [])])
      -- The unlimited cases should have been handled above
      low' = case low of
        InclusiveLim l -> toPolynomial l
        ExclusiveLim l -> add1 $ toPolynomial l
        Unlimited      -> undefined
      high' = case high of
        InclusiveLim h -> add1 $ toPolynomial h
        ExclusiveLim h -> toPolynomial h
        Unlimited      -> undefined
  PairType l r -> mulC (indexSetSize l) (indexSetSize r)
  _ -> error $ "Not implemented " ++ pprint con
indexSetSize (RecordTy (NoExt types)) = let
  sizes = map indexSetSize (F.toList types)
  one = liftC $ toPolynomial $ IdxRepVal 1
  in foldl mulC one sizes
indexSetSize (VariantTy (NoExt types)) = let
  sizes = map indexSetSize (F.toList types)
  zero = liftC $ toPolynomial $ IdxRepVal 0
  in foldl add zero sizes
indexSetSize ty = error $ "Not implemented " ++ pprint ty

toPolynomial :: Atom n -> Polynomial n
toPolynomial atom = case atom of
  Var v                  -> poly [(1, mono [(v, 1)])]
  Con (Lit (Int64Lit x)) -> fromInt x
  Con (Lit (Int32Lit x)) -> fromInt x
  Con (Lit (Word8Lit x)) -> fromInt x
  Con (IntRangeVal _ _ i) -> toPolynomial i
  -- TODO: Coercions? Unit constructor?
  _ -> unreachable
  where
    fromInt i = poly [((fromIntegral i) % 1, mono [])]
    unreachable = error $ "Unsupported or invalid atom in index set: " ++ pprint atom

-- === Building ===

_evalClampPolynomial :: MonadBuilder n m => ClampPolynomial n -> m (Atom n)
_evalClampPolynomial cp = evalPolynomialP (evalClampMonomial Var) cp

evalSumClampPolynomial :: MonadBuilder n m => SumClampPolynomial n -> Atom n -> m (Atom n)
evalSumClampPolynomial (SumClampPolynomial cp summedVar) a =
  evalPolynomialP (evalClampMonomial varVal) cp
  where varVal v = if MVar v == sumVar summedVar then a else Var v

-- We have to be extra careful here, because we're evaluating a polynomial
-- that we know is guaranteed to return an integral number, but it has rational
-- coefficients. This is why we have to find the least common multiples and do the
-- accumulation over numbers multiplied by that LCM. We essentially do fixed point
-- fractional math here.
evalPolynomialP :: MonadBuilder n m => (mono -> m (Atom n)) -> PolynomialP mono -> m (Atom n)
evalPolynomialP evalMono p = do
  let constLCM = asAtom $ foldl lcm 1 $ fmap (denominator . snd) $ toList p
  monoAtoms <- flip traverse (toList p) $ \(m, c) -> do
    lcmFactor <- constLCM `idiv` (asAtom $ denominator c)
    constFactor <- imul (asAtom $ numerator c) lcmFactor
    imul constFactor =<< evalMono m
  total <- foldM iadd (IdxRepVal 0) monoAtoms
  total `idiv` constLCM
  where
    -- TODO: Check for overflows. We might also want to bail out if the LCM is too large,
    --       because it might be causing overflows due to all arithmetic being shifted.
    asAtom = IdxRepVal . fromInteger

evalMonomial :: MonadBuilder n m => (Var n -> Atom n) -> Monomial n -> m (Atom n)
evalMonomial varVal m = do
  varAtoms <- traverse (\(MVar v, e) -> ipow (varVal v) e) $ toList m
  foldM imul (IdxRepVal 1) varAtoms

evalClampMonomial :: MonadBuilder n m => (Var n -> Atom n) -> ClampMonomial n -> m (Atom n)
evalClampMonomial varVal (ClampMonomial clamps m) = do
  valuesToClamp <- traverse (evalPolynomialP (evalMonomial varVal) . coerce) clamps
  clampsProduct <- foldM imul (IdxRepVal 1) =<< traverse clampPositive valuesToClamp
  mval <- evalMonomial varVal m
  imul clampsProduct mval

ipow :: MonadBuilder n m => Atom n -> Int -> m (Atom n)
ipow x i = foldM imul (IdxRepVal 1) (replicate i x)

-- === Polynomial math ===

mulC :: ClampPolynomial n -> ClampPolynomial n -> ClampPolynomial n
mulC x y = cpoly [(cx * cy, mulMono mx my) | (mx, cx) <- toList x, (my, cy) <- toList y]
  where mulMono (ClampMonomial cx mx) (ClampMonomial cy my) = ClampMonomial (cx ++ cy) (unionWith (+) mx my)

add :: Ord mono => PolynomialP mono -> PolynomialP mono -> PolynomialP mono
add x y = unionWith (+) x y

sub :: Ord mono => PolynomialP mono -> PolynomialP mono -> PolynomialP mono
sub x y = add x (negate <$> y)

sumPolys :: Ord mono => [PolynomialP mono] -> PolynomialP mono
sumPolys = unionsWith (+)

mulConst :: Ord mono => Constant -> PolynomialP mono -> PolynomialP mono
mulConst c p = (*c) <$> p

-- (Lazy) infinite list of powers of p
powersL :: (a -> a -> a) -> a -> a -> [a]
powersL mult e p = e : fmap (mult p) (powersL mult e p)

powersC :: ClampPolynomial n -> [ClampPolynomial n]
powersC = powersL mulC (liftC $ poly [(1, mono [])])

-- Finds a closed form for (\sum_{name = 0}^{(sumVar name) - 1} poly) for given name and polynomial.
-- This is the function that is meant to introduce the type SumPolynomial.
sumC :: Var n -> ClampPolynomial n -> SumClampPolynomial n
sumC = undefined
-- sumC v p = SumClampPolynomial sp v
--   where
--     sp = sumPolys $ fmap (\(m, c) -> mulConst c $ sumMonoC m) $ toList p
--     sumMonoC :: ClampMonomial n -> ClampPolynomial n
--     sumMonoC (ClampMonomial clamps m) = if v `isin` foldMap freeVarsC clamps
--       then error $ "Summation of variables appearing under clamps not implemented yet"
--       else imapMonos (ClampMonomial clamps) sm
--         where (SumPolynomial sm _) = sumMono v m

sumMono :: Var n -> Monomial n -> SumPolynomial n
sumMono v m = flip SumPolynomial v $ case lookup mv m of
  -- TODO: Implement the formula for arbitrary order polynomials
  Nothing -> poly [(1, insert sv 1 c)]
  Just 0  -> error "Each variable appearing in a monomial should have a positive power"
  Just 1  -> poly [(1/2, insert sv 2 c), (-1/2, insert sv 1 c)]
  _       -> error "Not implemented yet!"
  where
    mv = MVar v
    sv = sumVar v
    c = delete mv m

-- Substitutes the sum variable for a given polynomial.
psubstSumVar :: SumClampPolynomial n -> ClampPolynomial n -> ClampPolynomial n
psubstSumVar = undefined
-- psubstSumVar (SumClampPolynomial p v) sp =
--   sumPolys $ fmap (\(cm, c) -> mulConst c $ substNoClamp cm) $ toList p
--   where
--     substNoClamp (ClampMonomial clamps m) =
--       if (dropMVar $ sumVar v) `isin` foldMap freeVarsC clamps
--         then error "Sum variable should not appear under clamps"
--         else imapMonos (\(ClampMonomial clamps' m') -> ClampMonomial (clamps ++ clamps') m') mp
--           where mp = psubstSumVarMono m (coerce $ sumVar v, sp)

-- Substitutes v for sp in m
psubstSumVarMono :: Monomial n -> (Var n, ClampPolynomial n) -> ClampPolynomial n
psubstSumVarMono m (v, sp) = case lookup (MVar v) m of
  Nothing -> liftC $ poly [(1, m)]
  Just 0  -> error "Each variable appearing in a monomial should have a positive power"
  Just n  -> mulC (liftC $ poly [(1, (delete (MVar v) m))]) (powersC sp !! n)

-- === Constructors and singletons ===

poly :: [(Constant, Monomial n)] -> Polynomial n
poly monos = fromListWith (+) $ fmap swap monos

mono :: [(Var n, Int)] -> Monomial n
mono vars = fromListWith (error "Duplicate entries for variable") $ coerce vars

cpoly :: [(Constant, ClampMonomial n)] -> ClampPolynomial n
cpoly cmonos = fromListWith (+) $ fmap swap cmonos

cmono :: [Clamp n] -> Monomial n -> ClampMonomial n
cmono = ClampMonomial

-- === Type classes and helpers ===

-- TODO: make this another case of `MVar`
sumVar :: Var n -> MVar n
sumVar = undefined
-- sumVar (_ :> t) = MVar $ (Name SumName "s" 0) :> t

showMono :: Monomial n -> String
showMono m = concat $ intersperse " " $ fmap (\(n, p) -> asStr $ pretty n <> "^" <> pretty p) $ toList m

showPolyP :: (mono -> String) -> PolynomialP mono -> String
showPolyP mshow p = concat $ intersperse " + " $ fmap (\(m, c) -> show c ++ " " ++ mshow m) $ toList p

showPoly :: Polynomial n -> String
showPoly p = showPolyP showMono p

showSumPolyC :: SumClampPolynomial n -> String
showSumPolyC (SumClampPolynomial cp _) = showPolyC cp

showPolyC :: ClampPolynomial n -> String
showPolyC cp = showPolyP showMonoC cp

showMonoC :: ClampMonomial n -> String
showMonoC (ClampMonomial clamps m) =
  concat $ (fmap (\(Clamp p) -> "max(0, " ++ showPoly p ++ ")") clamps) ++ [showMono m]

instance Eq (MVar n) where
  (MVar (AnnVar n t)) == (MVar (AnnVar n' t'))
      | n == n'   = undefined -- if t == t' then True else mVarTypeErr
      | otherwise = False

mVarTypeErr :: a
mVarTypeErr = error "MVars with equal names, but different types"

instance Ord (MVar n) where
  (MVar (AnnVar n t)) <= (MVar (AnnVar n' t'))
      | n == n'   = undefined -- if t == t' then True else mVarTypeErr
      | otherwise = n <= n'

instance Pretty (MVar n) where
  pretty (MVar v) = pretty v


-- -- We deliberately skip the variables in the types, since we treat all variables
-- -- with index set types as their ordinals.
-- freeVarsM :: Monomial n -> Env Type
-- freeVarsM m = foldMap (varAsEnv . coerce) $ keys m

-- freeVarsP :: Polynomial n -> Env Type
-- freeVarsP p = foldMap freeVarsM $ keys p

-- freeVarsC :: Clamp n -> Env Type
-- freeVarsC (Clamp p) = freeVarsP p

imapMonos :: (Ord mono, Ord mono') => (mono -> mono') -> PolynomialP mono -> PolynomialP mono'
imapMonos = mapKeysWith (error "Expected an injective map")

liftC :: Polynomial n -> ClampPolynomial n
liftC = imapMonos $ cmono []

clamp :: Polynomial n -> ClampPolynomial n
clamp p = cpoly [(1, cmono [Clamp p] (mono []))]

dropMVar :: MVar n -> Var n
dropMVar = coerce
