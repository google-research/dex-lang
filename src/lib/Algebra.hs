-- Copyright 2020 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module Algebra (offsetToE, elemCountE, applyIdxs,
                showPolyC, showSumPolyC) where

import Prelude hiding (lookup, sum, pi)
import Control.Monad
import qualified Data.Foldable as F
import Data.Ratio
import Data.Map.Strict hiding (foldl, map)
import Data.Text.Prettyprint.Doc
import Data.List (intersperse)
import Data.Tuple (swap)
import Data.Coerce

import Env
import LabeledItems
import Syntax
import PPrint
import Builder ( MonadBuilder, iadd, imul, idiv, clampPositive, ptrOffset
               , indexToIntE, indexSetSizeE )

-- MVar is like Var, but it additionally defines Ord. The invariant here is that the variables
-- should never be shadowing, and so it is sufficient to only use the name for equality and
-- order checks, as name equality should imply type equality.
newtype MVar = MVar Var deriving Show

-- Set of monomials, each multiplied by a constant.
type Constant         = Rational
type PolynomialP mono = Map mono Constant

-- Set of variables, each with its power.
-- Note that some variables appearing in monomials will be index set variables, which
-- we identify with their ordinals.
type Monomial         = Map MVar Int
type Polynomial       = PolynomialP Monomial

-- Clamp represents the expression max(poly, 0).
newtype Clamp         = Clamp Polynomial               deriving (Show, Eq, Ord)
-- TODO: Make clamps a map of powers!
-- A product of a number of clamps and a monomial.
data ClampMonomial    = ClampMonomial [Clamp] Monomial deriving (Show, Eq, Ord)
type ClampPolynomial  = PolynomialP ClampMonomial

-- Polynomials that use the special singleton sumVar inside, with the type of sumVar
-- given by Var bundled in this ADT.
data SumPolynomial      = SumPolynomial Polynomial Var           deriving (Show, Eq)
data SumClampPolynomial = SumClampPolynomial ClampPolynomial Var deriving (Show, Eq)

applyIdxs :: MonadBuilder m => Atom -> IndexStructure -> m Atom
applyIdxs ptr Empty = return ptr
applyIdxs ptr idxs@(Nest ~(Bind i) rest) = do
  ordinal <- indexToIntE $ Var i
  offset <- offsetToE idxs ordinal
  ptr' <- ptrOffset ptr offset
  applyIdxs ptr' rest

offsetToE :: MonadBuilder m => IndexStructure -> Atom -> m Atom
offsetToE idxs i = evalSumClampPolynomial (offsets idxs) i

elemCountE :: MonadBuilder m => IndexStructure -> m Atom
elemCountE idxs = case idxs of
  Empty    -> return $ IdxRepVal 1
  Nest b _ -> offsetToE idxs =<< indexSetSizeE (binderType b)

elemCount :: IndexStructure -> ClampPolynomial
elemCount idxs = case idxs of
  Empty -> liftC $ poly [(1, mono [])]
  Nest b _ -> (offsets idxs) `psubstSumVar` (indexSetSize $ binderType b)

offsets :: IndexStructure -> SumClampPolynomial
offsets idxs = case idxs of
  -- TODO: not sure about `fromBind` here`
  Nest b body -> sumC (fromBind "_" b) $ elemCount body
  _ -> error $ "Not a non-empty index structure " ++ pprint idxs

indexSetSize :: Type -> ClampPolynomial
indexSetSize (TC con) = case con of
  ProdType tys          -> foldl mulC (liftC $ toPolynomial $ IdxRepVal 1) $
    indexSetSize <$> F.toList tys
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

toPolynomial :: Atom -> Polynomial
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

_evalClampPolynomial :: MonadBuilder m => ClampPolynomial -> m Atom
_evalClampPolynomial cp = evalPolynomialP (evalClampMonomial Var) cp

evalSumClampPolynomial :: MonadBuilder m => SumClampPolynomial -> Atom -> m Atom
evalSumClampPolynomial (SumClampPolynomial cp summedVar) a =
  evalPolynomialP (evalClampMonomial varVal) cp
  where varVal v = if MVar v == sumVar summedVar then a else Var v

-- We have to be extra careful here, because we're evaluating a polynomial
-- that we know is guaranteed to return an integral number, but it has rational
-- coefficients. This is why we have to find the least common multiples and do the
-- accumulation over numbers multiplied by that LCM. We essentially do fixed point
-- fractional math here.
evalPolynomialP :: MonadBuilder m => (mono -> m Atom) -> PolynomialP mono -> m Atom
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

evalMonomial :: MonadBuilder m => (Var -> Atom) -> Monomial -> m Atom
evalMonomial varVal m = do
  varAtoms <- traverse (\(MVar v, e) -> ipow (varVal v) e) $ toList m
  foldM imul (IdxRepVal 1) varAtoms

evalClampMonomial :: MonadBuilder m => (Var -> Atom) -> ClampMonomial -> m Atom
evalClampMonomial varVal (ClampMonomial clamps m) = do
  valuesToClamp <- traverse (evalPolynomialP (evalMonomial varVal) . coerce) clamps
  clampsProduct <- foldM imul (IdxRepVal 1) =<< traverse clampPositive valuesToClamp
  mval <- evalMonomial varVal m
  imul clampsProduct mval

ipow :: MonadBuilder m => Atom -> Int -> m Atom
ipow x i = foldM imul (IdxRepVal 1) (replicate i x)

-- === Polynomial math ===

mulC :: ClampPolynomial -> ClampPolynomial -> ClampPolynomial
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

powersC :: ClampPolynomial -> [ClampPolynomial]
powersC = powersL mulC (liftC $ poly [(1, mono [])])

-- Finds a closed form for (\sum_{name = 0}^{(sumVar name) - 1} poly) for given name and polynomial.
-- This is the function that is meant to introduce the type SumPolynomial.
sumC :: Var -> ClampPolynomial -> SumClampPolynomial
sumC v p = SumClampPolynomial sp v
  where
    sp = sumPolys $ fmap (\(m, c) -> mulConst c $ sumMonoC m) $ toList p
    sumMonoC :: ClampMonomial -> ClampPolynomial
    sumMonoC (ClampMonomial clamps m) = if v `isin` foldMap freeVarsC clamps
      then error $ "Summation of variables appearing under clamps not implemented yet"
      else imapMonos (ClampMonomial clamps) sm
        where (SumPolynomial sm _) = sumMono v m

sumMono :: Var -> Monomial -> SumPolynomial
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
psubstSumVar :: SumClampPolynomial -> ClampPolynomial -> ClampPolynomial
psubstSumVar (SumClampPolynomial p v) sp =
  sumPolys $ fmap (\(cm, c) -> mulConst c $ substNoClamp cm) $ toList p
  where
    substNoClamp (ClampMonomial clamps m) =
      if (dropMVar $ sumVar v) `isin` foldMap freeVarsC clamps
        then error "Sum variable should not appear under clamps"
        else imapMonos (\(ClampMonomial clamps' m') -> ClampMonomial (clamps ++ clamps') m') mp
          where mp = psubstSumVarMono m (coerce $ sumVar v, sp)

-- Substitutes v for sp in m
psubstSumVarMono :: Monomial -> (Var, ClampPolynomial) -> ClampPolynomial
psubstSumVarMono m (v, sp) = case lookup (MVar v) m of
  Nothing -> liftC $ poly [(1, m)]
  Just 0  -> error "Each variable appearing in a monomial should have a positive power"
  Just n  -> mulC (liftC $ poly [(1, (delete (MVar v) m))]) (powersC sp !! n)

-- === Constructors and singletons ===

poly :: [(Constant, Monomial)] -> Polynomial
poly monos = fromListWith (+) $ fmap swap monos

mono :: [(Var, Int)] -> Monomial
mono vars = fromListWith (error "Duplicate entries for variable") $ coerce vars

cpoly :: [(Constant, ClampMonomial)] -> ClampPolynomial
cpoly cmonos = fromListWith (+) $ fmap swap cmonos

cmono :: [Clamp] -> Monomial -> ClampMonomial
cmono = ClampMonomial

-- === Type classes and helpers ===

sumVar :: Var -> MVar
sumVar (_ :> t) = MVar $ (Name SumName "s" 0) :> t

showMono :: Monomial -> String
showMono m = concat $ intersperse " " $ fmap (\(n, p) -> docAsStr $ pretty n <> "^" <> pretty p) $ toList m

showPolyP :: (mono -> String) -> PolynomialP mono -> String
showPolyP mshow p = concat $ intersperse " + " $ fmap (\(m, c) -> show c ++ " " ++ mshow m) $ toList p

showPoly :: Polynomial -> String
showPoly p = showPolyP showMono p

showSumPolyC :: SumClampPolynomial -> String
showSumPolyC (SumClampPolynomial cp _) = showPolyC cp

showPolyC :: ClampPolynomial -> String
showPolyC cp = showPolyP showMonoC cp

showMonoC :: ClampMonomial -> String
showMonoC (ClampMonomial clamps m) =
  concat $ (fmap (\(Clamp p) -> "max(0, " ++ showPoly p ++ ")") clamps) ++ [showMono m]

instance Eq MVar where
  (MVar (n :> t)) == (MVar (n' :> t')) | n == n'   = if t == t' then True else mVarTypeErr
                                       | otherwise = False

mVarTypeErr :: a
mVarTypeErr = error "MVars with equal names, but different types"

instance Ord MVar where
  (MVar (n :> t)) <= (MVar (n' :> t')) | n == n'   = if t == t' then True else mVarTypeErr
                                       | otherwise = n <= n'

instance Pretty MVar where
  pretty (MVar v) = pretty v


-- We deliberately skip the variables in the types, since we treat all variables
-- with index set types as their ordinals.
freeVarsM :: Monomial -> Env Type
freeVarsM m = foldMap (varAsEnv . coerce) $ keys m

freeVarsP :: Polynomial -> Env Type
freeVarsP p = foldMap freeVarsM $ keys p

freeVarsC :: Clamp -> Env Type
freeVarsC (Clamp p) = freeVarsP p

imapMonos :: (Ord mono, Ord mono') => (mono -> mono') -> PolynomialP mono -> PolynomialP mono'
imapMonos = mapKeysWith (error "Expected an injective map")

liftC :: Polynomial -> ClampPolynomial
liftC = imapMonos $ cmono []

clamp :: Polynomial -> ClampPolynomial
clamp p = cpoly [(1, cmono [Clamp p] (mono []))]

dropMVar :: MVar -> Var
dropMVar = coerce
