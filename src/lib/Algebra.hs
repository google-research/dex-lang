-- Copyright 2020 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module Algebra (Constant, Monomial, Polynomial,
                elemCount, offsetTo,
                evalPolynomial, evalSumPolynomial,
                showPoly) where

import Prelude hiding (lookup, sum, pi)
import Control.Monad
import Data.Ratio
import Data.Map.Strict hiding (foldl)
import Data.Text.Prettyprint.Doc
import Data.List (intersperse)
import Data.Coerce

import Env
import Syntax
import PPrint
import Embed (MonadEmbed, iadd, imul, idiv)

-- MVar is like Var, but it additionally defines Ord. The invariant here is that the variables
-- should never be shadowing, and so it is sufficient to only use the name for equality and
-- order checks, as name equality should imply type equality.
newtype MVar = MVar Var deriving Show

type Constant   = Rational
type Monomial   = Map MVar Int           -- each variable with its power
type Polynomial = Map Monomial Constant  -- set of monomials times a constant

data SumPolynomial = SumPolynomial Polynomial Var

elemCount :: ScalarTableType -> Polynomial
elemCount t = case t of
  BaseTy _  -> poly [(1, mono [])]
  TabTy v _ -> (offsetTo t) `psubstSumVar` (indexSetSize $ varType v)
  _ -> error $ "Not a ScalarTableType: " ++ pprint t

offsetTo :: ScalarTableType -> SumPolynomial
offsetTo t = case t of
  TabTy v body -> sum v $ elemCount body
  _ -> error $ "Not a non-scalar ScalarTableType: " ++ pprint t

-- TODO: Reuse the implmentation from Embed once clamps are supported
indexSetSize :: Type -> Polynomial
indexSetSize (TC con) = case con of
  IntRange low high -> toPolynomial high `sub` toPolynomial low -- TODO: Clamp!
  IndexRange n low high -> high' `sub` low' -- TODO: Clamp!
    where
      low' = case low of
        Unlimited -> mempty
        _         -> error "Index ranges with lower bounds are not supported"
      high' = case high of
        InclusiveLim l -> add (toPolynomial l) (poly [(1, mono [])])
        ExclusiveLim _ -> error "Exclusive limits not supported"
        Unlimited      -> indexSetSize n
  _ -> error $ "Not implemented " ++ pprint con
indexSetSize ty = error $ "Not implemented " ++ pprint ty

toPolynomial :: Atom -> Polynomial
toPolynomial atom = case atom of
  Var v -> poly [(1, mono [(v, 1)])]
  Con con -> case con of
    Lit (IntLit l) -> poly [((toInteger l) % 1, mono [])]
    _ -> unreachable
  _ -> unreachable
  where unreachable = error $ "Unsupported or invalid atom in index set: " ++ pprint atom

-- === Embedding ===

evalPolynomial :: MonadEmbed m => Polynomial -> m Atom
evalPolynomial p = eval p Var

evalSumPolynomial :: MonadEmbed m => SumPolynomial -> Atom -> m Atom
evalSumPolynomial (SumPolynomial p summedVar) a = eval p varVal
  where varVal v = if MVar v == sumVar summedVar then a else Var v

-- We have to be extra careful here, because we're evaluating a polynomial
-- that we know is guaranteed to return an integral number, but it has rational
-- coefficients. This is why we have to find the least common multiples and do the
-- accumulation over numbers multiplied by that LCM. We essentially do fixed point
-- fractional math here.
eval :: MonadEmbed m => Polynomial -> (Var -> Atom) -> m Atom
eval p varVal = do
  let constLCM = asAtom $ foldl lcm 1 $ fmap (denominator . snd) $ toList p
  monoAtoms <- flip traverse (toList p) $ \(m, c) -> do
    lcmFactor <- constLCM `idiv` (asAtom $ denominator c)
    constFactor <- imul (asAtom $ numerator c) lcmFactor
    imul constFactor =<< evalMonomialSum m
  total <- foldM iadd (IntVal 0) monoAtoms
  total `idiv` constLCM
  where
    -- TODO: Check for overflows. We might also want to bail out if the LCM is too large,
    --       because it might be causing overflows due to all arithmetic being shifted.
    asAtom = IntVal . fromInteger
    evalMonomialSum m = do
      varAtoms <- traverse (\(MVar v, e) -> ipow (varVal v) e) $ toList m
      foldM imul (IntVal 1) varAtoms

ipow :: MonadEmbed m => Atom -> Int -> m Atom
ipow x i = foldM imul (IntVal 1) (replicate i x)

-- === Polynomial math ===

mul :: Polynomial -> Polynomial -> Polynomial
mul x y = poly [(cx * cy, mulMono mx my) | (mx, cx) <- toList x, (my, cy) <- toList y]
  where mulMono = unionWith (+) -- + because monomials store variable powers

add :: Polynomial -> Polynomial -> Polynomial
add x y = unionWith (+) x y

sub :: Polynomial -> Polynomial -> Polynomial
sub x y = add x (negate <$> y)

sumPolys :: [Polynomial] -> Polynomial
sumPolys = unionsWith (+)

mulConst :: Constant -> Polynomial -> Polynomial
mulConst c p = (*c) <$> p

-- Finds a closed form for (\sum_{name = 0}^{(sumVar name) - 1} poly) for given name and polynomial.
-- This is the function that is meant to introduce the type SumPolynomial.
sum :: Var -> Polynomial -> SumPolynomial
sum v p = SumPolynomial sp v
  where
    sp = sumPolys $ fmap (\(m, c) -> mulConst c $ sumMono m) $ toList p
    mv = MVar v
    sv = sumVar v
    -- TODO: Implement the formula for arbitrary order polynomials
    sumMono m = case lookup mv m of
      Nothing -> poly [(1, insert sv 1 c)]
      Just 0  -> error "Each variable appearing in a monomial should have a positive power"
      Just 1  -> poly [(1/2, insert sv 2 c), (-1/2, insert sv 1 c)]
      _       -> error "Not implemented yet!"
      where c = delete mv m

-- Substitutes the sum variable for a given polynomial.
-- One of the eliminators for SumPolynomial.
psubstSumVar :: SumPolynomial -> Polynomial -> Polynomial
psubstSumVar (SumPolynomial p v) sp = psubst p (coerce $ sumVar v, sp)

-- (Lazy) infinite list of powers of p
powers :: Polynomial -> [Polynomial]
powers p = poly [(1, mono [])] : fmap (mul p) (powers p)

-- Substitutes v for sp in p
psubst :: Polynomial -> (Var, Polynomial) -> Polynomial
psubst p env = sumPolys $ fmap (\(m, c) -> mulConst c $ psubstMono m env) $ toList p

-- Substitutes v for sp in m
psubstMono :: Monomial -> (Var, Polynomial) -> Polynomial
psubstMono m (v, sp) = case lookup (MVar v) m of
  Nothing -> poly [(1, m)]
  Just 0  -> error "Each variable appearing in a monomial should have a positive power"
  Just n  -> mul (poly [(1, (delete (MVar v) m))]) (powers sp !! n)

-- === Constructors and singletons ===

poly :: [(Constant, Monomial)] -> Polynomial
poly monos = fromListWith (+) $ fmap swap monos
  where swap (x, y) = (y, x)

mono :: [(Var, Int)] -> Monomial
mono vars = fromListWith (error "Duplicate entries for variable") $ coerce vars

-- === Type classes and helpers ===

sumVar :: Var -> MVar
sumVar (_ :> t) = MVar $ (Name SumName "s" 0) :> t

showMono :: Monomial -> String
showMono m = concat $ intersperse " " $ fmap (\(n, p) -> asStr $ pretty n <> "^" <> pretty p) $ toList m

showPoly :: Polynomial -> String
showPoly p = concat $ intersperse " + " $ fmap (\(m, c) -> show c ++ " " ++ showMono m) $ toList p

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
