-- Copyright 2020 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE UndecidableInstances #-}

module Algebra (
  Polynomial, ClampPolynomial, PolyName, emitCPoly,
  emptyMonomial, poly, mono, liftC, sumC, psubst,
  liftPoly, indexSetSizeCPoly, showPoly, showPolyC) where

import Prelude hiding (lookup, sum, pi)
import Control.Monad
import Data.Functor
import qualified Data.Foldable as F
import Data.Ratio
import Data.Map.Strict hiding (foldl, map)
import Data.Text.Prettyprint.Doc
import Data.List (intersperse)
import Data.Tuple (swap)
import Data.Coerce

import Builder hiding (sub, add)
import LabeledItems
import Syntax
import Type
import Name
import Err

type PolyName = Name AtomNameC
type PolyBinder = NameBinder AtomNameC

-- Set of monomials, each multiplied by a constant.
type Constant         = Rational
newtype PolynomialP (mono::E) (n::S) =
  Polynomial { fromPolynomial :: Map (mono n) Constant }
  deriving (Show, Eq, Ord)

-- Set of variables, each with its power.
data Monomial n = Monomial { fromMonomial :: Map (PolyName n) Int }
                  deriving (Show, Eq, Ord)
type Polynomial = PolynomialP Monomial

-- Clamp represents the expression max(poly, 0).
newtype Clamp (n::S) = Clamp (Polynomial n)
        deriving (Show, Eq, Ord, HoistableE, SinkableE, AlphaEqE)

-- TODO: Make clamps a map of powers!
-- A product of a number of clamps and a monomial.
data ClampMonomial   (n::S) = ClampMonomial [Clamp n] (Monomial n) deriving (Show, Eq, Ord)
type ClampPolynomial = PolynomialP ClampMonomial :: E

-- === Polynomial math ===

mulC :: ClampPolynomial n-> ClampPolynomial n -> ClampPolynomial n
mulC (Polynomial x) (Polynomial y) =
  cpoly [ (cx * cy, mulMono mx my)
        | (mx, cx) <- toList x, (my, cy) <- toList y]
  where mulMono (ClampMonomial cx (Monomial mx))
                (ClampMonomial cy (Monomial my)) =
          ClampMonomial (cx ++ cy) (Monomial $ unionWith (+) mx my)

add :: OrdE mono => PolynomialP mono n -> PolynomialP mono n -> PolynomialP mono n
add x y = Polynomial $ unionWith (+) (fromPolynomial x) (fromPolynomial y)

sub :: OrdE mono => PolynomialP mono n -> PolynomialP mono n -> PolynomialP mono n
sub x y = add x (Polynomial $ negate <$> fromPolynomial y)

sumPolys :: OrdE mono => [PolynomialP mono n] -> PolynomialP mono n
sumPolys ps = Polynomial $ unionsWith (+) $ map fromPolynomial ps

mulConst :: OrdE mono => Constant -> PolynomialP mono n -> PolynomialP mono n
mulConst c (Polynomial p) = Polynomial $ (*c) <$> p

-- (Lazy) infinite list of powers of p
powersL :: (a -> a -> a) -> a -> a -> [a]
powersL mult e p = e : fmap (mult p) (powersL mult e p)

powersC :: ClampPolynomial n -> [ClampPolynomial n]
powersC p = coerce $ powersL mulC (liftC $ poly [(1, mono [])]) p

-- evaluates `\sum_{i=0}^(lim-1) p`
sumC :: PolyName n -> Abs PolyBinder ClampPolynomial n -> ClampPolynomial n
sumC lim (Abs i p) = sumPolys polys
  where polys = (toList $ fromPolynomial p) <&> \(m, c) ->
                  mulConst c $ sumMonoC lim (Abs i m)

sumMonoC :: PolyName n -> Abs PolyBinder ClampMonomial n -> ClampPolynomial n
sumMonoC lim (Abs b (ClampMonomial clamps m)) =
  case hoist b (ListE clamps) of
    HoistFailure _ ->
      error $ "Summation of variables appearing under clamps not implemented yet"
    HoistSuccess (ListE clamps') ->
      imapMonos (ClampMonomial clamps') $ sumMono lim (Abs b m)

sumMono :: PolyName n -> Abs PolyBinder Monomial n -> Polynomial n
sumMono lim (Abs b (Monomial m)) = case lookup (binderName b) m of
  -- TODO: Implement the formula for arbitrary order polynomials
  Nothing -> poly [(1, Monomial $ insert lim 1 c)]
  Just 0  -> error "Each variable appearing in a monomial should have a positive power"
  Just 1  -> poly [(1/2, Monomial $ insert lim 2 c), (-1/2, Monomial $ insert lim 1 c)]
  _       -> error "Not implemented yet!"
  where
    c = fromMonomial $ ignoreHoistFailure $ hoist b $  -- failure impossible
          Monomial $ delete (binderName b) m

psubst :: Abs PolyBinder ClampPolynomial n -> ClampPolynomial n -> ClampPolynomial n
psubst (Abs b (Polynomial p)) x = sumPolys ps
  where
    ps = toList p <&> \(cm, c) -> mulConst c $ substNoClamp cm
    substNoClamp (ClampMonomial clamps m) =
      case hoist b (ListE clamps) of
        HoistFailure _ -> error "Sum variable should not appear under clamps"
        HoistSuccess (ListE clampsHoisted) ->
          imapMonos (\(ClampMonomial clamps' m') -> ClampMonomial (clampsHoisted ++ clamps') m') mp
          where mp = psubstMono (Abs b m) x

psubstMono :: Abs PolyBinder Monomial n -> ClampPolynomial n -> ClampPolynomial n
psubstMono (Abs b (Monomial m)) x = case lookup (binderName b) m of
  Nothing -> liftC $ poly [(1, m')]
    where m' = ignoreHoistFailure $ hoist b $ Monomial m
  Just 0  -> error "Each variable appearing in a monomial should have a positive power"
  Just n  -> mulC (liftC $ poly [(1, m')]) (powersC x !! n)
    where m' = ignoreHoistFailure $ hoist b $ Monomial $ delete (binderName b) m

-- === Constructors and singletons ===

poly :: [(Constant, Monomial n)] -> Polynomial n
poly monos = Polynomial $ fromListWith (+) $ fmap swap monos

mono :: [(PolyName n, Int)] -> Monomial n
mono vars = Monomial $ fromListWith (error "Duplicate entries for variable") vars

cpoly :: [(Constant, ClampMonomial n)] -> ClampPolynomial n
cpoly cmonos = Polynomial $ fromListWith (+) $ fmap swap cmonos

cmono :: [Clamp n] -> Monomial n -> ClampMonomial n
cmono = ClampMonomial

onePoly :: Polynomial n
onePoly = poly [(1, mono [])]

zeroPoly :: Polynomial n
zeroPoly = poly []

-- === Type classes and helpers ===

showMono :: Monomial n -> String
showMono (Monomial m) =
  concat $ intersperse " " $ fmap (\(n, p) -> docAsStr $ pretty n <> "^" <> pretty p) $ toList m

showPolyP :: (mono n -> String) -> PolynomialP mono n -> String
showPolyP mshow (Polynomial p) =
  concat $ intersperse " + " $ fmap (\(m, c) -> show c ++ " " ++ mshow m) $ toList p

showPoly :: Polynomial n -> String
showPoly p = showPolyP showMono p

showPolyC :: ClampPolynomial n -> String
showPolyC cp = showPolyP showMonoC cp

showMonoC :: ClampMonomial n -> String
showMonoC (ClampMonomial clamps m) =
  concat $ (fmap (\(Clamp p) -> "max(0, " ++ showPoly p ++ ")") clamps) ++ [showMono m]

imapMonos :: (OrdE mono, OrdE mono') => (mono n -> mono' n')
          -> PolynomialP mono n -> PolynomialP mono' n'
imapMonos f (Polynomial m) =
  Polynomial $ mapKeysWith (error "Expected an injective map") f m

emptyMonomial :: ClampMonomial n
emptyMonomial = cmono [] $ mono []

liftPoly :: mono n -> PolynomialP mono n
liftPoly m = Polynomial $ singleton m (fromInteger 1)

liftC :: Polynomial n -> ClampPolynomial n
liftC = imapMonos $ cmono []

clamp :: Polynomial n -> ClampPolynomial n
clamp p = cpoly [(1, cmono [Clamp p] (mono []))]

-- === index set size as a clamped polymonial ===

-- TODO: figure out what to do here when we make index sets a user-definable
-- thing
indexSetSizeCPoly :: EnvReader m => Type n -> m n (ClampPolynomial n)
indexSetSizeCPoly (TC con) = case con of
  ProdType tys -> do
    sizes <- mapM indexSetSizeCPoly (F.toList tys)
    return $ foldl mulC (liftC onePoly) sizes
  IntRange low high     -> do
    low'  <- toPolynomial low
    high' <- toPolynomial high
    return $ clamp $ high' `sub` low'
  IndexRange n low high -> case (low, high) of
    -- When one bound is left unspecified, the size expressions are guaranteed
    -- to be non-negative, so we don't have to clamp them.
    (Unlimited, _) -> liftC <$> mkHigh -- `sub` 0
    (_, Unlimited) -> do
      n' <- indexSetSizeCPoly n
      low' <- liftC <$> mkLow
      return $ n' `sub` low'
    -- When both bounds are specified, we may have to clamp to avoid negative terms
    _ -> do
      high' <- mkHigh
      low'  <- mkLow
      return $ clamp $ high' `sub` low'
    where
      add1 = add (poly [(1, mono [])])
      -- The unlimited cases should have been handled above
      mkLow = case low of
        InclusiveLim l -> toPolynomial l
        ExclusiveLim l -> add1 <$> toPolynomial l
        Unlimited      -> error "unreachable"
      mkHigh = case high of
        InclusiveLim h -> add1 <$> toPolynomial h
        ExclusiveLim h -> toPolynomial h
        Unlimited      -> error "unreachable"
  _ -> error $ "Not implemented " ++ pprint con
indexSetSizeCPoly (RecordTy (NoExt types)) = do
  sizes <- mapM indexSetSizeCPoly (F.toList types)
  return $ foldl mulC (liftC onePoly) sizes
indexSetSizeCPoly (VariantTy (NoExt types)) = do
  sizes <- mapM indexSetSizeCPoly (F.toList types)
  return $ foldl add (liftC zeroPoly) sizes
indexSetSizeCPoly ty = error $ "Not implemented " ++ pprint ty

toPolynomial :: EnvReader m => Atom n -> m n (Polynomial n)
toPolynomial atom = case atom of
  -- XXX: here, we expect the type of `v` to be either `IdxRepTy` or
  -- an index set. But we should check it.
  Var v -> return $ poly [(1, mono [(v, 1)])]
  IdxRepVal x -> return $ fromInt x
  Con (IntRangeVal _ _ i) -> toPolynomial i
  -- TODO: Coercions? Unit constructor?
  _ -> unreachable
  where
    fromInt i = poly [((fromIntegral i) % 1, mono [])]
    unreachable = error $ "Unsupported or invalid atom in index set: " ++ pprint atom


-- === polynomials to Core expressions ===

emitCPoly :: (Emits n, Builder m) => ClampPolynomial n -> m n (Atom n)
emitCPoly = emitPolynomialP emitClampMonomial

-- We have to be extra careful here, because we're evaluating a polynomial
-- that we know is guaranteed to return an integral number, but it has rational
-- coefficients. This is why we have to find the least common multiples and do the
-- accumulation over numbers multiplied by that LCM. We essentially do fixed point
-- fractional math here.
emitPolynomialP :: (Emits n, Builder m)
                => (mono n -> m n (Atom n)) -> PolynomialP mono n -> m n (Atom n)
emitPolynomialP evalMono (Polynomial p) = do
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

emitClampMonomial :: (Emits n, Builder m) => ClampMonomial n -> m n (Atom n)
emitClampMonomial (ClampMonomial clamps m) = do
  valuesToClamp <- traverse (emitPolynomialP emitMonomial . coerce) clamps
  clampsProduct <- foldM imul (IdxRepVal 1) =<< traverse clampPositive valuesToClamp
  mval <- emitMonomial m
  imul clampsProduct mval

emitMonomial :: (Emits n, Builder m) => Monomial n -> m n (Atom n)
emitMonomial (Monomial m) = do
  varAtoms <- forM (toList m) \(v, e) -> do
    v' <- emitPolyName v
    ipow v' e
  foldM imul (IdxRepVal 1) varAtoms

ipow :: (Emits n, Builder m) => Atom n -> Int -> m n (Atom n)
ipow x i = foldM imul (IdxRepVal 1) (replicate i x)

-- XXX: names in polynomials can either be integers (IdxRepTy), or indices of
-- some index set. In the latter case, we identify them with their ordinals for
-- the purposes of doing polynomial manipulation. But when we eventually emit
-- them into a realy dex program we need to the conversion-to-ordinal
-- explicitly.
emitPolyName :: (Emits n, Builder m) => PolyName n -> m n (Atom n)
emitPolyName v = do
  getType (Var v) >>= \case
    IdxRepTy -> return $ Var v
    _ -> indexToInt $ Var v

-- === instances ===

instance GenericE Monomial where
  type RepE Monomial = ListE (PairE PolyName (LiftE Int))
  fromE (Monomial m) = ListE $ toList m <&> \(v, n) -> PairE v (LiftE n)
  toE (ListE pairs) = Monomial $ fromList $ pairs <&> \(PairE v (LiftE n)) -> (v, n)

instance SinkableE  Monomial
instance HoistableE Monomial
instance AlphaEqE   Monomial

instance GenericE ClampMonomial where
  type RepE ClampMonomial = PairE (ListE Clamp) Monomial
  fromE (ClampMonomial clamps m) = PairE (ListE clamps) m
  toE   (PairE (ListE clamps) m) = ClampMonomial clamps m

instance SinkableE  ClampMonomial
instance HoistableE ClampMonomial
instance AlphaEqE   ClampMonomial

instance OrdE mono => GenericE (PolynomialP mono) where
  type RepE (PolynomialP mono) = ListE (PairE mono (LiftE Constant))
  fromE (Polynomial m) = ListE $ toList m <&> \(x, n) -> PairE x (LiftE n)
  toE (ListE pairs) = Polynomial $ fromList $ pairs <&> \(PairE x (LiftE n)) -> (x, n)

instance (OrdE mono, SinkableE  mono) => SinkableE  (PolynomialP mono)
instance (OrdE mono, HoistableE mono) => HoistableE (PolynomialP mono)
instance (OrdE mono, AlphaEqE   mono) => AlphaEqE   (PolynomialP mono)
