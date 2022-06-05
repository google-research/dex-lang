-- Copyright 2020 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE UndecidableInstances #-}

module Algebra (
  Polynomial, PolyName, emitPolynomial,
  emptyMonomial, sumC, psubst,
  liftPoly, showPoly, blockAsCPoly) where

import Prelude hiding (lookup, sum, pi)
import Control.Monad
import Data.Functor
import Data.Ratio
import Control.Applicative
import Data.Map.Strict hiding (foldl, map, empty, (!))
import Data.Text.Prettyprint.Doc
import Data.List (intersperse)
import Data.Tuple (swap)
import Data.Coerce

import Builder hiding (sub, add)
import Simplify
import Syntax
import QueryType
import Name
import Err
import MTL1

type PolyName = Name AtomNameC
type PolyBinder = NameBinder AtomNameC

type Constant = Rational

-- Set of variables, each with its power.
data Monomial n = Monomial { fromMonomial :: Map (PolyName n) Int }
                  deriving (Show, Eq, Ord)

-- Set of monomials, each multiplied by a constant.
newtype Polynomial (n::S) =
  Polynomial { fromPolynomial :: Map (Monomial n) Constant }
  deriving (Show, Eq, Ord)

-- === Polynomial math ===

mulC :: Polynomial n-> Polynomial n -> Polynomial n
mulC (Polynomial x) (Polynomial y) =
  poly [ (cx * cy, mulMono mx my)
       | (mx, cx) <- toList x, (my, cy) <- toList y]
  where mulMono (Monomial mx) (Monomial my) = Monomial $ unionWith (+) mx my

add :: Polynomial n -> Polynomial n -> Polynomial n
add x y = Polynomial $ unionWith (+) (fromPolynomial x) (fromPolynomial y)

sub :: Polynomial n -> Polynomial n -> Polynomial n
sub x y = add x (Polynomial $ negate <$> fromPolynomial y)

sumPolys :: [Polynomial n] -> Polynomial n
sumPolys ps = Polynomial $ unionsWith (+) $ map fromPolynomial ps

mulConst :: Constant -> Polynomial n -> Polynomial n
mulConst c (Polynomial p) = Polynomial $ (*c) <$> p

-- (Lazy) infinite list of powers of p
powersL :: (a -> a -> a) -> a -> a -> [a]
powersL mult e p = e : fmap (mult p) (powersL mult e p)

powersC :: Polynomial n -> [Polynomial n]
powersC p = coerce $ powersL mulC (poly [(1, mono [])]) p

-- evaluates `\sum_{i=0}^(lim-1) p`
sumC :: PolyName n -> Abs PolyBinder Polynomial n -> Polynomial n
sumC lim (Abs i p) = sumPolys polys
  where polys = (toList $ fromPolynomial p) <&> \(m, c) ->
                  mulConst c $ sumMono lim (Abs i m)

sumMono :: PolyName n -> Abs PolyBinder Monomial n -> Polynomial n
sumMono lim (Abs b (Monomial m)) = case lookup (binderName b) m of
  -- TODO: Implement the formula for arbitrary order polynomials
  Nothing  -> poly [(1, Monomial $ insert lim 1 c)]
  Just 0   -> error "Each variable appearing in a monomial should have a positive power"
  -- Summing exclusive of `lim`: Sum_{i=1}^{n-1} i = (n-1)n/2 = 1/2 n^2 - 1/2 n
  Just 1   -> poly [(1/2, Monomial $ insert lim 2 c), (-1/2, Monomial $ insert lim 1 c)]
  -- Summing exclusive of `lim`: Sum_{i=1}^{n-1} i^2 = (n-1)n(2n-1)/6 = 1/3 n^3 - 1/2 n^2 + 1/6 n
  Just 2   -> poly [(1/3, Monomial $ insert lim 3 c), (-1/2, Monomial $ insert lim 2 c), (1/6, Monomial $ insert lim 1 c)]
  (Just n) -> error $ "Triangular arrays of order " ++ show n ++ " not implemented yet!"
  where
    c = fromMonomial $ ignoreHoistFailure $ hoist b $  -- failure impossible
          Monomial $ delete (binderName b) m

psubst :: Abs PolyBinder Polynomial n -> Polynomial n -> Polynomial n
psubst (Abs b (Polynomial p)) x = sumPolys ps
  where ps = toList p <&> \(m, c) -> mulConst c $ psubstMono (Abs b m) x

psubstMono :: Abs PolyBinder Monomial n -> Polynomial n -> Polynomial n
psubstMono (Abs b (Monomial m)) x = case lookup (binderName b) m of
  Nothing -> poly [(1, m')]
    where m' = ignoreHoistFailure $ hoist b $ Monomial m
  Just 0  -> error "Each variable appearing in a monomial should have a positive power"
  Just n  -> mulC (poly [(1, m')]) (powersC x !! n)
    where m' = ignoreHoistFailure $ hoist b $ Monomial $ delete (binderName b) m

-- === Constructors and singletons ===

poly :: [(Constant, Monomial n)] -> Polynomial n
poly monos = Polynomial $ fromListWith (+) $ fmap swap monos

mono :: [(PolyName n, Int)] -> Monomial n
mono vars = Monomial $ fromListWith (error "Duplicate entries for variable") vars

-- === Type classes and helpers ===

showMono :: Monomial n -> String
showMono (Monomial m) =
  concat $ intersperse " " $ fmap (\(n, p) -> docAsStr $ pretty n <> "^" <> pretty p) $ toList m

showPoly :: Polynomial n -> String
showPoly (Polynomial p) =
  concat $ intersperse " + " $ fmap (\(m, c) -> show c ++ " " ++ showMono m) $ toList p

emptyMonomial :: Monomial n
emptyMonomial = mono []

liftPoly :: Monomial n -> Polynomial n
liftPoly m = Polynomial $ singleton m (fromInteger 1)

-- === core expressions as polynomials ===

type CPolySubstVal = SubstVal AtomNameC (MaybeE Polynomial)

blockAsCPoly :: (EnvExtender m, EnvReader m) => Block n -> m n (Maybe (Polynomial n))
blockAsCPoly (Block _ decls' result') =
  runMaybeT1 $ runSubstReaderT idSubst $ go $ Abs decls' $ Atom result'
  where
    go :: (EnvExtender2 m, EnvReader2 m, SubstReader CPolySubstVal m, Alternative2 m)
       => Abs (Nest Decl) Expr o -> m o o (Polynomial o)
    go (Abs decls result) = case decls of
      Empty -> exprAsCPoly result
      Nest decl@(Let _ (DeclBinding _ _ expr)) restDecls -> do
        let rest = Abs restDecls result
        cp <- toMaybeE <$> optional (exprAsCPoly expr)
        refreshAbs (Abs decl rest) \(Let b _) rest' -> do
          extendSubst (b@>SubstVal (sink cp)) $ do
            cpresult <- go rest'
            case hoist b cpresult of
              HoistSuccess ans -> return ans
              HoistFailure _   -> empty

    exprAsCPoly :: (EnvReader2 m, SubstReader CPolySubstVal m, Alternative2 m) => Expr o -> m o o (Polynomial o)
    exprAsCPoly e = case e of
      Atom a                    -> intAsCPoly a
      Op (BinOp IAdd x y) -> add  <$> intAsCPoly x <*> intAsCPoly y
      -- XXX: we rely on the wrapping behavior of subtraction on unsigned ints
      -- so that the distributive law holds, `a * (b - c) == (a * b) - (a * c)`
      Op (BinOp ISub x y) -> sub  <$> intAsCPoly x <*> intAsCPoly y
      Op (BinOp IMul x y) -> mulC <$> intAsCPoly x <*> intAsCPoly y
      -- TODO: Remove once IntRange and IndexRange are defined in the surface language
      Op (CastOp IdxRepTy v)    -> getType v >>= \case
        IdxRepTy -> intAsCPoly v
        _        -> indexAsCPoly v
      _ -> empty

    -- We identify index typed values as their ordinals. This assumes that all
    -- index vars appearing in the size expressions will come from dependent
    -- dimensions, so that summing over those dims will erase those vars from
    -- polynomials.
    indexAsCPoly :: (SubstReader CPolySubstVal m, Alternative2 m)
                 => Atom i -> m i o (Polynomial o)
    indexAsCPoly = \case
      Var v                       -> varAsCPoly v
      Con (FinVal _ i)            -> intAsCPoly i
      _                           -> empty

    intAsCPoly :: (SubstReader CPolySubstVal m, Alternative2 m)
                => Atom i -> m i o (Polynomial o)
    intAsCPoly = \case
      Var v       -> varAsCPoly v
      -- XXX: this case is needed to handle the Nat-wrapper types, RangeFrom,
      -- RangeFromExc, RangeTo, and RangeToExc. But user-defined index sets
      -- won't always just be wrappers around `Nat`! So we need Algebra to be
      -- aware of their definitions.
      ProjectElt (0:|[]) v -> varAsCPoly v
      IdxRepVal x -> return $ fromInt x
      _ -> empty
      where
        fromInt i = poly [((fromIntegral i) % 1, mono [])]

    varAsCPoly :: (SubstReader CPolySubstVal m, Alternative2 m)
               => AtomName i -> m i o (Polynomial o)
    varAsCPoly v = getSubst <&> (!v) >>= \case
      SubstVal NothingE   -> empty
      SubstVal (JustE cp) -> return cp
      SubstVal _          -> error "impossible"
      Rename   v'         -> return $ poly [(1, mono [(v', 1)])]

-- === polynomials to Core expressions ===

-- We have to be extra careful here, because we're evaluating a polynomial
-- that we know is guaranteed to return an integral number, but it has rational
-- coefficients. This is why we have to find the least common multiples and do the
-- accumulation over numbers multiplied by that LCM. We essentially do fixed point
-- fractional math here.
emitPolynomial :: (Emits n, Builder m) => Polynomial n -> m n (Atom n)
emitPolynomial (Polynomial p) = do
  let constLCM = asAtom $ foldl lcm 1 $ fmap (denominator . snd) $ toList p
  monoAtoms <- flip traverse (toList p) $ \(m, c) -> do
    lcmFactor <- constLCM `idiv` (asAtom $ denominator c)
    constFactor <- imul (asAtom $ numerator c) lcmFactor
    imul constFactor =<< emitMonomial m
  total <- foldM iadd (IdxRepVal 0) monoAtoms
  total `idiv` constLCM
  where
    -- TODO: Check for overflows. We might also want to bail out if the LCM is too large,
    --       because it might be causing overflows due to all arithmetic being shifted.
    asAtom = IdxRepVal . fromInteger

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
emitPolyName v =
  lookupAtomName v >>= \case
    IxBound ixTy -> emitSimplified $ ordinal (sink ixTy) (sink $ Var v)
    _ -> return $ Var v

-- === instances ===

instance GenericE Monomial where
  type RepE Monomial = ListE (PairE PolyName (LiftE Int))
  fromE (Monomial m) = ListE $ toList m <&> \(v, n) -> PairE v (LiftE n)
  {-# INLINE fromE #-}
  toE (ListE pairs) = Monomial $ fromList $ pairs <&> \(PairE v (LiftE n)) -> (v, n)
  {-# INLINE toE #-}

instance SinkableE  Monomial
instance HoistableE Monomial
instance AlphaEqE   Monomial

instance GenericE Polynomial where
  type RepE Polynomial = ListE (PairE Monomial (LiftE Constant))
  fromE (Polynomial m) = ListE $ toList m <&> \(x, n) -> PairE x (LiftE n)
  {-# INLINE fromE #-}
  toE (ListE pairs) = Polynomial $ fromList $ pairs <&> \(PairE x (LiftE n)) -> (x, n)
  {-# INLINE toE #-}

instance SinkableE  Polynomial
instance HoistableE Polynomial
instance AlphaEqE   Polynomial
