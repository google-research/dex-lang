-- Copyright 2020 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE UndecidableInstances #-}

module Algebra (sumUsingPolys) where

import Prelude hiding (lookup, sum, pi)
import Control.Monad
import Data.Functor
import Data.Ratio
import Control.Applicative
import Data.Map.Strict hiding (foldl, map, empty, (!))
import Data.Text.Prettyprint.Doc
import Data.List (intersperse)
import Data.Tuple (swap)

import Builder hiding (sub, add, mul)
import Core
import Err
import IRVariants
import MTL1
import Name
import Subst
import QueryType
import Types.Core
import Types.Imp
import Types.Primitives
import Util (Tree (..))

type PolyName = EitherE (AtomName SimpIR) ImpName
type PolyBinder = AtomNameBinder SimpIR

type Constant = Rational

-- Set of variables, each with its power.
data Monomial n = Monomial { fromMonomial :: Map (PolyName n) Int }
                  deriving (Show, Eq, Ord)

-- Set of monomials, each multiplied by a constant.
newtype Polynomial (n::S) =
  Polynomial { fromPolynomial :: Map (Monomial n) Constant }
  deriving (Show, Eq, Ord)

-- This is the main entrypoint. Doing polynomial math sometimes lets
-- us compute sums in closed form. This tries to compute
-- `\sum_{i=0}^(lim-1) body`. `i`, `lim`, and `body` should all have type `Nat`.
sumUsingPolys :: (Builder SimpIR m, Fallible1 m, Emits n)
              => Atom SimpIR n -> Abs (Binder SimpIR) (Block SimpIR) n -> m n (Atom SimpIR n)
sumUsingPolys lim (Abs i body) = do
  sumAbs <- refreshAbs (Abs i body) \(i':>_) body' -> do
    blockAsPoly body' >>= \case
      Just poly' -> return $ Abs i' poly'
      Nothing -> throw NotImplementedErr $
        "Algebraic simplification failed to model index computations:\n"
        ++ "Trying to sum from 0 to " ++ pprint lim ++ " - 1, \\"
        ++ pprint i' ++ "." ++ pprint body'
  limName <- emit (Atom lim)
  emitPolynomial $ sum (LeftE limName) sumAbs

mul :: Polynomial n-> Polynomial n -> Polynomial n
mul (Polynomial x) (Polynomial y) =
  poly [ (cx * cy, mulMono mx my)
       | (mx, cx) <- toList x, (my, cy) <- toList y]

mulMono :: Monomial n -> Monomial n -> Monomial n
mulMono (Monomial mx) (Monomial my) = Monomial $ unionWith (+) mx my

add :: Polynomial n -> Polynomial n -> Polynomial n
add x y = Polynomial $ unionWith (+) (fromPolynomial x) (fromPolynomial y)

sub :: Polynomial n -> Polynomial n -> Polynomial n
sub x y = add x (Polynomial $ negate <$> fromPolynomial y)

sumPolys :: [Polynomial n] -> Polynomial n
sumPolys ps = Polynomial $ unionsWith (+) $ map fromPolynomial ps

mulConst :: Constant -> Polynomial n -> Polynomial n
mulConst c (Polynomial p) = Polynomial $ (*c) <$> p

-- evaluates `\sum_{i=0}^(lim-1) p`
sum :: PolyName n -> Abs PolyBinder Polynomial n -> Polynomial n
sum lim (Abs i p) = sumPolys polys
  where polys = (toList $ fromPolynomial p) <&> \(m, c) ->
                 mulConst c $ sumMono lim (Abs i m)

sumMono :: PolyName n -> Abs PolyBinder Monomial n -> Polynomial n
sumMono lim (Abs b (Monomial m)) = case lookup (LeftE $ binderName b) m of
  -- TODO: Implement the formula for arbitrary order polynomials
  Nothing  -> poly [ (   1, mulMono c $ mono [(lim, 1)])]
  Just 0   -> error "Each variable appearing in a monomial should have a positive power"
  -- Summing exclusive of `lim`: Sum_{i=1}^{n-1} i = (n-1)n/2 = 1/2 n^2 - 1/2 n
  Just 1   -> poly [ ( 1/2, mulMono c $ mono [(lim, 2)])
                   , (-1/2, mulMono c $ mono [(lim, 1)])]
  -- Summing exclusive of `lim`: Sum_{i=1}^{n-1} i^2 = (n-1)n(2n-1)/6 = 1/3 n^3 - 1/2 n^2 + 1/6 n
  Just 2   -> poly [ ( 1/3, mulMono c $ mono [(lim, 3)])
                   , (-1/2, mulMono c $ mono [(lim, 2)])
                   , ( 1/6, mulMono c $ mono [(lim, 1)])]
  (Just n) -> error $ "Triangular arrays of order " ++ show n ++ " not implemented yet!"
  where
    c = ignoreHoistFailure $ hoist b $  -- failure impossible
          Monomial $ delete (LeftE $ binderName b) m

-- === Constructors and singletons ===

poly :: [(Constant, Monomial n)] -> Polynomial n
poly monos = Polynomial $ fromListWith (+) $ fmap swap monos

mono :: [(PolyName n, Int)] -> Monomial n
mono vars = Monomial $ fromListWith (error "Duplicate entries for variable") vars

-- === Type classes and helpers ===

showMono :: Monomial n -> String
showMono (Monomial m) =
  concat $ intersperse " " $ fmap (\(n, p) -> docAsStr $ pretty n <> "^" <> pretty p) $ toList m

_showPoly :: Polynomial n -> String
_showPoly (Polynomial p) =
  concat $ intersperse " + " $ fmap (\(m, c) -> show c ++ " " ++ showMono m) $ toList p

-- === core expressions as polynomials ===

data PolySubstVal (c::C) (n::S) where
  PolySubstVal :: Maybe (Polynomial n) -> PolySubstVal (AtomNameC SimpIR) n
  PolyRename   :: Name c n             -> PolySubstVal c n

instance SinkableV PolySubstVal
instance SinkableE (PolySubstVal c)  where sinkingProofE = undefined
instance FromName PolySubstVal where fromName = PolyRename

type BlockTraverserM i o a = SubstReaderT PolySubstVal (MaybeT1 (BuilderM SimpIR)) i o a

blockAsPoly
  :: (EnvExtender m, EnvReader m)
  => Block SimpIR n -> m n (Maybe (Polynomial n))
blockAsPoly (Block _ decls result) =
  liftBuilder $ runMaybeT1 $ runSubstReaderT idSubst $ blockAsPolyRec decls result

blockAsPolyRec :: Nest (Decl SimpIR) i i' -> Atom SimpIR i' -> BlockTraverserM i o (Polynomial o)
blockAsPolyRec decls result = case decls of
  Empty -> atomAsPoly result
  Nest (Let b (DeclBinding _ _ expr)) restDecls -> do
    p <- optional (exprAsPoly expr)
    extendSubst (b@>PolySubstVal p) $ blockAsPolyRec restDecls result

  where
    atomAsPoly :: Atom SimpIR i -> BlockTraverserM i o (Polynomial o)
    atomAsPoly = \case
      Var v       -> atomNameAsPoly v
      RepValAtom (RepVal _ (Leaf (IVar v' _))) -> impNameAsPoly v'
      IdxRepVal i -> return $ poly [((fromIntegral i) % 1, mono [])]
      _ -> empty

    impNameAsPoly :: ImpName i -> BlockTraverserM i o (Polynomial o)
    impNameAsPoly v = getSubst <&> (!v) >>= \case
      PolyRename v' -> return $ poly [(1, mono [(RightE v', 1)])]

    atomNameAsPoly :: AtomName SimpIR i -> BlockTraverserM i o (Polynomial o)
    atomNameAsPoly v = getSubst <&> (!v) >>= \case
      PolySubstVal Nothing   -> empty
      PolySubstVal (Just cp) -> return cp
      PolyRename   v'        ->
        getType v' >>= \case
          IdxRepTy -> return $ poly [(1, mono [(LeftE v', 1)])]
          _ -> empty

    exprAsPoly :: Expr SimpIR i -> BlockTraverserM i o (Polynomial o)
    exprAsPoly e = case e of
      Atom a -> atomAsPoly a
      PrimOp (BinOp op x y) -> case op of
        IAdd -> add <$> atomAsPoly x <*> atomAsPoly y
        IMul -> mul <$> atomAsPoly x <*> atomAsPoly y
        -- XXX: we rely on the wrapping behavior of subtraction on unsigned ints
        -- so that the distributive law holds, `a * (b - c) == (a * b) - (a * c)`
        ISub -> sub <$> atomAsPoly x <*> atomAsPoly y
        -- This is to handle `idiv` generated by `emitPolynomial`
        IDiv -> case y of
          IdxRepVal n -> mulConst (1 / fromIntegral n) <$> atomAsPoly x
          _ -> empty
        _ -> empty
      _ -> empty

-- === polynomials to Core expressions ===

-- We have to be extra careful here, because we're evaluating a polynomial
-- that we know is guaranteed to return an integral number, but it has rational
-- coefficients. This is why we have to find the least common multiples and do the
-- accumulation over numbers multiplied by that LCM. We essentially do fixed point
-- fractional math here.
emitPolynomial :: (Emits n, Builder SimpIR m) => Polynomial n -> m n (Atom SimpIR n)
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

emitMonomial :: (Emits n, Builder SimpIR m) => Monomial n -> m n (Atom SimpIR n)
emitMonomial (Monomial m) = do
  varAtoms <- forM (toList m) \(v, e) -> case v of
    LeftE v' -> ipow (Var v') e
    RightE v' -> do
      let atom = RepValAtom $ RepVal IdxRepTy (Leaf (IVar v' IIdxRepTy))
      ipow atom e
  foldM imul (IdxRepVal 1) varAtoms

ipow :: (Emits n, Builder SimpIR m) => Atom SimpIR n -> Int -> m n (Atom SimpIR n)
ipow x i = foldM imul (IdxRepVal 1) (replicate i x)

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
