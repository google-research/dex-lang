-- Copyright 2022 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE UndecidableInstances #-}

module Optimize
  ( optimize, hoistLoopInvariant, dceTop) where

import Data.Functor
import Control.Monad
import Control.Monad.State.Strict

import Types.Core
import Types.Primitives
import Types.Top
import MTL1
import Name
import Subst
import IRVariants
import Core
import CheapReduction
import Builder
import QueryType
import Util (iota)
import Err

optimize :: EnvReader m => STopLam n -> m n (STopLam n)
optimize = dceTop     -- Clean up user code
       >=> unrollLoops
       >=> dceTop     -- Clean up peephole-optimized code after unrolling
       >=> hoistLoopInvariant

-- === Loop unrolling ===

unrollLoops :: EnvReader m => STopLam n -> m n (STopLam n)
unrollLoops lam = liftLamExpr lam unrollLoopsExpr
{-# SCC unrollLoops #-}

unrollLoopsExpr :: EnvReader m => SExpr n -> m n (SExpr n)
unrollLoopsExpr b = liftM fst $
  liftBuilder $ runStateT1 (runSubstReaderT idSubst (runULM $ buildBlock $ ulExpr b)) (ULS 0)

newtype ULS n = ULS Int deriving Show
newtype ULM i o a = ULM { runULM :: SubstReaderT AtomSubstVal (StateT1 ULS (BuilderM SimpIR)) i o a}
  deriving (MonadFail, Fallible, Functor, Applicative, Monad, ScopeReader,
            EnvReader, EnvExtender, Builder SimpIR, SubstReader AtomSubstVal,
            ScopableBuilder SimpIR, MonadState (ULS o))

instance SinkableE ULS where
  sinkingProofE _ (ULS c) = ULS c
instance HoistableState ULS where
  hoistState _ _ (ULS c) = (ULS c)
  {-# INLINE hoistState #-}

instance NonAtomRenamer (ULM i o) i o where renameN = substM
instance Visitor (ULM i o) SimpIR i o where
  visitAtom = visitAtomDefault
  visitType = visitTypeDefault
  visitPi   = visitPiDefault
  visitLam  = visitLamEmits
instance ExprVisitorEmits (ULM i o) SimpIR i o where
  visitExprEmits = ulExpr

-- TODO: Refine the cost accounting so that operations that will become
-- constant-foldable after inlining don't count towards it.
ulExpr :: Emits o => SExpr i -> ULM i o (SAtom o)
ulExpr expr = case expr of
  PrimOp (Hof (TypedHof _ (For Fwd ixTy body))) ->
    case ixTypeDict ixTy of
      DictCon (IxRawFin (IdxRepVal n)) -> do
        (body', bodyCost) <- withLocalAccounting $ visitLamEmits body
        -- We add n (in the form of (... + 1) * n) for the cost of the TabCon reconstructing the result.
        case (bodyCost + 1) * (fromIntegral n) <= unrollBlowupThreshold of
          True -> case body' of
            UnaryLamExpr b' block' -> do
              vals <- dropSubst $ forM (iota n) \i -> do
                extendSubst (b' @> SubstVal (IdxRepVal i)) $ ulExpr block'
              inc $ fromIntegral n  -- To account for the TabCon we emit below
              getLamExprType body' >>= \case
                PiType (UnaryNest (tb:>_)) valTy -> do
                  let tabTy = toType $ TabPiType (DictCon $ IxRawFin (IdxRepVal n)) (tb:>IdxRepTy) valTy
                  emit $ TabCon tabTy vals
                _ -> error "Expected `for` body to have a Pi type"
            _ -> error "Expected `for` body to be a lambda expression"
          False -> do
            inc bodyCost
            ixTy' <- visitGeneric ixTy
            emitHof $ For Fwd ixTy' body'
      _ -> nothingSpecial
  -- Avoid unrolling loops with large table literals
  TabCon _ els -> inc (length els) >> nothingSpecial
  Block _ (Abs decls body) -> visitDeclsEmits decls $ ulExpr body
  _ -> nothingSpecial
  where
    inc i = modify \(ULS n) -> ULS (n + i)
    nothingSpecial = inc 1 >> visitGeneric expr >>= emit
    unrollBlowupThreshold = 12
    withLocalAccounting m = do
      oldCost <- get
      ans <- put (ULS 0) *> m
      ULS newCost <- get
      put oldCost $> (ans, newCost)
    {-# INLINE withLocalAccounting #-}

-- === Loop invariant code motion ===

data LICMTag
type LICMM = AtomSubstBuilder LICMTag SimpIR

liftLICMM :: EnvReader m => LICMM n n a -> m n a
liftLICMM cont = liftAtomSubstBuilder cont

instance NonAtomRenamer (LICMM i o) i o where renameN = substM
instance Visitor (LICMM i o) SimpIR i o where
  visitAtom = visitAtomDefault
  visitType = visitTypeDefault
  visitPi   = visitPiDefault
  visitLam  = visitLamEmits

instance ExprVisitorEmits (LICMM i o) SimpIR i o where
  visitExprEmits = licmExpr

hoistLoopInvariantExpr :: EnvReader m => SExpr n -> m n (SExpr n)
hoistLoopInvariantExpr body = liftLICMM $ buildBlock $ visitExprEmits body
{-# SCC hoistLoopInvariantExpr #-}

hoistLoopInvariant :: EnvReader m => STopLam n -> m n (STopLam n)
hoistLoopInvariant lam = liftLamExpr lam hoistLoopInvariantExpr
{-# INLINE hoistLoopInvariant #-}

licmExpr :: Emits o => SExpr i -> LICMM i o (SAtom o)
licmExpr = \case
  PrimOp (Hof (TypedHof _ (For dir ix (LamExpr (UnaryNest b) body)))) -> undefined
    -- ix' <- substM ix
    -- Abs hdecls destsAndBody <- visitBinders (UnaryNest b) \(UnaryNest b') -> do
    --   Abs decls ans <- buildScoped $ visitExprEmits body
    --   liftEnvReaderM $ runSubstReaderT idSubst $
    --       seqLICM REmpty mempty (asNameBinder b') REmpty decls ans
    -- PairE (ListE []) (Abs lnb bodyAbs) <- emitDecls $ Abs hdecls destsAndBody
    -- ixTy <- substM $ binderType b
    -- body' <- withFreshBinder noHint ixTy \i -> do
    --   block <- mkBlock =<< applyRename (lnb@>binderName i) bodyAbs
    --   return $ UnaryLamExpr i block
    -- emitHof $ For dir ix' body'
  Block _ (Abs decls result) -> visitDeclsEmits decls $ licmExpr result
  expr -> visitGeneric expr >>= emit

-- === Dead code elimination ===

newtype FV n = FV (NameSet n) deriving (Semigroup, Monoid)
instance SinkableE FV where
  sinkingProofE _ _ = todoSinkableProof
instance HoistableState FV where
  hoistState _ b (FV ns) = FV $ hoistFilterNameSet b ns
  {-# INLINE hoistState #-}

newtype DCEM n a = DCEM { runDCEM :: StateT1 FV EnvReaderM n a }
  deriving ( Functor, Applicative, Monad, EnvReader, ScopeReader
           , MonadState (FV n), EnvExtender)

dceTop :: EnvReader m => STopLam n -> m n (STopLam n)
dceTop lam = liftLamExpr lam dceExpr
{-# INLINE dceTop #-}

dceExpr :: EnvReader m => SExpr n -> m n (SExpr n)
dceExpr b = liftEnvReaderM $ evalStateT1 (runDCEM $ dce b) mempty
{-# SCC dceExpr #-}

class HasDCE (e::E) where
  dce :: e n -> DCEM n (e n)
  default dce :: VisitGeneric e SimpIR => e n -> DCEM n (e n)
  dce = visitGeneric

instance NonAtomRenamer (DCEM o) o o where renameN = dce
instance Visitor (DCEM o) SimpIR o o where
  visitType = dce
  visitAtom = dce
  visitLam  = dce
  visitPi   = dce

instance Color c => HasDCE (Name c) where
  dce n = modify (<> FV (freeVarsE n)) $> n

instance HasDCE SAtom where
  dce atom = case atom of
    Stuck _ _ -> modify (<> FV (freeVarsE atom)) $> atom
    Con con   -> Con <$> visitGeneric con

instance HasDCE SType where
  dce (TyCon e) = TyCon <$> visitGeneric e

instance HasDCE (PiType SimpIR) where
  dce (PiType bs effTy) = do
    dceBinders bs effTy \bs' effTy' -> PiType bs' <$> dce effTy'

instance HasDCE (LamExpr SimpIR) where
  dce (LamExpr bs e) = dceBinders bs e \bs' e' -> LamExpr bs' <$> dce e'

instance HasDCE (Expr SimpIR) where
  dce = \case
    Block effTy block -> do
      -- The free vars accumulated in the state of DCEM should correspond to
      -- the free vars of the Abs of the block answer, by the decls traversed
      -- so far. dceNest takes care to uphold this invariant, but we temporarily
      -- reset the state to an empty map, just so that names from the surrounding
      -- block don't end up influencing elimination decisions here. Note that we
      -- restore the state (and accumulate free vars of the DCE'd block into it)
      -- right after dceNest.
      effTy' <- dce effTy
      old <- get
      put mempty
      block' <- dceBlock block
      modify (<> old)
      return $ Block effTy' block'
    e -> visitGeneric e

dceBinders
  :: (HoistableB b, BindsEnv b, RenameB b, RenameE e)
  => b n l -> e l
  -> (forall l'. b n l' -> e l' -> DCEM l' a)
  -> DCEM n a
dceBinders b e cont = do
  ans <- refreshAbs (Abs b e) \b' e' -> cont b' e'
  modify (<>FV (freeVarsB b))
  return ans
{-# INLINE dceBinders #-}

wrapWithCachedFVs :: HoistableE e => e n -> DCEM n (CachedFVs e n)
wrapWithCachedFVs e = do
  FV fvs <- get
#ifdef DEX_DEBUG
  let fvsAreCorrect = nameSetRawNames fvs == nameSetRawNames (freeVarsE e)
#else
  -- Verification of this invariant defeats the performance benefits of
  -- avoiding the extra traversal (e.g. actually having linear complexity),
  -- so we only do that in debug builds.
  let fvsAreCorrect = True
#endif
  case fvsAreCorrect of
    True -> return $ UnsafeCachedFVs fvs e
    False -> error $ "Free variables were computed incorrectly."

hoistUsingCachedFVs :: (BindsNames b, HoistableE e) =>
  b n l -> e l -> DCEM l (HoistExcept (e n))
hoistUsingCachedFVs b e = hoistViaCachedFVs b <$> wrapWithCachedFVs e

data ElimResult n where
  ElimSuccess :: SBlock n -> ElimResult n
  ElimFailure :: SDecl n l -> SBlock l -> ElimResult n

dceBlock :: SBlock n -> DCEM n (SBlock n)
dceBlock (Abs decls ans) = case decls of
  Empty -> Abs Empty <$> dce ans
  Nest b@(Let _ decl) bs -> do
    -- Note that we only ever dce the abs below under this refreshAbs,
    -- which will remove any references to b upon exit (it happens
    -- because refreshAbs of StateT1 triggers hoistState, which we
    -- implement by deleting the entries that can't hoist).
    dceAttempt <- refreshAbs (Abs b (Abs bs ans)) \b' (Abs bs' ans') -> do
      below <- dceBlock $ Abs bs' ans'
      case isPure decl of
        False -> return $ ElimFailure b' below
        True  -> do
          hoistUsingCachedFVs b' below <&> \case
            HoistSuccess below' -> ElimSuccess below'
            HoistFailure _ -> ElimFailure b' below
    case dceAttempt of
      ElimSuccess below' -> return below'
      ElimFailure (Let b' (DeclBinding ann expr)) (Abs bs'' ans'') -> do
        expr' <- dce expr
        modify (<>FV (freeVarsB b'))
        return $ Abs (Nest (Let b' (DeclBinding ann expr')) bs'') ans''

instance HasDCE (Effects SimpIR)
instance HasDCE (EffTy   SimpIR)
