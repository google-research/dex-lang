-- Copyright 2022 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE UndecidableInstances #-}

module Optimize (earlyOptimize, optimize) where

import Data.Functor
import Data.List.NonEmpty qualified as NE
import Control.Monad
import Control.Monad.State.Strict

import Types.Core
import Types.Primitives
import MTL1
import Name
import Core
import GenericTraversal
import Builder
import QueryType

earlyOptimize :: EnvReader m => Block n -> m n (Block n)
earlyOptimize = unrollTrivialLoops

optimize :: EnvReader m => Block n -> m n (Block n)
optimize = dceBlock     -- Clean up user code
       >=> unrollLoops
       >=> dceBlock     -- Clean up peephole-optimized code after unrolling

-- === Trivial loop unrolling ===
-- This pass unrolls loops that use Fin 0 or Fin 1 as an index set.

data UTLS n = UTLS
type UTLM = GenericTraverserM UTLS
instance SinkableE UTLS where
  sinkingProofE _ UTLS = UTLS
instance HoistableState UTLS where
  hoistState _ _ _ = UTLS
  {-# INLINE hoistState #-}

data IndexSetKind n
  = EmptyIxSet
  | SingletonIxSet (Atom n)
  | UnknownIxSet

isTrivialIndex :: Type i -> UTLM i o (IndexSetKind o)
isTrivialIndex = \case
  TC (Fin     (IdxRepVal n)) | n <= 0 -> return EmptyIxSet
  TC (Fin  nv@(IdxRepVal n)) | n == 1 ->
    liftM (SingletonIxSet . Con) $ FinVal <$> substM nv <*> pure (IdxRepVal 0)
  _ -> return UnknownIxSet

instance GenericTraverser UTLS where
  traverseExpr expr = case expr of
    Hof (For _ ixDict (Lam (LamExpr b body@(Block _ decls a)))) -> do
      isTrivialIndex (binderType b) >>= \case
        UnknownIxSet     -> traverseExprDefault expr
        SingletonIxSet i -> do
          ixTy <- ixTyFromDict =<< substM ixDict
          ans <- extendSubst (b @> SubstVal i) $ traverseDeclNest decls $ traverseAtom a
          liftM Atom $ buildTabLam noHint ixTy $ const $ return $ sink ans
        EmptyIxSet -> do
          ixTy <- ixTyFromDict =<< substM ixDict
          liftM Atom $ buildTabLam noHint ixTy \i -> do
            resTy' <- extendSubst (b @> Rename i) $ getTypeSubst body
            emitOp $ ThrowError (sink resTy')
    _ -> traverseExprDefault expr

unrollTrivialLoops :: EnvReader m => Block n -> m n (Block n)
unrollTrivialLoops b = liftM fst $ liftGenericTraverserM UTLS $ traverseGenericE b

-- === Peephole optimizations ===

peepholeExpr :: GenericTraverser s => Expr o -> GenericTraverserM s i o (Either (Atom o) (Expr o))
peepholeExpr expr = case expr of
  -- TODO: Support more casts!
  Op (CastOp IdxRepTy (Con (FinVal _ i))) -> return $ Left i
  Op (CastOp (BaseTy (Scalar Int32Type)) (Con (Lit (Word32Lit x)))) ->
    return $ Left $ Con $ Lit $ Int32Lit $ fromIntegral x
  Op (CastOp (BaseTy (Scalar Word64Type)) (Con (Lit (Word32Lit x)))) ->
    return $ Left $ Con $ Lit $ Word64Lit $ fromIntegral x
  -- TODO: Support more unary and binary ops!
  Op (BinOp IAdd (IdxRepVal a) (IdxRepVal b)) -> return $ Left $ IdxRepVal $ a + b
  TabApp (Var t) ((Con (FinVal _ (IdxRepVal ord))) NE.:| []) -> do
    lookupAtomName t >>= \case
      LetBound (DeclBinding PlainLet _ (Op (TabCon _ elems))) ->
        return $ Left $ elems !! (fromIntegral ord)
      _ -> return $ Right expr
  -- TODO: Apply a function to literals when it has a cheap body?
  -- Think, partial evaluation of threefry.
  _ -> return $ Right expr

-- === Loop unrolling ===

unrollLoops :: EnvReader m => Block n -> m n (Block n)
unrollLoops b = liftM fst $ liftGenericTraverserM (ULS 0) $ traverseGenericE b

newtype ULS n = ULS Int deriving Show
type ULM = GenericTraverserM ULS
instance SinkableE ULS where
  sinkingProofE _ (ULS c) = ULS c
instance HoistableState ULS where
  hoistState _ _ (ULS c) = (ULS c)
  {-# INLINE hoistState #-}

-- TODO: Refine the cost accounting so that operations that will become
-- constant-foldable after inlining don't count towards it.
instance GenericTraverser ULS where
  traverseInlineExpr expr = case expr of
    Hof (For Fwd ixDict body@(Lam (LamExpr b _))) -> do
      case binderType b of
        FinConst n -> do
          (body', bodyCost) <- withLocalAccounting $ traverseAtom body
          case bodyCost * (fromIntegral n) <= unrollBlowupThreshold of
            True -> case body' of
              Lam (LamExpr b' block') -> do
                vals <- dropSubst $ forM [0..(fromIntegral n :: Int) - 1] \ord -> do
                  let i = Con $ FinVal (IdxRepVal n) (IdxRepVal $ fromIntegral ord)
                  extendSubst (b' @> SubstVal i) $ emitSubstBlock block'
                getType body' >>= \case
                  Pi (PiType (PiBinder tb _ _) _ valTy) -> do
                    let tabTy = TabPi $ TabPiType (tb:>IxType (FinConst n) (DictCon (IxFin $ IdxRepVal n))) valTy
                    return $ Right $ Op $ TabCon tabTy vals
                  _ -> error "Expected for body to have a Pi type"
              _ -> error "Expected for body to be a lambda expression"
            False -> do
              inc bodyCost
              ixDict' <- traverseGenericE ixDict
              return $ Right $ Hof $ For Fwd ixDict' body'
        _ -> nothingSpecial
    _ -> nothingSpecial
    where
      inc i = modify \(ULS n) -> ULS (n + i)
      nothingSpecial = inc 1 >> (traverseExprDefault expr >>= peepholeExpr)
      unrollBlowupThreshold = 12
      withLocalAccounting m = do
        oldCost <- get
        ans <- put (ULS 0) *> m
        ULS newCost <- get
        put oldCost $> (ans, newCost)
      {-# INLINE withLocalAccounting #-}

emitSubstBlock :: Emits o => Block i -> ULM i o (Atom o)
emitSubstBlock (Block _ decls ans) = traverseDeclNest decls $ traverseAtom ans

-- === Dead code elimination ===

newtype FV n = FV (NameSet n) deriving (Semigroup, Monoid)
instance SinkableE FV where
  sinkingProofE _ _ = todoSinkableProof
instance HoistableState FV where
  hoistState _ b (FV ns) = FV $ hoistFilterNameSet b ns
  {-# INLINE hoistState #-}

type DCEM = StateT1 FV EnvReaderM

dceBlock :: EnvReader m => Block n -> m n (Block n)
dceBlock b = liftEnvReaderM $ evalStateT1 (dce b) mempty

class HasDCE (e::E) where
  dce :: e n -> DCEM n (e n)
  default dce :: (GenericE e, HasDCE (RepE e)) => e n -> DCEM n (e n)
  dce e = confuseGHC >>= \_ -> toE <$> dce (fromE e)

-- The interesting instances

instance Color c => HasDCE (Name c) where
  dce n = modify (<> FV (freeVarsE n)) $> n

instance HasDCE Block where
  dce (Block ann decls ans) = case (ann, decls) of
    (NoBlockAnn      , Empty) -> Block NoBlockAnn Empty <$> dce ans
    (NoBlockAnn      , _    ) -> error "should be unreachable"
    (BlockAnn ty effs, _    ) -> do
      -- The free vars accumulated in the state of DCEM should correspond to
      -- the free vars of the Abs of the block answer, by the decls traversed
      -- so far. dceNest takes care to uphold this invariant, but we temporarily
      -- reset the state to an empty map, just so that names from the surrounding
      -- block don't end up influencing elimination decisions here. Note that we
      -- restore the state (and accumulate free vars of the DCE'd block into it)
      -- right after dceNest.
      old <- get
      put mempty
      Abs decls' ans' <- dceNest decls ans
      modify (<> old)
      ty' <- dce ty
      effs' <- dce effs
      return $ Block (BlockAnn ty' effs') decls' ans'

data CachedFVs e n = UnsafeCachedFVs { _cachedFVs :: (NameSet n), fromCachedFVs :: (e n) }
instance HoistableE (CachedFVs e) where
  freeVarsE (UnsafeCachedFVs fvs _) = fvs

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
    False -> error "Free variables were computed incorrectly."

hoistUsingCachedFVs :: (BindsNames b, HoistableE e) => b n l -> e l -> DCEM l (HoistExcept (e n))
hoistUsingCachedFVs b e = do
  ec <- wrapWithCachedFVs e
  return $ case hoist b ec of
    HoistSuccess e' -> HoistSuccess $ fromCachedFVs e'
    HoistFailure err -> HoistFailure err

data ElimResult n where
  ElimSuccess :: Abs (Nest Decl) Atom n -> ElimResult n
  ElimFailure :: Decl n l -> Abs (Nest Decl) Atom l -> ElimResult n

dceNest :: Nest Decl n l -> Atom l -> DCEM n (Abs (Nest Decl) Atom n)
dceNest decls ans = case decls of
  Empty -> Abs Empty <$> dce ans
  Nest b@(Let _ decl) bs -> do
    isPureDecl <- isPure decl
    -- Note that we only ever dce the abs below under this refreshAbs,
    -- which will remove any references to b upon exit (it happens
    -- because refreshAbs of StateT1 triggers hoistState, which we
    -- implement by deleting the entries that can't hoist).
    dceAttempt <- refreshAbs (Abs b (Abs bs ans)) \b' (Abs bs' ans') -> do
      below <- dceNest bs' ans'
      case isPureDecl of
        False -> return $ ElimFailure b' below
        True  -> do
          hoistUsingCachedFVs b' below <&> \case
            HoistSuccess below' -> ElimSuccess below'
            HoistFailure _ -> ElimFailure b' below
    case dceAttempt of
      ElimSuccess below' -> return below'
      ElimFailure (Let b' decl') (Abs bs'' ans'') -> do
        decl'' <- dce decl'
        modify (<>FV (freeVarsB b'))
        return $ Abs (Nest (Let b' decl'') bs'') ans''

-- The generic instances

instance (HasDCE e1, HasDCE e2) => HasDCE (ExtLabeledItemsE e1 e2)
instance HasDCE Expr
instance HasDCE Atom
instance HasDCE LamExpr
instance HasDCE TabLamExpr
instance HasDCE PiType
instance HasDCE TabPiType
instance HasDCE DepPairType
instance HasDCE EffectRow
instance HasDCE Effect
instance HasDCE DictExpr
instance HasDCE DictType
instance HasDCE FieldRowElems
instance HasDCE FieldRowElem
instance HasDCE DataDefParams
instance HasDCE DeclBinding

-- The instances for RepE types

instance (HasDCE e1, HasDCE e2) => HasDCE (PairE e1 e2) where
  dce (PairE l r) = PairE <$> dce l <*> dce r
  {-# INLINE dce #-}
instance (HasDCE e1, HasDCE e2) => HasDCE (EitherE e1 e2) where
  dce = \case
    LeftE  l -> LeftE  <$> dce l
    RightE r -> RightE <$> dce r
  {-# INLINE dce #-}
instance ( HasDCE e0, HasDCE e1, HasDCE e2, HasDCE e3
         , HasDCE e4, HasDCE e5, HasDCE e6, HasDCE e7
         ) => HasDCE (EitherE8 e0 e1 e2 e3 e4 e5 e6 e7) where
  dce = \case
    Case0 x0 -> Case0 <$> dce x0
    Case1 x1 -> Case1 <$> dce x1
    Case2 x2 -> Case2 <$> dce x2
    Case3 x3 -> Case3 <$> dce x3
    Case4 x4 -> Case4 <$> dce x4
    Case5 x5 -> Case5 <$> dce x5
    Case6 x6 -> Case6 <$> dce x6
    Case7 x7 -> Case7 <$> dce x7
  {-# INLINE dce #-}
instance (BindsEnv b, SubstB Name b, HoistableB b, SubstE Name e, HasDCE e) => HasDCE (Abs b e) where
  dce a = do
    a'@(Abs b' _) <- refreshAbs a \b e -> Abs b <$> dce e
    modify (<>FV (freeVarsB b'))
    return a'
  {-# INLINE dce #-}
instance HasDCE (LiftE a) where
  dce x = return x
  {-# INLINE dce #-}
instance HasDCE VoidE where
  dce _ = error "impossible"
  {-# INLINE dce #-}
instance HasDCE UnitE where
  dce UnitE = return UnitE
  {-# INLINE dce #-}
instance (Traversable f, HasDCE e) => HasDCE (ComposeE f e) where
  dce (ComposeE xs) = ComposeE <$> traverse dce xs
  {-# INLINE dce #-}
instance HasDCE e => HasDCE (ListE e) where
  dce (ListE xs) = ListE <$> traverse dce xs
  {-# INLINE dce #-}

-- See Note [Confuse GHC] from Simplify.hs
confuseGHC :: EnvReader m => m n (DistinctEvidence n)
confuseGHC = getDistinct
{-# INLINE confuseGHC #-}
