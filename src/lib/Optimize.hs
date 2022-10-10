-- Copyright 2022 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE UndecidableInstances #-}

module Optimize
  ( earlyOptimize, optimize
  , peepholeOp, hoistLoopInvariantIxDest, dceIxDestBlock
  ) where

import Data.Functor
import Data.Word
import Data.Bits
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
import Util (iota)

earlyOptimize :: EnvReader m => Block n -> m n (Block n)
earlyOptimize = unrollTrivialLoops

optimize :: EnvReader m => Block n -> m n (Block n)
optimize = dceBlock     -- Clean up user code
       >=> unrollLoops
       >=> dceBlock     -- Clean up peephole-optimized code after unrolling
       >=> hoistLoopInvariant

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
  TC (Fin (NatVal n)) | n <= 0 -> return EmptyIxSet
  TC (Fin (NatVal n)) | n == 1 ->
    return $ SingletonIxSet $ Con $ Newtype (FinConst n) (NatVal 0)
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

peepholeOp :: Op o -> EnvReaderM o (Either (Atom o) (Op o))
peepholeOp op = case op of
  CastOp (BaseTy (Scalar sTy)) (Con (Lit l)) -> return $ case sTy of
    -- TODO: Support all casts.
    Int32Type -> case l of
      Int32Lit  _  -> lit l
      Int64Lit  i  -> lit $ Int32Lit  $ fromIntegral i
      Word8Lit  i  -> lit $ Int32Lit  $ fromIntegral i
      Word32Lit i  -> lit $ Int32Lit  $ fromIntegral i
      Word64Lit i  -> lit $ Int32Lit  $ fromIntegral i
      Float32Lit _ -> noop
      Float64Lit _ -> noop
      PtrLit     _ -> noop
    Int64Type -> case l of
      Int32Lit  i  -> lit $ Int64Lit  $ fromIntegral i
      Int64Lit  _  -> lit l
      Word8Lit  i  -> lit $ Int64Lit  $ fromIntegral i
      Word32Lit i  -> lit $ Int64Lit  $ fromIntegral i
      Word64Lit i  -> lit $ Int64Lit  $ fromIntegral i
      Float32Lit _ -> noop
      Float64Lit _ -> noop
      PtrLit     _ -> noop
    Word8Type -> case l of
      Int32Lit  i  -> lit $ Word8Lit  $ fromIntegral i
      Int64Lit  i  -> lit $ Word8Lit  $ fromIntegral i
      Word8Lit  _  -> lit l
      Word32Lit i  -> lit $ Word8Lit  $ fromIntegral i
      Word64Lit i  -> lit $ Word8Lit  $ fromIntegral i
      Float32Lit _ -> noop
      Float64Lit _ -> noop
      PtrLit     _ -> noop
    Word32Type -> case l of
      Int32Lit  i  -> lit $ Word32Lit $ fromIntegral i
      Int64Lit  i  -> lit $ Word32Lit $ fromIntegral i
      Word8Lit  i  -> lit $ Word32Lit $ fromIntegral i
      Word32Lit _  -> lit l
      Word64Lit i  -> lit $ Word32Lit $ fromIntegral i
      Float32Lit _ -> noop
      Float64Lit _ -> noop
      PtrLit     _ -> noop
    Word64Type -> case l of
      Int32Lit  i  -> lit $ Word64Lit $ fromIntegral (fromIntegral i :: Word32)
      Int64Lit  i  -> lit $ Word64Lit $ fromIntegral i
      Word8Lit  i  -> lit $ Word64Lit $ fromIntegral i
      Word32Lit i  -> lit $ Word64Lit $ fromIntegral i
      Word64Lit _  -> lit l
      Float32Lit _ -> noop
      Float64Lit _ -> noop
      PtrLit     _ -> noop
    _ -> noop
  -- TODO: Support more unary and binary ops.
  BinOp IAdd l r -> return $ case (l, r) of
    -- TODO: Shortcut when either side is zero.
    (Con (Lit ll), Con (Lit rl)) -> case (ll, rl) of
      (Word32Lit lv, Word32Lit lr) -> lit $ Word32Lit $ lv + lr
      _ -> noop
    _ -> noop
  BinOp (ICmp cop) (Con (Lit ll)) (Con (Lit rl)) ->
    return $ lit $ Word8Lit $ fromIntegral $ fromEnum $ case (ll, rl) of
      (Int32Lit  lv, Int32Lit  rv) -> cmp cop lv rv
      (Int64Lit  lv, Int64Lit  rv) -> cmp cop lv rv
      (Word8Lit  lv, Word8Lit  rv) -> cmp cop lv rv
      (Word32Lit lv, Word32Lit rv) -> cmp cop lv rv
      (Word64Lit lv, Word64Lit rv) -> cmp cop lv rv
      _ -> error "Ill typed ICmp?"
  BinOp (FCmp cop) (Con (Lit ll)) (Con (Lit rl)) ->
    return $ lit $ Word8Lit $ fromIntegral $ fromEnum $ case (ll, rl) of
      (Float32Lit lv, Float32Lit rv) -> cmp cop lv rv
      (Float64Lit lv, Float64Lit rv) -> cmp cop lv rv
      _ -> error "Ill typed FCmp?"
  BinOp BOr (Con (Lit (Word8Lit lv))) (Con (Lit (Word8Lit rv))) ->
    return $ lit $ Word8Lit $ lv .|. rv
  BinOp BAnd (Con (Lit (Word8Lit lv))) (Con (Lit (Word8Lit rv))) ->
    return $ lit $ Word8Lit $ lv .&. rv
  ToEnum ty (Con (Lit (Word8Lit tag))) -> Left <$> case ty of
    TypeCon _ defName _ -> do
      DataDef _ _ cons <- lookupDataDef defName
      return $ Con $ Newtype ty $ SumVal (cons <&> const UnitTy) (fromIntegral tag) UnitVal
    SumTy cases -> return $ SumVal cases (fromIntegral tag) UnitVal
    _ -> error "Ill typed ToEnum?"
  SumTag (Con (Newtype _ (SumVal _ tag _))) -> return $ lit $ Word8Lit $ fromIntegral tag
  SumTag (SumVal _ tag _)                   -> return $ lit $ Word8Lit $ fromIntegral tag
  _ -> return noop
  where
    noop = Right op
    lit = Left . Con . Lit

    cmp :: Ord a => CmpOp -> a -> a -> Bool
    cmp = \case
      Less         -> (<)
      Greater      -> (>)
      Equal        -> (==)
      LessEqual    -> (<=)
      GreaterEqual -> (>=)

peepholeExpr :: Expr o -> EnvReaderM o (Either (Atom o) (Expr o))
peepholeExpr expr = case expr of
  Op op -> fmap Op <$> peepholeOp op
  TabApp (Var t) ((Con (Newtype (TC (Fin _)) (NatVal ord))) NE.:| []) ->
    lookupAtomName t <&> \case
      LetBound (DeclBinding PlainLet _ (Op (TabCon _ elems))) ->
        -- It is not safe to assume that this index can always be simplified!
        -- For example, it might be coming from an unsafe_from_ordinal that is
        -- under a case branch that would be dead for all invalid indices.
        if 0 <= ord && fromIntegral ord < length elems
          then Left $ elems !! fromIntegral ord
          else Right expr
      _ -> Right expr
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
          -- We add n (in the form of (... + 1) * n) for the cost of the TabCon reconstructing the result.
          case (bodyCost + 1) * (fromIntegral n) <= unrollBlowupThreshold of
            True -> case body' of
              Lam (LamExpr b' block') -> do
                vals <- dropSubst $ forM (iota n) \ord -> do
                  let i = Con $ Newtype (FinConst n) (NatVal ord)
                  extendSubst (b' @> SubstVal i) $ emitSubstBlock block'
                inc $ fromIntegral n  -- To account for the TabCon we emit below
                getType body' >>= \case
                  Pi (PiType (PiBinder tb _ _) _ valTy) -> do
                    let tabTy = TabPi $ TabPiType (tb:>IxType (FinConst n) (DictCon (IxFin $ NatVal n))) valTy
                    return $ Right $ Op $ TabCon tabTy vals
                  _ -> error "Expected for body to have a Pi type"
              _ -> error "Expected for body to be a lambda expression"
            False -> do
              inc bodyCost
              ixDict' <- traverseGenericE ixDict
              return $ Right $ Hof $ For Fwd ixDict' body'
        _ -> nothingSpecial
    -- Avoid unrolling loops with large table literals
    Op (TabCon _ els) -> inc (length els) >> nothingSpecial
    _ -> nothingSpecial
    where
      inc i = modify \(ULS n) -> ULS (n + i)
      nothingSpecial = inc 1 >> (traverseExprDefault expr >>= liftEnvReaderM . peepholeExpr)
      unrollBlowupThreshold = 12
      withLocalAccounting m = do
        oldCost <- get
        ans <- put (ULS 0) *> m
        ULS newCost <- get
        put oldCost $> (ans, newCost)
      {-# INLINE withLocalAccounting #-}

emitSubstBlock :: Emits o => Block i -> ULM i o (Atom o)
emitSubstBlock (Block _ decls ans) = traverseDeclNest decls $ traverseAtom ans

-- === Loop invariant code motion ===

-- TODO: Resolve import cycle with Lower
type IxDestBlock = Abs (Nest Decl) (Abs Binder Block)

hoistLoopInvariantIxDest :: EnvReader m => IxDestBlock n -> m n (IxDestBlock n)
hoistLoopInvariantIxDest (Abs ixs (Abs (db:>dTy) body)) =
  liftM fst $ liftGenericTraverserM LICMS $
    buildScoped $ traverseDeclNest ixs do
      dTy' <- traverseGenericE dTy
      buildAbs (getNameHint db) dTy' \v -> extendRenamer (db@>v) $ traverseGenericE body

hoistLoopInvariant :: EnvReader m => Block n -> m n (Block n)
hoistLoopInvariant body = liftM fst $ liftGenericTraverserM LICMS $ traverseGenericE body

data LICMS (n::S) = LICMS
instance SinkableE LICMS where
  sinkingProofE _ LICMS = LICMS
instance HoistableState LICMS where
  hoistState _ _ LICMS = LICMS

instance GenericTraverser LICMS where
  traverseExpr = \case
    Hof (Seq dir ix (ProdVal dests) (Lam (LamExpr b body))) -> do
      ix' <- traverseAtom ix
      dests' <- traverse traverseAtom dests
      let numCarries = length dests
      Abs hdecls destsAndBody <- traverseLamBinder b \b' -> do
        -- First, traverse the block, to allow any Hofs inside it to hoist their own decls.
        Block _ decls ans <- traverseGenericE body
        -- Now, we process the decls and decide which ones to hoist.
        liftEnvReaderM $ runSubstReaderT idSubst $
            seqLICM numCarries REmpty mempty (asNameBinder b') REmpty decls ans
      PairE (ListE extraDests) (Abs lnb bodyAbs) <- emitDecls hdecls destsAndBody
      -- Append the destinations of hoisted Allocs as loop carried values.
      let dests'' = ProdVal $ dests' ++ (Var <$> extraDests)
      carryTy <- getType dests''
      lbTy <- getType ix' <&> \case
        DictTy (DictType _ _ [ixTy]) -> PairTy ixTy carryTy
        _ -> error "Expected a dict"
      body' <- rebuildBody b body lnb lbTy bodyAbs
      return $ Hof $ Seq dir ix' dests'' body'
    Hof (For dir ix (Lam (LamExpr b body))) -> do
      ix' <- traverseAtom ix
      Abs hdecls destsAndBody <- traverseLamBinder b \b' -> do
        Block _ decls ans <- traverseGenericE body
        liftEnvReaderM $ runSubstReaderT idSubst $
            seqLICM 0 REmpty mempty (asNameBinder b') REmpty decls ans
      PairE (ListE []) (Abs lnb bodyAbs) <- emitDecls hdecls destsAndBody
      ixTy <- substM $ binderType b
      body' <- rebuildBody b body lnb ixTy bodyAbs
      return $ Hof $ For dir ix' body'
    expr -> traverseExprDefault expr
    where
      rebuildBody :: LamBinder i i' -> Block i'
                  -> AtomNameBinder n l -> Type n -> Abs (Nest Decl) Atom l
                  -> GenericTraverserM LICMS i n (Atom n)
      rebuildBody b body@(Block ann _ _) lnb lbTy bodyAbs = do
        Distinct <- getDistinct
        refreshAbs (Abs (lnb:>lbTy) bodyAbs) \lb (Abs decls ans) -> do
          extendRenamer (b@>binderName lb) do
            ann'@(BlockAnn _ eff') <- case ann of
              BlockAnn ty eff -> BlockAnn <$> substM ty <*> substM eff
              NoBlockAnn -> BlockAnn <$> getTypeSubst body <*> pure Pure
            let b'' = LamBinder (asNameBinder lb) (sink lbTy) PlainArrow eff'
            return $ Lam $ LamExpr b'' $ Block ann' decls ans

seqLICM :: Int
        -> RNest Decl n1 n2      -- hoisted decls
        -> [AtomName n2]         -- hoisted dests
        -> AtomNameBinder n2 n3  -- loop binder
        -> RNest Decl n3 n4      -- loop-dependent decls
        -> Nest Decl m1 m2       -- decls remaining to process
        -> Atom m2               -- loop result
        -> SubstReaderT AtomSubstVal EnvReaderM m1 n4
             (Abs (Nest Decl)
                (PairE (ListE AtomName)
                       (Abs AtomNameBinder (Abs (Nest Decl) Atom))) n1)
seqLICM !nextProj !top !topDestNames !lb !reg decls ans = case decls of
  Empty -> do
    ans' <- substM ans
    return $ Abs (unRNest top) $ PairE (ListE $ reverse topDestNames) $ Abs lb $ Abs (unRNest reg) ans'
  Nest (Let bb binding) bs -> do
    binding' <- substM binding
    effs <- getEffects binding'
    withFreshBinder (getNameHint bb) binding' \bb' -> do
      let b = Let bb' binding'
      let moveOn = extendRenamer (bb@>binderName bb') $
                     seqLICM nextProj top topDestNames lb (RNest reg b) bs ans
      case effs of
        -- OPTIMIZE: We keep querying the ScopeFrag of lb and reg here, leading to quadratic runtime
        Pure -> case exchangeBs $ PairB (PairB lb reg) b of
          HoistSuccess (PairB b' lbreg@(PairB lb' reg')) -> extendSubst (bb@>bsv') $
              seqLICM nextProj' (RNest top b') topDestNames' lb' reg' bs ans
              where
                (nextProj', topDestNames', bsv') =
                  withSubscopeDistinct lbreg $ withExtEvidence b' $ case b' of
                    Let bn (DeclBinding _ _ (Op (AllocDest _))) ->
                      ( nextProj + 1
                      , binderName bn : sinkList topDestNames
                      , SubstVal $ ProjectElt (nextProj NE.:| [1]) $ withExtEvidence reg' $ sink $ binderName lb')
                    _ -> (nextProj, sinkList topDestNames, Rename $ sink $ binderName b')
          HoistFailure _ -> moveOn
        _ -> moveOn

-- === Dead code elimination ===

newtype FV n = FV (NameSet n) deriving (Semigroup, Monoid)
instance SinkableE FV where
  sinkingProofE _ _ = todoSinkableProof
instance HoistableState FV where
  hoistState _ b (FV ns) = FV $ hoistFilterNameSet b ns
  {-# INLINE hoistState #-}

type DCEM = StateT1 FV EnvReaderM

dceIxDestBlock :: EnvReader m => IxDestBlock n -> m n (IxDestBlock n)
dceIxDestBlock idb = liftEnvReaderM $
  refreshAbs idb \ixs db ->
    refreshAbs db \d b -> Abs ixs . Abs d <$> dceBlock b

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
instance HasDCE EffectOpType
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
