-- Copyright 2022 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE UndecidableInstances #-}

module Optimize
  ( optimize, peepholeOp
  , hoistLoopInvariant, hoistLoopInvariantDest
  , dceTop, dceTopDest
  , foldCast ) where

import Data.Functor
import Data.Word
import Data.Bits
import Data.Bits.Floating
import Data.List
import Data.List.NonEmpty qualified as NE
import Control.Monad
import Control.Monad.State.Strict
import GHC.Float

import Types.Core
import Types.Primitives
import MTL1
import Name
import Subst
import IRVariants
import Core
import GenericTraversal
import Builder
import QueryType
import Util (iota)

optimize :: EnvReader m => SLam n -> m n (SLam n)
optimize = dceTop     -- Clean up user code
       >=> unrollLoops
       >=> dceTop     -- Clean up peephole-optimized code after unrolling
       >=> hoistLoopInvariant
{-# SCC optimize #-}

-- === Peephole optimizations ===

peepholeOp :: PrimOp (Atom SimpIR o) -> EnvReaderM o (Either (SAtom o) (PrimOp (Atom SimpIR o)))
peepholeOp op = case op of
  MiscOp (CastOp (BaseTy (Scalar sTy)) (Con (Lit l))) -> return $ case foldCast sTy l of
    Just l' -> lit l'
    Nothing -> noop
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
  MiscOp (ToEnum ty (Con (Lit (Word8Lit tag)))) -> Left <$> case ty of
    SumTy cases -> return $ SumVal cases (fromIntegral tag) UnitVal
    _ -> error "Ill typed ToEnum?"
  MiscOp (SumTag (SumVal _ tag _))                   -> return $ lit $ Word8Lit $ fromIntegral tag
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
    -- This rounds to nearest.  Empirically (see test suite), it also seems to
    -- break ties the same way LLVM does, but I don't have a proof of that.
    -- LLVM's tie-breaking may be system-specific?
    fixUlp orig candidate = closest [candidate, candidatem1, candidatep1] where
      candidatem1 = nextDown candidate
      candidatep1 = nextUp candidate
      closest items = minimumBy (\ca cb -> err ca `compare` err cb) items
      err cand = absdiff orig (round cand)
      absdiff a b = if a >= b then a - b else b - a

peepholeExpr :: SExpr o -> EnvReaderM o (Either (SAtom o) (SExpr o))
peepholeExpr expr = case expr of
  PrimOp op -> fmap PrimOp <$> peepholeOp op
  TabApp (Var t) (IdxRepVal ord NE.:| []) ->
    lookupAtomName t <&> \case
      LetBound (DeclBinding ann _ (TabCon Nothing tabTy elems))
        | ann /= NoInlineLet && isFinTabTy tabTy->
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
  where isFinTabTy = \case
          TabPi (TabPiType (_:>(IxType _ (IxDictRawFin _))) _) -> True
          _ -> False

-- === Loop unrolling ===

unrollLoops :: EnvReader m => SLam n -> m n (SLam n)
unrollLoops = liftLamExpr unrollLoopsBlock

unrollLoopsBlock :: EnvReader m => SBlock n -> m n (SBlock n)
unrollLoopsBlock b = liftM fst $ liftGenericTraverserM (ULS 0) $ traverseGenericE b

newtype ULS n = ULS Int deriving Show
type ULM = GenericTraverserM SimpIR UnitB ULS
instance SinkableE ULS where
  sinkingProofE _ (ULS c) = ULS c
instance HoistableState ULS where
  hoistState _ _ (ULS c) = (ULS c)
  {-# INLINE hoistState #-}

-- TODO: Refine the cost accounting so that operations that will become
-- constant-foldable after inlining don't count towards it.
instance GenericTraverser SimpIR UnitB ULS where
  traverseInlineExpr expr = case expr of
    Hof (For Fwd ixDict body) ->
      case ixDict of
        IxDictRawFin (IdxRepVal n) -> do
          (body', bodyCost) <- withLocalAccounting $ traverseGenericE body
          -- We add n (in the form of (... + 1) * n) for the cost of the TabCon reconstructing the result.
          case (bodyCost + 1) * (fromIntegral n) <= unrollBlowupThreshold of
            True -> case body' of
              UnaryLamExpr b' block' -> do
                vals <- dropSubst $ forM (iota n) \i -> do
                  extendSubst (b' @> SubstVal (IdxRepVal i)) $ emitSubstBlock block'
                inc $ fromIntegral n  -- To account for the TabCon we emit below
                getNaryLamExprType body' >>= \case
                  NaryPiType (UnaryNest (tb:>_)) _ valTy -> do
                    let ixTy = IxType IdxRepTy (IxDictRawFin (IdxRepVal n))
                    let tabTy = TabPi $ TabPiType (tb:>ixTy) valTy
                    return $ Right $ TabCon Nothing tabTy vals
                  _ -> error "Expected `for` body to have a Pi type"
              _ -> error "Expected `for` body to be a lambda expression"
            False -> do
              inc bodyCost
              ixDict' <- traverseGenericE ixDict
              return $ Right $ Hof $ For Fwd ixDict' body'
        _ -> nothingSpecial
    -- Avoid unrolling loops with large table literals
    TabCon _ _ els -> inc (length els) >> nothingSpecial
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

emitSubstBlock :: Emits o => SBlock i -> ULM i o (SAtom o)
emitSubstBlock (Block _ decls ans) = traverseDeclNest decls $ traverseAtom ans

-- === Loop invariant code motion ===

hoistLoopInvariantBlock :: EnvReader m => SBlock n -> m n (SBlock n)
hoistLoopInvariantBlock body = liftM fst $ liftGenericTraverserM LICMS $ traverseGenericE body
{-# SCC hoistLoopInvariantBlock #-}

hoistLoopInvariantDestBlock :: EnvReader m => DestBlock SimpIR n -> m n (DestBlock SimpIR n)
hoistLoopInvariantDestBlock (DestBlock (db:>dTy) body) =
  liftM fst $ liftGenericTraverserM LICMS do
    dTy' <- traverseGenericE dTy
    (Abs db' body') <- buildAbs (getNameHint db) dTy' \v ->
      extendRenamer (db@>v) $ traverseGenericE body
    return $ DestBlock db' body'
{-# SCC hoistLoopInvariantDestBlock #-}

hoistLoopInvariant :: EnvReader m => SLam n -> m n (SLam n)
hoistLoopInvariant = liftLamExpr hoistLoopInvariantBlock
{-# INLINE hoistLoopInvariant #-}

hoistLoopInvariantDest :: EnvReader m => DestLamExpr SimpIR n -> m n (DestLamExpr SimpIR n)
hoistLoopInvariantDest (DestLamExpr bs body) = liftEnvReaderM $
  refreshAbs (Abs bs body) \bs' body' ->
    DestLamExpr bs' <$> hoistLoopInvariantDestBlock body'

data LICMS (n::S) = LICMS
instance SinkableE LICMS where
  sinkingProofE _ LICMS = LICMS
instance HoistableState LICMS where
  hoistState _ _ LICMS = LICMS

instance GenericTraverser SimpIR UnitB LICMS where
  traverseExpr = \case
    DAMOp (Seq dir ix (ProdVal dests) (LamExpr (UnaryNest b) body)) -> do
      ix' <- substM ix
      dests' <- traverse traverseAtom dests
      let numCarriesOriginal = length dests'
      Abs hdecls destsAndBody <- traverseBinder b \b' -> do
        -- First, traverse the block, to allow any Hofs inside it to hoist their own decls.
        Block _ decls ans <- traverseGenericE body
        -- Now, we process the decls and decide which ones to hoist.
        liftEnvReaderM $ runSubstReaderT idSubst $
            seqLICM REmpty mempty (asNameBinder b') REmpty decls ans
      PairE (ListE extraDests) ab <- emitDecls hdecls destsAndBody
      -- Append the destinations of hoisted Allocs as loop carried values.
      let dests'' = ProdVal $ dests' ++ (Var <$> extraDests)
      carryTy <- getType dests''
      lbTy <- ixTyFromDict ix' <&> \case IxType ixTy _ -> PairTy ixTy carryTy
      extraDestsTyped <- forM extraDests \d -> (d,) <$> getType d
      Abs extraDestBs (Abs lb bodyAbs) <- return $ abstractFreeVars extraDestsTyped ab
      body' <- withFreshBinder noHint lbTy \lb' -> do
        (oldIx, allCarries) <- fromPair $ Var $ binderName lb'
        (oldCarries, newCarries) <- splitAt numCarriesOriginal <$> getUnpacked allCarries
        let oldLoopBinderVal = PairVal oldIx (ProdVal oldCarries)
        let s = extraDestBs @@> map SubstVal newCarries <.> lb @> SubstVal oldLoopBinderVal
        block <- applySubst s bodyAbs >>= makeBlockFromDecls
        return $ UnaryLamExpr lb' block
      return $ DAMOp $ Seq dir ix' dests'' body'
    Hof (For dir ix (LamExpr (UnaryNest b) body)) -> do
      ix' <- substM ix
      Abs hdecls destsAndBody <- traverseBinder b \b' -> do
        Block _ decls ans <- traverseGenericE body
        liftEnvReaderM $ runSubstReaderT idSubst $
            seqLICM REmpty mempty (asNameBinder b') REmpty decls ans
      PairE (ListE []) (Abs lnb bodyAbs) <- emitDecls hdecls destsAndBody
      ixTy <- substM $ binderType b
      body' <- withFreshBinder noHint ixTy \i -> do
        block <- applyRename (lnb@>binderName i) bodyAbs >>= makeBlockFromDecls
        return $ UnaryLamExpr i block
      return $ Hof $ For dir ix' body'
    expr -> traverseExprDefault expr

seqLICM :: RNest SDecl n1 n2      -- hoisted decls
        -> [SAtomName n2]         -- hoisted dests
        -> AtomNameBinder SimpIR n2 n3   -- loop binder
        -> RNest SDecl n3 n4      -- loop-dependent decls
        -> Nest SDecl m1 m2       -- decls remaining to process
        -> SAtom m2               -- loop result
        -> SubstReaderT AtomSubstVal EnvReaderM m1 n4
             (Abs (Nest SDecl)            -- hoisted decls
                (PairE (ListE SAtomName)  -- hoisted allocs (these should go in the loop carry)
                       (Abs (AtomNameBinder SimpIR) -- loop binder
                            (Abs (Nest SDecl)       -- non-hoisted decls
                             SAtom))) n1)           -- final result
seqLICM !top !topDestNames !lb !reg decls ans = case decls of
  Empty -> do
    ans' <- substM ans
    return $ Abs (unRNest top) $ PairE (ListE $ reverse topDestNames) $ Abs lb $ Abs (unRNest reg) ans'
  Nest (Let bb binding) bs -> do
    binding' <- substM binding
    effs <- getEffects binding'
    withFreshBinder (getNameHint bb) binding' \(bb':>_) -> do
      let b = Let bb' binding'
      let moveOn = extendRenamer (bb@>binderName bb') $
                     seqLICM top topDestNames lb (RNest reg b) bs ans
      case effs of
        -- OPTIMIZE: We keep querying the ScopeFrag of lb and reg here, leading to quadratic runtime
        Pure -> case exchangeBs $ PairB (PairB lb reg) b of
          HoistSuccess (PairB b' lbreg@(PairB lb' reg')) -> do
            withSubscopeDistinct lbreg $ withExtEvidence b' $
              extendRenamer (bb@>sink (binderName b')) do
                extraTopDestNames <- return case b' of
                  Let bn (DeclBinding _ _ (DAMOp (AllocDest _))) -> [binderName bn]
                  _ -> []
                seqLICM (RNest top b') (extraTopDestNames ++ sinkList topDestNames) lb' reg' bs ans
              where
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

dceTop :: EnvReader m => SLam n -> m n (SLam n)
dceTop = liftLamExpr dceBlock
{-# INLINE dceTop #-}

dceTopDest :: EnvReader m => DestLamExpr SimpIR n -> m n (DestLamExpr SimpIR n)
dceTopDest (DestLamExpr bs body) = liftEnvReaderM $
  refreshAbs (Abs bs body) \bs' body' -> DestLamExpr bs' <$> dceDestBlock body'
{-# INLINE dceTopDest #-}

dceBlock :: EnvReader m => SBlock n -> m n (SBlock n)
dceBlock b = liftEnvReaderM $ evalStateT1 (dce b) mempty
{-# SCC dceBlock #-}

dceDestBlock :: EnvReader m => DestBlock SimpIR n -> m n (DestBlock SimpIR n)
dceDestBlock (DestBlock d b) = liftEnvReaderM $
  refreshAbs (Abs d b) \d' b' -> DestBlock d' <$> dceBlock b'
{-# INLINE dceDestBlock #-}

class HasDCE (e::E) where
  dce :: e n -> DCEM n (e n)
  default dce :: (GenericE e, HasDCE (RepE e)) => e n -> DCEM n (e n)
  dce e = confuseGHC >>= \_ -> toE <$> dce (fromE e)

-- The interesting instances

instance Color c => HasDCE (Name c) where
  dce n = modify (<> FV (freeVarsE n)) $> n

instance HasDCE SBlock where
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
  ElimSuccess :: Abs (Nest SDecl) SAtom n -> ElimResult n
  ElimFailure :: SDecl n l -> Abs (Nest SDecl) SAtom l -> ElimResult n

dceNest :: Nest SDecl n l -> SAtom l -> DCEM n (Abs (Nest SDecl) SAtom n)
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
instance HasDCE SExpr
instance HasDCE (RefOp SimpIR)
instance HasDCE (BaseMonoid SimpIR)
instance HasDCE (Hof SimpIR)
instance HasDCE SAtom
instance HasDCE (LamExpr     SimpIR)
instance HasDCE (TabPiType   SimpIR)
instance HasDCE (DepPairType SimpIR)
instance HasDCE (EffectRowTail SimpIR)
instance HasDCE (EffectRow     SimpIR)
instance HasDCE (Effect        SimpIR)
instance HasDCE (DeclBinding   SimpIR)
instance HasDCE (DAMOp         SimpIR)
instance HasDCE (IxDict        SimpIR)

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
instance (BindsEnv b, RenameB b, HoistableB b, RenameE e, HasDCE e) => HasDCE (Abs b e) where
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
instance HasDCE e => HasDCE (WhenE True e) where
  dce (WhenE e) = WhenE <$> dce e
instance HasDCE (WhenE False e) where
  dce _ = undefined

instance HasDCE (RepVal SimpIR) where
  dce e = modify (<> FV (freeVarsE e)) $> e

instance HasDCE (WhenCore SimpIR e) where dce = \case
instance HasDCE e => HasDCE (WhenCore CoreIR e) where
  dce (WhenIRE e) = WhenIRE <$> dce e

instance HasDCE (WhenSimp CoreIR e) where dce = \case
instance HasDCE e => HasDCE (WhenSimp SimpIR e) where
  dce (WhenIRE e) = WhenIRE <$> dce e

-- See Note [Confuse GHC] from Simplify.hs
confuseGHC :: EnvReader m => m n (DistinctEvidence n)
confuseGHC = getDistinct
{-# INLINE confuseGHC #-}
