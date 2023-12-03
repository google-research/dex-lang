-- Copyright 2022 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module OccAnalysis (analyzeOccurrences) where

import Control.Monad.State.Strict
import Data.List (foldl')
import Data.Maybe (fromMaybe)
import Control.Monad.Reader.Class

import Core
import CheapReduction
import IRVariants
import Name
import MTL1
import Occurrence hiding (Var)
import Occurrence qualified as Occ
import Types.Core
import Types.Primitives
import Types.Top
import QueryType

-- === External API ===

-- This annotates every `Let` binding in the given `Block` with an `OccInfo`
-- annotation holding a summary of how that binding is used.  It also eliminates
-- unused pure bindings as it goes, since it has all the needed information.

analyzeOccurrences :: EnvReader m => TopLam SimpIR n -> m n (TopLam SimpIR n)
analyzeOccurrences lam = liftLamExpr lam \e -> liftOCCM $ occ accessOnce e
{-# INLINE analyzeOccurrences #-}

-- === Overview ===

-- We analyze every binding in the program for occurrence information,
-- namely information on how much it is used.
--
-- If a (pure) binding is not used at all, we take the opportunity to
-- eliminate it.  Otherwise, we track both static and dynamic usage
-- information:
-- - If a binding is used statically at most once, then inlining it
--   does not increase code size
-- - If a binding is used dynamically at most once, then inlining it
--   does not increase runtime work
--
-- The static usage information is just an Int counting the number of
-- static uses.  The dynamic usage information is an
-- Occ.DynUseInfo, counting an upper bound on the number of
-- dynamic uses, and keeping track of how many dimensions of indexing
-- have to be apparent for inlining to be work-preserving.  (For
-- example, if the usage is `for i. xs.i`, in order to inline `xs`
-- safely, we need to have access to the `for` expression that
-- constructed it so as to cancel against the indexing expression.)

-- === Data Structure ===

-- Our primary operating structure is a map (potentially partial) from names to
-- their current Occ.AccessInfo information.

newtype FV (n::S) = FV { freeVars :: (NameMapE (AtomNameC SimpIR) AccessInfo n) }

instance Monoid (FV n) where
  mempty = FV mempty
  mappend = (<>)

instance Semigroup (FV n) where
  (FV m1) <> (FV m2) = FV $ unionWithNameMapE plus m1 m2

deriving instance MaxPlus (FV n)

instance SinkableE FV where
  sinkingProofE _ _ = todoSinkableProof
instance HoistableState FV where
  -- By this point we need to make sure that none of the AccessInfo in the map
  -- refer to the binder being hoisted above.
  hoistState _ b (FV ns) = FV $ case hoistNameMapE b ns of
    HoistFailure vs -> error $ "Could not hoist: " ++ show vs ++ " escaped"
    HoistSuccess ns' -> ns'
  {-# INLINE hoistState #-}

-- Close every AccessInfo in the given FV by abstracting over the given binder
-- with `Occ.ForEach`, i.e., because it's the binder of a `for`.
-- We internally sink back under the binder because we are not (yet) removing
-- the entry for the binder itself, and the type of NameMapE cannot represent a
-- map from names in `l` to E-kinded things with names in `n` (though maybe it
-- should be changed?)
abstractFor :: DExt n l => Binder SimpIR n l -> FV l -> FV l
abstractFor (b:>_) (FV fvs) = FV $ mapNameMapE update fvs where
  update (AccessInfo s dyn) = sink $ AccessInfo s $ ForEach b dyn

-- Change all the AccessInfos to assume their objects are dynamically used many
-- times, as in the body of a `while`.
useManyTimes :: FV n -> FV n
useManyTimes (FV fvs) = FV $ mapNameMapE update fvs where
  update (AccessInfo s d) = AccessInfo s $ accessMuch d

-- Change all the AccessInfos to assume their objects are _statically_ used many
-- times, as for expressions that will be inlined unpredictably.
-- TODO(precision): If this is for a `view`, we could use the occurrence
-- information of the view itself to predict how much of an amplification
-- inlining it would cause.
useManyTimesStatic :: FV n -> FV n
useManyTimesStatic (FV fvs) = FV $ mapNameMapE update fvs where
  -- TODO(code cleanliness): Do we want to change the static counter to a Count
  -- so the Unbounded constructor is available here?
  update (AccessInfo _ d) = AccessInfo maxBound d

-- === Monad ===

-- We carry the above FV data structure, which is accumulated bottom up; and
-- also an environment accumulated top down that gives, for each name we have
-- encountered, an `IxExpr` summarizing what indexing by that name might mean,
-- should such indexing occur in that name's scope.
--
-- These `IxExpr`s are in terms of
-- - Binders already in scope when the analysis begins (e.g., the top-level
--   environment), and
-- - Binders introduced by `for`

type OCCM = ReaderT1 (NameMapE (AtomNameC SimpIR) IxExpr) (StateT1 FV EnvReaderM)

liftOCCM :: (EnvReader m) => OCCM n a -> m n a
liftOCCM action = liftEnvReaderM $ fst
  <$> runStateT1 (runReaderT1 mempty action) mempty
{-# INLINE liftOCCM #-}

getAccessInfo :: SAtomName n -> OCCM n (AccessInfo n)
getAccessInfo name = fromMaybe zero <$> gets (lookupNameMapE name . freeVars)
{-# INLINE getAccessInfo #-}

countFreeVarsAsOccurrences :: (HoistableE e) => e n -> OCCM n ()
countFreeVarsAsOccurrences obj =
  forM_ (freeAtomVarsList obj) \name -> do
    modify (<> FV (singletonNameMapE name $ AccessInfo One accessOnce))

countFreeVarsAsOccurrencesB :: (HoistableB b) => b n l -> OCCM n ()
countFreeVarsAsOccurrencesB obj =
  forM_ (freeAtomVarsList $ Abs obj UnitE) \name -> do
    modify (<> FV (singletonNameMapE name $ AccessInfo One accessOnce))

-- Run the given action with its own FV state, and return the FVs it accumulates
-- for post-processing.  Merging them back in is up to the caller.
separately :: OCCM n a -> OCCM n (a, FV n)
separately action = do
  r <- ask
  lift11 $ lift11 $ runStateT1 (runReaderT1 r action) mempty

-- Run the given action with its own FV state, and process its accumulated FVs
-- before merging.
censored :: (FV n -> FV n) -> OCCM n a -> OCCM n a
censored f act = do
  (a, fvs) <- separately act
  modify (<> f fvs)
  return a

-- Run the given action with its own FV state, then merge its accumulated FVs
-- afterwards.  (This is only meaningful if the action reads the FV state.)
isolated :: OCCM n a -> OCCM n a
isolated = censored id
{-# INLINE isolated #-}

-- Extend the IxExpr environment
extend :: (BindsOneName b (AtomNameC SimpIR))
  => b any n -> IxExpr n -> OCCM n a -> OCCM n a
extend b ix = local (<> singletonNameMapE (binderName b) ix)

-- Look up the `IxExpr` for a given name.  If the name doesn't occur in the map,
-- we return a `Occ.Var` of the name itself, thus claiming that the name is its
-- own summary.  This is what we want for `for` binders and top-level names.
ixExpr :: SAtomName n -> OCCM n (IxExpr n)
ixExpr name = do
  ixExprs <- ask
  case lookupNameMapE name ixExprs of
    Just ans -> return $ ans
    Nothing -> return $ Occ.Var name

-- `TabLamExpr` and `IxDicts` are meant to be inlined themselves, so we
-- have to assume that their occurrences may be replicated many times,
-- including statically.
inlinedLater :: (HoistableE e) => e n -> OCCM n (e n)
inlinedLater obj = do
  void $ censored (useManyTimesStatic . useManyTimes)
    $ countFreeVarsAsOccurrences obj
  return obj

-- === Computing IxExpr summaries ===

summaryExpr :: SExpr n -> OCCM n (IxExpr n)
summaryExpr = \case
  Atom atom -> summary atom
  expr -> unknown expr

summary :: SAtom n -> OCCM n (IxExpr n)
summary atom = case atom of
  Stuck _ stuck -> case stuck of
    Var v -> ixExpr $ atomVarName v
    _ -> unknown atom
  Con c -> case c of
    -- TODO Represent the actual literal value?
    Lit _ -> return $ Deterministic []
    ProdCon elts -> Product <$> mapM summary elts
    SumCon _ tag payload -> Inject tag <$> summary payload
    HeapVal -> invalid "HeapVal"
    DepPair _ _ _ -> error "not implemented"
  where
    invalid tag = error $ "Unexpected indexing by " ++ tag

unknown :: HoistableE e => e n -> OCCM n (IxExpr n)
unknown _ = return IxAll
  -- TODO(precision) It should be possible to return `Deterministic <free
  -- variables>` in most cases.  That's only unsound if
  -- - Any of the ixExpr of the free variables are themselves IxAll (which is
  --   easy to detect); or
  -- - The object has a funny effect like `IO`.  (Note that we wouldn't have to
  --   detect reader, writer, and state effects specially, because the summary
  --   of the reference should already have any necessary `IxAll` in it.)

-- === Visitor for the generic cases (carries Access in the reader) ===

newtype OCCMVisitor n a =
  OCCMVisitor { runOCCMVisitor' :: ReaderT1 Access OCCM n a }
  deriving (Functor, Applicative, Monad, MonadReader (Access n))

runOCCMVisitor :: Access n -> OCCMVisitor n a -> OCCM n a
runOCCMVisitor access cont = runReaderT1 access $ runOCCMVisitor' cont

occGeneric :: VisitGeneric e SimpIR => Access n -> e n -> OCCM n (e n)
occGeneric access x = runOCCMVisitor access $ visitGeneric x

instance NonAtomRenamer (OCCMVisitor n) n n where renameN = pure
instance Visitor (OCCMVisitor n) SimpIR n n where
  visitType = visitViaOcc
  visitAtom = visitViaOcc
  visitLam  = visitViaOcc
  visitPi   = visitViaOcc

visitViaOcc :: HasOCC e => e n -> OCCMVisitor n (e n)
visitViaOcc x = ask >>= \access -> OCCMVisitor $ lift11 $ occ access x

-- === The actual occurrence analysis ===

class HasOCC (e::E) where
  occ :: Access n -> e n -> OCCM n (e n)

instance HasOCC SAtom where
  occ a = \case
    Stuck t e -> Stuck <$> occ a t <*> occ a e
    Con con -> liftM Con $ runOCCMVisitor a $ visitGeneric con

instance HasOCC SStuck where
  occ a = \case
    Var (AtomVar n ty) -> do
      modify (<> FV (singletonNameMapE n $ AccessInfo One a))
      ty' <- occTy ty
      return $ Var (AtomVar n ty')
    StuckProject i x -> StuckProject <$> pure i <*> occ a x
    StuckTabApp array ixs -> do
      (a', ixs') <- occIdx a ixs
      array' <- occ a' array
      return $ StuckTabApp array' ixs'
    PtrVar t p -> return $ PtrVar t p
    RepValAtom x -> return $ RepValAtom x

instance HasOCC SType where
  occ a (TyCon con) = liftM TyCon $ runOCCMVisitor a $ visitGeneric con

-- TODO What, actually, is the right thing to do for type annotations?  Do we
-- want a rule like "we never inline into type annotations", or such?  For
-- now, traversing with the main analysis seems safe.
occTy :: SType n -> OCCM n (SType n)
occTy ty = occ accessOnce ty

instance HasOCC SLam where
  occ a (LamExpr bs body) = do
    lam@(LamExpr bs' _) <- refreshAbs (Abs bs body) \bs' body' ->
      LamExpr bs' <$> occ (sink a) body'
    countFreeVarsAsOccurrencesB bs'
    return lam

instance HasOCC (PiType SimpIR) where
  occ _ (PiType bs effTy) = do
    -- The way this and hoistState are written, the pass will crash if any of
    -- the AccessInfos reference this binder.
    piTy@(PiType bs' _) <- refreshAbs (Abs bs effTy) \b effTy' ->
      -- I (dougalm) am not sure about this. I'm just trying to mimic the old
      -- behavior when this would go through the `HasOCC PairE` instance.
      PiType b <$> occGeneric accessOnce effTy'
    countFreeVarsAsOccurrencesB bs'
    return piTy

instance HasOCC (EffTy SimpIR) where
  occ _ (EffTy effs ty) = do
    ty' <- occTy ty
    countFreeVarsAsOccurrences effs
    return $ EffTy effs ty'

data ElimResult (n::S) where
  ElimSuccess :: Abs (Nest SDecl) SExpr n -> ElimResult n
  ElimFailure :: SDecl n l -> UsageInfo -> Abs (Nest SDecl) SExpr l -> ElimResult n

occNest :: Access n -> Abs (Nest SDecl) SExpr n
        -> OCCM n (Abs (Nest SDecl) SExpr n)
occNest a (Abs decls ans) = case decls of
  Empty -> Abs Empty <$> occ a ans
  Nest d@(Let _ binding) ds -> do
    isPureDecl <- return $ isPure binding
    dceAttempt <- refreshAbs (Abs d (Abs ds ans))
      \d'@(Let b' (DeclBinding _ expr')) rest -> do
        exprIx <- summaryExpr $ sink expr'
        extend b' exprIx do
          below <- isolated $ occNest (sink a) rest >>= wrapWithCachedFVs
          accessInfo <- getAccessInfo $ binderName d'
          let usage = usageInfo accessInfo
          let dceAttempt = case isPureDecl of
               False -> ElimFailure d' usage $ fromCachedFVs below
               True  ->
                 case hoistViaCachedFVs d' below of
                   HoistSuccess below' -> ElimSuccess below'
                   HoistFailure _ -> ElimFailure d' usage $ fromCachedFVs below
          return dceAttempt
    case dceAttempt of
      ElimSuccess below' -> return below'
      ElimFailure (Let b' binding') usage (Abs ds'' ans'') -> do
        -- Using accessOnce here, instead of the computed Access for
        -- the decl's binder.  This means that variable bindings cut
        -- occurrence analysis, and each binding is considered for
        -- inlining separately.
        DeclBinding _ expr <- occ accessOnce binding'
        -- We save effects information here because the inliner will want to
        -- query the effects of an expression before it is substituted, and the
        -- type querying subsystem is not set up to do that.
        effs <- return $ getEffects expr
        let ann = case effs of
              Pure -> OccInfoPure usage
              _    -> OccInfoImpure usage
        let binding'' = DeclBinding ann expr
        return $ Abs (Nest (Let b' binding'') ds'') ans''

wrapWithCachedFVs :: forall e n. HoistableE e => e n -> OCCM n (CachedFVs e n)
wrapWithCachedFVs e = do
  FV fvMap <- get
  let fvs = keySetNameMapE fvMap
#ifdef DEX_DEBUG
  let fvsOk = map getRawName (freeVarsList e :: [SAtomName n]) == nameSetRawNames fvs
#else
  -- Verification of this invariant defeats the performance benefits of
  -- avoiding the extra traversal (e.g. actually having linear complexity),
  -- so we only do that in debug builds.
  let fvsOk = True
#endif
  case fvsOk of
    True -> return $ UnsafeCachedFVs fvs e
    False -> error $ "Free variables were computed incorrectly."

instance HasOCC (DeclBinding SimpIR) where
  occ a (DeclBinding ann expr) = do
    expr' <- occ a expr
    return $ DeclBinding ann expr'

instance HasOCC SExpr where
  occ a = \case
    Block effTy (Abs decls ans) -> do
      effTy' <- occ a effTy
      Abs decls' ans' <- occNest a (Abs decls ans)
      return $ Block effTy' (Abs decls' ans')
    TabApp t array ix -> do
      t' <- occTy t
      (a', ix') <- occIdx a ix
      array' <- occ a' array
      return $ TabApp t' array' ix'
    Case scrut alts (EffTy effs ty) -> do
      scrut' <- occ accessOnce scrut
      scrutIx <- summary scrut
      (alts', innerFVs) <- unzip <$> mapM (separately . occAlt a scrutIx) alts
      modify (<> foldl' Occ.max zero innerFVs)
      ty' <- occTy ty
      countFreeVarsAsOccurrences effs
      return $ Case scrut' alts' (EffTy effs ty')
    PrimOp (Hof op) -> PrimOp . Hof <$> occ a op
    PrimOp (RefOp ref op) -> do
      ref' <- occ a ref
      PrimOp . RefOp ref' <$> occ a op
    expr -> occGeneric a expr

occIdx :: Access n -> SAtom n -> OCCM n (Access n, SAtom n)
occIdx acc ix = do
  (summ, ix') <- occurrenceAndSummary ix
  return (location summ acc, ix')

-- Arguments: Usage of the return value, summary of the scrutinee, the
-- alternative itself.
occAlt :: Access n -> IxExpr n -> Alt SimpIR n -> OCCM n (Alt SimpIR n)
occAlt acc scrut alt = do
  (Abs (b':>ty) body') <- refreshAbs alt \b@(nb:>_) body -> do
    -- We use `unknown` here as a conservative approximation of the case binder
    -- being the scrutinee with the top constructor removed.  If we statically
    -- knew what that constructor was we could remove it, but I guess that
    -- case-of-known-constructor optimization would have already eliminated this
    -- case statement in that event.
    scrutIx <- unknown $ sink scrut
    extend nb scrutIx do
      body' <- occ (sink acc) body
      return $ Abs b body'
  ty' <- occTy ty
  return $ Abs (b':>ty') body'

occurrenceAndSummary :: SAtom n -> OCCM n (IxExpr n, SAtom n)
occurrenceAndSummary atom = do
  atom' <- occ accessOnce atom
  ix <- summary atom'
  return (ix, atom')

instance HasOCC (TypedHof SimpIR) where
  occ a (TypedHof effTy hof) = TypedHof <$> occ a effTy <*> occ a hof

instance HasOCC (Hof SimpIR) where
  occ a hof = case hof of
    For ann ixDict (UnaryLamExpr b body) -> do
      ixDict' <- inlinedLater ixDict
      occWithBinder (Abs b body) \b' body' -> do
        extend b' (Occ.Var $ binderName b') do
          body'' <- censored (abstractFor b') (occ accessOnce body')
          return $ For ann ixDict' (UnaryLamExpr b' body'')
    For _ _ _ -> error "For body should be a unary lambda expression"
    While body -> While <$> censored useManyTimes (occ accessOnce body)
    RunReader ini bd -> do
      iniIx <- summary ini
      bd' <- oneShot a [Deterministic [], iniIx] bd
      ini' <- occ accessOnce ini
      return $ RunReader ini' bd'
    RunWriter Nothing (BaseMonoid empty combine) bd -> do
      -- There is no way to read from the reference in a Writer, so the only way
      -- an indexing expression can depend on it is by referring to the
      -- reference itself.  One way to so refer that is opaque to occurrence
      -- analysis would be to pass the reference to a standalone function which
      -- returns an index (presumably without actually reading any information
      -- from said reference).
      --
      -- To cover this case, we write `Deterministic []` here.  This is correct,
      -- because RunWriter creates the reference without reading any external
      -- names.  In particular, in the event of `RunWriter` in a loop, the
      -- different references across loop iterations are not distinguishable.
      -- The same argument holds for the heap parameter.
      bd' <- oneShot a [Deterministic [], Deterministic []] bd
      -- We will process the combining function when we meet it in MExtend ops
      -- (but we won't attempt to eliminate dead code in it).
      empty' <- occ accessOnce empty
      return $ RunWriter Nothing (BaseMonoid empty' combine) bd'
    RunWriter (Just _) _ _ ->
      error "Expecting to do occurrence analysis before destination passing."
    RunState Nothing ini bd -> do
      -- If we wanted to be more precise, the summary for the reference should
      -- be something about the stuff that might flow into the `put` operations
      -- affecting that reference.  Using `IxAll` is a conservative
      -- approximation (in downstream analysis it means "assume I touch every
      -- value").
      bd' <- oneShot a [Deterministic [], IxAll] bd
      ini' <- occ accessOnce ini
      return $ RunState Nothing ini' bd'
    RunState (Just _) _ _ ->
      error "Expecting to do occurrence analysis before destination passing."
    RunIO bd -> RunIO <$> occ a bd
    RunInit _ ->
      -- Though this is probably not too hard to implement.  Presumably
      -- the lambda is one-shot.
      error "Expecting to do occurrence analysis before lowering."

oneShot :: Access n -> [IxExpr n] -> LamExpr SimpIR n -> OCCM n (LamExpr SimpIR n)
oneShot acc [] (LamExpr Empty body) =
  LamExpr Empty <$> occ acc body
oneShot acc (ix:ixs) (LamExpr (Nest b bs) body) = do
  occWithBinder (Abs b (LamExpr bs body)) \b' restLam ->
    extend b' (sink ix) do
      LamExpr bs' body' <- oneShot (sink acc) (map sink ixs) restLam
      return $ LamExpr (Nest b' bs') body'
oneShot _ _ _ = error "zip error"

-- Going under a lambda binder.
occWithBinder
  :: (RenameE e)
  => Abs (Binder SimpIR) e n
  -> (forall l. DExt n l => Binder SimpIR n l -> e l -> OCCM l a)
  -> OCCM n a
occWithBinder (Abs (b:>ty) body) cont = do
  (ty', fvs) <- separately $ occTy ty
  ans <- refreshAbs (Abs (b:>ty') body) cont
  modify (<> fvs)
  return ans
{-# INLINE occWithBinder #-}

instance HasOCC (RefOp SimpIR) where
  occ _ = \case
    MExtend (BaseMonoid empty combine) val -> do
      valIx <- summary val
      -- Treat the combining function as inlined here and called once
      combine' <- oneShot accessOnce [Deterministic [], valIx] combine
      val' <- occ accessOnce val
      -- TODO(precision) The empty value of the monoid is presumably dead here,
      -- but we pretend like it's not to make sure that occurrence analysis
      -- results mention every free variable in the traversed expression.  This
      -- may lead to missing an opportunity to inline something into the empty
      -- value of the given monoid, since references thereto will be overcounted.
      empty' <- occ accessOnce empty
      return $ MExtend (BaseMonoid empty' combine') val'
    -- I'm pretty sure the others are all strict, and not usefully analyzable
    -- for what they do to the incoming access pattern.
    MPut x -> MPut <$> occ accessOnce x
    MGet -> return MGet
    MAsk -> return MAsk
    IndexRef t i -> IndexRef <$> occTy t <*> occ accessOnce i
    ProjRef t i -> ProjRef <$> occTy t <*> pure i
  {-# INLINE occ #-}
