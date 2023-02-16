-- Copyright 2022 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module Inline (inlineBindings) where

import Data.Functor
import Data.List.NonEmpty qualified as NE

import Builder
import Core
import Err
import CheapReduction
import IRVariants
import LabeledItems
import Name
import Subst
import Occurrence hiding (Var)
import Types.Core
import Types.Primitives

-- === External API ===

inlineBindings :: (EnvReader m) => SLam n -> m n (SLam n)
inlineBindings = liftLamExpr inlineBindingsBlock
{-# INLINE inlineBindings #-}

inlineBindingsBlock :: (EnvReader m) => SBlock n -> m n (SBlock n)
inlineBindingsBlock blk = liftInlineM $ buildScopedAssumeNoDecls $ inline Stop blk
{-# SCC inlineBindingsBlock #-}

-- === Data Structure ===

data InlineExpr (r::IR) (o::S) where
  DoneEx :: SExpr o -> InlineExpr SimpIR o
  SuspEx :: SExpr i -> Subst InlineSubstVal i o -> InlineExpr SimpIR o

instance Show (InlineExpr r n) where
  show = \case
    DoneEx e -> "finished " ++ show e
    SuspEx e _ -> "unfinished " ++ show e

instance RenameE (InlineExpr r) where
  renameE (scope, subst) = \case
    DoneEx e -> DoneEx $ renameE (scope, subst) e
    SuspEx e s -> SuspEx e $ renameE (scope, subst) s

instance SinkableE (InlineExpr r) where
  sinkingProofE rename = \case
    DoneEx e   -> DoneEx $ sinkingProofE rename e
    SuspEx e s -> SuspEx e $ sinkingProofE rename s

type InlineSubstVal = SubstVal InlineExpr

newtype InlineM (i::S) (o::S) (a:: *) = InlineM
  { runInlineM :: SubstReaderT InlineSubstVal (BuilderM SimpIR) i o a }
  deriving ( Functor, Applicative, Monad, MonadFail, Fallible, ScopeReader
           , EnvExtender, EnvReader, SubstReader InlineSubstVal, (Builder SimpIR)
           , (ScopableBuilder SimpIR))

liftInlineM :: (EnvReader m) => InlineM n n a -> m n a
liftInlineM act = liftBuilder $ runSubstReaderT idSubst $ runInlineM act
{-# INLINE liftInlineM #-}

-- === Inliner ===

data SizePreservationInfo =
  -- Explicit noinline, or inlining doesn't preserve work
    NoInline
  -- Used once statically, ergo size-preserving to inline.  In Secrets, this
  -- corresponds to either OnceSafe, or OnceUnsafe with whnfOrBot == True
  | UsedOnce
  -- Used more than once statically, ergo potentially size-increasing to inline.
  -- In Secrets, this corresponds to either MultiSafe, or MultiUnsafe with
  -- whnfOrBot == True
  | UsedMulti
  deriving (Eq, Show)

inlineDecls :: Emits o => Nest SDecl i i' -> InlineM i' o a -> InlineM i o a
inlineDecls decls cont = do
  s <- inlineDeclsSubst decls
  withSubst s cont
{-# INLINE inlineDecls #-}

inlineDeclsSubst :: Emits o => Nest SDecl i i' -> InlineM i o (Subst InlineSubstVal i' o)
inlineDeclsSubst = \case
  Empty -> getSubst
  Nest (Let b (DeclBinding ann _ expr)) rest -> do
    if preInlineUnconditionally ann then do
      s <- getSubst
      extendSubst (b @> SubstVal (SuspEx expr s)) $ inlineDeclsSubst rest
    else do
      expr' <- inlineExpr Stop expr
      -- If the inliner starts moving effectful expressions, it may become
      -- necessary to query the effects of the new expression here.
      let presInfo = resolveWorkConservation ann expr'
      -- A subtlety from the Secrets paper.  In Haskell, it is feasible to have
      -- a binding whose occurrence information indicates multiple uses, but
      -- which does a small, bounded amount of runtime work.  GHC will inline
      -- such a binding, but not into contexts where GHC knows that no further
      -- optimizations are possible.  The example given in the paper is
      --   f = \x -> E
      --   g = \ys -> map f ys
      -- Inlining f here is useless because it's not applied, and mildly costly
      -- because it causes the closure to be allocated at every call to g rather
      -- than just once.
      -- TODO If we want to track this subtlety, we should make room for it in
      -- the SizePreservationInfo ADT (maybe rename it), maybe with a
      -- OnceButDuplicatesBoundedWork constructor.  Then only the true UsedOnce
      -- would be inlined unconditionally here, and the
      -- OnceButDuplicatesBoundedWork constructor could be inlined or not
      -- depending on its usage context.  (This would correspond to the case
      -- OnceUnsafe with whnfOrBot == True in the Secrets paper.)
      if presInfo == UsedOnce then do
        let substVal = case expr' of
             Atom (Var name') -> Rename name'
             _ -> SubstVal (DoneEx expr')
        extendSubst (b @> substVal) $ inlineDeclsSubst rest
      else do
        -- expr' can't be Atom (Var x) here
        name' <- emitDecl (getNameHint b) (dropOccInfo ann) expr'
        extendSubst (b @> Rename name') do
          -- TODO For now, this inliner does not do any conditional inlining.
          -- In order to do it, we would need to augment the environment at this
          -- point, associating name' to (expr', presInfo) so name' could be
          -- inlined at use sites.
          --
          -- Conditional inlining is different in Dex vs Haskell because Dex is
          -- strict.  To wit, once we have emitted the bidning for `expr'`, we
          -- are committed to doing the work it represents unless it's inlined
          -- _everywhere_.  For example,
          --   xs = <something>
          --   case <foo> of
          --     Nothing -> xs  -- ok to inline here
          --     Just _ -> xs ... xs  -- not ok here
          -- If this were Haskell, it would be work-preserving for GHC to inline
          -- `xs` into the `Nothing` arm, but in Dex it's not, unless we first
          -- explicitly push the binding into the case like
          --   case <foo> of
          --     Nothing -> xs = <something>; xs
          --     Just _ -> xs = <something>; xs ... xs
          --
          -- That said, the Secrets paper says that GHC only conditionally
          -- inlines zero-work bindings anyway (or, more precisely, "bounded
          -- finite work" bindings).  All the heuristics about whether to inline
          -- at a particular site are about code size and not increasing it
          -- overmuch.  But, of course, inlining even zero-work bindings can
          -- help runtime performance because it can unblock other optimizations
          -- that otherwise could not occur across the binding.
          inlineDeclsSubst rest
  where
    dropOccInfo PlainLet = PlainLet
    dropOccInfo NoInlineLet = NoInlineLet
    dropOccInfo (OccInfoPure _) = PlainLet
    dropOccInfo (OccInfoImpure _) = PlainLet
    resolveWorkConservation PlainLet _ =
      NoInline  -- No occurrence info, assume the worst
    resolveWorkConservation NoInlineLet _ = NoInline
    -- Quick hack to always unconditionally inline renames, until we get
    -- a better story about measuring the sizes of atoms and expressions.
    resolveWorkConservation (OccInfoPure _) (Atom (Var _)) = UsedOnce
    resolveWorkConservation (OccInfoPure (UsageInfo s (ixDepth, d))) expr
      | d <= One = case ixDepthExpr expr >= ixDepth of
        True -> if s <= One then UsedOnce else UsedMulti
        False -> NoInline
    resolveWorkConservation (OccInfoPure (UsageInfo s _)) (Atom _) =
      if s <= One then UsedOnce else UsedMulti
    -- TODO In Haskell, inlining expressions that are guaranteed to be bottom is
    -- also work-preserving, and profitable because it can avoid allocating
    -- thunks.  Do we care about that case here?  (It can also change the
    -- semantics in a strict language, from "error" to "no error" (or to
    -- "different error").)
    resolveWorkConservation (OccInfoPure _) _ = NoInline
    -- TODO Tagging impure expressions "noinline" here misses two potential
    -- opportunities.
    -- - The OccInfo annotation is from the target expression before inlining.
    --   It's conceivable that inlining will expose a peephole optimization that
    --   removes the effect, making the post-inlining expression pure.  It would
    --   be nice to be able to inline it here in this case, but (i) as of this
    --   writing, the inliner does not remove effects, and (ii) even if it did,
    --   we could recover the end state by running another inlining pass.
    -- - More interestingly, the inliner could reorder provably-independent
    --   effects, like `State` on two different heap parameters.  For that,
    --   however, we would need to know something about the locations into which
    --   an effectful binding could be moved, and whether doing so reorders
    --   effects that should not be reordered.  And because the inliner inlines
    --   multiple bindings in one pass, we may also need to be careful about any
    --   effectful bindings that are already in the substitution.
    resolveWorkConservation (OccInfoImpure _) _ = NoInline
    -- This function for detecting available indexing depth reports all decls as
    -- aborting indexing, even if the decl will be inlined away later.
    --
    -- For example, the binding
    --   xs = for i.
    --     ys = for j. <something>
    --     for k. ys.k
    -- really does have two available indexing levels, because the ys binding is
    -- inlinable into the result of the outer `for`; but the below function will
    -- not detect it, and thus we will decline to inline `xs` into a context
    -- where two levels of indexing are required.  However, we can recover the
    -- desired effect by running a second pass of occurrence analysis and
    -- inlining.
    --
    -- A more subtle case occurs with
    --   xs = for i.
    --     ys = for j. <something>
    --     view k. ys.k
    -- (note the `view`).  In this case, if we went ahead and inlined `xs` into
    -- a context that required two levels of indexing, we would temporarily
    -- duplicate work, but a second pass of occurence analysis and inlining
    -- would fix it by inlining `ys`.  However, if we decline to inline here,
    -- running inlining on the body of `for i.` will not inline into the `view`,
    -- because in general views are supposed to be duplicable all over.  Maybe
    -- the solution is to just not have view atoms in the IR by this point,
    -- since their main purpose is to force inlining in the simplifier, and if
    -- one just stuck like this it has become equivalent to a `for` anyway.
    ixDepthExpr :: Expr SimpIR n -> Int
    ixDepthExpr (Hof (For _ _ (UnaryLamExpr _ body))) = 1 + ixDepthBlock body
    ixDepthExpr _ = 0
    ixDepthBlock :: Block SimpIR n -> Int
    ixDepthBlock (exprBlock -> (Just expr)) = ixDepthExpr expr
    ixDepthBlock (AtomicBlock result) = ixDepthExpr $ Atom result
    ixDepthBlock _ = 0

-- Should we decide to inline this binding wherever it appears, before we even
-- know the expression?  "Yes" only if we know it only occurs once, and in a
-- context where inlining it does not duplicate work.
preInlineUnconditionally :: LetAnn -> Bool
preInlineUnconditionally = \case
  PlainLet -> False  -- "Missing occurrence annotation"
  NoInlineLet -> False
  OccInfoPure (UsageInfo s (0, d)) | s <= One && d <= One -> True
  OccInfoPure _ -> False
  OccInfoImpure _ -> False

-- A context in which an E-kinded thing is to be reconstructed.  This amounts to
-- a defunctionalization of the interesting part of rebuilding an expression,
-- which supports now-local optimizations in `reconstruct`.  Read `reconstruct`
-- together with this data type: `reconstruct` is an interpreter for it.
--
-- Note: This pattern of inserting an object into a context can do local
-- optimizations that would otherwise be hidden from a peephole optimizer by
-- intervening bindings.  For example, table indexing only permits an Atom in
-- the array position, but `reconstruct` can check whether it's trying to insert
-- a `for` expression into that spot and perform the beta reduction immediately,
-- instead of emitting the binding.
data Context (from::E) (to::E) (o::S) where
  Stop :: Context e e o
  TabAppCtx :: NE.NonEmpty (SAtom i) -> Subst InlineSubstVal i o
            -> Context SExpr e o -> Context SExpr e o
  EmitToAtomCtx :: Context SAtom e o -> Context SExpr e o
  EmitToNameCtx :: Context SAtomName e o -> Context SAtom e o
  RepWrap :: GenericE e1 => Context e1 e2 o -> Context (RepE e1) e2 o

class Inlinable (e1::E) where
  inline :: Emits o => Context e1 e2 o -> e1 i -> InlineM i o (e2 o)
  default inline :: (GenericE e1, Inlinable (RepE e1), Emits o)
    => Context e1 e2 o -> e1 i -> InlineM i o (e2 o)
  inline ctx e = confuseGHC >>= \_ -> inline (RepWrap ctx) (fromE e)

inlineExpr :: Emits o => Context SExpr e o -> SExpr i -> InlineM i o (e o)
inlineExpr ctx = \case
  Atom atom -> inlineAtom ctx atom
  TabApp tbl ixs -> do
    s <- getSubst
    inlineAtom (TabAppCtx ixs s ctx) tbl
  expr -> (inline Stop (fromE expr) <&> toE) >>= reconstruct ctx

inlineAtom :: Emits o => Context SExpr e o -> SAtom i -> InlineM i o (e o)
inlineAtom ctx = \case
  Var name -> inlineName ctx name
  ProjectElt i x -> do
    let (idxs, v) = asNaryProj i x
    ans <- normalizeNaryProj (NE.toList idxs) =<< inline Stop (Var v)
    reconstruct ctx $ Atom ans
  atom -> (inline Stop (fromE atom) <&> Atom . toE) >>= reconstruct ctx

inlineName :: Emits o => Context SExpr e o -> SAtomName i -> InlineM i o (e o)
inlineName ctx name =
  lookupSubstM name >>= \case
    Rename name' -> do
      -- This is the considerInline function from the Secrets paper; this
      -- is where we decide whether to inline a binding that isn't to be
      -- inlined unconditionally.
      -- For now, we just don't.  If we did, we would want to start with
      -- something like
      -- lookupEnv name' >>= \case
      --   (expr', presInfo) | inline presInfo expr' ctx -> inline
      --   no info -> do not inline (as now)
      reconstruct ctx (Atom $ Var name')
    SubstVal (DoneEx expr) -> dropSubst $ inlineExpr ctx expr
    SubstVal (SuspEx expr s') -> withSubst s' $ inlineExpr ctx expr

instance Inlinable (RefOp SimpIR) where
  inline ctx e = (inline Stop (fromE e) <&> toE) >>= reconstruct ctx
  {-# INLINE inline #-}

instance Inlinable (Hof SimpIR) where
  inline ctx e = (inline Stop (fromE e) <&> toE) >>= reconstruct ctx
  {-# INLINE inline #-}

instance Inlinable (BaseMonoid SimpIR) where
  inline ctx e = (inline Stop (fromE e) <&> toE) >>= reconstruct ctx
  {-# INLINE inline #-}

instance Inlinable SAtomName where
  inline ctx a = inlineName (EmitToAtomCtx $ EmitToNameCtx ctx) a

instance Inlinable SAtom where
  inline ctx a = inlineAtom (EmitToAtomCtx ctx) a

instance Inlinable SBlock where
  inline ctx (Block ann decls ans) = case (ann, decls) of
    (NoBlockAnn, Empty) ->
      (Block NoBlockAnn Empty <$> inline Stop ans) >>= reconstruct ctx
    (NoBlockAnn, _) -> error "should be unreachable"
    (BlockAnn ty effs, _) -> do
      (Abs decls' ans') <- buildScoped $ inlineDecls decls $ inline Stop ans
      ty' <- inline Stop ty
      effs' <- inline Stop effs  -- TODO Really?
      reconstruct ctx $ Block (BlockAnn ty' effs') decls' ans'

-- Still using InlineM because we may call back into inlining, and we wish to
-- retain our output binding environment.
reconstruct :: Emits o => Context e1 e2 o -> e1 o -> InlineM i o (e2 o)
reconstruct ctx e = case ctx of
  Stop -> return e
  TabAppCtx ixs s ctx' -> withSubst s $ reconstructTabApp ctx' e ixs
  EmitToAtomCtx ctx' -> emitExprToAtom e >>= reconstruct ctx'
  EmitToNameCtx ctx' -> emit (Atom e) >>= reconstruct ctx'
  RepWrap ctx' -> reconstruct ctx' $ toE e
{-# INLINE reconstruct #-}

reconstructTabApp :: Emits o
  => Context SExpr e o -> SExpr o -> NE.NonEmpty (SAtom i) -> InlineM i o (e o)
reconstructTabApp ctx expr ixs =
  case fromNaryForExpr (NE.length ixs) expr of
    Just (bsCount, LamExpr bs (Block _ decls result)) -> do
      let (ixsPref, ixsRest) = NE.splitAt bsCount ixs
      -- Note: There's a decision here.  Is it ok to inline the atoms in
      -- `ixsPref` into the body `decls`?  If so, should we pre-process them and
      -- carry them in `DoneEx`, or suspend them in `SuspEx`?  (If not, we can
      -- emit fresh bindings and use `Rename`.)  We can't make this decision
      -- properly without annotating the `for` binders with occurrence
      -- information; even though `ixsPref` itself are atoms, we may be carrying
      -- suspended inlining decisions that would want to make one an expression,
      -- and thus force-inlining it may duplicate work.
      --
      -- There remains a decision between just emitting bindings, or running
      -- `mapM (inline $ EmitToAtomCtx Stop)` and inlining the resulting atoms.
      -- In the work-heavy case where an element of `ixsPref` becomes an
      -- expression after inlining, the result will be the same; but in the
      -- work-light case where the element remains an atom, more inlining can
      -- proceed.  This decision only affects the runtime of the inliner and the
      -- code size of the IR the inliner produces.
      --
      -- Current status: Emitting bindings in the interest if "launch and
      -- iterate"; have not tried `EmitToAtomCtx`.
      ixsPref' <- mapM (inline $ EmitToNameCtx Stop) ixsPref
      s <- getSubst
      let moreSubst = bs @@> map Rename ixsPref'
      dropSubst $ extendSubst moreSubst do
        -- Decision here.  These decls have already been processed by the
        -- inliner once, so their occurrence information is stale (and should
        -- have been erased).  Do we rerun occurrence analysis, or just complete
        -- the pass without inlining any of them?
        -- - Con rerunning: Slower
        -- - Con completing: No detection of erroneous lack of occurrence info
        -- For now went with "completing"; to detect erroneous lack of
        -- occurrence info, change the relevant PlainLet cases above.
        --
        -- There's also a missed opportunity here to do more inlining in one
        -- pass: we lost the occurrence information of the bindings, so we lost
        -- the ability to inline them into the result, so in the common case
        -- that the result is a variable reference, we will find ourselves
        -- emitting a rename, _which will inhibit downstream inlining_ because a
        -- rename is not indexable.
        inlineDecls decls do
          let ctx' = case NE.nonEmpty ixsRest of
                Just rest' -> TabAppCtx rest' s ctx
                Nothing -> ctx
          inlineAtom ctx' result
    Nothing -> do
      array' <- emitExprToAtom expr
      ixs' <- mapM (inline Stop) ixs
      reconstruct ctx $ TabApp array' ixs'

-- === The generic instances ===

instance Inlinable (Name DataDefNameC) where
  inline ctx n = substM n >>= reconstruct ctx
instance Inlinable (Name ClassNameC) where
  inline ctx n = substM n >>= reconstruct ctx
instance Inlinable (Name InstanceNameC) where
  inline ctx n = substM n >>= reconstruct ctx
instance Inlinable (Name PtrNameC) where
  inline ctx n = substM n >>= reconstruct ctx
instance Inlinable (Name EffectNameC) where
  inline ctx n = substM n >>= reconstruct ctx
instance Inlinable (Name HandlerNameC) where
  inline ctx n = substM n >>= reconstruct ctx
instance Inlinable (Name SpecializedDictNameC) where
  inline ctx n = substM n >>= reconstruct ctx
instance Inlinable (Name TopFunNameC) where
  inline ctx n = substM n >>= reconstruct ctx

instance Inlinable e => Inlinable (ComposeE PrimOp e) where
  inline ctx (ComposeE op) =
    (ComposeE <$> traverse (inline Stop) op) >>= reconstruct ctx
  {-# INLINE inline #-}
instance Inlinable e => Inlinable (ComposeE (PrimCon SimpIR) e) where
  inline ctx (ComposeE con) =
    (ComposeE <$> traverse (inline Stop) con) >>= reconstruct ctx
  {-# INLINE inline #-}
instance Inlinable e => Inlinable (ComposeE (PrimTC SimpIR) e) where
  inline ctx (ComposeE tc) =
    (ComposeE <$> traverse (inline Stop) tc) >>= reconstruct ctx
  {-# INLINE inline #-}
instance Inlinable e => Inlinable (ComposeE LabeledItems e) where
  inline ctx (ComposeE items) =
    (ComposeE <$> traverse (inline Stop) items) >>= reconstruct ctx
  {-# INLINE inline #-}

instance (Inlinable e1, Inlinable e2) => Inlinable (ExtLabeledItemsE e1 e2)
instance Inlinable (LamExpr SimpIR)
instance Inlinable (TabPiType SimpIR)
instance Inlinable (DepPairType SimpIR)
instance Inlinable (EffectRowTail SimpIR)
instance Inlinable (EffectRow SimpIR)
instance Inlinable (Effect   SimpIR)
instance Inlinable (DAMOp SimpIR)
instance Inlinable (IxDict SimpIR)

instance Inlinable (RepVal SimpIR) where
  inline ctx (RepVal ty rep) =
    (RepVal <$> inline Stop ty <*> mapM substMAssumingRenameOnly rep) >>= reconstruct ctx

instance (Inlinable e1, Inlinable e2) => Inlinable (PairE e1 e2) where
  inline ctx (PairE l r) =
    (PairE <$> inline Stop l <*> inline Stop r) >>= reconstruct ctx
  {-# INLINE inline #-}
instance (Inlinable e1, Inlinable e2) => Inlinable (EitherE e1 e2) where
  inline ctx = \case
    LeftE  l -> (LeftE  <$> inline Stop l) >>= reconstruct ctx
    RightE r -> (RightE <$> inline Stop r) >>= reconstruct ctx
  {-# INLINE inline #-}
instance ( Inlinable e1, Inlinable e2, Inlinable e3, Inlinable e4
         , Inlinable e5, Inlinable e6, Inlinable e7, Inlinable e8
         ) => Inlinable (EitherE8 e1 e2 e3 e4 e5 e6 e7 e8) where
  inline ctx = \case
    Case0 x -> (Case0 <$> inline Stop x) >>= reconstruct ctx
    Case1 x -> (Case1 <$> inline Stop x) >>= reconstruct ctx
    Case2 x -> (Case2 <$> inline Stop x) >>= reconstruct ctx
    Case3 x -> (Case3 <$> inline Stop x) >>= reconstruct ctx
    Case4 x -> (Case4 <$> inline Stop x) >>= reconstruct ctx
    Case5 x -> (Case5 <$> inline Stop x) >>= reconstruct ctx
    Case6 x -> (Case6 <$> inline Stop x) >>= reconstruct ctx
    Case7 x -> (Case7 <$> inline Stop x) >>= reconstruct ctx
  {-# INLINE inline #-}

instance (RenameB b, BindsEnv b) => Inlinable (Abs b (Atom SimpIR)) where
  inline ctx (Abs b body) = do
    s <- getSubst
    babs <- runSubstReaderT (asRenameSubst s) $ renameM (Abs b (idSubstFrag b))
    abs' <- refreshAbs babs \b' frag ->
      extendSubst frag $ do
        Abs b' <$> (buildScopedAssumeNoDecls $ inline Stop body)
    reconstruct ctx abs'

instance (RenameB b, BindsEnv b) => Inlinable (Abs b (Block SimpIR)) where
  inline ctx (Abs b body) = do
    s <- getSubst
    babs <- runSubstReaderT (asRenameSubst s) $ renameM (Abs b (idSubstFrag b))
    abs' <- refreshAbs babs \b' frag ->
      extendSubst frag $ do
        Abs b' <$> (buildBlock $ (inline Stop body >>= emitBlock))
    reconstruct ctx abs'

asRenameSubst :: Subst InlineSubstVal i o -> Subst Name i o
asRenameSubst s = newSubst $ assumingRenameOnly s where
  assumingRenameOnly :: Color c => Subst InlineSubstVal i o -> Name c i -> Name c o
  assumingRenameOnly subst n = case subst ! n of
    Rename n' -> n'
    SubstVal v -> error $ "Unexpected non-rename substitution "
      ++ "maps " ++ (show n) ++ " to " ++ (show v)

substMAssumingRenameOnly :: (SinkableE e, RenameE e) => e i -> InlineM i o (e o)
substMAssumingRenameOnly e = do
  s <- getSubst
  runSubstReaderT (asRenameSubst s) $ renameM e

instance (RenameB b, BindsEnv b)
  => Inlinable (Abs b (PairE (EffectRow SimpIR) (Atom SimpIR))) where
  inline ctx (Abs b body) = do
    s <- getSubst
    babs <- runSubstReaderT (asRenameSubst s) $ renameM (Abs b (idSubstFrag b))
    abs' <- refreshAbs babs \b' frag ->
      extendSubst frag $ do
        Abs b' <$> (buildScopedAssumeNoDecls $ inline Stop body)
    reconstruct ctx abs'

instance Inlinable (LiftE a) where
  inline ctx (LiftE a) = reconstruct ctx (LiftE a)
  {-# INLINE inline #-}
instance Inlinable VoidE where
  inline _ _ = error "impossible"
  {-# INLINE inline #-}
instance Inlinable UnitE where
  inline ctx UnitE = reconstruct ctx UnitE
  {-# INLINE inline #-}
instance Inlinable e => Inlinable (ListE e) where
  inline ctx (ListE items) =
    (ListE <$> traverse (inline Stop) items) >>= reconstruct ctx
  {-# INLINE inline #-}
instance Inlinable e => Inlinable (WhenE True e) where
  inline ctx (WhenE e) = (WhenE <$> inline Stop e) >>= reconstruct ctx
  {-# INLINE inline #-}
instance Inlinable (WhenE False e) where
  inline _ _ = error "Unreachable"
  {-# INLINE inline #-}

instance Inlinable (WhenCore SimpIR e) where inline _ = \case
instance Inlinable e => Inlinable (WhenCore CoreIR e) where
  inline ctx (WhenIRE e) = (WhenIRE <$> inline Stop e) >>= reconstruct ctx
  {-# INLINE inline #-}

instance Inlinable (WhenSimp CoreIR e) where inline _ = \case
instance Inlinable e => Inlinable (WhenSimp SimpIR e) where
  inline ctx (WhenIRE e) = (WhenIRE <$> inline Stop e) >>= reconstruct ctx
  {-# INLINE inline #-}

-- See Note [Confuse GHC] from Simplify.hs
confuseGHC :: EnvReader m => m n (DistinctEvidence n)
confuseGHC = getDistinct
{-# INLINE confuseGHC #-}
