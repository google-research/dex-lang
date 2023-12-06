-- Copyright 2022 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module Inline (inlineBindings) where

import Builder
import Core
import Err
import CheapReduction
import IRVariants
import Name
import Subst
import Occurrence hiding (Var)
import PeepholeOptimize
import Types.Core
import Types.Primitives
import Types.Top

-- === External API ===

inlineBindings :: (EnvReader m) => STopLam n -> m n (STopLam n)
inlineBindings lam = liftLamExpr lam \body -> liftInlineM $ buildBlock $ inlineExpr Stop body
{-# INLINE inlineBindings #-}
{-# SCC inlineBindings #-}

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

inlineDeclsSubst :: Emits o => Nest SDecl i i' -> InlineM i o (Subst InlineSubstVal i' o)
inlineDeclsSubst = \case
  Empty -> getSubst
  Nest (Let b (DeclBinding ann expr)) rest -> do
    if preInlineUnconditionally ann then do
      s <- getSubst
      extendSubst (b @> SubstVal (SuspEx expr s)) $ inlineDeclsSubst rest
    else do
      expr' <- peepholeExpr <$> inlineExpr Stop expr
      -- If the inliner starts moving effectful expressions, it may become
      -- necessary to query the effects of the new expression here.
      let presInfo = resolveWorkConservation ann expr'
      -- See NoteSecretsSubtlety
      if presInfo == UsedOnce then do
        let substVal = case expr' of
             Atom (Stuck _ (Var name')) -> Rename $ atomVarName name'
             _ -> SubstVal (DoneEx expr')
        extendSubst (b @> substVal) $ inlineDeclsSubst rest
      else do
        -- expr' can't be Atom (Var x) here
        name' <- emitDecl (getNameHint b) (dropOccInfo ann) expr'
        extendSubst (b @> Rename (atomVarName name')) do
          -- See NoteConditionalInlining
          inlineDeclsSubst rest
  where
    dropOccInfo PlainLet = PlainLet
    dropOccInfo LinearLet = LinearLet
    dropOccInfo InlineLet = InlineLet
    dropOccInfo NoInlineLet = NoInlineLet
    dropOccInfo (OccInfoPure _) = PlainLet
    dropOccInfo (OccInfoImpure _) = PlainLet
    resolveWorkConservation PlainLet _ =
      NoInline  -- No occurrence info, assume the worst
    resolveWorkConservation LinearLet _ = NoInline
    resolveWorkConservation InlineLet _ = NoInline
    resolveWorkConservation NoInlineLet _ = NoInline
    -- Quick hack to always unconditionally inline renames, until we get
    -- a better story about measuring the sizes of atoms and expressions.
    resolveWorkConservation (OccInfoPure _) (Atom (Stuck _ (Var _))) = UsedOnce
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
    ixDepthExpr (PrimOp (Hof (TypedHof _ (For _ _ (UnaryLamExpr _ body))))) = 1 + ixDepthExpr body
    ixDepthExpr _ = 0

-- Should we decide to inline this binding wherever it appears, before we even
-- know the expression?  "Yes" only if we know it only occurs once, and in a
-- context where inlining it does not duplicate work.
preInlineUnconditionally :: LetAnn -> Bool
preInlineUnconditionally = \case
  PlainLet -> False  -- "Missing occurrence annotation"
  InlineLet   -> True
  NoInlineLet -> False
  LinearLet   -> False
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
  TabAppCtx :: SAtom i -> Subst InlineSubstVal i o
            -> Context SExpr e o -> Context SExpr e o
  CaseCtx :: [SAlt i] -> SType i -> EffectRow SimpIR i
          -> Subst InlineSubstVal i o
          -> Context SExpr e o -> Context SExpr e o
  EmitToAtomCtx :: Context SAtom e o -> Context SExpr e o
  EmitToNameCtx :: Context SAtomVar e o -> Context SAtom e o

class Inlinable (e1::E) where
  inline :: Emits o => Context e1 e2 o -> e1 i -> InlineM i o (e2 o)

  default inline :: (VisitGeneric e1 SimpIR, Emits o)
    => Context e1 e2 o -> e1 i -> InlineM i o (e2 o)
  inline ctx e = visitGeneric e >>= reconstruct ctx

instance NonAtomRenamer (InlineM i o) i o where renameN = substM
instance Emits o => Visitor (InlineM i o) SimpIR i o where
  visitType = inline Stop
  visitAtom = inline Stop
  visitLam  = inline Stop
  visitPi   = inline Stop

inlineExpr :: Emits o => Context SExpr e o -> SExpr i -> InlineM i o (e o)
inlineExpr ctx = \case
  Atom atom -> inlineAtom ctx atom
  TabApp _ tbl ix -> do
    s <- getSubst
    inlineAtom (TabAppCtx ix s ctx) tbl
  Case scrut alts (EffTy effs resultTy) -> do
    s <- getSubst
    inlineAtom (CaseCtx alts resultTy effs s ctx) scrut
  Block _ (Abs decls ans) -> do
    s <- inlineDeclsSubst decls
    withSubst s $ inlineExpr ctx ans
  expr -> visitGeneric expr >>= reconstruct ctx

inlineAtom :: Emits o => Context SExpr e o -> SAtom i -> InlineM i o (e o)
inlineAtom ctx = \case
  Stuck _ stuck -> inlineStuck ctx stuck
  Con con -> (toExpr <$> visitGeneric con) >>= reconstruct ctx

inlineStuck :: Emits o => Context SExpr e o -> SStuck i -> InlineM i o (e o)
inlineStuck ctx = \case
  Var name -> inlineName ctx name
  StuckProject i x -> do
    ans <- proj i =<< emit =<< inlineStuck Stop x
    reconstruct ctx $ Atom ans
  StuckTabApp _ _ -> error "not implemented"
  PtrVar t p -> do
    s <- mkStuck =<< (PtrVar t <$> substM p)
    reconstruct ctx (toExpr s)
  RepValAtom repVal -> do
    s <- mkStuck =<< (RepValAtom <$> visitGeneric repVal)
    reconstruct ctx (toExpr s)

inlineName :: Emits o => Context SExpr e o -> SAtomVar i -> InlineM i o (e o)
inlineName ctx name =
  lookupSubstM (atomVarName name) >>= \case
    Rename name' -> do
      -- This is the considerInline function from the Secrets paper; this
      -- is where we decide whether to inline a binding that isn't to be
      -- inlined unconditionally.
      -- For now, we just don't.  If we did, we would want to start with
      -- something like
      -- lookupEnv name' >>= \case
      --   (expr', presInfo) | inline presInfo expr' ctx -> inline
      --   no info -> do not inline (as now)
      v <- toAtomVar name'
      reconstruct ctx (toExpr v)
    SubstVal (DoneEx expr) -> dropSubst $ inlineExpr ctx expr
    SubstVal (SuspEx expr s') -> withSubst s' $ inlineExpr ctx expr

instance Inlinable SAtomVar where
  inline ctx a = inlineName (EmitToAtomCtx $ EmitToNameCtx ctx) a

instance Inlinable SAtom where
  inline ctx a = inlineAtom (EmitToAtomCtx ctx) a

instance Inlinable SType where
  inline ctx (TyCon ty) = (TyCon <$> visitGeneric ty) >>= reconstruct ctx

instance Inlinable SLam where
  inline ctx (LamExpr bs body) = do
    reconstruct ctx =<< withBinders bs \bs' -> do
      body' <- buildBlock $ inlineExpr Stop body
      return $ LamExpr bs' body'

withBinders
  :: Nest SBinder i i'
  -> (forall o'. DExt o o' => Nest SBinder o o' -> InlineM i' o' a)
  -> InlineM i o a
withBinders Empty cont = getDistinct >>= \Distinct -> cont Empty
withBinders (Nest (b:>ty) bs) cont = do
  ty' <- buildScopedAssumeNoDecls $ inline Stop ty
  withFreshBinder (getNameHint b) ty' \b' ->
    extendRenamer (b@>binderName b') do
      withBinders bs \bs' -> cont $ Nest b' bs'

instance Inlinable (PiType SimpIR) where
  inline ctx (PiType bs effTy)  =
    reconstruct ctx =<< withBinders bs \bs' -> do
      effTy' <- buildScopedAssumeNoDecls $ inline Stop effTy
      return $ PiType bs' effTy'

-- Still using InlineM because we may call back into inlining, and we wish to
-- retain our output binding environment.
reconstruct :: Emits o => Context e1 e2 o -> e1 o -> InlineM i o (e2 o)
reconstruct ctx e = case ctx of
  Stop -> return e
  TabAppCtx ix s ctx' -> withSubst s $ reconstructTabApp ctx' e ix
  CaseCtx alts resultTy effs s ctx' ->
    withSubst s $ reconstructCase ctx' e alts resultTy effs
  EmitToAtomCtx ctx' -> emit  e >>= reconstruct ctx'
  EmitToNameCtx ctx' -> emitToVar e >>= reconstruct ctx'
{-# INLINE reconstruct #-}

reconstructTabApp :: Emits o
  => Context SExpr e o -> SExpr o -> SAtom i -> InlineM i o (e o)
reconstructTabApp ctx expr i = case expr of
  PrimOp (Hof (TypedHof _ (For _ _ (UnaryLamExpr b body)))) -> do
    -- See NoteReconstructTabAppDecisions
    AtomVar i' _ <- inline (EmitToNameCtx Stop) i
    dropSubst $ extendSubst (b@>Rename i') do
      inlineExpr ctx body
  _ -> do
    array' <- emit expr
    i' <- inline Stop i
    reconstruct ctx =<< mkTabApp array' i'

reconstructCase :: Emits o
  => Context SExpr e o -> SExpr o -> [SAlt i] -> SType i -> EffectRow SimpIR i
  -> InlineM i o (e o)
reconstructCase ctx scrutExpr alts resultTy effs =
  case scrutExpr of
    Case sscrut salts _ -> do
      -- Perform case-of-case optimization
      -- TODO Add join points to reduce code duplication (and repeated inlining)
      -- of the arms of the outer case
      resultTy' <- inline Stop resultTy
      reconstruct ctx =<< (buildCase' sscrut resultTy' \i val -> do
        ans <- applyAbs (sink $ salts !! i) (SubstVal val) >>= emit
        buildCase ans (sink resultTy') \j jval -> do
          Abs b body <- return $ alts !! j
          extendSubst (b @> (SubstVal $ DoneEx $ Atom jval)) do
            inlineExpr Stop body >>= emit)
    _ -> do
      -- Attempt case-of-known-constructor optimization
      -- I can't use `buildCase` here because I want to propagate the incoming
      -- context `ctx` into the selected alternative if the optimization fires,
      -- but leave it around the whole reconstructed `Case` if it doesn't.
      scrut <- emit scrutExpr
      case scrut of
        Con con -> do
          SumCon _ i val <- return con
          Abs b body <- return $ alts !! i
          extendSubst (b @> (SubstVal $ DoneEx $ Atom val)) do
            inlineExpr ctx body
        Stuck _ _ -> do
          alts' <- mapM visitAlt alts
          resultTy' <- inline Stop resultTy
          effs' <- inline Stop effs
          reconstruct ctx $ Case scrut alts' (EffTy effs' resultTy')

instance Inlinable (EffectRow SimpIR)
instance Inlinable (EffTy     SimpIR)

-- === NoteReconstructTabAppDecisions ===

-- There's a decision here. Is it ok to inline the atoms in `ixsPref` into the
-- body `decls`? If so, should we pre-process them and carry them in `DoneEx`,
-- or suspend them in `SuspEx`? (If not, we can emit fresh bindings and use
-- `Rename`.) We can't make this decision properly without annotating the `for`
-- binders with occurrence information; even though `ixsPref` itself are atoms,
-- we may be carrying suspended inlining decisions that would want to make one
-- an expression, and thus force-inlining it may duplicate work.
--
-- There remains a decision between just emitting bindings, or running `mapM
-- (inline $ EmitToAtomCtx Stop)` and inlining the resulting atoms. In the
-- work-heavy case where an element of `ixsPref` becomes an expression after
-- inlining, the result will be the same; but in the work-light case where the
-- element remains an atom, more inlining can proceed. This decision only
-- affects the runtime of the inliner and the code size of the IR the inliner
-- produces.
--
-- Current status: Emitting bindings in the interest if "launch and iterate";
-- have not tried `EmitToAtomCtx`. Decision here. These decls have already been
-- processed by the inliner once, so their occurrence information is stale (and
-- should have been erased). Do we rerun occurrence analysis, or just complete
-- the pass without inlining any of them?
-- - Con rerunning: Slower
-- - Con completing: No detection of erroneous lack of occurrence info
-- For now went with "completing"; to detect erroneous lack of
-- occurrence info, change the relevant PlainLet cases above.
--
-- There's also a missed opportunity here to do more inlining in one pass: we
-- lost the occurrence information of the bindings, so we lost the ability to
-- inline them into the result, so in the common case that the result is a
-- variable reference, we will find ourselves emitting a rename, _which will
-- inhibit downstream inlining_ because a rename is not indexable.

-- === NoteConditionalInlining ===

-- TODO For now, this inliner does not do any conditional inlining. In order to
-- do it, we would need to augment the environment at this point, associating
-- name' to (expr', presInfo) so name' could be inlined at use sites.
--
-- Conditional inlining is different in Dex vs Haskell because Dex is strict. To
-- wit, once we have emitted the bidning for `expr'`, we are committed to doing
-- the work it represents unless it's inlined _everywhere_. For example,
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
-- That said, the Secrets paper says that GHC only conditionally inlines
-- zero-work bindings anyway (or, more precisely, "bounded finite work"
-- bindings). All the heuristics about whether to inline at a particular site
-- are about code size and not increasing it overmuch. But, of course, inlining
-- even zero-work bindings can help runtime performance because it can unblock
-- other optimizations that otherwise could not occur across the binding.

-- === NoteSecretsSubtlety ===

-- A subtlety from the Secrets paper. In Haskell, it is feasible to have a
-- binding whose occurrence information indicates multiple uses, but which does
-- a small, bounded amount of runtime work. GHC will inline such a binding, but
-- not into contexts where GHC knows that no further optimizations are possible.
-- The example given in the paper is
--   f = \x -> E
--   g = \ys -> map f ys
-- Inlining f here is useless because it's not applied, and mildly costly
-- because it causes the closure to be allocated at every call to g rather than
-- just once.
-- TODO If we want to track this subtlety, we should make room for it in
-- the SizePreservationInfo ADT (maybe rename it), maybe with a
-- OnceButDuplicatesBoundedWork constructor.  Then only the true UsedOnce
-- would be inlined unconditionally here, and the
-- OnceButDuplicatesBoundedWork constructor could be inlined or not
-- depending on its usage context.  (This would correspond to the case
-- OnceUnsafe with whnfOrBot == True in the Secrets paper.)
