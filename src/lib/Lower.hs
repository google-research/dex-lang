-- Copyright 2022 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE UndecidableInstances #-}

module Lower (lowerFullySequential, IxBlock, IxDestBlock, vectorizeLoops, emitIx) where

import Prelude hiding (id, (.))
import Data.Word
import Data.Functor
import Data.Set qualified as S
import Data.List.NonEmpty qualified as NE
import Data.Text.Prettyprint.Doc (pretty, viaShow, (<+>))
import Control.Category
import Control.Monad.Reader
import Unsafe.Coerce
import GHC.Exts (inline)

import Types.Core
import Types.Primitives

import Err
import Name
import MTL1
import Core
import Builder
import PPrint
import QueryType
import GenericTraversal
import Simplify (buildBlockSimplified)
import Util (foldMapM, enumerate)

-- A block preceded by a bunch of Ix instance bindings (all Decls bind Atoms)
type IxBlock = Abs (Nest Decl) Block
-- A bunch of Ix instance bindings, a binder for the destination of block result, body.
type IxDestBlock = Abs (Nest Decl) (Abs Binder Block)

-- === Ix dictionary hoisting ===
--
-- Up until this pass, Ix dictionaries are embedded deep inside the table types
-- and for loops. That's ok for as long as we don't particularly care about the low-level
-- details of array lowering. However, when simplifying the invariants and constructors
-- of our IR, we can't just ignore those dicts! They can contain arbitrary user code!
-- This pass hoists all of the DictExprs that construct Ix dicts out of the types and emits
-- them as proper decls. It also hoists them as far up the block (and super-blocks) as
-- possible. This makes it easier to subsequently perform CSE on those afterwards.
--
-- Note that while this pass has the capability to abstract Ix dicts, it only uses it
-- when hoisting above all binders other than Decls. It is never necessary to hoist above
-- a Decl: all arrays that use this Ix cannot escape the block in which this Decl is anyway
-- (or else the type of that block would leak variables!).

-- XXX: Re-deriving the block type might fail, due to the extra local dictionary decls!!
-- We might need to recreate the result atom...
--
-- The same thing should never happen in sub-blocks of the outer block. If a block
-- result would contain a block-local dict, then that dict must be unhoistable. But
-- the only reason why the dict would be unhoistable is because it references a local
-- piece of data that must appear in the array type itself. So the array type must have
-- been unhoistable itself, which means that the input wasn't well-typed in the first place.
emitIx :: EnvReader m => Block n -> m n (IxBlock n)
emitIx block = do
  Distinct <- getDistinct
  env <- unsafeGetEnv
  (ems, Abs (EmitIxEmissions ds nodecls) outBlock) <-
    return $ runHardFail $ runInplaceT env $ locallyMutableInplaceT $
      runSubstReaderT idSubst $ runEmitIxM $ emitIxE $ sink block
  return $ case ems of
    EmitIxEmissions REmpty REmpty -> case nodecls of
      REmpty -> Abs (unRNest ds) outBlock
      _ -> error "unexpected decl emissions!"
    _ -> error "unexpected emissions"
{-# INLINE emitIx #-}

--- The interesting instances ---

class HasEmitIx (e::E) where
  -- Ideally, we'd use an EmitsDicts predicate, kind of how we use EmitsInf within Inference.
  -- But for now we just go with the slightly unsafe path and dynamic checks that verify
  -- no unexpected emissions took place.
  emitIxE :: Mut o => e i -> EmitIxM i o (e o)
  default emitIxE :: (GenericE e, HasEmitIx (RepE e), Mut o) => e i -> EmitIxM i o (e o)
  emitIxE e = confuseGHC >>= \_ -> toE <$> emitIxE (fromE e)

class HasEmitIxB (b::B) where
  emitIxB :: Mut o => b i i' -> (forall o'. DExt o o' => b o o' -> EmitIxM i' o' a) -> EmitIxM i o a

-- DictExprs should appear in the IR only through DictCon, which we handle below.
instance HasEmitIx DictExpr where
  emitIxE _ = error "unhandled dict!"
instance HasEmitIx Atom where
  emitIxE = \case
    DictCon de -> do
      de' <- emitIxDict de
      dictTy' <- getType de'
      case dictTy' of
        DictTy (DictType "Ix" _ _) -> do
          EmitIxM $ SubstReaderT $ lift $ freshExtendSubInplaceT noHint \b ->
            (EmitIxDictEmission $ Let b $ DeclBinding PlainLet dictTy' $ Atom $ DictCon de', Var $ binderName b)
        -- Non-Ix dicts can be embedded in TypeCon params
        _ -> return $ DictCon de'
    atom -> toE <$> emitIxE (fromE atom)
    where emitIxDict dict = toE <$> emitIxE (fromE dict)

instance HasEmitIx Block where
  emitIxE (Block _ idecls (ians :: Atom i')) = buildEmitIxBlock $ go idecls
    where
      go :: Mut o => Nest Decl i i' -> EmitIxM i o (Atom o)
      go = \case
        Empty -> emitIxE ians
        Nest (Let b (DeclBinding ann _ e)) ds -> do
          b' <- emitIxDecl (getNameHint b) ann =<< emitIxE e
          extendSubst (b@>b') $ go ds

-- TODO: This might unnecessarily hoist dicts above e.g. lambda binders.
-- We could avoid doing that by specializing the LamExpr instance below.
instance (BindsEnv b, SubstB Name b, SubstE Name e, SubstE AtomSubstVal e, SinkableE e, HasEmitIx e, HasEmitIxB b, BindsOneAtomName b) => HasEmitIx (Abs b e) where
  emitIxE (Abs b body) = do
    reemitIxDicts =<< emitIxB b \b' -> do
      -- This scope is an overapproximation of the scope we need, because it also
      -- includes b. It's unclear to me how to get rid of those casts, since we do
      -- want the scope after all emissions coming from b's annotations, but before
      -- b itself. And there's no easy way to get it with the way the code is set up
      -- right now.
      scope <- unsafeGetScope
      bodyEms <- emitIxScoped $ emitIxE body
      -- We only emit decls while traversing Blocks, and the implementation for
      -- emitIxE should handle that locally. No other place should emit!
      refreshAbs bodyEms \(EmitIxEmissions ds REmpty) body' -> do
        (PairB ds' b'', s, _) <- return $ generalizeIxDicts (unsafeCoerceE scope) b' ds
        body'' <- applySubst s body'
        return $ Abs ds' $ Abs b'' body''
  {-# INLINE emitIxE #-}

-- Like exchangeBs, but generalizes whenever hoisting fails.
generalizeIxDicts :: (Distinct p, BindsNames b, SinkableB b, BindsOneAtomName b)
                  => Scope n -> b n l -> RNest Decl l p -> (PairB (RNest Decl) b n p, SubstFrag AtomSubstVal n p p, Scope p)
generalizeIxDicts scope topB dicts = go REmpty scope topB emptyInFrag $ unRNest dicts
  where
    go :: (Distinct p, BindsNames b, SinkableB b, BindsOneAtomName b)
       => RNest Decl n l                -- hoisted Ix dict decls
       -> Scope l                       -- scope, for substitutions
       -> b l q                         -- the binder we're hoisting above
       -> SubstFrag AtomSubstVal n l q  -- a substitution instantiating abstracted dicts
       -> Nest Decl q p                 -- Ix dicts left to hoist
       -> (PairB (RNest Decl) b n p, SubstFrag AtomSubstVal n p p, Scope p)
    go acc !sc !b !s rest = withSubscopeDistinct rest $ case rest of
      Empty -> (PairB acc b, s <.> b@>Rename (binderName b), sc `extScope` b)
      Nest d@(Let db binding) ds -> withSubscopeDistinct ds do
        -- We have to apply the substitution derived from the dict decls above to to current one.
        let env = withExtEvidence acc $ withExtEvidence b $
                    (sc `extScope` b, substFromFrag $ s <.> b@>Rename (binderName b))
        let DeclBinding ann ty (Atom da) = substE env binding
        -- Now we try to hoist.
        case exchangeBs $ PairB b d of
          HoistSuccess (PairB d'@(Let db' _) b') -> withSubscopeDistinct b' do
            let s' = withExtEvidence d $ sink s <.> db' @> Rename (sink $ binderName db')
            go (RNest acc d') (sc `extScope` db') b' s' ds
          -- If hoisting fails, we wrap the decl in a lambda that abstracts the binder
          -- and create a subst that replaces any occurence of the dict with the application.
          HoistFailure _ -> case exchangeNameBinder b db of
            PairB db' b' -> withSubscopeDistinct b' $ go acc' (sc `extScope` db') b' s' ds
              where
                ty' = Pi $ PiType (PiBinder (asNameBinder b) (binderType b) PlainArrow) Pure ty
                expr' = Atom $ Lam $ LamExpr (LamBinder (asNameBinder b) (binderType b) PlainArrow Pure) $ AtomicBlock da
                acc' = RNest acc $ Let db' $ DeclBinding ann ty' expr'

                sv = withExtEvidence b' $ DictCon $ InstantiatedGiven (Var $ sink $ binderName db') $ (Var $ binderName b') NE.:| []
                s' = withExtEvidence d $ sink s <.> db' @> SubstVal sv

    extScope :: (BindsNames b, Distinct l) => Scope n -> b n l -> Scope l
    extScope s b = s `extendOutMap` toScopeFrag b

    substFromFrag :: (FromName v, SinkableV v, DExt n l) => SubstFrag v n l l -> Subst v l l
    substFromFrag = (sink idSubst <>>)

--- The monad ---

newtype EmitIxM (i::S) (o::S) (a:: *) =
  EmitIxM { runEmitIxM :: SubstReaderT Name (InplaceT Env EmitIxEmissions HardFailM) i o a }
  deriving (Functor, Applicative, Monad, MonadFail, Fallible, ScopeReader, SubstReader Name, EnvReader, EnvExtender)

emitIxScoped :: SinkableE e
             => (forall o'. (Mut o', DExt o o') => EmitIxM i o' (e o'))
             -> EmitIxM i o (Abs EmitIxEmissions e o)
emitIxScoped cont = EmitIxM $ SubstReaderT $ ReaderT \env ->
  locallyMutableInplaceT $ runSubstReaderT (sink env) $ runEmitIxM cont
{-# INLINE emitIxScoped #-}

emitIxDecl :: Mut o => NameHint -> LetAnn -> Expr o -> EmitIxM i o (AtomName o)
emitIxDecl hint ann expr = do
  ty <- getType expr
  EmitIxM $ liftSubstReaderT $ freshExtendSubInplaceT hint \b ->
    (EmitIxDeclEmission $ Let b $ DeclBinding ann ty expr, binderName b)
{-# INLINE emitIxDecl #-}

-- TODO: We know they're fresh! Avoid the unnecessary checks
reemitIxDicts :: (Mut o, SubstE Name e) => Abs (RNest Decl) e o -> EmitIxM i o (e o)
reemitIxDicts (Abs dicts e) =
  EmitIxM $ liftSubstReaderT $ extendInplaceT $ Abs (EmitIxEmissions dicts emptyOutFrag) e

buildEmitIxBlock :: Mut o  -- Re-emits hoisted dictionaries
                 => (forall o'. (Mut o', DExt o o') => EmitIxM i o' (Atom o'))
                 -> EmitIxM i o (Block o)
buildEmitIxBlock cont = do
  Abs (EmitIxEmissions ds decls) ansWithTy <- emitIxScoped $ withType =<< cont
  Abs decls' ansWithTy' <- EmitIxM $ liftSubstReaderT $
    extendInplaceT $ Abs (EmitIxEmissions ds REmpty) $ Abs decls ansWithTy
  absToBlock =<< computeAbsEffects (Abs (unRNest decls') ansWithTy')

--- Emission types ---

data EmitIxEmissions (n::S) (l::S) where
  -- hoisted dicts, local decls
  EmitIxEmissions :: RNest Decl n p -> RNest Decl p l -> EmitIxEmissions n l
instance GenericB EmitIxEmissions where
  type RepB EmitIxEmissions = PairB (RNest Decl) (RNest Decl)
  fromB (EmitIxEmissions ds dcls) = PairB ds dcls
  {-# INLINE fromB #-}
  toB   (PairB ds dcls) = EmitIxEmissions ds dcls
  {-# INLINE toB #-}
instance ProvesExt   EmitIxEmissions
instance BindsNames  EmitIxEmissions
instance SinkableB   EmitIxEmissions
instance HoistableB  EmitIxEmissions
instance SubstB Name EmitIxEmissions
instance OutFrag EmitIxEmissions where
  emptyOutFrag = EmitIxEmissions emptyOutFrag emptyOutFrag
  catOutFrags _ (EmitIxEmissions ds dcls) (EmitIxEmissions ds' dcls') =
    case withSubscopeDistinct dcls' $ tryHoist dcls ds' of
      PairB ds'' dcls'' -> EmitIxEmissions (ds >>> ds'') (dcls'' >>> dcls')

tryHoist :: Distinct q => RNest Decl n p -> RNest Decl p q -> PairB (RNest Decl) (RNest Decl) n q
tryHoist REmpty  ds    = PairB ds REmpty
tryHoist topDcls topDs = go REmpty topDcls $ unRNest topDs
  where
    -- TODO: Optimize this: we repeatedly query free vars and bound names in exchangeBs!
    go :: Distinct q => RNest Decl n l -> RNest Decl l p -> Nest Decl p q -> PairB (RNest Decl) (RNest Decl) n q
    go ds dcls = \case
      Empty -> PairB ds dcls
      Nest d' ds' -> withSubscopeDistinct ds' $ case exchangeBs $ PairB dcls d' of
        HoistSuccess (PairB d'' dcls') -> go (RNest ds d'') dcls' ds'
        HoistFailure _                 -> go ds (RNest dcls d') ds'

instance BindsEnv EmitIxEmissions where
  toEnvFrag (EmitIxEmissions ds dcls) =
    withSubscopeDistinct dcls $ toEnvFrag ds `catEnvFrags` toEnvFrag dcls
instance ExtOutMap Env EmitIxEmissions where
  extendOutMap env ems = env `extendOutMap` toEnvFrag ems

newtype EmitIxDeclEmission (n::S) (l::S) = EmitIxDeclEmission (Decl n l)
  deriving (ProvesExt, BindsNames, SinkableB, SubstB Name, BindsEnv)
instance ExtOutMap Env EmitIxDeclEmission where
  extendOutMap env ems = env `extendOutMap` toEnvFrag ems
instance ExtOutFrag EmitIxEmissions EmitIxDeclEmission where
  extendOutFrag (EmitIxEmissions ds dcls) (EmitIxDeclEmission d) = EmitIxEmissions ds $ RNest dcls d
  {-# INLINE extendOutFrag #-}

newtype EmitIxDictEmission (n::S) (l::S) = EmitIxDictEmission (Decl n l)
  deriving (ProvesExt, BindsNames, SinkableB, SubstB Name, BindsEnv)
instance ExtOutMap Env EmitIxDictEmission where
  extendOutMap env ems = env `extendOutMap` toEnvFrag ems
-- TODO: Cache bound vars?
instance ExtOutFrag EmitIxEmissions EmitIxDictEmission where
  extendOutFrag (EmitIxEmissions ds dcls) (EmitIxDictEmission d) =
    case exchangeBs $ PairB dcls d of
      HoistSuccess (PairB d' dcls') -> EmitIxEmissions (RNest ds d') dcls'
      HoistFailure _                -> EmitIxEmissions ds $ RNest dcls d


--- The generic instances ---

instance (HasEmitIx e1, HasEmitIx e2) => HasEmitIx (ExtLabeledItemsE e1 e2)
instance HasEmitIx Expr
instance HasEmitIx LamExpr
instance HasEmitIx TabLamExpr
instance HasEmitIx PiType
instance HasEmitIx TabPiType
instance HasEmitIx DepPairType
instance HasEmitIx EffectRow
instance HasEmitIx Effect
instance HasEmitIx DictType
instance HasEmitIx FieldRowElems
instance HasEmitIx FieldRowElem
instance HasEmitIx DataDefParams
instance HasEmitIx DeclBinding
instance HasEmitIx IxType

instance (HasEmitIx ann, Color c, ToBinding ann c) => HasEmitIxB (BinderP c ann) where
  emitIxB (b:>ann) cont = do
    ann' <- emitIxE ann
    withFreshBinder (getNameHint b) ann' \b' ->
      extendRenamer (b@>binderName b') $ cont $ b':>ann'
instance HasEmitIxB LamBinder where
  emitIxB (LamBinder b ty arr eff) cont = do
    ty' <- emitIxE ty
    withFreshBinder (getNameHint b) (LamBinding arr ty') \b' ->
      extendRenamer (b@>binderName b') $ cont . LamBinder b' ty' arr =<< substM eff
instance HasEmitIxB PiBinder where
  emitIxB (PiBinder b ty arr) cont = do
    ty' <- emitIxE ty
    withFreshBinder (getNameHint b) (PiBinding arr ty') \b' ->
      extendRenamer (b@>binderName b') $ cont $ PiBinder b' ty' arr
-- Only used for the traversal of reference constructors that should never appear at this stage.
instance HasEmitIxB (NonDepNest BoxPtr) where
  emitIxB _ _ = error "not implemented"
instance {-# OVERLAPPING #-} HasEmitIx (Abs (NonDepNest BoxPtr) e) where
  emitIxE = error "should be unreachable"

--- The instances for RepE types ---

instance Color c => HasEmitIx (Name c) where
  emitIxE = substM
instance (HasEmitIx e1, HasEmitIx e2) => HasEmitIx (PairE e1 e2) where
  emitIxE (PairE l r) = PairE <$> emitIxE l <*> emitIxE r
  {-# INLINE emitIxE #-}
instance (HasEmitIx e1, HasEmitIx e2) => HasEmitIx (EitherE e1 e2) where
  emitIxE = \case
    LeftE  l -> LeftE  <$> emitIxE l
    RightE r -> RightE <$> emitIxE r
  {-# INLINE emitIxE #-}
instance ( HasEmitIx e0, HasEmitIx e1, HasEmitIx e2, HasEmitIx e3
         , HasEmitIx e4, HasEmitIx e5, HasEmitIx e6, HasEmitIx e7
         ) => HasEmitIx (EitherE8 e0 e1 e2 e3 e4 e5 e6 e7) where
  emitIxE = \case
    Case0 x0 -> Case0 <$> emitIxE x0
    Case1 x1 -> Case1 <$> emitIxE x1
    Case2 x2 -> Case2 <$> emitIxE x2
    Case3 x3 -> Case3 <$> emitIxE x3
    Case4 x4 -> Case4 <$> emitIxE x4
    Case5 x5 -> Case5 <$> emitIxE x5
    Case6 x6 -> Case6 <$> emitIxE x6
    Case7 x7 -> Case7 <$> emitIxE x7
  {-# INLINE emitIxE #-}
instance HasEmitIx (LiftE a) where
  emitIxE (LiftE x) = return $ LiftE x
  {-# INLINE emitIxE #-}
instance HasEmitIx VoidE where
  emitIxE _ = error "impossible"
  {-# INLINE emitIxE #-}
instance HasEmitIx UnitE where
  emitIxE UnitE = return UnitE
  {-# INLINE emitIxE #-}
instance (Traversable f, HasEmitIx e) => HasEmitIx (ComposeE f e) where
  emitIxE (ComposeE xs) = ComposeE <$> traverse emitIxE xs
  {-# INLINE emitIxE #-}
instance HasEmitIx e => HasEmitIx (ListE e) where
  emitIxE (ListE xs) = ListE <$> traverse emitIxE xs
  {-# INLINE emitIxE #-}

-- === For loop resolution ===

-- The `lowerFullySequential` pass makes two related changes:
-- - All `for` loops become `seq` loops
-- - Arrays are now explicily allocated as `Dest`s (whither the
--   content is written in due course)
--
-- We also perform destination passing here, to elide as many copies
-- as possible.
--
-- The idea for multithreading parallelism is to add IR elements that
-- specify parallelization strategy (`Seq` specifies sequential
-- execution) and add lowerings similar to lowerFullySequential that
-- choose which one(s) to use.

-- The `For` constructor of `PrimHof` disappears from the IR due to
-- this pass, and the `Seq`, `AllocDest`, `Place`, `RememberDest`, and
-- `Freeze` constructors appear.
--
-- All the `Place`s in the resulting IR are non-conflicting: every
-- array element is only written to once.
--
-- The traversal for a block or subexpression returns an `Atom`
-- representing the returned value.  If a destination was passed in,
-- the traversal is also responsible for arranging to write that value
-- into that destination (possibly by forwarding (a part of) the
-- destination to a sub-block or sub-expression, hence "desintation
-- passing style").

lowerFullySequential :: EnvReader m => IxBlock n -> m n (IxDestBlock n)
lowerFullySequential (Abs ixs b) = liftM fst $ liftGenericTraverserM LFS do
  buildScoped $ traverseDeclNest ixs do
    resultDestTy <- RawRefTy <$> getTypeSubst b
    withFreshBinder (getNameHint @String "ans") resultDestTy \destBinder -> do
      Abs (destBinder:>resultDestTy) <$> buildBlock do
        let dest = Var $ sink $ binderName destBinder
        traverseBlockWithDest dest b $> UnitVal

data LFS (n::S) = LFS
type LowerM = GenericTraverserM LFS
instance SinkableE LFS where
  sinkingProofE _ LFS = LFS
instance HoistableState LFS where
  hoistState _ _ LFS = LFS
  {-# INLINE hoistState #-}

-- It would be nice to figure out a way to not have to update the effect
-- annotations manually... The only interesting case below is really the For.
instance GenericTraverser LFS where
  traverseExpr expr = case expr of
    Op (TabCon ty els) -> traverseTabCon Nothing ty els
    Hof (For dir ixDict (Lam body)) -> traverseFor Nothing dir ixDict body
    Case _ _ _ _ -> do
      Case e alts ty _ <- traverseExprDefault expr
      eff' <- foldMapM getEffects alts
      return $ Case e alts ty eff'
    _ -> traverseExprDefault expr
  traverseAtom atom = case atom of
    Lam _ -> do
      traverseAtomDefault atom >>= \case
        Lam (LamExpr (LamBinder b ty arr _) body@(Block ann _ _)) -> do
          let eff' = case ann of BlockAnn _ e -> e; NoBlockAnn -> Pure
          return $ Lam $ LamExpr (LamBinder b ty arr eff') body
        _ -> error "Expected a lambda"
    _ -> traverseAtomDefault atom

type Dest = Atom

traverseFor :: Emits o => Maybe (Dest o) -> ForAnn -> Atom i -> LamExpr i -> LowerM i o (Expr o)
traverseFor maybeDest dir ixDict lam@(LamExpr (LamBinder ib ty arr eff) body) = do
  initDest <- case maybeDest of
    Just  d -> return d
    Nothing -> emitOp . AllocDest =<< getTypeSubst (Hof $ For dir ixDict (Lam lam))
  destTy <- getType initDest
  ty' <- substM ty
  ixDict' <- substM ixDict
  eff' <- substM $ ignoreHoistFailure $ hoist ib eff
  let eff'' = extendEffRow (S.singleton IOEffect) eff'
  body' <- buildLam noHint arr (PairTy ty' destTy) eff'' \b' -> do
    (i, dest) <- fromPair $ Var b'
    idest <- emitOp $ IndexRef dest i
    void $ extendSubst (ib @> SubstVal i) $ traverseBlockWithDest idest body
    return UnitVal
  let seqHof = Hof $ Seq dir ixDict' initDest body'
  Op . Freeze . Var <$> emit seqHof

traverseTabCon :: Emits o => Maybe (Dest o) -> Type i -> [Atom i] -> LowerM i o (Expr o)
traverseTabCon maybeDest tabTy elems = do
  tabTy'@(TabPi (TabPiType (_:>ixTy') _)) <- substM tabTy
  dest <- case maybeDest of
    Just  d -> return d
    Nothing -> emitOp $ AllocDest tabTy'
  Abs bord ufoBlock <- buildAbs noHint IdxRepTy \ord -> do
    buildBlockSimplified $ unsafeFromOrdinal (sink ixTy') $ Var $ sink ord
  forM_ (enumerate elems) \(ord, e) -> do
    i <- dropSubst $ extendSubst (bord@>SubstVal (IdxRepVal (fromIntegral ord))) $
      traverseBlock ufoBlock
    idest <- indexRef dest i
    place (FullDest idest) =<< traverseAtom e
  return $ Op $ Freeze dest


-- Destination-passing traversals
--
-- The idea here is to try to reuse the memory already allocated for outputs of surrounding
-- higher order functions for values produced inside nested blocks. As an example,
-- consider two perfectly nested for loops:
--
-- for i:(Fin 10).
--   v = for j:(Fin 20). ...
--   v
--
-- (binding of the for as v is necessary since Blocks end with Atoms).
--
-- The outermost loop will have to allocate the memory for a 2D array. But it would be
-- a waste if the inner loop kept allocating 20-element blocks only to copy them into
-- that full outermost buffer. Instead, we invoke traverseBlockWithDest on the body
-- of the i-loop, which will realize that v has a valid destination. Then,
-- traverseExprWithDest will be called at the for decl and will translate the j-loop
-- so that it never allocates scratch space for its result, but will put it directly in
-- the corresponding slice of the full 2D buffer.

type DestAssignment (i'::S) (o::S) = AtomNameMap (ProjDest o) i'

data ProjDest o
  = FullDest (Dest o)
  | ProjDest (NE.NonEmpty Int) (Dest o)  -- dest corresponds to the projection applied to name

lookupDest :: DestAssignment i' o -> AtomName i' -> Maybe (ProjDest o)
lookupDest = flip lookupNameMap

-- Matches up the free variables of the atom, with the given dest. For example, if the
-- atom is a pair of two variables, the dest might be split into per-component dests,
-- and a dest assignment mapping each side to its respective dest will be returned.
-- This function works on a best-effort basis. It's never an error to not split the dest
-- as much as possible, but it can lead to unnecessary copies being done at run-time.
--
-- XXX: When adding more cases, be careful about potentially repeated vars in the output!
decomposeDest :: Emits o => Dest o -> Atom i' -> LowerM i o (Maybe (DestAssignment i' o))
decomposeDest dest = \case
  Var v -> return $ Just $ singletonNameMap v $ FullDest dest
  ProjectElt ps v -> return $ Just $ singletonNameMap v $ ProjDest ps dest
  _ -> return Nothing

traverseBlockWithDest :: Emits o => Dest o -> Block i -> LowerM i o (Atom o)
traverseBlockWithDest dest (Block _ decls ans) = do
  decomposeDest dest ans >>= \case
    Nothing -> do
      ans' <- traverseDeclNest decls $ traverseAtom ans
      place (FullDest dest) ans'
      return ans'
    Just destMap -> do
      s <- getSubst
      case isDistinctNest decls of
        Nothing -> error "Non-distinct decls?"
        Just DistinctBetween -> do
          s' <- traverseDeclNestWithDestS destMap s decls
          -- But we have to emit explicit writes, for all the vars that are not defined in decls!
          forM_ (toListNameMap $ hoistFilterNameMap decls destMap) \(n, d) ->
            place d $ case s ! n of Rename v -> Var v; SubstVal a -> a
          withSubst s' $ substM ans


traverseDeclNestWithDestS
  :: forall i i' l o. (Emits o, DistinctBetween l i')
  => DestAssignment i' o -> Subst AtomSubstVal l o -> Nest Decl l i' -> LowerM i o (Subst AtomSubstVal i' o)
traverseDeclNestWithDestS destMap s = \case
  Empty -> return s
  Nest (Let b (DeclBinding ann _ expr)) rest -> do
    DistinctBetween <- return $ withExtEvidence rest $ shortenBetween @i' b
    let maybeDest = lookupDest destMap $ sinkBetween $ binderName b
    expr' <- withSubst s $ traverseExprWithDest maybeDest expr
    v <- emitDecl (getNameHint b) ann expr'
    traverseDeclNestWithDestS destMap (s <>> (b @> Rename v)) rest

traverseExprWithDest :: forall i o. Emits o => Maybe (ProjDest o) -> Expr i -> LowerM i o (Expr o)
traverseExprWithDest dest expr = case expr of
  Op (TabCon ty els) -> traverseTabCon tabDest ty els
  Hof (For dir ixDict (Lam body)) -> traverseFor tabDest dir ixDict body
  Hof (RunWriter Nothing m body) -> traverseRWS Writer body \ref' body' -> do
    m' <- traverse traverseGenericE m
    return $ RunWriter ref' m' body'
  Hof (RunState Nothing s body) -> traverseRWS State body \ref' body' -> do
    s' <- traverseAtom s
    return $ RunState ref' s' body'
  _ -> generic
  where
    tabDest = dest <&> \case FullDest d -> d; ProjDest _ _ -> error "unexpected projection"

    generic = do
      expr' <- traverseExprDefault expr
      case dest of
        Nothing -> return expr'
        Just d  -> do
          ans <- Var <$> emit expr'
          place d ans
          return $ Atom ans

    traverseRWS :: RWS -> Atom i -> (Maybe (Dest o) -> Atom o -> LowerM i o (Hof o)) -> LowerM i o (Expr o)
    traverseRWS rws (Lam (BinaryLamExpr hb rb body)) mkHof = do
      unpackRWSDest dest >>= \case
        Nothing -> generic
        Just (bodyDest, refDest) -> do
          let RefTy _ ty = binderType rb
          ty' <- traverseGenericE $ ignoreHoistFailure $ hoist hb ty
          liftM Hof $ mkHof refDest =<<
            buildEffLam rws (getNameHint rb) ty' \hb' rb' ->
              extendRenamer (hb@>hb' <.> rb@>rb') do
                case bodyDest of
                  Nothing -> traverseBlock body
                  Just bd -> traverseBlockWithDest (sink bd) body
    traverseRWS _ _ _ = error "Expected a binary lambda expression"

    unpackRWSDest = \case
      Nothing -> return Nothing
      Just d -> case d of
        FullDest fd -> do
          bd <- getProjRef 0 fd
          rd <- getProjRef 1 fd
          return $ Just (Just bd, Just rd)
        ProjDest (0 NE.:| []) pd -> return $ Just (Just pd, Nothing)
        ProjDest (1 NE.:| []) pd -> return $ Just (Nothing, Just pd)
        ProjDest _ _ -> return Nothing


place :: Emits o => ProjDest o -> Atom o -> LowerM i o ()
place pd x = case pd of
  FullDest d -> void $ emitOp $ Place d x
  ProjDest p d -> void $ emitOp $ Place d $ getProjection (NE.toList p) x

-- === Vectorization ===

-- WATCH OUT! This vectorization assumes that all raw references represent
-- destinations, and so no Place operations can cause write conflicts.

-- TODO: Local vector values? We might want to pack short and pure for loops into vectors,
-- to support things like float3 etc.
data Stability
  = Uniform    -- constant across vectorized dimension
  | Varying    -- varying across vectorized dimension
  | Contiguous -- varying, but contiguous across vectorized dimension
  | ProdStability [Stability]
  deriving (Eq, Show)

data VSubstValC (c::C) (n::S) where
  VVal :: Stability -> Atom n -> VSubstValC AtomNameC n
type VAtom = VSubstValC AtomNameC
instance SinkableV VSubstValC
instance SinkableE (VSubstValC c) where
  sinkingProofE fresh (VVal s x) = VVal s $ sinkingProofE fresh x

instance PrettyPrec (VSubstValC c n) where
  prettyPrec (VVal s atom) = atPrec LowestPrec $ "@" <> viaShow s <+> pretty atom

type TopVectorizeM = BuilderT (ReaderT Word32 HardFailM)

vectorizeLoops :: EnvReader m => Word32 -> Block n -> m n (Block n)
vectorizeLoops vectorByteWidth (Block _ decls ans) = do
  liftM (runHardFail . (`runReaderT` vectorByteWidth)) $ liftBuilderT $ buildBlock $ do
    s <- vectorizeLoopsRec emptyInFrag decls
    applySubst s ans
{-# INLINE vectorizeLoops #-}

vectorizeLoopsRec :: (Ext i o, Emits o)
                  => SubstFrag Name i i' o -> Nest Decl i' i''
                  -> TopVectorizeM o (SubstFrag Name i i'' o)
vectorizeLoopsRec frag = \case
  Empty -> return frag
  Nest (Let b (DeclBinding ann _ expr)) rest -> do
    vectorByteWidth <- ask
    let narrowestTypeByteWidth = 1  -- TODO: This is too conservative! Find the shortest type in the loop.
    let loopWidth = vectorByteWidth `div` narrowestTypeByteWidth
    v <- case expr of
      Hof (Seq dir (DictCon (IxFin (IdxRepVal n))) dest (Lam body))
        | n `mod` loopWidth == 0 -> do
          Distinct <- getDistinct
          let vn = IdxRepVal $ n `div` loopWidth
          body' <- vectorizeSeq loopWidth (TC $ Fin vn) frag body
          dest' <- applySubst frag dest
          emit $ Hof $ Seq dir (DictCon $ IxFin vn) dest' body'
      _ -> emitDecl (getNameHint b) ann =<< applySubst frag expr
    vectorizeLoopsRec (frag <.> b @> v) rest

vectorizeSeq :: forall i i' o. (Distinct o, Ext i o)
             => Word32 -> Type o -> SubstFrag Name i i' o -> LamExpr i'
             -> TopVectorizeM o (Atom o)
vectorizeSeq loopWidth newIxTy frag (LamExpr (LamBinder b ty arr eff) body) = do
  case eff of
    Pure -> do
      ty' <- case ty of
        ProdTy [_, ref] -> do
          ref' <- applySubst frag ref
          return $ ProdTy [newIxTy, ref']
        _ -> error "Unexpected seq binder type"
      liftM (runHardFail . (`runReaderT` loopWidth)) $ liftBuilderT $ do
        buildLam (getNameHint b) arr (sink ty') Pure \ci -> do
          (vi, dest) <- fromPair $ Var ci
          viOrd <- emitOp $ CastOp IdxRepTy vi
          iOrd <- emitOp $ BinOp IMul viOrd (IdxRepVal loopWidth)
          i <- emitOp $ CastOp (sink newIxTy) iOrd
          let s = newSubst iSubst <>> b @> VVal (ProdStability [Contiguous, Uniform]) (PairVal i dest)
          runSubstReaderT s $ runVectorizeM $ vectorizeBlock body $> UnitVal
    _ -> error "Effectful loop vectorization not implemented!"
  where
    iSubst :: (DExt o o', Color c) => Name c i' -> VSubstValC c o'
    iSubst v = case lookupSubstFragProjected frag v of
      Left v'  -> sink $ fromNameVAtom v'
      Right v' -> sink $ fromNameVAtom v'

fromNameVAtom :: forall c n. Color c => Name c n -> VSubstValC c n
fromNameVAtom v = case eqColorRep @c @AtomNameC of
  Just ColorsEqual -> VVal Uniform $ Var v
  _ -> error "Unexpected non-atom name"

newtype VectorizeM i o a =
  VectorizeM { runVectorizeM :: SubstReaderT VSubstValC (BuilderT (ReaderT Word32 HardFailM)) i o a }
  deriving ( Functor, Applicative, Monad, Fallible, MonadFail, SubstReader VSubstValC
           , Builder, EnvReader, EnvExtender, ScopeReader, ScopableBuilder )

getLoopWidth :: VectorizeM i o Word32
getLoopWidth = VectorizeM $ SubstReaderT $ ReaderT $ const $ ask

vectorizeBlock :: Emits o => Block i -> VectorizeM i o (VAtom o)
vectorizeBlock (Block _ decls (ans :: Atom i')) = go decls
  where
    go :: Emits o => Nest Decl i i' -> VectorizeM i o (VAtom o)
    go = \case
      Empty -> vectorizeAtom ans
      Nest (Let b (DeclBinding ann _ expr)) rest -> do
        unless (ann == PlainLet) $ error "Encountered a non-plain let?"
        v <- vectorizeExpr expr
        extendSubst (b @> v) $ go rest

vectorizeExpr :: Emits o => Expr i -> VectorizeM i o (VAtom o)
vectorizeExpr expr = case expr of
  Atom atom -> vectorizeAtom atom
  Op op -> vectorizeOp op
  -- Vectorizing IO might not always be safe! Here, we depend on vectorizeOp
  -- being picky about the IO-inducing ops it supports, and expect it to
  -- complain about FFI calls and the like.
  Hof (RunIO (Lam (LamExpr (LamBinder b UnitTy PlainArrow _) body))) -> do
    -- TODO: buildBlockAux?
    (vy, lam') <- withFreshBinder (getNameHint b) UnitTy \b' -> do
      Abs decls (LiftE vy `PairE` yWithTy) <- buildScoped do
        VVal vy y <- extendSubst (b @> VVal Uniform UnitVal) $ vectorizeBlock body
        PairE (LiftE vy) <$> withType y
      body' <- absToBlock =<< computeAbsEffects (Abs decls yWithTy)
      effs' <- getEffects body'
      return (vy, LamExpr (LamBinder b' UnitTy PlainArrow effs') body')
    VVal vy . Var <$> emit (Hof (RunIO (Lam lam')))
  _ -> error $ "Cannot vectorize expr: " ++ pprint expr

vectorizeOp :: Emits o => Op i -> VectorizeM i o (VAtom o)
vectorizeOp op = do
  op' <- (inline traversePrimOp) vectorizeAtom op
  case op' of
    IndexRef (VVal Uniform ref) (VVal Contiguous i) -> do
      TC (RefType _ (TabTy tb a)) <- getType ref
      vty <- getVectorType $ case hoist tb a of
        HoistSuccess a' -> a'
        HoistFailure _  -> error "Can't vectorize dependent table application"
      VVal Contiguous <$> emitOp (VectorSubref ref i vty)
    Place (VVal vref ref) sval@(VVal vval val) -> do
      VVal Uniform <$> case (vref, vval) of
        (Uniform   , Uniform   ) -> emitOp $ Place ref val
        (Uniform   , _         ) -> error "Write conflict? This should never happen!"
        (Varying   , _         ) -> error "Vector scatter not implemented"
        (Contiguous, Varying   ) -> emitOp $ Place ref val
        (Contiguous, Contiguous) -> emitOp . Place ref =<< ensureVarying sval
        _ -> error "Not implemented yet"
    UnOp opk sx@(VVal vx x) -> do
      let v = case vx of Uniform -> Uniform; _ -> Varying
      x' <- if vx /= v then ensureVarying sx else return x
      VVal v <$> emitOp (UnOp opk x')
    BinOp opk sx@(VVal vx x) sy@(VVal vy y) -> do
      let v = case (vx, vy) of (Uniform, Uniform) -> Uniform; _ -> Varying
      x' <- if vx /= v then ensureVarying sx else return x
      y' <- if vy /= v then ensureVarying sy else return y
      VVal v <$> emitOp (BinOp opk x' y')
    CastOp (VVal Uniform ty) (VVal vx x) -> do
      ty' <- case vx of
        Uniform    -> return ty
        Varying    -> getVectorType ty
        Contiguous -> return ty
        ProdStability _ -> error "Unexpected cast of product type"
      VVal vx <$> emitOp (CastOp ty' x)
    PtrOffset (VVal Uniform ptr) (VVal Contiguous off) -> do
      VVal Contiguous <$> emitOp (PtrOffset ptr off)
    PtrLoad (VVal Contiguous ptr) -> do
      BaseTy (PtrType (addrSpace, a)) <- getType ptr
      BaseTy av <- getVectorType $ BaseTy a
      ptr' <- emitOp $ CastOp (BaseTy $ PtrType (addrSpace, av)) ptr
      VVal Varying <$> emitOp (PtrLoad ptr')
    _ -> error $ "Can't vectorize op: " ++ pprint op'

vectorizeAtom :: Atom i -> VectorizeM i o (VAtom o)
vectorizeAtom atom = case atom of
  Var v -> lookupSubstM v
  ProjectElt p v -> do
    VVal vv v' <- lookupSubstM v
    return $ VVal (projStability (reverse $ NE.toList p) vv) $ getProjection (NE.toList p) v'
  Con (Lit l) -> return $ VVal Uniform $ Con $ Lit l
  _ -> do
    subst <- getSubst
    VVal Uniform <$> fmapNamesM (uniformSubst subst) atom
  where
    uniformSubst :: Color c => Subst VSubstValC i o -> Name c i -> AtomSubstVal c o
    uniformSubst subst n = case subst ! n of
      VVal Uniform x -> SubstVal x
      _ -> error $ "Can't vectorize atom " ++ pprint atom
    projStability p s = case (p, s) of
      ([]  , _                ) -> s
      (i:is, ProdStability sbs) -> projStability is (sbs !! i)
      (_   , Uniform          ) -> s
      _ -> error "Invalid projection"

getVectorType :: Type o -> VectorizeM i o (Atom o)
getVectorType ty = case ty of
  BaseTy (Scalar sbt) -> do
    els <- getLoopWidth
    return $ BaseTy $ Vector [els] sbt
  -- TODO: Should we support tables?
  _ -> error $ "Can't make a vector of " ++ pprint ty

ensureVarying :: Emits o => VAtom o -> VectorizeM i o (Atom o)
ensureVarying (VVal s val) = case s of
  Varying -> return val
  Uniform -> do
    vty <- getVectorType =<< getType val
    emitOp $ VectorBroadcast val vty
  -- Note that the implementation of this case will depend on val's type.
  Contiguous -> do
    ty <- getType val
    vty <- getVectorType ty
    case ty of
      BaseTy (Scalar sbt) -> do
        bval <- emitOp $ VectorBroadcast val vty
        iota <- emitOp $ VectorIota vty
        emitOp $ BinOp (if isIntegral sbt then IAdd else FAdd) bval iota
      _ -> error "Not implemented"
  ProdStability _ -> error "Not implemented"

-- === Extensions to the name system ===

class DistinctBetween (n::S) (l::S)
instance DistinctBetween VoidS VoidS

data DistinctBetweenEvidence (n::S) (l::S) where
  DistinctBetween :: DistinctBetween n l => DistinctBetweenEvidence n l

fabricateDistinctBetweenEvidence :: forall n l. DistinctBetweenEvidence n l
fabricateDistinctBetweenEvidence = unsafeCoerce $ DistinctBetween @VoidS @VoidS

sinkBetween :: DistinctBetween n l => e n -> e l
sinkBetween = unsafeCoerceE

shortenBetween :: forall l n n' b. (ProvesExt b, Ext n' l, DistinctBetween n l) => b n n' -> DistinctBetweenEvidence n' l
shortenBetween _ = unsafeCoerce $ DistinctBetween @n @l

isDistinctNest :: Nest Decl n l -> Maybe (DistinctBetweenEvidence n l)
isDistinctNest nest = case noShadows $ toScopeFrag nest of
  True  -> Just $ fabricateDistinctBetweenEvidence
  False -> Nothing

-- See Note [Confuse GHC] from Simplify.hs
confuseGHC :: EnvReader m => m n (DistinctEvidence n)
confuseGHC = getDistinct
{-# INLINE confuseGHC #-}
