-- Copyright 2021 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Builder (
  emit, emitOp, emitUnOp,
  buildPureLam, BuilderT (..), Builder (..), Builder2, BuilderM,
  runBuilderT, buildBlock, app, add, mul, sub, neg, div',
  iadd, imul, isub, idiv, ilt, ieq, irem,
  fpow, flog, fLitLike, recGetHead, buildPureNaryLam,
  emitMethodType, emitSuperclass,
  makeSuperclassGetter, makeMethodGetter,
  select, getUnpacked, emitUnpacked,
  fromPair, getFst, getSnd, getProj, getProjRef, getNaryProjRef, naryApp,
  ptrOffset, unsafePtrLoad, ptrLoad,
  getClassDef, getDataCon,
  Emits, EmitsEvidence (..), buildPi, buildNonDepPi,
  buildLam, buildTabLam, buildLamGeneral,
  buildAbs, buildNaryAbs, buildNaryLam, buildNullaryLam,
  buildAlt, buildUnaryAlt, buildUnaryAtomAlt,
  buildNewtype, fromNewtype,
  emitDataDef, emitClassDef, emitDataConName, emitTyConName,
  buildCase, buildSplitCase,
  emitBlock, emitDecls, BuilderEmissions, emitAtomToName,
  TopBuilder (..), TopBuilderT (..), runTopBuilderT, TopBuilder2,
   emitSourceMap, emitSynthCandidates,
  TopEnvFrag (..),
  inlineLastDecl, fabricateEmitsEvidence, fabricateEmitsEvidenceM,
  singletonBinderNest, varsAsBinderNest, typesAsBinderNest,
  runBuilderM, liftBuilder, makeBlock,
  indexToInt, indexSetSize, intToIndex, litValToPointerlessAtom, emitPtrLit,
  liftMonoidEmpty, liftMonoidCombine,
  telescopicCapture, telescopicCaptureBlock, unpackTelescope,
  applyRecon, applyReconAbs, clampPositive,
  emitRunWriter, mCombine, emitRunState, emitRunReader, buildFor, unzipTab, buildForAnn,
  zeroAt, zeroLike, maybeTangentType, tangentType,
  addTangent, updateAddAt, tangentBaseMonoidFor,
  buildEffLam,
  ReconAbs, ReconstructAtom (..), buildNullaryPi, buildNaryPi
  ) where

import Control.Applicative
import Control.Monad
import Control.Monad.Reader
import Control.Monad.Writer.Strict hiding (Alt)
import qualified Data.Map.Strict as M
import Data.Functor ((<&>))
import Data.Foldable (toList)
import Data.List (elemIndex)
import Data.Maybe (fromJust)
import Data.Graph (graphFromEdges, topSort)
import GHC.Stack

import qualified Unsafe.Coerce as TrulyUnsafe

import Name
import Syntax
import Type
import PPrint ()
import CheapReduction
import MTL1

import LabeledItems
import Util (enumerate, scanM, restructure, transitiveClosureM, bindM2)
import Err

-- === Ordinary (local) builder class ===

class (EnvReader m, EnvExtender m, Fallible1 m)
      => Builder (m::MonadKind1) where
  emitDecl
    :: (Builder m, Emits n)
    => NameHint -> LetAnn -> Expr n -> m n (AtomName n)
  buildScoped
    :: (SinkableE e, Immut n)
    => (forall l. (Emits l, DExt n l) => m l (e l))
    -> m n (DistinctAbs (Nest Decl) e n)

type Builder2 (m :: MonadKind2) = forall i. Builder (m i)

emit :: (Builder m, Emits n) => Expr n -> m n (AtomName n)
emit expr = emitDecl NoHint PlainLet expr

emitOp :: (Builder m, Emits n) => Op n -> m n (Atom n)
emitOp op = Var <$> emit (Op op)

emitUnOp :: (Builder m, Emits n) => UnOp -> Atom n -> m n (Atom n)
emitUnOp op x = emitOp $ ScalarUnOp op x

emitBlock :: (Builder m, Emits n) => Block n -> m n (Atom n)
emitBlock (Block _ decls result) = do
  result' <- emitDecls decls result
  case result' of
    Atom x -> return x
    _ -> Var <$> emit result'

emitDecls :: (Builder m, Emits n, SubstE Name e, SinkableE e)
          => Nest Decl n l -> e l -> m n (e n)
emitDecls decls result = runSubstReaderT idSubst $ emitDecls' decls result

emitDecls' :: (Builder m, Emits o, SubstE Name e, SinkableE e)
           => Nest Decl i i' -> e i' -> SubstReaderT Name m i o (e o)
emitDecls' Empty e = substM e
emitDecls' (Nest (Let b (DeclBinding ann _ expr)) rest) e = do
  expr' <- substM expr
  v <- emitDecl (getNameHint b) ann expr'
  extendSubst (b @> v) $ emitDecls' rest e

emitAtomToName :: (Builder m, Emits n) => Atom n -> m n (AtomName n)
emitAtomToName (Var v) = return v
emitAtomToName x = emit (Atom x)

-- === Top-level builder class ===

class (EnvReader m, MonadFail1 m)
      => TopBuilder (m::MonadKind1) where
  -- `emitBinding` is expressible in terms of `emitEnv` but it can be
  -- implemented more efficiently by avoiding a double substitution
  -- XXX: emitBinding/emitEnv don't extend the synthesis candidates
  emitBinding :: Mut n => NameColor c => NameHint -> Binding c n -> m n (Name c n)
  emitEnv :: (Mut n, SinkableE e, SubstE Name e)
                  => Abs TopEnvFrag e n -> m n (e n)
  emitNamelessEnv :: TopEnvFrag n n -> m n ()
  localTopBuilder :: (Immut n, SinkableE e)
                  => (forall l. (Mut l, DExt n l) => m l (e l))
                  -> m n (DistinctAbs TopEnvFrag e n)

emitSourceMap :: TopBuilder m => SourceMap n -> m n ()
emitSourceMap sm = emitNamelessEnv $ TopEnvFrag emptyOutFrag mempty sm

emitSynthCandidates :: TopBuilder m => SynthCandidates n -> m n ()
emitSynthCandidates sc = emitNamelessEnv $ TopEnvFrag emptyOutFrag sc mempty

newtype TopBuilderT (m::MonadKind) (n::S) (a:: *) =
  TopBuilderT { runTopBuilderT' :: InplaceT Env TopEnvFrag m n a }
  deriving ( Functor, Applicative, Monad, MonadFail, Fallible
           , CtxReader, ScopeReader, MonadTrans1, MonadReader r, MonadIO)

instance Fallible m => EnvReader (TopBuilderT m) where
  getEnv = TopBuilderT $ getOutMapInplaceT

instance Fallible m => TopBuilder (TopBuilderT m) where
  emitBinding hint binding = TopBuilderT $
    emitInplaceT hint binding \b binding' ->
      TopEnvFrag (toEnvFrag (b:>binding')) mempty mempty

  emitEnv ab = TopBuilderT do
    extendInplaceT do
      scope <- getScope
      ab' <- sinkM ab
      return $ refreshAbs scope ab'

  emitNamelessEnv bs = TopBuilderT $ extendTrivialInplaceT bs

  localTopBuilder cont = TopBuilderT $
    locallyMutableInplaceT $ runTopBuilderT' cont

instance (SinkableV v, TopBuilder m) => TopBuilder (SubstReaderT v m i) where
  emitBinding hint binding = SubstReaderT $ lift $ emitBinding hint binding
  emitEnv ab = SubstReaderT $ lift $ emitEnv ab
  emitNamelessEnv bs = SubstReaderT $ lift $ emitNamelessEnv bs
  localTopBuilder cont = SubstReaderT $ ReaderT \env -> do
    localTopBuilder do
      Distinct <- getDistinct
      runReaderT (runSubstReaderT' cont) (sink env)

runTopBuilderT
  :: (Fallible m, Distinct n)
  => Env n
  -> TopBuilderT m n a
  -> m a
runTopBuilderT bindings cont = do
  Immut <- return $ toImmutEvidence bindings
  liftM snd $ runInplaceT bindings $ runTopBuilderT' $ cont

type TopBuilder2 (m :: MonadKind2) = forall i. TopBuilder (m i)

-- === BuilderT ===

type BuilderEmissions = Nest Decl

instance ExtOutMap Env BuilderEmissions where
  extendOutMap bindings emissions =
    bindings `extendOutMap` toEnvFrag emissions

newtype BuilderT (m::MonadKind) (n::S) (a:: *) =
  BuilderT { runBuilderT' :: InplaceT Env BuilderEmissions m n a }
  deriving ( Functor, Applicative, Monad, MonadTrans1, MonadFail, Fallible
           , CtxReader, ScopeReader, Alternative, Searcher, MonadWriter w)

type BuilderM = BuilderT HardFailM

runBuilderT
  :: (Fallible m, Distinct n)
  => Env n
  -> BuilderT m n a
  -> m a
runBuilderT bindings cont = do
  Immut <- return $ toImmutEvidence bindings
  (Empty, result) <- runInplaceT bindings $ runBuilderT' cont
  return result

runBuilderM :: Distinct n => Env n -> BuilderM n a -> a
runBuilderM bindings m = runHardFail $ runBuilderT bindings m

liftBuilder
  :: (EnvReader m, SinkableE e)
  => (forall l. (Immut l, DExt n l) => BuilderM l (e l))
  -> m n (e n)
liftBuilder cont = liftImmut do
  DB bindings <- getDB
  return $ runBuilderM bindings $ cont

instance Fallible m => Builder (BuilderT m) where
  emitDecl hint ann expr = do
    ty <- getType expr
    BuilderT $ emitInplaceT hint (DeclBinding ann ty expr) \b rhs ->
      Nest (Let b rhs) Empty

  buildScoped cont = BuilderT $
    locallyMutableInplaceT $
      runBuilderT' do
        Emits <- fabricateEmitsEvidenceM
        Distinct <- getDistinct
        cont

instance Fallible m => EnvReader (BuilderT m) where
  getEnv = BuilderT $ getOutMapInplaceT

instance Fallible m => EnvExtender (BuilderT m) where
  extendEnv frag cont = BuilderT $
    extendInplaceTLocal (\bindings -> extendOutMap bindings frag) $
      withExtEvidence (toExtEvidence frag) $
        runBuilderT' cont

instance (SinkableV v, Builder m) => Builder (SubstReaderT v m i) where
  emitDecl hint ann expr = SubstReaderT $ lift $ emitDecl hint ann expr
  buildScoped cont = SubstReaderT $ ReaderT \env ->
    buildScoped $
      runReaderT (runSubstReaderT' cont) (sink env)

instance (SinkableE e, Builder m) => Builder (OutReaderT e m) where
  emitDecl hint ann expr =
    OutReaderT $ lift $ emitDecl hint ann expr
  buildScoped cont = OutReaderT $ ReaderT \env ->
    buildScoped do
      env' <- sinkM env
      runReaderT (runOutReaderT' cont) env'

instance (SinkableE e, Builder m) => Builder (ReaderT1 e m) where
  emitDecl hint ann expr =
    ReaderT1 $ lift $ emitDecl hint ann expr
  buildScoped cont = ReaderT1 $ ReaderT \env ->
    buildScoped do
      env' <- sinkM env
      runReaderT (runReaderT1' cont) env'

-- === Emits predicate ===

-- We use the `Emits` predicate on scope parameters to indicate that we may emit
-- decls. This lets us ensure that a computation *doesn't* emit decls, by
-- supplying a fresh name without supplying the `Emits` predicate.

class Mut n => Emits (n::S)
data EmitsEvidence (n::S) where
  Emits :: Emits n => EmitsEvidence n
instance Emits UnsafeS

fabricateEmitsEvidence :: forall n. EmitsEvidence n
fabricateEmitsEvidence =
  withEmitsEvidence (error "pure fabrication" :: EmitsEvidence n) Emits

fabricateEmitsEvidenceM :: forall m n. Monad1 m => m n (EmitsEvidence n)
fabricateEmitsEvidenceM = return fabricateEmitsEvidence

withEmitsEvidence :: forall n a. EmitsEvidence n -> (Emits n => a) -> a
withEmitsEvidence _ cont = fromWrapWithEmits
 ( TrulyUnsafe.unsafeCoerce ( WrapWithEmits cont :: WrapWithEmits n       a
                                               ) :: WrapWithEmits UnsafeS a)
newtype WrapWithEmits n r =
  WrapWithEmits { fromWrapWithEmits :: Emits n => r }

-- === lambda-like things ===

buildBlock
  :: Builder m
  => (forall l. (Emits l, DExt n l) => m l (Atom l))
  -> m n (Block n)
buildBlock cont = liftImmut do
  DistinctAbs decls results <- buildScoped do
    result <- cont
    ty <- getType result
    return $ result `PairE` ty
  let (result `PairE` ty) = results
  ty' <- liftHoistExcept $ hoist decls ty
  Abs decls' result' <- return $ inlineLastDecl decls $ Atom result
  return $ Block (BlockAnn ty') decls' result'

makeBlock :: EnvReader m => Nest Decl n l -> Expr l -> m l (Block n)
makeBlock decls expr = do
  ty <- getType expr
  let ty' = ignoreHoistFailure $ hoist decls ty
  return $ Block (BlockAnn ty') decls expr

inlineLastDecl :: Nest Decl n l -> Expr l -> Abs (Nest Decl) Expr n
inlineLastDecl Empty result = Abs Empty result
inlineLastDecl (Nest (Let b (DeclBinding _ _ expr)) Empty) (Atom (Var v))
  | v == binderName b = Abs Empty expr
inlineLastDecl (Nest decl rest) result =
  case inlineLastDecl rest result of
   Abs decls' result' ->
     Abs (Nest decl decls') result'

buildPureLam :: Builder m
             => NameHint -> Arrow -> Type n
             -> (forall l. (Emits l, DExt n l) => AtomName l -> m l (Atom l))
             -> m n (Atom n)
buildPureLam hint arr ty body = do
  buildLamGeneral hint arr ty (const $ return Pure) \v -> do
    Distinct <- getDistinct
    body v

buildTabLam
  :: Builder m
  => NameHint -> Type n
  -> (forall l. (Emits l, DExt n l) => AtomName l -> m l (Atom l))
  -> m n (Atom n)
buildTabLam hint ty body = buildLam hint TabArrow ty Pure body

buildLam
  :: Builder m
  => NameHint -> Arrow -> Type n -> EffectRow n
  -> (forall l. (Emits l, DExt n l) => AtomName l -> m l (Atom l))
  -> m n (Atom n)
buildLam hint arr ty eff body = buildLamGeneral hint arr ty (const $ sinkM eff) body

buildNullaryLam :: Builder m
                => EffectRow n
                -> (forall l. (Emits l, DExt n l) => m l (Atom l))
                -> m n (Atom n)
buildNullaryLam effs cont = buildLam "ignore" PlainArrow UnitTy effs \_ -> cont

buildNullaryPi :: Builder m
               => EffectRow n
               -> (forall l. DExt n l => m l (Type l))
               -> m n (Type n)
buildNullaryPi effs cont =
  Pi <$> buildPi "ignore" PlainArrow UnitTy \_ -> do
    resultTy <- cont
    return (sink effs, resultTy)

buildLamGeneral
  :: Builder m
  => NameHint -> Arrow -> Type n
  -> (forall l. (Immut l, DExt n l) => AtomName l -> m l (EffectRow l))
  -> (forall l. (Emits l, DExt n l) => AtomName l -> m l (Atom l))
  -> m n (Atom n)
buildLamGeneral hint arr ty fEff fBody = liftImmut do
  withFreshBinder hint (LamBinding arr ty) \b -> do
    let v = binderName b
    effs <- fEff v
    body <- withAllowedEffects effs $ buildBlock $ fBody $ sink v
    return $ Lam $ LamExpr (LamBinder b ty arr effs) body

-- Body must be an Atom because otherwise the nullary case would require
-- emitting decls into the enclosing scope.
buildPureNaryLam :: Builder m
                 => EmptyAbs (Nest PiBinder) n
                 -> (forall l. DExt n l => [AtomName l] -> m l (Atom l))
                 -> m n (Atom n)
buildPureNaryLam (EmptyAbs Empty) cont = do
  Distinct <- getDistinct
  cont []
buildPureNaryLam (EmptyAbs (Nest (PiBinder b ty arr) rest)) cont = do
  buildPureLam (getNameHint b) arr ty \x -> do
    restAbs <- sinkM $ Abs b $ EmptyAbs rest
    rest' <- applyAbs restAbs x
    buildPureNaryLam rest' \xs -> do
      x' <- sinkM x
      cont (x':xs)
buildPureNaryLam _ _ = error "impossible"

buildPi :: (Fallible1 m, Builder m)
        => NameHint -> Arrow -> Type n
        -> (forall l. DExt n l => AtomName l -> m l (EffectRow l, Type l))
        -> m n (PiType n)
buildPi hint arr ty body = liftImmut do
  withFreshPiBinder hint (PiBinding arr ty) \b -> do
    (effs, resultTy) <- body $ binderName b
    return $ PiType b effs resultTy

buildNaryPi
  :: Builder m
  => EmptyAbs (Nest Binder) n
  -> (forall l. (Distinct l, DExt n l) => [AtomName l] -> m l (Type l))
  -> m n (Type n)
buildNaryPi (EmptyAbs Empty) cont = do
  Distinct <- getDistinct
  cont []
buildNaryPi (EmptyAbs (Nest (b:>ty) bs)) cont = do
  Pi <$> buildPi (getNameHint b) PlainArrow ty \v -> do
    bs' <- applySubst (b@>v) $ EmptyAbs bs
    piTy <- buildNaryPi bs' \vs -> cont $ sink v : vs
    return (Pure, piTy)

buildNonDepPi :: EnvReader m
              => NameHint -> Arrow -> Type n -> EffectRow n -> Type n
              -> m n (PiType n)
buildNonDepPi hint arr argTy effs resultTy = liftBuilder do
  argTy' <- sinkM argTy
  buildPi hint arr argTy' \_ -> do
    resultTy' <- sinkM resultTy
    effs'     <- sinkM effs
    return (effs', resultTy')

buildAbs
  :: ( EnvReader m, EnvExtender m
     , SinkableE e, NameColor c, ToBinding binding c)
  => NameHint
  -> binding n
  -> (forall l. (Immut l, DExt n l) => Name c l -> m l (e l))
  -> m n (Abs (BinderP c binding) e n)
buildAbs hint binding cont = liftImmut do
  withFreshBinder hint binding \b -> do
    body <- cont $ binderName b
    return $ Abs (b:>binding) body

singletonBinder :: Builder m => NameHint -> Type n -> m n (EmptyAbs Binder n)
singletonBinder hint ty = buildAbs hint ty \_ -> return UnitE

varsAsBinderNest :: EnvReader m => [AtomName n] -> m n (EmptyAbs (Nest Binder) n)
varsAsBinderNest [] = return $ EmptyAbs Empty
varsAsBinderNest (v:vs) = do
  rest <- varsAsBinderNest vs
  ty <- getType v
  Abs b (Abs bs UnitE) <- return $ abstractFreeVar v rest
  return $ EmptyAbs (Nest (b:>ty) bs)

typesAsBinderNest :: EnvReader m => [Type n] -> m n (EmptyAbs (Nest Binder) n)
typesAsBinderNest types = liftImmut $ liftEnvReaderM $ go types
  where
    go :: forall n. Immut n => [Type n] -> EnvReaderM n (EmptyAbs (Nest Binder) n)
    go tys = case tys of
      [] -> return $ Abs Empty UnitE
      ty:rest -> withFreshBinder NoHint ty \b -> do
        Abs bs UnitE <- go $ map sink rest
        return $ Abs (Nest (b:>ty) bs) UnitE

singletonBinderNest :: Builder m
                    => NameHint -> Type n -> m n (EmptyAbs (Nest Binder) n)
singletonBinderNest hint ty = do
  EmptyAbs b <- singletonBinder hint ty
  return $ EmptyAbs (Nest b Empty)

buildNaryAbs
  :: (Builder m, SinkableE e, SubstE Name e, SubstE AtomSubstVal e, HoistableE e)
  => EmptyAbs (Nest Binder) n
  -> (forall l. (Immut l, Distinct l, DExt n l) => [AtomName l] -> m l (e l))
  -> m n (Abs (Nest Binder) e n)
buildNaryAbs (EmptyAbs Empty) body =
  liftImmut do
    Distinct <- getDistinct
    Abs Empty <$> body []
buildNaryAbs (EmptyAbs (Nest (b:>ty) bs)) body = do
  Abs b' (Abs bs' body') <-
    buildAbs (getNameHint b) ty \v -> do
      ab <- sinkM $ Abs b (EmptyAbs bs)
      bs' <- applyAbs ab v
      buildNaryAbs bs' \vs -> do
        v' <- sinkM v
        body $ v' : vs
  return $ Abs (Nest b' bs') body'
buildNaryAbs _ _ = error "impossible"

buildNaryLam
  :: (Builder m, Emits n)
  => EmptyAbs (Nest Binder) n
  -> (forall l. (Emits l, Distinct l, DExt n l) => [AtomName l] -> m l (Atom l))
  -> m n (Atom n)
buildNaryLam binderNest body = do
  naryAbs <- buildNaryAbs binderNest \vs ->
    buildBlock $ body $ map sink vs
  case naryAbsToNaryLam naryAbs of
    AtomicBlock atom -> return atom
    block -> emitBlock block
  where
    naryAbsToNaryLam :: Abs (Nest Binder) Block n -> Block n
    naryAbsToNaryLam (Abs nest block) = case nest of
      Empty -> block
      Nest (b:>ty) bs ->
        AtomicBlock $ Lam $ LamExpr (LamBinder b ty PlainArrow Pure) $
          naryAbsToNaryLam $ Abs bs block

buildAlt
  :: Builder m
  => EmptyAbs (Nest Binder) n
  -> (forall l. (Distinct l, Emits l, DExt n l) => [AtomName l] -> m l (Atom l))
  -> m n (Alt n)
buildAlt bs body = do
  buildNaryAbs bs \xs -> do
    buildBlock do
      Distinct <- getDistinct
      xs' <- mapM sinkM xs
      body xs'

buildUnaryAlt
  :: Builder m
  => Type n
  -> (forall l. (Emits l, DExt n l) => AtomName l -> m l (Atom l))
  -> m n (Alt n)
buildUnaryAlt ty body = do
  bs <- singletonBinderNest NoHint ty
  buildAlt bs \[v] -> body v

buildUnaryAtomAlt
  :: Builder m
  => Type n
  -> (forall l. (Distinct l, DExt n l) => AtomName l -> m l (Atom l))
  -> m n (AltP Atom n)
buildUnaryAtomAlt ty body = do
  bs <- singletonBinderNest NoHint ty
  buildNaryAbs bs \[v] -> do
    Distinct <- getDistinct
    body v

buildNewtype :: Builder m
             => SourceName
             -> EmptyAbs (Nest Binder) n
             -> (forall l. (Immut l, DExt n l) => [AtomName l] -> m l (Type l))
             -> m n (DataDef n)
buildNewtype name paramBs body = do
  Abs paramBs' argBs <- buildNaryAbs paramBs \params -> do
    ty <- body params
    singletonBinderNest NoHint ty
  return $ DataDef name paramBs' [DataConDef ("mk" <> name) argBs]

fromNewtype :: [DataConDef n]
            -> Maybe (Type n)
fromNewtype [DataConDef _ (EmptyAbs (Nest (_:>ty) Empty))] = Just ty
fromNewtype _ = Nothing

-- TODO: consider a version with nonempty list of alternatives where we figure
-- out the result type from one of the alts rather than providing it explicitly
buildCase :: (Emits n, Builder m)
          => Atom n -> Type n
          -> (forall l. (Emits l, DExt n l) => Int -> [AtomName l] -> m l (Atom l))
          -> m n (Atom n)
buildCase scrut resultTy indexedAltBody = do
  eff <- getAllowedEffects
  scrutTy <- getType scrut
  altsBinderTys <- caseAltsBinderTys scrutTy
  alts <- forM (enumerate altsBinderTys) \(i, bs) -> do
    buildNaryAbs bs \xs -> do
      buildBlock do
        ListE xs' <- sinkM $ ListE xs
        indexedAltBody i xs'
  liftM Var $ emit $ Case scrut alts resultTy eff

buildSplitCase :: (Emits n, Builder m)
               => LabeledItems (Type n) -> Atom n -> Type n
               -> (forall l. (Emits l, DExt n l) => AtomName l -> m l (Atom l))
               -> (forall l. (Emits l, DExt n l) => AtomName l -> m l (Atom l))
               -> m n (Atom n)
buildSplitCase tys scrut resultTy match fallback = do
  split <- emitOp $ VariantSplit tys scrut
  buildCase split resultTy \i [v] ->
    case i of
      0 -> match v
      1 -> fallback v
      _ -> error "should only have two cases"

buildEffLam
  :: Builder m
  => RWS -> NameHint -> Type n
  -> (forall l. (Emits l, DExt n l) => AtomName l -> AtomName l -> m l (Atom l))
  -> m n (Atom n)
buildEffLam rws hint ty body = do
  eff <- getAllowedEffects
  buildLam "h" PlainArrow TyKind Pure \h -> do
    let eff' = extendEffect (RWSEffect rws (Just h)) (sink eff)
    buildLam hint PlainArrow (RefTy (Var h) (sink ty)) eff' \ref ->
      body (sink h) ref

buildForAnn
  :: (Emits n, Builder m)
  => NameHint -> ForAnn -> Type n
  -> (forall l. (Emits l, DExt n l) => AtomName l -> m l (Atom l))
  -> m n (Atom n)
buildForAnn hint ann ty body = do
  -- TODO: consider only tracking the effects that are actually needed.
  eff <- getAllowedEffects
  lam <- buildLam hint PlainArrow ty eff body
  liftM Var $ emit $ Hof $ For ann lam

buildFor :: (Emits n, Builder m)
         => NameHint -> Direction -> Type n
         -> (forall l. (Emits l, DExt n l) => AtomName l -> m l (Atom l))
         -> m n (Atom n)
buildFor hint dir ty body = buildForAnn hint (RegularFor dir) ty body

unzipTab :: (Emits n, Builder m) => Atom n -> m n (Atom n, Atom n)
unzipTab tab = do
  TabTy b _ <- getType tab
  fsts <- buildLam "i" TabArrow (binderType b) Pure \i ->
            liftM fst $ app (sink tab) (Var i) >>= fromPair
  snds <- buildLam "i" TabArrow (binderType b) Pure \i ->
            liftM snd $ app (sink tab) (Var i) >>= fromPair
  return (fsts, snds)

emitRunWriter
  :: (Emits n ,Builder m)
  => NameHint -> Type n -> BaseMonoid n
  -> (forall l. (Emits l, DExt n l) => AtomName l -> AtomName l -> m l (Atom l))
  -> m n (Atom n)
emitRunWriter hint accTy bm body = do
  lam <- buildEffLam Writer hint accTy \h ref -> body h ref
  liftM Var $ emit $ Hof $ RunWriter bm lam

mCombine :: (Emits n, Builder m) => Atom n -> Atom n -> Atom n -> m n (Atom n)
mCombine monoidDict x y = do
  ty <- getType x
  Just method <- lookupSourceMap MethodNameRep "mcombine"
  MethodBinding _ _ projection <- lookupEnv method
  naryApp projection [ty, monoidDict, x, y]

emitRunState
  :: (Emits n ,Builder m)
  => NameHint -> Atom n
  -> (forall l. (Emits l, DExt n l) => AtomName l -> AtomName l -> m l (Atom l))
  -> m n (Atom n)
emitRunState hint initVal body = do
  stateTy <- getType initVal
  lam <- buildEffLam State hint stateTy \h ref -> body h ref
  liftM Var $ emit $ Hof $ RunState initVal lam

emitRunReader
  :: (Emits n ,Builder m)
  => NameHint -> Atom n
  -> (forall l. (Emits l, DExt n l) => AtomName l -> AtomName l -> m l (Atom l))
  -> m n (Atom n)
emitRunReader hint r body = do
  rTy <- getType r
  lam <- buildEffLam Reader hint rTy \h ref -> body h ref
  liftM Var $ emit $ Hof $ RunReader r lam

-- === vector space (ish) type class ===

zeroAt :: HasCallStack => Builder m => Type n -> m n (Atom n )
zeroAt ty = case ty of
  BaseTy bt  -> return $ Con $ Lit $ zeroLit bt
  ProdTy tys -> ProdVal <$> mapM zeroAt tys
  RecordTy (Ext tys Nothing) -> Record <$> mapM zeroAt tys
  TabTy b bodyTy ->
    buildTabLam (getNameHint b) (binderType b) \i ->
      zeroAt =<< applySubst (b@>i) bodyTy
  _ -> unreachable
  where
    unreachable :: a
    unreachable = error $ "Missing zero case for a tangent type: " ++ pprint ty
    zeroLit bt = case bt of
      Scalar Float64Type -> Float64Lit 0.0
      Scalar Float32Type -> Float32Lit 0.0
      Vector st          -> VecLit $ replicate vectorWidth $ zeroLit $ Scalar st
      _                  -> unreachable

zeroLike :: (HasCallStack, HasType e, Builder m) => e n -> m n (Atom n )
zeroLike x = zeroAt =<< getType x

tangentType :: Type n -> Type n
tangentType ty = case maybeTangentType ty of
  Just tanTy -> tanTy
  Nothing -> error $ "can't differentiate wrt type: " ++ pprint ty

maybeTangentType :: Type n -> Maybe (Type n)
maybeTangentType ty = case ty of
  RecordTy (NoExt items) -> RecordTy <$> NoExt <$> mapM maybeTangentType items
  TypeCon _ _ _ -> Nothing -- Need to synthesize or look up a tangent ADT
  Pi (PiType b@(PiBinder _ _ TabArrow) Pure bodyTy) -> do
    bodyTanTy <- maybeTangentType bodyTy
    return $ Pi (PiType b Pure bodyTanTy)
  TC con    -> case con of
    BaseType (Scalar Float64Type) -> return $ TC con
    BaseType (Scalar Float32Type) -> return $ TC con
    BaseType (Vector Float64Type) -> return $ TC con
    BaseType (Vector Float32Type) -> return $ TC con
    BaseType   _                  -> return $ UnitTy
    IntRange   _ _                -> return $ UnitTy
    IndexRange _ _ _              -> return $ UnitTy
    IndexSlice _ _                -> return $ UnitTy
    ProdType   tys                -> ProdTy <$> traverse maybeTangentType tys
    _ -> Nothing
  _ -> Nothing

tangentBaseMonoidFor :: Builder m => Type n -> m n (BaseMonoid n)
tangentBaseMonoidFor ty = do
  zero <- zeroAt ty
  adder <- buildLam "t" PlainArrow ty Pure \v -> updateAddAt $ Var v
  return $ BaseMonoid zero adder

addTangent :: (Emits n, Builder m) => Atom n -> Atom n -> m n (Atom n)
addTangent x y = do
  getType x >>= \case
    RecordTy (NoExt tys) -> do
      elems <- bindM2 (zipWithM addTangent) (getUnpacked x) (getUnpacked y)
      return $ Record $ restructure elems tys
    TabTy b _  -> buildFor (getNameHint b) Fwd (binderType b) \i -> do
      bindM2 addTangent (app (sink x) (Var i)) (app (sink y) (Var i))
    TC con -> case con of
      BaseType (Scalar _) -> emitOp $ ScalarBinOp FAdd x y
      BaseType (Vector _) -> emitOp $ VectorBinOp FAdd x y
      ProdType _          -> do
        xs <- getUnpacked x
        ys <- getUnpacked y
        ProdVal <$> zipWithM addTangent xs ys
      ty -> notTangent ty
    ty -> notTangent ty
    where notTangent ty = error $ "Not a tangent type: " ++ pprint ty

updateAddAt :: (Emits n, Builder m) => Atom n -> m n (Atom n)
updateAddAt x = do
  ty <- getType x
  buildLam "t" PlainArrow ty Pure \v -> addTangent (sink x) (Var v)

-- === builder versions of common top-level emissions ===

litValToPointerlessAtom :: (Mut n, TopBuilder m) => LitVal -> m n (Atom n)
litValToPointerlessAtom litval = case litval of
  PtrLit ptrTy ptr -> Var <$> emitPtrLit "ptr" ptrTy ptr
  VecLit _ -> error "not implemented"
  _ -> return $ Con $ Lit litval

emitPtrLit :: (Mut n, TopBuilder m) => NameHint -> PtrType -> Ptr () -> m n (AtomName n)
emitPtrLit hint ptrTy ptr =
  emitBinding hint $ AtomNameBinding $ PtrLitBound ptrTy ptr

emitDataDef :: (Mut n, TopBuilder m) => DataDef n -> m n (DataDefName n)
emitDataDef dataDef@(DataDef sourceName _ _) =
  emitBinding hint $ DataDefBinding dataDef
  where hint = getNameHint sourceName

emitClassDef :: (Mut n, TopBuilder m) => ClassDef n -> Atom n -> m n (Name ClassNameC n)
emitClassDef classDef@(ClassDef name _ _) dictTyAtom =
  emitBinding (getNameHint name) $ ClassBinding classDef dictTyAtom

emitDataConName :: (Mut n, TopBuilder m) => DataDefName n -> Int -> Atom n -> m n (Name DataConNameC n)
emitDataConName dataDefName conIdx conAtom = do
  DataDef _ _ dataCons <- lookupDataDef dataDefName
  let (DataConDef name _) = dataCons !! conIdx
  emitBinding (getNameHint name) $ DataConBinding dataDefName conIdx conAtom

emitSuperclass :: (Mut n ,TopBuilder m)
               => ClassName n -> Int -> m n (Name SuperclassNameC n)
emitSuperclass dataDef idx = do
  getter <- makeSuperclassGetter dataDef idx
  emitSynthCandidates $ SynthCandidates [] [getter] mempty
  emitBinding hint $ SuperclassBinding dataDef idx getter
  where hint = getNameHint $ "Proj" <> show idx <> pprint dataDef

zipNest :: (forall ii ii'. a -> b ii ii' -> b' ii ii')
        -> [a]
        -> Nest b  i i'
        -> Nest b' i i'
zipNest _ _ Empty = Empty
zipNest f (x:t) (Nest b rest) = Nest (f x b) $ zipNest f t rest
zipNest _ _ _ = error "List too short!"

zipPiBinders :: [Arrow] -> Nest Binder i i' -> Nest PiBinder i i'
zipPiBinders = zipNest \arr (b :> ty) -> PiBinder b ty arr

makeSuperclassGetter :: EnvReader m => Name ClassNameC n -> Int -> m n (Atom n)
makeSuperclassGetter classDefName methodIdx = liftBuilder do
  classDefName' <- sinkM classDefName
  ClassDef _ _ defName <- getClassDef classDefName'
  DataDef sourceName paramBs _ <- lookupDataDef defName
  buildPureNaryLam (EmptyAbs $ zipPiBinders (repeat ImplicitArrow) paramBs) \params -> do
    defName' <- sinkM defName
    let tc = TypeCon sourceName defName' (map Var params)
    buildPureLam "subclassDict" PlainArrow tc \dict ->
      return $ getProjection [methodIdx] $ getProjection [0, 0] $ Var dict

emitMethodType :: (Mut n, TopBuilder m)
               => NameHint -> ClassName n -> [Bool] -> Int -> m n (Name MethodNameC n)
emitMethodType hint classDef explicit idx = do
  getter <- makeMethodGetter classDef explicit idx
  emitBinding hint $ MethodBinding classDef idx getter

makeMethodGetter :: EnvReader m => Name ClassNameC n -> [Bool] -> Int -> m n (Atom n)
makeMethodGetter classDefName explicit methodIdx = liftBuilder do
  classDefName' <- sinkM classDefName
  ClassDef _ _ defName <- getClassDef classDefName'
  DataDef sourceName paramBs _ <- lookupDataDef defName
  let arrows = explicit <&> \case True -> PlainArrow; False -> ImplicitArrow
  buildPureNaryLam (EmptyAbs $ zipPiBinders arrows paramBs) \params -> do
    defName' <- sinkM defName
    buildPureLam "dict" ClassArrow (TypeCon sourceName defName' (map Var params)) \dict ->
      return $ getProjection [methodIdx] $ getProjection [1, 0] $ Var dict

emitTyConName :: (Mut n, TopBuilder m) => DataDefName n -> Atom n -> m n (Name TyConNameC n)
emitTyConName dataDefName tyConAtom = do
  emitBinding (getNameHint dataDefName) $ TyConBinding dataDefName tyConAtom

getDataCon :: EnvReader m => Name DataConNameC n -> m n (DataDefName n, Int)
getDataCon v = do
  ~(DataConBinding defName idx _) <- lookupEnv v
  return (defName, idx)

getClassDef :: EnvReader m => Name ClassNameC n -> m n (ClassDef n)
getClassDef classDefName = do
  ~(ClassBinding classDef _) <- lookupEnv classDefName
  return classDef

-- === builder versions of common local ops ===

recGetHead :: EnvReader m => Label -> Atom n -> m n (Atom n)
recGetHead l x = do
  ~(RecordTy (Ext r _)) <- getType x
  let i = fromJust $ elemIndex l $ map fst $ toList $ reflectLabels r
  return $ getProjection [i] x

fLitLike :: (Builder m, Emits n) => Double -> Atom n -> m n (Atom n)
fLitLike x t = do
  ty <- getType t
  case ty of
    BaseTy (Scalar Float64Type) -> return $ Con $ Lit $ Float64Lit x
    BaseTy (Scalar Float32Type) -> return $ Con $ Lit $ Float32Lit $ realToFrac x
    _ -> error "Expected a floating point scalar"

neg :: (Builder m, Emits n) => Atom n -> m n (Atom n)
neg x = emitOp $ ScalarUnOp FNeg x

add :: (Builder m, Emits n) => Atom n -> Atom n -> m n (Atom n)
add x y = emitOp $ ScalarBinOp FAdd x y

-- TODO: Implement constant folding for fixed-width integer types as well!
iadd :: (Builder m, Emits n) => Atom n -> Atom n -> m n (Atom n)
iadd (Con (Lit l)) y | getIntLit l == 0 = return y
iadd x (Con (Lit l)) | getIntLit l == 0 = return x
iadd x@(Con (Lit _)) y@(Con (Lit _)) = return $ applyIntBinOp (+) x y
iadd x y = emitOp $ ScalarBinOp IAdd x y

mul :: (Builder m, Emits n) => Atom n -> Atom n -> m n (Atom n)
mul x y = emitOp $ ScalarBinOp FMul x y

imul :: (Builder m, Emits n) => Atom n -> Atom n -> m n (Atom n)
imul   (Con (Lit l)) y               | getIntLit l == 1 = return y
imul x                 (Con (Lit l)) | getIntLit l == 1 = return x
imul x@(Con (Lit _)) y@(Con (Lit _))                    = return $ applyIntBinOp (*) x y
imul x y = emitOp $ ScalarBinOp IMul x y

sub :: (Builder m, Emits n) => Atom n -> Atom n -> m n (Atom n)
sub x y = emitOp $ ScalarBinOp FSub x y

isub :: (Builder m, Emits n) => Atom n -> Atom n -> m n (Atom n)
isub x (Con (Lit l)) | getIntLit l == 0 = return x
isub x@(Con (Lit _)) y@(Con (Lit _)) = return $ applyIntBinOp (-) x y
isub x y = emitOp $ ScalarBinOp ISub x y

select :: (Builder m, Emits n) => Atom n -> Atom n -> Atom n -> m n (Atom n)
select (Con (Lit (Word8Lit p))) x y = return $ if p /= 0 then x else y
select p x y = emitOp $ Select p x y

div' :: (Builder m, Emits n) => Atom n -> Atom n -> m n (Atom n)
div' x y = emitOp $ ScalarBinOp FDiv x y

idiv :: (Builder m, Emits n) => Atom n -> Atom n -> m n (Atom n)
idiv x (Con (Lit l)) | getIntLit l == 1 = return x
idiv x@(Con (Lit _)) y@(Con (Lit _)) = return $ applyIntBinOp div x y
idiv x y = emitOp $ ScalarBinOp IDiv x y

irem :: (Builder m, Emits n) => Atom n -> Atom n -> m n (Atom n)
irem x y = emitOp $ ScalarBinOp IRem x y

fpow :: (Builder m, Emits n) => Atom n -> Atom n -> m n (Atom n)
fpow x y = emitOp $ ScalarBinOp FPow x y

flog :: (Builder m, Emits n) => Atom n -> m n (Atom n)
flog x = emitOp $ ScalarUnOp Log x

ilt :: (Builder m, Emits n) => Atom n -> Atom n -> m n (Atom n)
ilt x@(Con (Lit _)) y@(Con (Lit _)) = return $ applyIntCmpOp (<) x y
ilt x y = emitOp $ ScalarBinOp (ICmp Less) x y

ieq :: (Builder m, Emits n) => Atom n -> Atom n -> m n (Atom n)
ieq x@(Con (Lit _)) y@(Con (Lit _)) = return $ applyIntCmpOp (==) x y
ieq x y = emitOp $ ScalarBinOp (ICmp Equal) x y

fromPair :: (Builder m, Emits n) => Atom n -> m n (Atom n, Atom n)
fromPair pair = do
  ~[x, y] <- getUnpacked pair
  return (x, y)

getProj :: (Builder m, Emits n) => Int -> Atom n -> m n (Atom n)
getProj i x = do
  xs <- getUnpacked x
  return $ xs !! i

getFst :: (Builder m, Emits n) => Atom n -> m n (Atom n)
getFst p = fst <$> fromPair p

getSnd :: (Builder m, Emits n) => Atom n -> m n (Atom n)
getSnd p = snd <$> fromPair p

-- the rightmost index is applied first
getNaryProjRef :: (Builder m, Emits n) => [Int] -> Atom n -> m n (Atom n)
getNaryProjRef [] ref = return ref
getNaryProjRef (i:is) ref = getProjRef i =<< getNaryProjRef is ref

getProjRef :: (Builder m, Emits n) => Int -> Atom n -> m n (Atom n)
getProjRef i r = emitOp $ ProjRef i r

-- XXX: getUnpacked must reduce its argument to enforce the invariant that
-- ProjectElt atoms are always fully reduced (to avoid type errors between two
-- equivalent types spelled differently).
getUnpacked :: (Fallible1 m, EnvReader m) => Atom n -> m n [Atom n]
getUnpacked atom = do
  atom' <- cheapReduce atom
  ty <- getType atom'
  len <- projectLength ty
  return $ map (\i -> getProjection [i] atom') [0..(len-1)]

-- TODO: should we just make all of these return names instead of atoms?
emitUnpacked :: (Builder m, Emits n) => Atom n -> m n [AtomName n]
emitUnpacked tup = do
  xs <- getUnpacked tup
  forM xs \x -> emit $ Atom x

app :: (Builder m, Emits n) => Atom n -> Atom n -> m n (Atom n)
app x i = Var <$> emit (App x i)

naryApp :: (Builder m, Emits n) => Atom n -> [Atom n] -> m n (Atom n)
naryApp f xs = foldM app f xs

indexAsInt :: (Builder m, Emits n) => Atom n -> m n (Atom n)
indexAsInt idx = emitOp $ ToOrdinal idx

ptrOffset :: (Builder m, Emits n) => Atom n -> Atom n -> m n (Atom n)
ptrOffset x (IdxRepVal 0) = return x
ptrOffset x i = emitOp $ PtrOffset x i

unsafePtrLoad :: (Builder m, Emits n) => Atom n -> m n (Atom n)
unsafePtrLoad x = do
  lam <- buildLam "_ign" PlainArrow UnitTy (oneEffect IOEffect) \_ ->
    ptrLoad =<< sinkM x
  liftM Var $ emit $ Hof $ RunIO $ lam

ptrLoad :: (Builder m, Emits n) => Atom n -> m n (Atom n)
ptrLoad x = emitOp $ PtrLoad x

liftMonoidEmpty :: (Builder m, Emits n)
                => Type n -> Atom n -> m n (Atom n)
liftMonoidEmpty accTy x = do
  xTy <- getType x
  alphaEq xTy accTy >>= \case
    True -> return x
    False -> case accTy of
      TabTy b eltTy -> do
        buildTabLam "i" (binderType b) \i -> do
          x' <- sinkM x
          ab <- sinkM $ Abs b eltTy
          eltTy' <- applyAbs ab i
          liftMonoidEmpty eltTy' x'
      _ -> error $ "Base monoid type mismatch: can't lift " ++
             pprint xTy ++ " to " ++ pprint accTy

liftMonoidCombine :: (Builder m, Emits n)
                  => Type n -> Atom n -> Atom n -> Atom n
                  -> m n (Atom n)
liftMonoidCombine accTy baseCombine x y = do
  Pi baseCombineTy <- getType baseCombine
  let baseTy = piArgType baseCombineTy
  alphaEq accTy baseTy >>= \case
    True -> naryApp baseCombine [x, y]
    False -> case accTy of
      TabTy b eltTy -> do
        buildFor "i" Fwd (binderType b) \i -> do
          xElt <- app (sink x) (Var i)
          yElt <- app (sink y) (Var i)
          eltTy' <- applySubst (b@>i) eltTy
          liftMonoidCombine eltTy' (sink baseCombine) xElt yElt
      _ -> error $ "Base monoid type mismatch: can't lift " ++
             pprint baseTy ++ " to " ++ pprint accTy

-- === index set type class ===

clampPositive :: (Builder m, Emits n) => Atom n -> m n (Atom n)
clampPositive x = do
  isNegative <- x `ilt` (IdxRepVal 0)
  select isNegative (IdxRepVal 0) x

intToIndex :: forall m n. (Builder m, Emits n) => Type n -> Atom n -> m n (Atom n)
intToIndex ty i = case ty of
  TC (IntRange        low high) -> return $ Con $ IntRangeVal        low high i
  TC (IndexRange from low high) -> return $ Con $ IndexRangeVal from low high i
  TC (ProdType types) -> (ProdVal . reverse) <$> intToProd (reverse types)
  RecordTy  (NoExt types) -> Record <$> intToProd types
  SumTy types             -> intToSum types [0..] $ SumVal ty
  VariantTy (NoExt types) -> intToSum types (reflectLabels types) $ uncurry $ Variant (NoExt types)
  _ -> error "not an (implemented) index set"
  where
    -- XXX: Expects that the types are in a minor-to-major order
    intToProd :: Traversable t => t (Type n) -> m n (t (Atom n))
    intToProd types = do
      sizes <- traverse indexSetSize types
      (strides, _) <- scanM
        (\sz prev -> do {v <- imul sz prev; return ((prev, v), v)}) sizes (IdxRepVal 1)
      offsets <- flip mapM (zip (toList types) (toList strides)) $
        \(ety, (s1, s2)) -> do
          x <- irem i s2
          y <- idiv x s1
          intToIndex ety y
      return $ restructure offsets types

    intToSum :: Traversable t => t (Type n) -> t l -> (l -> Atom n -> Atom n) -> m n (Atom n)
    intToSum types labels mkSum = do
      sizes <- traverse indexSetSize types
      (offsets, _) <- scanM (\sz prev -> (prev,) <$> iadd sz prev) sizes (IdxRepVal 0)
      let
        -- Find the right index by looping through the possible offsets
        go prev (label, cty, offset) = do
          shifted <- isub i offset
          -- TODO: This might run intToIndex on negative indices. Fix this!
          index   <- intToIndex cty shifted
          beforeThis <- ilt i offset
          select beforeThis prev $ mkSum label index
        (l, ty0, _):zs = zip3 (toList labels) (toList types) (toList offsets)
      start <- mkSum l <$> intToIndex ty0 i
      foldM go start zs

data IterOrder = MinorToMajor | MajorToMinor

indexToInt :: forall m n. (Builder m, Emits n) => Atom n -> m n (Atom n)
indexToInt (Con (IntRangeVal _ _ i))     = return i
indexToInt (Con (IndexRangeVal _ _ _ i)) = return i
indexToInt idx = getType idx >>= \case
  TC (IntRange _ _)     -> indexAsInt idx
  TC (IndexRange _ _ _) -> indexAsInt idx
  ProdTy           types  -> prodToInt MajorToMinor types
  RecordTy  (NoExt types) -> prodToInt MinorToMajor types
  SumTy            types  -> sumToInt types
  VariantTy (NoExt types) -> sumToInt types
  TC (ParIndexRange _ _ _) -> error "Int casts unsupported on ParIndexRange"
  ty -> error $ "Unexpected type " ++ pprint ty
  where
    prodToInt :: Traversable t => IterOrder -> t (Type n) -> m n (Atom n)
    prodToInt order types = do
      sizes <- toList <$> traverse indexSetSize types
      let rev = case order of MinorToMajor -> id; MajorToMinor -> reverse
      strides <- rev . fst <$> scanM (\sz prev -> (prev,) <$> imul sz prev) (rev sizes) (IdxRepVal 1)
      -- Unpack and sum the strided contributions
      subindices <- getUnpacked idx
      subints <- traverse indexToInt subindices
      scaled <- mapM (uncurry imul) $ zip strides subints
      foldM iadd (IdxRepVal 0) scaled

    sumToInt :: Traversable t => t (Type n) -> m n (Atom n)
    sumToInt types = do
      sizes <- traverse indexSetSize types
      (offsets, _) <- scanM (\sz prev -> (prev,) <$> iadd sz prev) sizes (IdxRepVal 0)
      alts <- flip mapM (zip (toList offsets) (toList types)) $
        \(offset, subty) -> buildUnaryAlt subty \subix -> do
          i <- indexToInt $ Var subix
          iadd (sink offset) i
      liftM Var $ emit $ Case idx alts IdxRepTy Pure

indexSetSize :: (Builder m, Emits n) => Type n -> m n (Atom n)
indexSetSize ty = case ty of
  TC (IntRange low high) -> clampPositive =<< high `isub` low
  TC (IndexRange n low high) -> do
    low' <- case low of
      InclusiveLim x -> indexToInt x
      ExclusiveLim x -> indexToInt x >>= iadd (IdxRepVal 1)
      Unlimited      -> return $ IdxRepVal 0
    high' <- case high of
      InclusiveLim x -> indexToInt x >>= iadd (IdxRepVal 1)
      ExclusiveLim x -> indexToInt x
      Unlimited      -> indexSetSize n
    clampPositive =<< high' `isub` low'
  TC (ProdType types) -> do
    sizes <- traverse indexSetSize types
    foldM imul (IdxRepVal 1) sizes
  RecordTy (NoExt types) -> do
    sizes <- traverse indexSetSize types
    foldM imul (IdxRepVal 1) sizes
  TC (SumType types) -> do
    sizes <- traverse indexSetSize types
    foldM iadd (IdxRepVal 0) sizes
  VariantTy (NoExt types) -> do
    sizes <- traverse indexSetSize types
    foldM iadd (IdxRepVal 0) sizes
  _ -> error $ "Not an (implemented) index set " ++ pprint ty

-- === capturing closures with telescopes ===

type ReconAbs e n = NaryAbs AtomNameC e n
data ReconstructAtom (n::S) =
   IdentityRecon
 | LamRecon (ReconAbs Atom n)

applyRecon :: (EnvReader m, Fallible1 m)
           => ReconstructAtom n -> Atom n -> m n (Atom n)
applyRecon IdentityRecon x = return x
applyRecon (LamRecon ab) x = applyReconAbs ab x

applyReconAbs
  :: (EnvReader m, Fallible1 m, SinkableE e, SubstE AtomSubstVal e)
  => ReconAbs e n -> Atom n -> m n (e n)
applyReconAbs ab x = do
  xs <- unpackTelescope x
  applyNaryAbs ab $ map SubstVal xs

telescopicCaptureBlock
  :: (EnvReader m, HoistableE e)
  => Nest Decl n l -> e l -> m l (Block n, ReconAbs e n)
telescopicCaptureBlock decls result = do
  (result', ty, ab) <- telescopicCapture decls result
  let block = Block (BlockAnn ty) decls (Atom result')
  return (block, ab)

telescopicCapture
  :: (EnvReader m, HoistableE e, HoistableB b)
  => b n l -> e l -> m l (Atom l, Type n, ReconAbs e n)
telescopicCapture bs e = do
  vs <- localVarsAndTypeVars bs e
  vTys <- mapM (getType . Var) vs
  let (vsSorted, tys) = unzip $ toposortAnnVars $ zip vs vTys
  ty <- liftImmut $ liftEnvReaderM $ buildTelescopeTy vs tys
  result <- buildTelescopeVal (map Var vsSorted) ty
  let ty' = ignoreHoistFailure $ hoist bs ty
  let ab  = ignoreHoistFailure $ hoist bs $ abstractFreeVarsNoAnn vsSorted e
  return (result, ty', ab)

-- XXX: assumes arguments are toposorted
buildTelescopeTy :: (EnvReader m, EnvExtender m, Immut n)
                 => [AtomName n] -> [Type n] -> m n (Type n)
buildTelescopeTy [] [] = return UnitTy
buildTelescopeTy (v:vs) (ty:tys) = do
  withFreshBinder (getNameHint v) (MiscBound ty) \b -> do
    ListE tys' <- applyAbs (sink $ abstractFreeVar v $ ListE tys) (binderName b)
    ListE vs' <- sinkM $ ListE vs
    innerTelescope <- buildTelescopeTy vs' tys'
    return case hoist b innerTelescope of
      HoistSuccess innerTelescope' -> PairTy ty innerTelescope'
      HoistFailure _ -> DepPairTy $ DepPairType (b:>ty) innerTelescope
buildTelescopeTy _ _ = error "zip mismatch"

buildTelescopeVal :: EnvReader m => [Atom n] -> Type n -> m n (Atom n)
buildTelescopeVal elts telescopeTy = go elts telescopeTy
  where
    go :: (EnvReader m) => [Atom n] -> Type n -> m n (Atom n)
    go [] UnitTy = return UnitVal
    go (x:xs) (PairTy _ xsTy) = do
      rest <- go xs xsTy
      return $ PairVal x rest
    go (x:xs) (DepPairTy ty) = do
      xsTy <- instantiateDepPairTy ty x
      rest <- go xs xsTy
      return $ DepPair x rest ty
    go _ _ = error "zip mismatch"

-- sorts name-annotation pairs so that earlier names may be occur free in later
-- annotations but not vice versa.
toposortAnnVars :: forall e c n. (NameColor c, HoistableE e)
                => [(Name c n, e n)] -> [(Name c n, e n)]
toposortAnnVars annVars =
  let (graph, vertexToNode, _) = graphFromEdges $ map annVarToNode annVars
  in map (nodeToAnnVar . vertexToNode) $ reverse $ topSort graph
  where
    annVarToNode :: (Name c n, e n) -> (e n, Name c n, [Name c n])
    annVarToNode (v, ann) = (ann, v, nameSetToList nameColorRep $ freeVarsE ann)

    nodeToAnnVar :: (e n, Name c n, [Name c n]) -> (Name c n, e n)
    nodeToAnnVar (ann, v, _) = (v, ann)

unpackTelescope :: (Fallible1 m, EnvReader m) => Atom n -> m n [Atom n]
unpackTelescope atom = do
  n <- telescopeLength <$> getType atom
  return $ go n atom
  where
    go :: Int -> Atom n -> [Atom n]
    go 0 _ = []
    go n pair = left : go (n-1) right
      where left  = getProjection [0] pair
            right = getProjection [1] pair

    telescopeLength :: Type n -> Int
    telescopeLength ty = case ty of
      UnitTy -> 0
      PairTy _ rest -> 1 + telescopeLength rest
      DepPairTy (DepPairType _ rest) -> 1 + telescopeLength rest
      _ -> error $ "not a valid telescope: " ++ pprint ty

-- gives a list of atom names that are free in `e`, including names mentioned in
-- the types of those names, recursively.
localVarsAndTypeVars
  :: forall m b e n l.
     (EnvReader m, BindsNames b, HoistableE e)
  => b n l -> e l -> m l [AtomName l]
localVarsAndTypeVars b e =
  transitiveClosureM varsViaType (localVars b e)
  where
    varsViaType :: AtomName l -> m l [AtomName l]
    varsViaType v = do
      ty <- getType $ Var v
      return $ nameSetToList nameColorRep $ freeVarsE ty

localVars :: (NameColor c, BindsNames b, HoistableE e)
          => b n l -> e l -> [Name c l]
localVars b e = nameSetToList nameColorRep $
  M.intersection (toNameSet (toScopeFrag b)) (freeVarsE e)

instance GenericE ReconstructAtom where
  type RepE ReconstructAtom = EitherE UnitE (NaryAbs AtomNameC Atom)
  toE = undefined
  fromE = undefined

instance SinkableE   ReconstructAtom
instance HoistableE  ReconstructAtom
instance AlphaEqE    ReconstructAtom
instance SubstE Name ReconstructAtom
instance SubstE AtomSubstVal ReconstructAtom
