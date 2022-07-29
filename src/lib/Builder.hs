-- Copyright 2021 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Builder (
  emit, emitOp, emitUnOp,
  buildPureLam, BuilderT (..), Builder (..), ScopableBuilder (..),
  Builder2, BuilderM, ScopableBuilder2,
  liftBuilderT, buildBlock, withType, absToBlock, app, add, mul, sub, neg, div',
  iadd, imul, isub, idiv, ilt, ieq, irem,
  fpow, flog, fLitLike, buildPureNaryLam, emitMethod,
  select, getUnpacked, emitUnpacked,
  fromPair, getFst, getSnd, getProj, getProjRef, getNaryProjRef, naryApp,
  tabApp, naryTabApp,
  indexRef, naryIndexRef,
  ptrOffset, unsafePtrLoad,
  getClassDef, getDataCon,
  Emits, EmitsEvidence (..), buildPi, buildNonDepPi,
  buildLam, buildTabLam, buildLamGeneral,
  buildAbs, buildNaryAbs, buildNaryLam, buildNullaryLam, buildNaryLamExpr, asNaryLam,
  buildAlt, buildUnaryAlt, buildUnaryAtomAlt,
  buildNewtype,
  emitDataDef, emitClassDef, emitInstanceDef, emitDataConName, emitTyConName,
  buildCase, emitMaybeCase, buildSplitCase,
  emitBlock, emitDecls, BuilderEmissions, emitAtomToName,
  TopBuilder (..), TopBuilderT (..), liftTopBuilderTWith, runTopBuilderT, TopBuilder2,
  emitSourceMap, emitSynthCandidates, addInstanceSynthCandidate,
  emitTopLet, emitImpFunBinding, emitSpecialization, emitAtomRules,
  lookupLoadedModule, bindModule, getAllRequiredObjectFiles, extendCache,
  extendImpCache, queryImpCache,
  extendSpecializationCache, querySpecializationCache,
  extendObjCache, queryObjCache, getCache, emitObjFile,
  TopEnvFrag (..), emitPartialTopEnvFrag, emitLocalModuleEnv,
  fabricateEmitsEvidence, fabricateEmitsEvidenceM,
  singletonBinderNest, varsAsBinderNest, typesAsBinderNest,
  liftBuilder, liftEmitBuilder, makeBlock, absToBlockInferringTypes,
  ordinal, indexSetSize, unsafeFromOrdinal, projectIxFinMethod,
  litValToPointerlessAtom, emitPtrLit,
  telescopicCapture, unpackTelescope,
  applyRecon, applyReconAbs, clampPositive,
  emitRunWriter, mCombine, emitRunState, emitRunReader, buildFor, unzipTab, buildForAnn,
  zeroAt, zeroLike, maybeTangentType, tangentType,
  addTangent, updateAddAt, tangentBaseMonoidFor,
  buildEffLam, catMaybesE, runMaybeWhile,
  ReconAbs, ReconstructAtom (..), buildNullaryPi, buildNaryPi,
  HoistingTopBuilder (..), liftTopBuilderHoisted,
  DoubleBuilderT (..), DoubleBuilder, liftDoubleBuilderT, runDoubleBuilderT,
  ) where

import Control.Applicative
import Control.Monad
import Control.Monad.Reader
import Control.Monad.Writer.Strict hiding (Alt)
import Control.Monad.State.Strict (MonadState, StateT (..), runStateT)
import qualified Data.Set        as S
import qualified Data.Map.Strict as M
import Data.Foldable (toList)
import Data.Functor ((<&>))
import Data.Graph (graphFromEdges, topSort)
import Data.Text.Prettyprint.Doc (Pretty (..), group, line, nest)
import GHC.Stack

import qualified Unsafe.Coerce as TrulyUnsafe

import qualified RawName as R
import Name
import Syntax
import QueryType
import PPrint (prettyBlock)
import CheapReduction
import MTL1
import {-# SOURCE #-} Interpreter
import LabeledItems
import Util (enumerate, restructure, transitiveClosureM, bindM2, iota)
import Err
import Types.Core
import Core

-- === Ordinary (local) builder class ===

class (EnvReader m, EnvExtender m, Fallible1 m)
      => Builder (m::MonadKind1) where
  emitDecl :: Emits n => NameHint -> LetAnn -> Expr n -> m n (AtomName n)

class Builder m => ScopableBuilder (m::MonadKind1) where
  buildScoped
    :: SinkableE e
    => (forall l. (Emits l, DExt n l) => m l (e l))
    -> m n (Abs (Nest Decl) e n)

type Builder2 (m :: MonadKind2) = forall i. Builder (m i)
type ScopableBuilder2 (m :: MonadKind2) = forall i. ScopableBuilder (m i)

emit :: (Builder m, Emits n) => Expr n -> m n (AtomName n)
emit expr = emitDecl noHint PlainLet expr
{-# INLINE emit #-}

emitOp :: (Builder m, Emits n) => Op n -> m n (Atom n)
emitOp op = Var <$> emit (Op op)
{-# INLINE emitOp #-}

emitUnOp :: (Builder m, Emits n) => UnOp -> Atom n -> m n (Atom n)
emitUnOp op x = emitOp $ UnOp op x

emitBlock :: (Builder m, Emits n) => Block n -> m n (Atom n)
emitBlock (Block _ decls result) = emitDecls decls result

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

-- === "Hoisting" top-level builder class ===

-- `emitHoistedEnv` lets you emit top env fragments, like cache entries or
-- top-level function definitions, from within a local context. The operation
-- may fail, returning `Nothing`, because the emission might mention local
-- variables that can't be hoisted the top level.
class (EnvReader m, MonadFail1 m) => HoistingTopBuilder m where
  emitHoistedEnv :: (SinkableE e, SubstE Name e, HoistableE e)
                 => Abs TopEnvFrag e n -> m n (Maybe (e n))

liftTopBuilderHoisted
  :: (HoistingTopBuilder m, SubstE Name e, SinkableE e, HoistableE e)
  => (forall l. (Mut l, DExt n l) => TopBuilderM l (e l))
  -> m n (Maybe (e n))
liftTopBuilderHoisted cont = do
  env <- unsafeGetEnv
  Distinct <- getDistinct
  emitHoistedEnv $ runHardFail $ runTopBuilderT env $ localTopBuilder cont

newtype DoubleBuilderT (m::MonadKind) (n::S) (a:: *) =
  DoubleBuilderT { runDoubleBuilderT' :: DoubleInplaceT Env TopEnvFrag BuilderEmissions m n a }
  deriving ( Functor, Applicative, Monad, MonadFail, Fallible
           , CtxReader, ScopeReader, MonadIO, Catchable, MonadReader r)

type DoubleBuilder = DoubleBuilderT HardFailM

-- TODO: do we really need to play these rank-2 games here?
liftDoubleBuilderT
  :: (EnvReader m, Fallible m', SinkableE e, SubstE Name e)
  => (forall l. DExt n l => DoubleBuilderT m' l (e l))
  -> m n (m' (Abs TopEnvFrag e n))
liftDoubleBuilderT cont = do
  env <- unsafeGetEnv
  Distinct <- getDistinct
  return $ runDoubleBuilderT env cont

runDoubleBuilderT
  :: (Distinct n, Fallible m, SinkableE e, SubstE Name e)
  => Env n
  -> (forall l. DExt n l => DoubleBuilderT m l (e l))
  -> m (Abs TopEnvFrag e n)
runDoubleBuilderT env cont = do
  Abs envFrag (DoubleInplaceTResult REmpty e) <-
    runDoubleInplaceT env $ runDoubleBuilderT' cont
  return $ Abs envFrag e

instance Fallible m => HoistingTopBuilder (DoubleBuilderT m) where
  emitHoistedEnv ab = DoubleBuilderT $ emitDoubleInplaceTHoisted ab

instance Monad m => EnvReader (DoubleBuilderT m) where
  unsafeGetEnv = DoubleBuilderT $ liftDoubleInplaceT $ unsafeGetEnv

instance Fallible m => Builder (DoubleBuilderT m) where
  emitDecl hint ann e = DoubleBuilderT $ liftDoubleInplaceT $ runBuilderT' $ emitDecl hint ann e

instance Fallible m => ScopableBuilder (DoubleBuilderT m) where
  -- TODO: find a safe API for DoubleInplaceT sufficient to implement this
  buildScoped cont = DoubleBuilderT do
    (ans, decls) <- UnsafeMakeDoubleInplaceT $
      StateT \s@(topScope, _) -> do
        Abs rdecls (PairE e (LiftE topDecls)) <-
          locallyMutableInplaceT do
            (e, (_, topDecls)) <- flip runStateT (topScope, emptyOutFrag) $
               unsafeRunDoubleInplaceT $ runDoubleBuilderT' do
                 Emits <- fabricateEmitsEvidenceM
                 Distinct <- getDistinct
                 cont
            return $ PairE e $ LiftE topDecls
        return ((Abs (unRNest rdecls) e, topDecls), s)
    unsafeEmitDoubleInplaceTHoisted decls
    return ans
  {-# INLINE buildScoped #-}

instance Fallible m => EnvExtender (DoubleBuilderT m) where
  refreshAbs ab cont = DoubleBuilderT do
    (ans, decls) <- UnsafeMakeDoubleInplaceT do
      StateT \s@(topScope, _) -> do
        (ans, (_, decls)) <- refreshAbs ab \b e -> do
          flip runStateT (topScope, emptyOutFrag) $
            unsafeRunDoubleInplaceT $ runDoubleBuilderT' $ cont b e
        return ((ans, decls), s)
    unsafeEmitDoubleInplaceTHoisted decls
    return ans
  {-# INLINE refreshAbs #-}

instance (SinkableV v, HoistingTopBuilder m) => HoistingTopBuilder (SubstReaderT v m i) where
  emitHoistedEnv ab = SubstReaderT $ lift $ emitHoistedEnv ab

-- === Top-level builder class ===

class (EnvReader m, MonadFail1 m)
      => TopBuilder (m::MonadKind1) where
  -- `emitBinding` is expressible in terms of `emitEnv` but it can be
  -- implemented more efficiently by avoiding a double substitution
  -- XXX: emitBinding/emitEnv don't extend the synthesis candidates
  emitBinding :: Mut n => Color c => NameHint -> Binding c n -> m n (Name c n)
  emitEnv :: (Mut n, SinkableE e, SubstE Name e) => Abs TopEnvFrag e n -> m n (e n)
  emitNamelessEnv :: TopEnvFrag n n -> m n ()
  localTopBuilder :: SinkableE e
                  => (forall l. (Mut l, DExt n l) => m l (e l))
                  -> m n (Abs TopEnvFrag e n)

emitPartialTopEnvFrag :: TopBuilder m => PartialTopEnvFrag n -> m n ()
emitPartialTopEnvFrag frag = emitNamelessEnv $ TopEnvFrag emptyOutFrag frag

emitLocalModuleEnv :: TopBuilder m => ModuleEnv n -> m n ()
emitLocalModuleEnv env = emitPartialTopEnvFrag $ mempty { fragLocalModuleEnv = env }

emitSourceMap :: TopBuilder m => SourceMap n -> m n ()
emitSourceMap sm = emitLocalModuleEnv $ mempty {envSourceMap = sm}

emitSynthCandidates :: TopBuilder m => SynthCandidates n -> m n ()
emitSynthCandidates sc = emitLocalModuleEnv $ mempty {envSynthCandidates = sc}

addInstanceSynthCandidate :: TopBuilder m => ClassName n -> InstanceName n -> m n ()
addInstanceSynthCandidate className instanceName =
  emitSynthCandidates $ SynthCandidates [] (M.singleton className [instanceName])

emitAtomRules :: TopBuilder m => AtomName n -> AtomRules n -> m n ()
emitAtomRules v rules = emitNamelessEnv $
  TopEnvFrag emptyOutFrag $ mempty { fragCustomRules = CustomRules $ M.singleton v rules }

emitTopLet :: (Mut n, TopBuilder m) => NameHint -> LetAnn -> Expr n -> m n (AtomName n)
emitTopLet hint letAnn expr = do
  ty <- getType expr
  emitBinding hint $ AtomNameBinding $ LetBound  (DeclBinding letAnn ty expr)

emitImpFunBinding :: (Mut n, TopBuilder m) => NameHint -> ImpFunction n -> m n (ImpFunName n)
emitImpFunBinding hint f = emitBinding hint $ ImpFunBinding f

emitSpecialization
  :: (Mut n, TopBuilder m)
  => SpecializationSpec n -> m n (AtomName n)
emitSpecialization s = do
  let hint = getNameHint s
  specializedTy <- specializedFunType s
  let binding = TopFunBound specializedTy $ SpecializedTopFun s
  name <- emitBinding hint $ toBinding binding
  extendSpecializationCache s name
  return name

bindModule :: (Mut n, TopBuilder m) => ModuleSourceName -> ModuleName n -> m n ()
bindModule sourceName internalName = do
  let loaded = LoadedModules $ M.singleton sourceName internalName
  emitPartialTopEnvFrag $ mempty {fragLoadedModules = loaded}

getAllRequiredObjectFiles :: EnvReader m => m n [ObjectFileName n]
getAllRequiredObjectFiles = do
  env <- withEnv moduleEnv
  ObjectFiles objs <- return $ envObjectFiles env
  return $ S.toList objs

lookupLoadedModule:: EnvReader m => ModuleSourceName -> m n (Maybe (ModuleName n))
lookupLoadedModule name = do
  loadedModules <- withEnv $ envLoadedModules . topEnv
  return $ M.lookup name $ fromLoadedModules loadedModules

extendCache :: TopBuilder m => Cache n -> m n ()
extendCache cache = emitPartialTopEnvFrag $ mempty {fragCache = cache}

extendImpCache :: TopBuilder m => AtomName n -> ImpFunName n -> m n ()
extendImpCache fSimp fImp =
  extendCache $ mempty { impCache = eMapSingleton fSimp fImp }

queryImpCache :: EnvReader m => AtomName n -> m n (Maybe (ImpFunName n))
queryImpCache v = do
  cache <- impCache <$> getCache
  return $ lookupEMap cache v

extendSpecializationCache :: TopBuilder m => SpecializationSpec n -> AtomName n -> m n ()
extendSpecializationCache specialization f =
  extendCache $ mempty { specializationCache = eMapSingleton specialization f }

querySpecializationCache :: EnvReader m => SpecializationSpec n -> m n (Maybe (AtomName n))
querySpecializationCache specialization = do
  cache <- specializationCache <$> getCache
  return $ lookupEMap cache specialization

extendObjCache :: (Mut n, TopBuilder m) => ImpFunName n -> CFun n -> m n ()
extendObjCache fImp cfun =
  extendCache $ mempty { objCache = eMapSingleton fImp cfun }

emitObjFile :: (Mut n, TopBuilder m) => NameHint -> ObjectFile n -> m n (ObjectFileName n)
emitObjFile hint objFile = do
  v <- emitBinding hint $ ObjectFileBinding objFile
  emitLocalModuleEnv $ mempty {envObjectFiles = ObjectFiles $ S.singleton v}
  return v

queryObjCache :: EnvReader m => ImpFunName n -> m n (Maybe (CFun n))
queryObjCache v = do
  cache <- objCache <$> getCache
  return $ lookupEMap cache v

getCache :: EnvReader m => m n (Cache n)
getCache = withEnv $ envCache . topEnv

newtype TopBuilderT (m::MonadKind) (n::S) (a:: *) =
  TopBuilderT { runTopBuilderT' :: InplaceT Env TopEnvFrag m n a }
  deriving ( Functor, Applicative, Monad, MonadFail, Fallible
           , CtxReader, ScopeReader, MonadTrans1, MonadReader r
           , MonadWriter w, MonadState s, MonadIO, Catchable)

type TopBuilderM = TopBuilderT HardFailM

-- We use this to implement things that look like `local` from `MonadReader`.
-- Does it make sense to but it in a transformer-like class, like we do with
-- `lift11`?
liftTopBuilderTWith :: Monad m => (forall a'. m a' -> m a')
                    -> TopBuilderT m n a -> TopBuilderT m n a
liftTopBuilderTWith modifyInner cont = TopBuilderT $
  liftBetweenInplaceTs modifyInner id id (runTopBuilderT' cont)

instance Fallible m => EnvReader (TopBuilderT m) where
  unsafeGetEnv = TopBuilderT $ getOutMapInplaceT
  {-# INLINE unsafeGetEnv #-}

instance Fallible m => TopBuilder (TopBuilderT m) where
  emitBinding hint binding = do
    Abs b v <- freshNameM hint
    let ab = Abs (b:>binding) v
    ab' <- liftEnvReaderM $ refreshAbs ab \b' v' -> do
      let envFrag = toEnvFrag b'
      let scs = bindingsFragToSynthCandidates envFrag
      let topFrag = TopEnvFrag envFrag $
            mempty { fragLocalModuleEnv = mempty { envSynthCandidates = scs} }
      return $ Abs topFrag v'
    TopBuilderT $ extendInplaceT ab'

  emitEnv ab = TopBuilderT $ extendInplaceT ab
  {-# INLINE emitEnv #-}

  emitNamelessEnv bs = TopBuilderT $ extendTrivialInplaceT bs
  {-# INLINE emitNamelessEnv #-}

  localTopBuilder cont = TopBuilderT $
    locallyMutableInplaceT $ runTopBuilderT' cont
  {-# INLINE localTopBuilder #-}

instance (SinkableV v, TopBuilder m) => TopBuilder (SubstReaderT v m i) where
  emitBinding hint binding = SubstReaderT $ lift $ emitBinding hint binding
  {-# INLINE emitBinding #-}
  emitEnv ab = SubstReaderT $ lift $ emitEnv ab
  {-# INLINE emitEnv #-}
  emitNamelessEnv bs = SubstReaderT $ lift $ emitNamelessEnv bs
  {-# INLINE emitNamelessEnv #-}
  localTopBuilder cont = SubstReaderT $ ReaderT \env -> do
    localTopBuilder do
      Distinct <- getDistinct
      runReaderT (runSubstReaderT' cont) (sink env)
  {-# INLINE localTopBuilder #-}

runTopBuilderT
  :: (Fallible m, Distinct n)
  => Env n
  -> TopBuilderT m n a
  -> m a
runTopBuilderT bindings cont = do
  liftM snd $ runInplaceT bindings $ runTopBuilderT' $ cont
{-# INLINE runTopBuilderT #-}

type TopBuilder2 (m :: MonadKind2) = forall i. TopBuilder (m i)

instance (SinkableE e, HoistableState e, TopBuilder m) => TopBuilder (StateT1 e m) where
  emitBinding hint binding = lift11 $ emitBinding hint binding
  {-# INLINE emitBinding #-}
  emitEnv ab = lift11 $ emitEnv ab
  {-# INLINE emitEnv #-}
  emitNamelessEnv frag = lift11 $ emitNamelessEnv frag
  {-# INLINE emitNamelessEnv #-}
  localTopBuilder _ = error "not implemented"

-- === BuilderT ===

type BuilderEmissions = RNest Decl

newtype BuilderT (m::MonadKind) (n::S) (a:: *) =
  BuilderT { runBuilderT' :: InplaceT Env BuilderEmissions m n a }
  deriving ( Functor, Applicative, Monad, MonadTrans1, MonadFail, Fallible
           , CtxReader, ScopeReader, Alternative, Searcher
           , MonadWriter w, MonadReader r)

type BuilderM = BuilderT HardFailM

liftBuilderT :: (Fallible m, EnvReader m') => BuilderT m n a -> m' n (m a)
liftBuilderT cont = do
  env <- unsafeGetEnv
  Distinct <- getDistinct
  return do
    (REmpty, result) <- runInplaceT env $ runBuilderT' cont
    return result
{-# INLINE liftBuilderT #-}

liftBuilder :: EnvReader m => BuilderM n a -> m n a
liftBuilder cont = liftM runHardFail $ liftBuilderT cont
{-# INLINE liftBuilder #-}

-- TODO: This should not fabricate Emits evidence!!
-- XXX: this uses unsafe functions in its implementations. It should be safe to
-- use, but be careful changing it.
liftEmitBuilder :: (Builder m, SinkableE e, SubstE Name e)
                => BuilderM n (e n) -> m n (e n)
liftEmitBuilder cont = do
  env <- unsafeGetEnv
  Distinct <- getDistinct
  let (result, decls, _) = runHardFail $ unsafeRunInplaceT (runBuilderT' cont) env emptyOutFrag
  Emits <- fabricateEmitsEvidenceM
  emitDecls (unsafeCoerceB $ unRNest decls) result

instance Fallible m => ScopableBuilder (BuilderT m) where
  buildScoped cont = BuilderT do
    Abs rdecls e <- locallyMutableInplaceT $
      runBuilderT' do
        Emits <- fabricateEmitsEvidenceM
        Distinct <- getDistinct
        cont
    return $ Abs (unRNest rdecls) e
  {-# INLINE buildScoped #-}

newtype BuilderDeclEmission (n::S) (l::S) = BuilderDeclEmission (Decl n l)
instance ExtOutMap Env BuilderDeclEmission where
  extendOutMap env (BuilderDeclEmission d) = env `extendOutMap` toEnvFrag d
  {-# INLINE extendOutMap #-}
instance ExtOutFrag BuilderEmissions BuilderDeclEmission where
  extendOutFrag rn (BuilderDeclEmission d) = RNest rn d
  {-# INLINE extendOutFrag #-}

instance Fallible m => Builder (BuilderT m) where
  emitDecl hint ann expr = do
    ty <- getType expr
    BuilderT $ freshExtendSubInplaceT hint \b ->
      (BuilderDeclEmission $ Let b $ DeclBinding ann ty expr, binderName b)
  {-# INLINE emitDecl #-}

instance Fallible m => EnvReader (BuilderT m) where
  unsafeGetEnv = BuilderT $ getOutMapInplaceT
  {-# INLINE unsafeGetEnv #-}

instance Fallible m => EnvExtender (BuilderT m) where
  refreshAbs ab cont = BuilderT $ refreshAbs ab \b e -> runBuilderT' $ cont b e
  {-# INLINE refreshAbs #-}

instance (SinkableV v, ScopableBuilder m) => ScopableBuilder (SubstReaderT v m i) where
  buildScoped cont = SubstReaderT $ ReaderT \env ->
    buildScoped $
      runReaderT (runSubstReaderT' cont) (sink env)
  {-# INLINE buildScoped #-}

instance (SinkableV v, Builder m) => Builder (SubstReaderT v m i) where
  emitDecl hint ann expr = SubstReaderT $ lift $ emitDecl hint ann expr
  {-# INLINE emitDecl #-}

instance (SinkableE e, ScopableBuilder m) => ScopableBuilder (OutReaderT e m) where
  buildScoped cont = OutReaderT $ ReaderT \env ->
    buildScoped do
      env' <- sinkM env
      runReaderT (runOutReaderT' cont) env'
  {-# INLINE buildScoped #-}

instance (SinkableE e, Builder m) => Builder (OutReaderT e m) where
  emitDecl hint ann expr =
    OutReaderT $ lift $ emitDecl hint ann expr
  {-# INLINE emitDecl #-}

instance (SinkableE e, ScopableBuilder m) => ScopableBuilder (ReaderT1 e m) where
  buildScoped cont = ReaderT1 $ ReaderT \env ->
    buildScoped do
      env' <- sinkM env
      runReaderT (runReaderT1' cont) env'
  {-# INLINE buildScoped #-}

instance (SinkableE e, Builder m) => Builder (ReaderT1 e m) where
  emitDecl hint ann expr =
    ReaderT1 $ lift $ emitDecl hint ann expr
  {-# INLINE emitDecl #-}

instance (SinkableE e, HoistableState e, Builder m) => Builder (StateT1 e m) where
  emitDecl hint ann expr = lift11 $ emitDecl hint ann expr
  {-# INLINE emitDecl #-}

instance (SinkableE e, HoistableState e, ScopableBuilder m) => ScopableBuilder (StateT1 e m) where
  buildScoped cont = StateT1 \s -> do
    Abs decls (e `PairE` s') <- buildScoped $ liftM toPairE $ runStateT1 cont =<< sinkM s
    let s'' = hoistState s decls s'
    return (Abs decls e, s'')
  {-# INLINE buildScoped #-}

instance Builder m => Builder (MaybeT1 m) where
  emitDecl hint ann expr = lift11 $ emitDecl hint ann expr
  {-# INLINE emitDecl #-}

-- === Emits predicate ===

-- We use the `Emits` predicate on scope parameters to indicate that we may emit
-- decls. This lets us ensure that a computation *doesn't* emit decls, by
-- supplying a fresh name without supplying the `Emits` predicate.

class Mut n => Emits (n::S)
data EmitsEvidence (n::S) where
  Emits :: Emits n => EmitsEvidence n
instance Emits UnsafeS

fabricateEmitsEvidence :: forall n. EmitsEvidence n
fabricateEmitsEvidence = withFabricatedEmits @n Emits
{-# INLINE fabricateEmitsEvidence #-}

fabricateEmitsEvidenceM :: forall m n. Monad1 m => m n (EmitsEvidence n)
fabricateEmitsEvidenceM = return fabricateEmitsEvidence
{-# INLINE fabricateEmitsEvidenceM #-}

withFabricatedEmits :: forall n a. (Emits n => a) -> a
withFabricatedEmits cont = fromWrapWithEmits
 ( TrulyUnsafe.unsafeCoerce ( WrapWithEmits cont :: WrapWithEmits n       a
                                               ) :: WrapWithEmits UnsafeS a)
{-# INLINE withFabricatedEmits #-}

newtype WrapWithEmits n r =
  WrapWithEmits { fromWrapWithEmits :: Emits n => r }

-- === lambda-like things ===

buildBlock
  :: ScopableBuilder m
  => (forall l. (Emits l, DExt n l) => m l (Atom l))
  -> m n (Block n)
buildBlock cont = buildScoped (cont >>= withType) >>= computeAbsEffects >>= absToBlock

withType :: (EnvReader m, HasType e) => e l -> m l ((e `PairE` Type) l)
withType e = do
  ty <- {-# SCC blockTypeNormalization #-} cheapNormalize =<< getType e
  return $ e `PairE` ty
{-# INLINE withType #-}

makeBlock :: Nest Decl n l -> EffectRow l -> Atom l -> Type l -> Block n
makeBlock decls effs atom ty = Block (BlockAnn ty' effs') decls atom where
  ty' = ignoreHoistFailure $ hoist decls ty
  effs' = ignoreHoistFailure $ hoist decls effs
{-# INLINE makeBlock #-}

absToBlockInferringTypes :: EnvReader m => Abs (Nest Decl) Atom n -> m n (Block n)
absToBlockInferringTypes ab = liftEnvReaderM do
  abWithEffs <-  computeAbsEffects ab
  refreshAbs abWithEffs \decls (effs `PairE` result) -> do
    ty <- cheapNormalize =<< getType result
    return $ ignoreExcept $
      absToBlock $ Abs decls (effs `PairE` (result `PairE` ty))
{-# INLINE absToBlockInferringTypes #-}

absToBlock :: (Fallible m) => Abs (Nest Decl) (EffectRow `PairE` (Atom `PairE` Type)) n -> m (Block n)
absToBlock (Abs decls (effs `PairE` (result `PairE` ty))) = do
  let msg = "Block:" <> nest 1 (prettyBlock decls result) <> line
            <> group ("Of type:" <> nest 2 (line <> pretty ty)) <> line
            <> group ("With effects:" <> nest 2 (line <> pretty effs))
  ty' <- liftHoistExcept' (docAsStr msg) $ hoist decls ty
  effs' <- liftHoistExcept' (docAsStr msg) $ hoist decls effs
  return $ Block (BlockAnn ty' effs') decls result
{-# INLINE absToBlock #-}

buildPureLam :: ScopableBuilder m
             => NameHint -> Arrow -> Type n
             -> (forall l. (Emits l, DExt n l) => AtomName l -> m l (Atom l))
             -> m n (Atom n)
buildPureLam hint arr ty body = do
  buildLamGeneral hint arr ty (const $ return Pure) \v -> do
    Distinct <- getDistinct
    body v

buildTabLam
  :: ScopableBuilder m
  => NameHint -> IxType n
  -> (forall l. (Emits l, DExt n l) => AtomName l -> m l (Atom l))
  -> m n (Atom n)
buildTabLam hint ty fBody = do
  withFreshBinder hint ty \b -> do
    let v = binderName b
    body <- withAllowedEffects Pure $ buildBlock $ fBody $ sink v
    return $ TabLam $ TabLamExpr (b:>ty) body

buildLam
  :: ScopableBuilder m
  => NameHint -> Arrow -> Type n -> EffectRow n
  -> (forall l. (Emits l, DExt n l) => AtomName l -> m l (Atom l))
  -> m n (Atom n)
buildLam hint arr ty eff body = buildLamGeneral hint arr ty (const $ sinkM eff) body

buildNullaryLam :: ScopableBuilder m
                => EffectRow n
                -> (forall l. (Emits l, DExt n l) => m l (Atom l))
                -> m n (Atom n)
buildNullaryLam effs cont = buildLam noHint PlainArrow UnitTy effs \_ -> cont

buildNullaryPi :: Builder m
               => EffectRow n
               -> (forall l. DExt n l => m l (Type l))
               -> m n (Type n)
buildNullaryPi effs cont =
  Pi <$> buildPi noHint PlainArrow UnitTy \_ -> do
    resultTy <- cont
    return (sink effs, resultTy)

buildLamGeneral
  :: ScopableBuilder m
  => NameHint -> Arrow -> Type n
  -> (forall l.           DExt n l  => AtomName l -> m l (EffectRow l))
  -> (forall l. (Emits l, DExt n l) => AtomName l -> m l (Atom l))
  -> m n (Atom n)
buildLamGeneral hint arr ty fEff fBody = do
  withFreshBinder hint (LamBinding arr ty) \b -> do
    let v = binderName b
    effs <- fEff v
    body <- withAllowedEffects effs $ buildBlock $ fBody $ sink v
    return $ Lam $ LamExpr (LamBinder b ty arr effs) body

-- Body must be an Atom because otherwise the nullary case would require
-- emitting decls into the enclosing scope.
buildPureNaryLam :: ScopableBuilder m
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
buildPi hint arr ty body = do
  withFreshPiBinder hint (PiBinding arr ty) \b -> do
    (effs, resultTy) <- body $ binderName b
    return $ PiType b effs resultTy

buildNaryPi
  :: Builder m
  => EmptyAbs (Nest Binder) n
  -> (forall l. (Distinct l, DExt n l) => [AtomName l] -> m l (Type l))
  -> m n (Type n)
buildNaryPi (Abs Empty UnitE) cont = do
  Distinct <- getDistinct
  cont []
buildNaryPi (Abs (Nest (b:>ty) bs) UnitE) cont = do
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
     , SinkableE e, Color c, ToBinding binding c)
  => NameHint
  -> binding n
  -> (forall l. DExt n l => Name c l -> m l (e l))
  -> m n (Abs (BinderP c binding) e n)
buildAbs hint binding cont = do
  withFreshBinder hint binding \b -> do
    body <- cont $ binderName b
    return $ Abs (b:>binding) body

varsAsBinderNest :: EnvReader m => [AtomName n] -> m n (EmptyAbs (Nest Binder) n)
varsAsBinderNest [] = return $ EmptyAbs Empty
varsAsBinderNest (v:vs) = do
  rest <- varsAsBinderNest vs
  ty <- getType v
  Abs b (Abs bs UnitE) <- return $ abstractFreeVar v rest
  return $ EmptyAbs (Nest (b:>ty) bs)

typesAsBinderNest :: EnvReader m => [Type n] -> m n (EmptyAbs (Nest Binder) n)
typesAsBinderNest types = liftEnvReaderM $ go types
  where
    go :: forall n. [Type n] -> EnvReaderM n (EmptyAbs (Nest Binder) n)
    go tys = case tys of
      [] -> return $ Abs Empty UnitE
      ty:rest -> withFreshBinder noHint ty \b -> do
        Abs bs UnitE <- go $ map sink rest
        return $ Abs (Nest (b:>ty) bs) UnitE

singletonBinderNest
  :: EnvReader m
  => NameHint -> ann n
  -> m n (EmptyAbs (Nest (BinderP AtomNameC ann)) n)
singletonBinderNest hint ann = do
  Abs b _ <- return $ newName hint
  return $ EmptyAbs (Nest (b:>ann) Empty)

buildNaryAbs
  :: ( ScopableBuilder m, SinkableE e, SubstE Name e, SubstE AtomSubstVal e, HoistableE e
     , BindsOneAtomName b, BindsEnv b, SubstB Name b)
  => EmptyAbs (Nest b) n
  -> (forall l. DExt n l => [AtomName l] -> m l (e l))
  -> m n (Abs (Nest b) e n)
buildNaryAbs (Abs n UnitE) body = do
  a <- liftBuilder $ buildNaryAbsRec [] n
  refreshAbs a \freshNest (ListE freshNames) ->
    Abs freshNest <$> body freshNames
{-# INLINE buildNaryAbs #-}

buildNaryAbsRec
  :: (BindsOneAtomName b, BindsEnv b, SubstB Name b)
  => [AtomName n] -> Nest b n l -> BuilderM n (Abs (Nest b) (ListE AtomName) n)
buildNaryAbsRec ns x = confuseGHC >>= \_ -> case x of
  Empty -> return $ Abs Empty $ ListE $ reverse ns
  Nest b bs -> do
    refreshAbs (Abs b (EmptyAbs bs)) \b' (EmptyAbs bs') -> do
      Abs bs'' ns'' <- buildNaryAbsRec (binderName b' : sinkList ns) bs'
      return $ Abs (Nest b' bs'') ns''

-- TODO: probably deprectate this version in favor of `buildNaryLamExpr`
buildNaryLam
  :: (ScopableBuilder m, Emits n)
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
    naryAbsToNaryLam (Abs binders block) = case binders of
      Empty -> block
      Nest (b:>ty) bs ->
        AtomicBlock $ Lam $ LamExpr (LamBinder b ty PlainArrow Pure) $
          naryAbsToNaryLam $ Abs bs block

asNaryLam :: EnvReader m => NaryPiType n -> Atom n -> m n (NaryLamExpr n)
asNaryLam ty f = liftBuilder do
  buildNaryLamExpr ty \xs ->
    naryApp (sink f) (map Var $ toList xs)

buildNaryLamExpr
  :: ScopableBuilder m
  => NaryPiType n
  -> (forall l. (Emits l, Distinct l, DExt n l) => NonEmpty (AtomName l) -> m l (Atom l))
  -> m n (NaryLamExpr n)
buildNaryLamExpr (NaryPiType (NonEmptyNest b bs) eff resultTy) cont =
  case bs of
    Empty -> do
      Abs b' (PairE eff' body') <- buildAbs (getNameHint b) (binderType b) \v -> do
        eff' <- applySubst (b@>v) eff
        result <- withAllowedEffects eff' $ buildBlock $ cont $ (sink v) :| []
        return $ PairE eff' result
      return $ NaryLamExpr (NonEmptyNest b' Empty) eff' body'
    Nest bnext rest -> do
      Abs b' lamExpr <- buildAbs (getNameHint b) (binderType b) \v -> do
        piTy' <- applySubst (b@>v) $ NaryPiType (NonEmptyNest bnext rest) eff resultTy
        buildNaryLamExpr piTy' \(v':|vs) -> cont $ sink v :| (v':vs)
      NaryLamExpr (NonEmptyNest bnext' rest') eff' body' <- return $ lamExpr
      return $ NaryLamExpr (NonEmptyNest b' (Nest bnext' rest')) eff' body'

buildAlt
  :: ScopableBuilder m
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
  :: ScopableBuilder m
  => Type n
  -> (forall l. (Emits l, DExt n l) => AtomName l -> m l (Atom l))
  -> m n (Alt n)
buildUnaryAlt ty body = do
  bs <- singletonBinderNest noHint ty
  buildAlt bs \[v] -> body v

buildUnaryAtomAlt
  :: ScopableBuilder m
  => Type n
  -> (forall l. (Distinct l, DExt n l) => AtomName l -> m l (Atom l))
  -> m n (AltP Atom n)
buildUnaryAtomAlt ty body = do
  bs <- singletonBinderNest noHint ty
  buildNaryAbs bs \[v] -> do
    Distinct <- getDistinct
    body v

buildNewtype :: ScopableBuilder m
             => SourceName
             -> EmptyAbs (Nest Binder) n
             -> (forall l. DExt n l => [AtomName l] -> m l (Type l))
             -> m n (DataDef n)
buildNewtype name paramBs body = do
  Abs paramBs' argBs <- buildNaryAbs paramBs \params -> do
    ty <- body params
    singletonBinderNest noHint ty
  return $ DataDef name (DataDefBinders paramBs' Empty) [DataConDef ("mk" <> name) argBs]

-- TODO: consider a version with nonempty list of alternatives where we figure
-- out the result type from one of the alts rather than providing it explicitly
buildCase :: (Emits n, ScopableBuilder m)
          => Atom n -> Type n
          -> (forall l. (Emits l, DExt n l) => Int -> [Atom l] -> m l (Atom l))
          -> m n (Atom n)
buildCase scrut resultTy indexedAltBody = do
  case trySelectBranch scrut of
    Just (i, args) -> do
      Distinct <- getDistinct
      indexedAltBody i (map sink args)
    Nothing -> do
      scrutTy <- getType scrut
      altsBinderTys <- caseAltsBinderTys scrutTy
      (alts, effs) <- unzip <$> forM (enumerate altsBinderTys) \(i, bs) -> do
        (Abs bs' (body `PairE` eff')) <- buildNaryAbs bs \xs -> do
          blk <- buildBlock do
            ListE xs' <- sinkM $ ListE xs
            indexedAltBody i (Var <$> xs')
          eff <- getEffects blk
          return $ blk `PairE` eff
        return (Abs bs' body, ignoreHoistFailure $ hoist bs' eff')
      liftM Var $ emit $ Case scrut alts resultTy $ mconcat effs

buildSplitCase :: (Emits n, ScopableBuilder m)
               => LabeledItems (Type n) -> Atom n -> Type n
               -> (forall l. (Emits l, DExt n l) => Atom l -> m l (Atom l))
               -> (forall l. (Emits l, DExt n l) => Atom l -> m l (Atom l))
               -> m n (Atom n)
buildSplitCase tys scrut resultTy match fallback = do
  split <- emitOp $ VariantSplit tys scrut
  buildCase split resultTy \i [v] ->
    case i of
      0 -> match v
      1 -> fallback v
      _ -> error "should only have two cases"

buildEffLam
  :: ScopableBuilder m
  => RWS -> NameHint -> Type n
  -> (forall l. (Emits l, DExt n l) => AtomName l -> AtomName l -> m l (Atom l))
  -> m n (Atom n)
buildEffLam rws hint ty body = do
  eff <- getAllowedEffects
  buildLam noHint PlainArrow TyKind Pure \h -> do
    let ty' = RefTy (Var h) (sink ty)
    withFreshBinder hint (LamBinding PlainArrow ty') \b -> do
      let ref = binderName b
      h' <- sinkM h
      let eff' = extendEffect (RWSEffect rws (Just h')) (sink eff)
      body' <- withAllowedEffects eff' $ buildBlock $ body (sink h) $ sink ref
      -- Contract the type of the produced function to only mention
      -- the effects actually demanded by the body.  This is safe because
      -- it's immediately consumed by an effect discharge primitive.
      effs <- getEffects body'
      return $ Lam $ LamExpr (LamBinder b ty' PlainArrow effs) body'

buildForAnn
  :: (Emits n, ScopableBuilder m)
  => NameHint -> ForAnn -> IxType n
  -> (forall l. (Emits l, DExt n l) => AtomName l -> m l (Atom l))
  -> m n (Atom n)
buildForAnn hint ann ixTy@(IxType iTy ixDict) body = do
  lam <- withFreshBinder hint ixTy \b -> do
    let v = binderName b
    body' <- buildBlock $ body $ sink v
    effs <- getEffects body'
    return $ Lam $ LamExpr (LamBinder b iTy PlainArrow effs) body'
  liftM Var $ emit $ Hof $ For ann ixDict lam

buildFor :: (Emits n, ScopableBuilder m)
         => NameHint -> Direction -> IxType n
         -> (forall l. (Emits l, DExt n l) => AtomName l -> m l (Atom l))
         -> m n (Atom n)
buildFor hint dir ty body = buildForAnn hint dir ty body

unzipTab :: (Emits n, Builder m) => Atom n -> m n (Atom n, Atom n)
unzipTab tab = do
  TabTy (_:>ixTy) _ <- getType tab
  fsts <- liftEmitBuilder $ buildTabLam noHint ixTy \i ->
            liftM fst $ tabApp (sink tab) (Var i) >>= fromPair
  snds <- liftEmitBuilder $ buildTabLam noHint ixTy \i ->
            liftM snd $ tabApp (sink tab) (Var i) >>= fromPair
  return (fsts, snds)

emitRunWriter
  :: (Emits n, ScopableBuilder m)
  => NameHint -> Type n -> BaseMonoid n
  -> (forall l. (Emits l, DExt n l) => AtomName l -> AtomName l -> m l (Atom l))
  -> m n (Atom n)
emitRunWriter hint accTy bm body = do
  lam <- buildEffLam Writer hint accTy \h ref -> body h ref
  liftM Var $ emit $ Hof $ RunWriter bm lam

mCombine :: (Emits n, Builder m) => Atom n -> Atom n -> Atom n -> m n (Atom n)
mCombine monoidDict x y = do
  method <- projMethod "mcombine" monoidDict
  naryApp method [x, y]

emitRunState
  :: (Emits n, ScopableBuilder m)
  => NameHint -> Atom n
  -> (forall l. (Emits l, DExt n l) => AtomName l -> AtomName l -> m l (Atom l))
  -> m n (Atom n)
emitRunState hint initVal body = do
  stateTy <- getType initVal
  lam <- buildEffLam State hint stateTy \h ref -> body h ref
  liftM Var $ emit $ Hof $ RunState initVal lam

emitRunReader
  :: (Emits n, ScopableBuilder m)
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
  StaticRecordTy tys -> Record <$> mapM zeroAt tys
  TabTy (b:>ixTy) bodyTy ->
    liftEmitBuilder $ buildTabLam (getNameHint b) ixTy \i ->
      zeroAt =<< applySubst (b@>i) bodyTy
  _ -> unreachable
  where
    unreachable :: a
    unreachable = error $ "Missing zero case for a tangent type: " ++ pprint ty
    zeroLit bt = case bt of
      Scalar Float64Type -> Float64Lit 0.0
      Scalar Float32Type -> Float32Lit 0.0
      _                  -> unreachable

zeroLike :: (HasCallStack, HasType e, Builder m) => e n -> m n (Atom n )
zeroLike x = zeroAt =<< getType x

tangentType :: EnvReader m => Type n -> m n (Type n)
tangentType ty = maybeTangentType ty >>= \case
  Just tanTy -> return tanTy
  Nothing -> error $ "can't differentiate wrt type: " ++ pprint ty

maybeTangentType :: EnvReader m => Type n -> m n (Maybe (Type n))
maybeTangentType ty = liftEnvReaderT $ maybeTangentType' ty

maybeTangentType' :: Type n -> EnvReaderT Maybe n (Type n)
maybeTangentType' ty = case ty of
  StaticRecordTy items -> StaticRecordTy <$> mapM rec items
  TypeCon _ _ _ -> rec =<< fromNewtypeWrapper ty
  TabTy b bodyTy -> do
    refreshAbs (Abs b bodyTy) \b' bodyTy' -> do
      bodyTanTy <- rec bodyTy'
      return $ TabTy b' bodyTanTy
  TC con    -> case con of
    BaseType (Scalar Float64Type) -> return $ TC con
    BaseType (Scalar Float32Type) -> return $ TC con
    BaseType   _                  -> return $ UnitTy
    Fin _                         -> return $ UnitTy
    ProdType   tys                -> ProdTy <$> traverse rec tys
    _ -> empty
  _ -> empty
  where rec = maybeTangentType'

fromNewtypeWrapper :: (EnvReader m, Fallible1 m) => Type n -> m n (Type n)
fromNewtypeWrapper ty = do
  TypeCon _ defName params <- return ty
  def <- lookupDataDef defName
  [con] <- instantiateDataDef def params
  DataConDef _ (EmptyAbs (Nest (_:>wrappedTy) Empty)) <- return con
  return wrappedTy

tangentBaseMonoidFor :: Builder m => Type n -> m n (BaseMonoid n)
tangentBaseMonoidFor ty = do
  zero <- zeroAt ty
  adder <- liftEmitBuilder $ buildLam noHint PlainArrow ty Pure \v -> updateAddAt $ Var v
  return $ BaseMonoid zero adder

addTangent :: (Emits n, Builder m) => Atom n -> Atom n -> m n (Atom n)
addTangent x y = do
  getType x >>= \case
    StaticRecordTy tys -> do
      elems <- bindM2 (zipWithM addTangent) (getUnpacked x) (getUnpacked y)
      return $ Record $ restructure elems tys
    TabTy (b:>ixTy) _  ->
      liftEmitBuilder $ buildFor (getNameHint b) Fwd ixTy \i -> do
        bindM2 addTangent (tabApp (sink x) (Var i)) (tabApp (sink y) (Var i))
    TC con -> case con of
      BaseType (Scalar _) -> emitOp $ BinOp FAdd x y
      ProdType _          -> do
        xs <- getUnpacked x
        ys <- getUnpacked y
        ProdVal <$> zipWithM addTangent xs ys
      ty -> notTangent ty
    ty -> notTangent ty
    where notTangent ty = error $ "Not a tangent type: " ++ pprint ty

updateAddAt :: (Emits n, Builder m) => Atom n -> m n (Atom n)
updateAddAt x = liftEmitBuilder do
  ty <- getType x
  buildLam noHint PlainArrow ty Pure \v -> addTangent (sink x) (Var v)

-- === builder versions of common top-level emissions ===

litValToPointerlessAtom :: (Mut n, TopBuilder m) => LitVal -> m n (Atom n)
litValToPointerlessAtom litval = case litval of
  PtrLit val -> Var <$> emitPtrLit (getNameHint @String "ptr") val
  _          -> return $ Con $ Lit litval

emitPtrLit :: (Mut n, TopBuilder m) => NameHint -> PtrLitVal -> m n (AtomName n)
emitPtrLit hint p@(PtrLitVal ty _) = do
  ptrName <- emitBinding hint $ PtrBinding p
  emitBinding hint $ AtomNameBinding $ PtrLitBound ty ptrName
emitPtrLit _ (PtrSnapshot _ _) = error "only used for serialization"

emitDataDef :: (Mut n, TopBuilder m) => DataDef n -> m n (DataDefName n)
emitDataDef dataDef@(DataDef sourceName _ _) =
  emitBinding hint $ DataDefBinding dataDef
  where hint = getNameHint sourceName

emitClassDef :: (Mut n, TopBuilder m) => ClassDef n -> m n (Name ClassNameC n)
emitClassDef classDef@(ClassDef name _ _ _ _) =
  emitBinding (getNameHint name) $ ClassBinding classDef

emitInstanceDef :: (Mut n, TopBuilder m) => InstanceDef n -> m n (Name InstanceNameC n)
emitInstanceDef instanceDef@(InstanceDef className _ _ _) = do
  emitBinding (getNameHint className) $ InstanceBinding instanceDef

emitDataConName :: (Mut n, TopBuilder m) => DataDefName n -> Int -> Atom n -> m n (Name DataConNameC n)
emitDataConName dataDefName conIdx conAtom = do
  DataDef _ _ dataCons <- lookupDataDef dataDefName
  let (DataConDef name _) = dataCons !! conIdx
  emitBinding (getNameHint name) $ DataConBinding dataDefName conIdx conAtom

zipNest :: (forall ii ii'. a -> b ii ii' -> b' ii ii')
        -> [a]
        -> Nest b  i i'
        -> Nest b' i i'
zipNest _ _ Empty = Empty
zipNest f (x:t) (Nest b rest) = Nest (f x b) $ zipNest f t rest
zipNest _ _ _ = error "List too short!"

zipPiBinders :: [Arrow] -> Nest Binder i i' -> Nest PiBinder i i'
zipPiBinders = zipNest \arr (b :> ty) -> PiBinder b ty arr

emitMethod
  :: (Mut n, TopBuilder m)
  => NameHint -> ClassName n -> [Bool] -> Int -> m n (Name MethodNameC n)
emitMethod hint classDef explicit idx = do
  getter <- makeMethodGetter classDef explicit idx
  f <- Var <$> emitTopLet hint PlainLet (Atom getter)
  emitBinding hint $ MethodBinding classDef idx f

makeMethodGetter :: EnvReader m => Name ClassNameC n -> [Bool] -> Int -> m n (Atom n)
makeMethodGetter className explicit methodIdx = liftBuilder do
  className' <- sinkM className
  ClassDef sourceName _ paramBs _ _ <- getClassDef className'
  let arrows = explicit <&> \case True -> PlainArrow; False -> ImplicitArrow
  buildPureNaryLam (EmptyAbs $ zipPiBinders arrows paramBs) \params -> do
    let dictTy = DictTy $ DictType sourceName (sink className') (map Var params)
    buildPureLam noHint ClassArrow dictTy \dict ->
      emitOp $ ProjMethod (Var dict) methodIdx

emitTyConName :: (Mut n, TopBuilder m) => DataDefName n -> Atom n -> m n (Name TyConNameC n)
emitTyConName dataDefName tyConAtom = do
  emitBinding (getNameHint dataDefName) $ TyConBinding dataDefName tyConAtom

getDataCon :: EnvReader m => Name DataConNameC n -> m n (DataDefName n, Int)
getDataCon v = do
  ~(DataConBinding defName idx _) <- lookupEnv v
  return (defName, idx)

getClassDef :: EnvReader m => Name ClassNameC n -> m n (ClassDef n)
getClassDef classDefName = do
  ~(ClassBinding classDef) <- lookupEnv classDefName
  return classDef

-- === builder versions of common local ops ===

fLitLike :: (Builder m, Emits n) => Double -> Atom n -> m n (Atom n)
fLitLike x t = do
  ty <- getType t
  case ty of
    BaseTy (Scalar Float64Type) -> return $ Con $ Lit $ Float64Lit x
    BaseTy (Scalar Float32Type) -> return $ Con $ Lit $ Float32Lit $ realToFrac x
    _ -> error "Expected a floating point scalar"

neg :: (Builder m, Emits n) => Atom n -> m n (Atom n)
neg x = emitOp $ UnOp FNeg x

add :: (Builder m, Emits n) => Atom n -> Atom n -> m n (Atom n)
add x y = emitOp $ BinOp FAdd x y

-- TODO: Implement constant folding for fixed-width integer types as well!
iadd :: (Builder m, Emits n) => Atom n -> Atom n -> m n (Atom n)
iadd (Con (Lit l)) y | getIntLit l == 0 = return y
iadd x (Con (Lit l)) | getIntLit l == 0 = return x
iadd x@(Con (Lit _)) y@(Con (Lit _)) = return $ applyIntBinOp (+) x y
iadd x y = emitOp $ BinOp IAdd x y

mul :: (Builder m, Emits n) => Atom n -> Atom n -> m n (Atom n)
mul x y = emitOp $ BinOp FMul x y

imul :: (Builder m, Emits n) => Atom n -> Atom n -> m n (Atom n)
imul   (Con (Lit l)) y               | getIntLit l == 1 = return y
imul x                 (Con (Lit l)) | getIntLit l == 1 = return x
imul x@(Con (Lit _)) y@(Con (Lit _))                    = return $ applyIntBinOp (*) x y
imul x y = emitOp $ BinOp IMul x y

sub :: (Builder m, Emits n) => Atom n -> Atom n -> m n (Atom n)
sub x y = emitOp $ BinOp FSub x y

isub :: (Builder m, Emits n) => Atom n -> Atom n -> m n (Atom n)
isub x (Con (Lit l)) | getIntLit l == 0 = return x
isub x@(Con (Lit _)) y@(Con (Lit _)) = return $ applyIntBinOp (-) x y
isub x y = emitOp $ BinOp ISub x y

select :: (Builder m, Emits n) => Atom n -> Atom n -> Atom n -> m n (Atom n)
select (Con (Lit (Word8Lit p))) x y = return $ if p /= 0 then x else y
select p x y = emitOp $ Select p x y

div' :: (Builder m, Emits n) => Atom n -> Atom n -> m n (Atom n)
div' x y = emitOp $ BinOp FDiv x y

idiv :: (Builder m, Emits n) => Atom n -> Atom n -> m n (Atom n)
idiv x (Con (Lit l)) | getIntLit l == 1 = return x
idiv x@(Con (Lit _)) y@(Con (Lit _)) = return $ applyIntBinOp div x y
idiv x y = emitOp $ BinOp IDiv x y

irem :: (Builder m, Emits n) => Atom n -> Atom n -> m n (Atom n)
irem x y = emitOp $ BinOp IRem x y

fpow :: (Builder m, Emits n) => Atom n -> Atom n -> m n (Atom n)
fpow x y = emitOp $ BinOp FPow x y

flog :: (Builder m, Emits n) => Atom n -> m n (Atom n)
flog x = emitOp $ UnOp Log x

ilt :: (Builder m, Emits n) => Atom n -> Atom n -> m n (Atom n)
ilt x@(Con (Lit _)) y@(Con (Lit _)) = return $ applyIntCmpOp (<) x y
ilt x y = emitOp $ BinOp (ICmp Less) x y

ieq :: (Builder m, Emits n) => Atom n -> Atom n -> m n (Atom n)
ieq x@(Con (Lit _)) y@(Con (Lit _)) = return $ applyIntCmpOp (==) x y
ieq x y = emitOp $ BinOp (ICmp Equal) x y

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
  atom' <- cheapNormalize atom
  ty <- getType atom'
  len <- projectLength ty
  return $ map (\i -> getProjection [i] atom') (iota len)
{-# SCC getUnpacked #-}

emitUnpacked :: (Builder m, Emits n) => Atom n -> m n [AtomName n]
emitUnpacked tup = do
  xs <- getUnpacked tup
  forM xs \x -> emit $ Atom x

app :: (Builder m, Emits n) => Atom n -> Atom n -> m n (Atom n)
app x i = Var <$> emit (App x (i:|[]))

naryApp :: (Builder m, Emits n) => Atom n -> [Atom n] -> m n (Atom n)
naryApp f xs = case nonEmpty xs of
  Nothing -> return f
  Just xs' -> Var <$> emit (App f xs')

tabApp :: (Builder m, Emits n) => Atom n -> Atom n -> m n (Atom n)
tabApp x i = Var <$> emit (TabApp x (i:|[]))

naryTabApp :: (Builder m, Emits n) => Atom n -> [Atom n] -> m n (Atom n)
naryTabApp f xs = case nonEmpty xs of
  Nothing -> return f
  Just xs' -> Var <$> emit (TabApp f xs')

indexRef :: (Builder m, Emits n) => Atom n -> Atom n -> m n (Atom n)
indexRef ref i = emitOp $ IndexRef ref i

naryIndexRef :: (Builder m, Emits n) => Atom n -> [Atom n] -> m n (Atom n)
naryIndexRef ref is = foldM indexRef ref is

ptrOffset :: (Builder m, Emits n) => Atom n -> Atom n -> m n (Atom n)
ptrOffset x (IdxRepVal 0) = return x
ptrOffset x i = emitOp $ PtrOffset x i
{-# INLINE ptrOffset #-}

unsafePtrLoad :: (Builder m, Emits n) => Atom n -> m n (Atom n)
unsafePtrLoad x = do
  lam <- liftEmitBuilder $ buildLam noHint PlainArrow UnitTy (oneEffect IOEffect) \_ ->
    emitOp . PtrLoad =<< sinkM x
  liftM Var $ emit $ Hof $ RunIO $ lam

-- === index set type class ===

clampPositive :: (Builder m, Emits n) => Atom n -> m n (Atom n)
clampPositive x = do
  isNegative <- x `ilt` (IdxRepVal 0)
  select isNegative (IdxRepVal 0) x

projMethod :: (Builder m, Emits n) => String -> Atom n -> m n (Atom n)
projMethod methodName dict = do
  getType dict >>= \case
    DictTy (DictType _ className _) -> do
      methodIdx <- getMethodIndex className methodName
      emitOp $ ProjMethod dict methodIdx
    _ -> error $ "Not a dict: " ++ pprint dict

unsafeFromOrdinal :: forall m n. (Builder m, Emits n) => IxType n -> Atom n -> m n (Atom n)
unsafeFromOrdinal (IxType _ dict) i = do
  f <- projMethod "unsafe_from_ordinal" dict
  app f i

ordinal :: forall m n. (Builder m, Emits n) => IxType n -> Atom n -> m n (Atom n)
ordinal (IxType _ dict) idx = do
  f <- projMethod "ordinal" dict
  app f idx

indexSetSize :: (Builder m, Emits n) => IxType n -> m n (Atom n)
indexSetSize (IxType _ dict) = projMethod "size" dict

projectIxFinMethod :: EnvReader m => Int -> Atom n -> m n (Atom n)
projectIxFinMethod methodIx n = liftBuilder do
  case methodIx of
    -- size
    0 -> return n
    -- ordinal
    1 -> buildPureLam noHint PlainArrow IdxRepTy \ix ->
           emitOp $ CastOp IdxRepTy $ Var ix
    -- unsafe_from_ordinal
    2 -> buildPureLam noHint PlainArrow IdxRepTy \ix ->
           return $ Con $ FinVal (sink n) $ Var ix
    _ -> error "Ix only has three methods"

-- === pseudo-prelude ===

-- Bool -> (Unit -> {|eff} a) -> (() -> {|eff} a) -> {|eff} a
-- XXX: the first argument is the true case, following the
-- surface-level `if ... then ... else ...`, but the order
-- is flipped in the actual `Case`, because False acts like 0.
-- TODO: consider a version that figures out the result type itself.
emitIf :: (Emits n, ScopableBuilder m)
       => Atom n
       -> Type n
       -> (forall l. (Emits l, DExt n l) => m l (Atom l))
       -> (forall l. (Emits l, DExt n l) => m l (Atom l))
       -> m n (Atom n)
emitIf predicate resultTy trueCase falseCase = do
  predicate' <- emitOp $ ToEnum (SumTy [UnitTy, UnitTy]) predicate
  buildCase predicate' resultTy \i [_] ->
    case i of
      0 -> falseCase
      1 -> trueCase
      _ -> error "should only have two cases"

emitMaybeCase :: (Emits n, ScopableBuilder m)
              => Atom n -> Type n
              -> (forall l. (Emits l, DExt n l) =>           m l (Atom l))
              -> (forall l. (Emits l, DExt n l) => Atom l -> m l (Atom l))
              -> m n (Atom n)
emitMaybeCase scrut resultTy nothingCase justCase = do
  buildCase scrut resultTy \i [v] ->
    case i of
      0 -> nothingCase
      1 -> justCase v
      _ -> error "should be a binary scrutinee"

-- Maybe a -> a
fromJustE :: (Emits n, Builder m) => Atom n -> m n (Atom n)
fromJustE x = liftEmitBuilder do
  MaybeTy a <- getType x
  emitMaybeCase x a
    (emitOp $ ThrowError $ sink a)
    (return)

-- Maybe a -> Bool
isJustE :: (Emits n, Builder m) => Atom n -> m n (Atom n)
isJustE x = liftEmitBuilder $
  emitMaybeCase x BoolTy (return FalseAtom) (\_ -> return TrueAtom)

-- Monoid a -> (n=>a) -> a
reduceE :: (Emits n, Builder m) => BaseMonoid n -> Atom n -> m n (Atom n)
reduceE monoid xs = liftEmitBuilder do
  TabTy (n:>ty) a <- getType xs
  a' <- return $ ignoreHoistFailure $ hoist n a
  getSnd =<< emitRunWriter noHint a' monoid \_ ref ->
    buildFor noHint Fwd (sink ty) \i -> do
      x <- tabApp (sink xs) (Var i)
      emitOp $ PrimEffect (sink $ Var ref) $ MExtend (fmap sink monoid) x

andMonoid :: EnvReader m => m n (BaseMonoid n)
andMonoid =  liftM (BaseMonoid TrueAtom) do
  liftBuilder $
    buildLam noHint PlainArrow BoolTy Pure \x ->
      buildLam noHint PlainArrow BoolTy Pure \y -> do
        emitOp $ BinOp BAnd (sink $ Var x) (Var y)

-- (a-> {|eff} b) -> n=>a -> {|eff} (n=>b)
mapE :: (Emits n, ScopableBuilder m)
     => (forall l. (Emits l, DExt n l) => Atom l -> m l (Atom l))
     -> Atom n -> m n (Atom n)
mapE f xs = do
  TabTy (n:>ty) _ <- getType xs
  buildFor (getNameHint n) Fwd ty \i -> do
    x <- tabApp (sink xs) (Var i)
    f x

-- (n:Type) ?-> (a:Type) ?-> (xs : n=>Maybe a) : Maybe (n => a) =
catMaybesE :: (Emits n, Builder m) => Atom n -> m n (Atom n)
catMaybesE maybes = do
  TabTy n (MaybeTy a) <- getType maybes
  justs <- liftEmitBuilder $ mapE isJustE maybes
  monoid <- andMonoid
  allJust <- reduceE monoid justs
  liftEmitBuilder $ emitIf allJust (MaybeTy $ TabTy n a)
    (JustAtom (sink $ TabTy n a) <$> mapE fromJustE (sink maybes))
    (return (NothingAtom $ sink $ TabTy n a))

emitWhile :: (Emits n, ScopableBuilder m)
          => (forall l. (Emits l, DExt n l) => m l (Atom l))
          -> m n ()
emitWhile body = do
  eff <- getAllowedEffects
  lam <- buildNullaryLam eff body
  void $ emit $ Hof $ While lam

-- Dex implementation, for reference
-- def whileMaybe (eff:Effects) -> (body: Unit -> {|eff} (Maybe Word8)) : {|eff} Maybe Unit =
--   hadError = yieldState False \ref.
--     while do
--       ans = liftState ref body ()
--       case ans of
--         Nothing ->
--           ref := True
--           False
--         Just cond -> W8ToB cond
--   if hadError
--     then Nothing
--     else Just ()

runMaybeWhile :: (Emits n, ScopableBuilder m)
              => (forall l. (Emits l, DExt n l) => m l (Atom l))
              -> m n (Atom n)
runMaybeWhile body = do
  hadError <- getSnd =<< emitRunState noHint FalseAtom \_ ref -> do
    emitWhile do
      ans <- body
      emitMaybeCase ans Word8Ty
        (emitOp (PrimEffect (sink $ Var ref) $ MPut TrueAtom) >> return FalseAtom)
        (return)
    return UnitVal
  emitIf hadError (MaybeTy UnitTy)
    (return $ NothingAtom UnitTy)
    (return $ JustAtom    UnitTy UnitVal)

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

telescopicCapture
  :: (EnvReader m, HoistableE e, HoistableB b)
  => b n l -> e l -> m l (Atom l, Type n, ReconAbs e n)
telescopicCapture bs e = do
  vs <- localVarsAndTypeVars bs e
  vTys <- mapM (getType . Var) vs
  let (vsSorted, tys) = unzip $ toposortAnnVars $ zip vs vTys
  ty <- liftEnvReaderM $ buildTelescopeTy vs tys
  result <- buildTelescopeVal (map Var vsSorted) ty
  let ty' = ignoreHoistFailure $ hoist bs ty
  let ab  = ignoreHoistFailure $ hoist bs $ abstractFreeVarsNoAnn vsSorted e
  return (result, ty', ab)

-- XXX: assumes arguments are toposorted
buildTelescopeTy :: (EnvReader m, EnvExtender m)
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
toposortAnnVars :: forall e c n. (Color c, HoistableE e)
                => [(Name c n, e n)] -> [(Name c n, e n)]
toposortAnnVars annVars =
  let (graph, vertexToNode, _) = graphFromEdges $ map annVarToNode annVars
  in map (nodeToAnnVar . vertexToNode) $ reverse $ topSort graph
  where
    annVarToNode :: (Name c n, e n) -> (e n, Name c n, [Name c n])
    annVarToNode (v, ann) = (ann, v, nameSetToList $ freeVarsE ann)

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
      return $ localVars b ty

localVars :: (Color c, BindsNames b, HoistableE e)
          => b n l -> e l -> [Name c l]
localVars b e = nameSetToList $
  R.intersection (toNameSet (toScopeFrag b)) (freeVarsE e)

instance GenericE ReconstructAtom where
  type RepE ReconstructAtom = EitherE UnitE (NaryAbs AtomNameC Atom)
  fromE IdentityRecon = LeftE UnitE
  fromE (LamRecon recon) = RightE recon
  toE (LeftE _) = IdentityRecon
  toE (RightE recon) = LamRecon recon

instance SinkableE   ReconstructAtom
instance HoistableE  ReconstructAtom
instance AlphaEqE    ReconstructAtom
instance SubstE Name ReconstructAtom
instance SubstE AtomSubstVal ReconstructAtom

instance Pretty (ReconstructAtom n) where
  pretty IdentityRecon = "Identity reconstruction"
  pretty (LamRecon ab) = "Reconstruction abs: " <> pretty ab

-- See Note [Confuse GHC] from Simplify.hs
confuseGHC :: BuilderM n (DistinctEvidence n)
confuseGHC = getDistinct
{-# INLINE confuseGHC #-}
