-- Copyright 2021 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}

module Builder where

import Control.Applicative
import Control.Monad
import Control.Monad.Reader
import Control.Monad.Writer.Strict hiding (Alt)
import Control.Monad.State.Strict (MonadState (..), StateT (..), runStateT)
import qualified Data.Map.Strict as M
import Data.Maybe (isJust)
import Data.Foldable (toList)
import Data.Functor ((<&>))
import Data.Graph (graphFromEdges, topSort)
import Data.List.NonEmpty (NonEmpty (..), nonEmpty)
import Data.Text.Prettyprint.Doc (Pretty (..), group, line, nest)
import Foreign.Ptr

import qualified Unsafe.Coerce as TrulyUnsafe

import CheapReduction
import Core
import Err
import IRVariants
import MTL1
import Subst
import Name
import PPrint (prettyBlock)
import QueryType
import RawName qualified as R
import Types.Core
import Types.Imp
import Types.Primitives
import Types.Source
import Util (enumerate, transitiveClosureM, bindM2, toSnocList, (...))

-- === Ordinary (local) builder class ===

class (EnvReader m, EnvExtender m, Fallible1 m, IRRep r)
      => Builder (r::IR) (m::MonadKind1) | m -> r where
  rawEmitDecl :: Emits n => NameHint -> LetAnn -> Expr r n -> m n (AtomName r n)

class Builder r m => ScopableBuilder (r::IR) (m::MonadKind1) | m -> r where
  buildScoped
    :: SinkableE e
    => (forall l. (Emits l, DExt n l) => m l (e l))
    -> m n (Abs (Nest (Decl r)) e n)

type SBuilder = Builder SimpIR
type CBuilder = Builder CoreIR

type Builder2         (r::IR) (m :: MonadKind2) = forall i. Builder         r (m i)
type ScopableBuilder2 (r::IR) (m :: MonadKind2) = forall i. ScopableBuilder r (m i)

emitDecl :: (Builder r m, Emits n) => NameHint -> LetAnn -> Expr r n -> m n (AtomName r n)
emitDecl _ _ (Atom (Var n)) = return n
emitDecl hint ann expr = rawEmitDecl hint ann expr
{-# INLINE emitDecl #-}

emit :: (Builder r m, Emits n) => Expr r n -> m n (AtomName r n)
emit expr = emitDecl noHint PlainLet expr
{-# INLINE emit #-}

emitHinted :: (Builder r m, Emits n) => NameHint -> Expr r n -> m n (AtomName r n)
emitHinted hint expr = emitDecl hint PlainLet expr
{-# INLINE emitHinted #-}

emitOp :: (Builder r m, Emits n) => PrimOp (Atom r n) -> m n (Atom r n)
emitOp op = Var <$> emit (PrimOp op)
{-# INLINE emitOp #-}

emitExpr :: (Builder r m, Emits n) => Expr r n -> m n (Atom r n)
emitExpr expr = Var <$> emit expr
{-# INLINE emitExpr #-}

emitUnOp :: (Builder r m, Emits n) => UnOp -> Atom r n -> m n (Atom r n)
emitUnOp op x = emitOp $ UnOp op x
{-# INLINE emitUnOp #-}

emitBlock :: (Builder r m, Emits n) => Block r n -> m n (Atom r n)
emitBlock (Block _ decls result) = emitDecls decls result

emitDecls :: (Builder r m, Emits n, RenameE e, SinkableE e)
          => Nest (Decl r) n l -> e l -> m n (e n)
emitDecls decls result = runSubstReaderT idSubst $ emitDecls' decls result

emitDecls' :: (Builder r m, Emits o, RenameE e, SinkableE e)
           => Nest (Decl r) i i' -> e i' -> SubstReaderT Name m i o (e o)
emitDecls' Empty e = renameM e
emitDecls' (Nest (Let b (DeclBinding ann _ expr)) rest) e = do
  expr' <- renameM expr
  v <- emitDecl (getNameHint b) ann expr'
  extendSubst (b @> v) $ emitDecls' rest e

emitExprToAtom :: (Builder r m, Emits n) => Expr r n -> m n (Atom r n)
emitExprToAtom (Atom atom) = return atom
emitExprToAtom expr = Var <$> emit expr
{-# INLINE emitExprToAtom #-}

buildScopedAssumeNoDecls :: (SinkableE e, ScopableBuilder r m)
  => (forall l. (Emits l, DExt n l) => m l (e l))
  -> m n (e n)
buildScopedAssumeNoDecls cont = do
  buildScoped cont >>= \case
    (Abs Empty e) -> return e
    _ -> error "Expected no decl emissions"
{-# INLINE buildScopedAssumeNoDecls #-}

-- === "Hoisting" top-level builder class ===

-- `emitHoistedEnv` lets you emit top env fragments, like cache entries or
-- top-level function definitions, from within a local context. The operation
-- may fail, returning `Nothing`, because the emission might mention local
-- variables that can't be hoisted the top level.
class (EnvReader m, MonadFail1 m) => HoistingTopBuilder frag m | m -> frag where
  emitHoistedEnv :: (SinkableE e, RenameE e, HoistableE e)
                 => Abs frag e n -> m n (Maybe (e n))
  canHoistToTop :: HoistableE e => e n -> m n Bool

liftTopBuilderHoisted
  :: (EnvReader m, RenameE e, SinkableE e, HoistableE e)
  => (forall l. (Mut l, DExt n l) => TopBuilderM l (e l))
  -> m n (Abs TopEnvFrag e n)
liftTopBuilderHoisted cont = do
  env <- unsafeGetEnv
  Distinct <- getDistinct
  return $ runHardFail $ runTopBuilderT env $ localTopBuilder cont

liftTopBuilderAndEmit
  :: (HoistingTopBuilder TopEnvFrag m, RenameE e, SinkableE e, HoistableE e)
  => (forall l. (Mut l, DExt n l) => TopBuilderM l (e l))
  -> m n (Maybe (e n))
liftTopBuilderAndEmit cont = do
  liftTopBuilderHoisted cont >>= emitHoistedEnv

newtype DoubleBuilderT (r::IR) (topEmissions::B) (m::MonadKind) (n::S) (a:: *) =
  DoubleBuilderT { runDoubleBuilderT' :: DoubleInplaceT Env topEmissions (BuilderEmissions r) m n a }
  deriving ( Functor, Applicative, Monad, MonadFail, Fallible
           , CtxReader, MonadIO, Catchable, MonadReader r')

deriving instance (ExtOutMap Env frag, HoistableB frag, OutFrag frag, Fallible m, IRRep r)
                  => ScopeReader (DoubleBuilderT r frag m)

type DoubleBuilder r = DoubleBuilderT r TopEnvFrag HardFailM

liftDoubleBuilderTNoEmissions
  :: (EnvReader m, Fallible m', IRRep r) => DoubleBuilderT r UnitB m' n a -> m n (m' a)
liftDoubleBuilderTNoEmissions cont = do
  env <- unsafeGetEnv
  Distinct <- getDistinct
  return do
    Abs UnitB (DoubleInplaceTResult REmpty (LiftE ans)) <-
      -- XXX: it's safe to use `unsafeCoerceM1` here. We don't need the rank-2
      -- trick because we've specialized on the `UnitB` case, so there can't be
      -- any top emissions.
      runDoubleInplaceT env $ unsafeCoerceM1 $ runDoubleBuilderT' $ LiftE <$> cont
    return ans

-- TODO: do we really need to play these rank-2 games here?
liftDoubleBuilderT
  :: ( EnvReader m, Fallible m', SinkableE e, RenameE e
     , ExtOutMap Env frag, OutFrag frag, IRRep r)
  => (forall l. DExt n l => DoubleBuilderT r frag m' l (e l))
  -> m n (m' (Abs frag e n))
liftDoubleBuilderT cont = do
  env <- unsafeGetEnv
  Distinct <- getDistinct
  return $ runDoubleBuilderT env cont

runDoubleBuilderT
  :: ( Distinct n, Fallible m, SinkableE e, RenameE e
     , ExtOutMap Env frag, OutFrag frag, IRRep r)
  => Env n
  -> (forall l. DExt n l => DoubleBuilderT r frag m l (e l))
  -> m (Abs frag e n)
runDoubleBuilderT env cont = do
  Abs envFrag (DoubleInplaceTResult REmpty e) <-
    runDoubleInplaceT env $ runDoubleBuilderT' cont
  return $ Abs envFrag e

instance (ExtOutMap Env f, OutFrag f, RenameB f, HoistableB f, Fallible m, IRRep r)
  => HoistingTopBuilder f (DoubleBuilderT r f m) where
  emitHoistedEnv ab = DoubleBuilderT $ emitDoubleInplaceTHoisted ab
  {-# INLINE emitHoistedEnv #-}
  canHoistToTop e = DoubleBuilderT $ canHoistToTopDoubleInplaceT e
  {-# INLINE canHoistToTop #-}

instance (ExtOutMap Env frag, HoistableB frag, OutFrag frag, Fallible m, IRRep r)
          => EnvReader (DoubleBuilderT r frag m) where
  unsafeGetEnv = DoubleBuilderT $ liftDoubleInplaceT $ unsafeGetEnv

instance ( RenameB frag, HoistableB frag, OutFrag frag
         , ExtOutMap Env frag, Fallible m, IRRep r)
        => Builder r (DoubleBuilderT r frag m) where
  rawEmitDecl hint ann e = DoubleBuilderT $ liftDoubleInplaceT $ runBuilderT' $ emitDecl hint ann e

instance ( RenameB frag, HoistableB frag, OutFrag frag
         , ExtOutMap Env frag, Fallible m, IRRep r)
         => ScopableBuilder r (DoubleBuilderT r frag m) where
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

-- TODO: derive this instead
instance ( IRRep r, RenameB frag, HoistableB frag, OutFrag frag
         , ExtOutMap Env frag, Fallible m)
         => EnvExtender (DoubleBuilderT r frag m) where
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

instance (SinkableV v, HoistingTopBuilder f m) => HoistingTopBuilder f (SubstReaderT v m i) where
  emitHoistedEnv ab = SubstReaderT $ lift $ emitHoistedEnv ab
  {-# INLINE emitHoistedEnv #-}
  canHoistToTop e = SubstReaderT $ lift $ canHoistToTop e
  {-# INLINE canHoistToTop #-}

-- === Top-level builder class ===

class (EnvReader m, MonadFail1 m) => TopBuilder (m::MonadKind1) where
  -- `emitBinding` is expressible in terms of `emitEnv` but it can be
  -- implemented more efficiently by avoiding a double substitution
  -- XXX: emitBinding/emitEnv don't extend the synthesis candidates
  -- TODO: do we actually need `emitBinding`? Top emissions probably aren't hot.
  emitBinding :: Mut n => Color c => NameHint -> Binding c n -> m n (Name c n)
  emitEnv :: (Mut n, SinkableE e, RenameE e) => Abs TopEnvFrag e n -> m n (e n)
  emitNamelessEnv :: TopEnvFrag n n -> m n ()
  localTopBuilder :: SinkableE e
                  => (forall l. (Mut l, DExt n l) => m l (e l))
                  -> m n (Abs TopEnvFrag e n)

emitBindingDefault :: (TopBuilder m, Mut n, Color c) => NameHint -> Binding c n -> m n (Name c n)
emitBindingDefault hint binding = do
  ab <- liftEnvReaderM $ withFreshBinder hint binding \b'-> do
    let topFrag = TopEnvFrag (toEnvFrag b') mempty
    return $ Abs topFrag $ binderName b'
  emitEnv ab

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

emitAtomRules :: TopBuilder m => AtomName CoreIR n -> AtomRules n -> m n ()
emitAtomRules v rules = emitNamelessEnv $
  TopEnvFrag emptyOutFrag $ mempty { fragCustomRules = CustomRules $ M.singleton v rules }

emitTopLet :: (Mut n, TopBuilder m) => NameHint -> LetAnn -> Expr CoreIR n -> m n (AtomName CoreIR n)
emitTopLet hint letAnn expr = do
  ty <- getType expr
  emitBinding hint $ AtomNameBinding $ LetBound (DeclBinding letAnn ty expr)

emitTopFunBinding :: (Mut n, TopBuilder m) => NameHint -> TopFunDef n -> LamExpr SimpIR n -> m n (TopFunName n)
emitTopFunBinding hint def f = do
  ty <- getNaryLamExprType f
  emitBinding hint $ TopFunBinding $ DexTopFun def ty f Waiting

updateTopFunStatus :: (Mut n, TopBuilder m) => TopFunName n -> EvalStatus (TopFunLowerings n) -> m n ()
updateTopFunStatus f status =
  emitPartialTopEnvFrag $ mempty {fragTopFunUpdates = toSnocList [(f, status)]}

updateTransposeRelation :: (Mut n, TopBuilder m) => TopFunName n -> TopFunName n -> m n ()
updateTransposeRelation f1 f2 =
  extendCache $ mempty { transpositionCache = eMapSingleton f1 f2 <> eMapSingleton f2 f1}

bindModule :: (Mut n, TopBuilder m) => ModuleSourceName -> ModuleName n -> m n ()
bindModule sourceName internalName = do
  let loaded = LoadedModules $ M.singleton sourceName internalName
  emitPartialTopEnvFrag $ mempty {fragLoadedModules = loaded}

lookupLoadedModule:: EnvReader m => ModuleSourceName -> m n (Maybe (ModuleName n))
lookupLoadedModule name = do
  loadedModules <- withEnv $ envLoadedModules . topEnv
  return $ M.lookup name $ fromLoadedModules loadedModules

lookupLoadedObject :: EnvReader m => FunObjCodeName n -> m n (Maybe NativeFunction)
lookupLoadedObject name = do
  loadedObjects <- withEnv $ envLoadedObjects . topEnv
  return $ M.lookup name $ fromLoadedObjects loadedObjects

extendLoadedObjects :: (Mut n, TopBuilder m) => FunObjCodeName n -> NativeFunction -> m n ()
extendLoadedObjects name ptr = do
  let loaded = LoadedObjects $ M.singleton name ptr
  emitPartialTopEnvFrag $ mempty {fragLoadedObjects = loaded}

extendCache :: TopBuilder m => Cache n -> m n ()
extendCache cache = emitPartialTopEnvFrag $ mempty {fragCache = cache}

extendSpecializationCache :: TopBuilder m => SpecializationSpec n -> TopFunName n -> m n ()
extendSpecializationCache specialization f =
  extendCache $ mempty { specializationCache = eMapSingleton specialization f }

querySpecializationCache :: EnvReader m => SpecializationSpec n -> m n (Maybe (TopFunName n))
querySpecializationCache specialization = do
  cache <- specializationCache <$> getCache
  return $ lookupEMap cache specialization

queryIxDictCache :: EnvReader m => AbsDict n -> m n (Maybe (Name SpecializedDictNameC n))
queryIxDictCache d = do
  cache <- ixDictCache <$> getCache
  return $ lookupEMap cache d

queryLinearizationCache :: EnvReader m => LinearizationSpec n -> m n (Maybe (TopFunName n, TopFunName n))
queryLinearizationCache s = do
  cache <- linearizationCache <$> getCache
  return $ fmap fromPairE $ lookupEMap cache s

extendLinearizationCache
  :: (TopBuilder m, Fallible1 m, Mut n)
  => LinearizationSpec n -> (TopFunName n, TopFunName n) -> m n ()
extendLinearizationCache s fs =
  extendCache $ mempty { linearizationCache = eMapSingleton s (toPairE fs) }

queryObjCache :: EnvReader m => TopFunName n -> m n (Maybe (FunObjCodeName n))
queryObjCache v = lookupEnv v >>= \case
  TopFunBinding (DexTopFun _ _ _ (Finished impl)) -> return $ Just $ topFunObjCode impl
  _ -> return Nothing

emitObjFile
  :: (Mut n, TopBuilder m)
  => NameHint -> FunObjCode -> LinktimeNames  n
  -> m n (FunObjCodeName n)
emitObjFile hint objFile names = do
  emitBinding hint $ FunObjCodeBinding objFile names

lookupPtrName :: EnvReader m => PtrName n -> m n (PtrType, Ptr ())
lookupPtrName v = lookupEnv v >>= \case
  PtrBinding ty p -> case p of
    PtrLitVal ptr -> return (ty, ptr)
    PtrSnapshot _ -> error "this case is only for serialization"
    NullPtr       -> error "not implemented"

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
      return $ Abs (TopEnvFrag (toEnvFrag b') mempty) v'
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

type TopBuilder2 (r::IR) (m :: MonadKind2) = forall i. TopBuilder (m i)

instance (SinkableE e, HoistableState e, TopBuilder m) => TopBuilder (StateT1 e m) where
  emitBinding hint binding = lift11 $ emitBinding hint binding
  {-# INLINE emitBinding #-}
  emitEnv ab = lift11 $ emitEnv ab
  {-# INLINE emitEnv #-}
  emitNamelessEnv frag = lift11 $ emitNamelessEnv frag
  {-# INLINE emitNamelessEnv #-}
  localTopBuilder _ = error "not implemented"

-- === BuilderT ===

type BuilderEmissions r = RNest (Decl r)

newtype BuilderT (r::IR) (m::MonadKind) (n::S) (a:: *) =
  BuilderT { runBuilderT' :: InplaceT Env (BuilderEmissions r) m n a }
  deriving ( Functor, Applicative, Monad, MonadTrans1, MonadFail, Fallible
           , Catchable, CtxReader, ScopeReader, Alternative, Searcher
           , MonadWriter w, MonadReader r')

type BuilderM (r::IR) = BuilderT r HardFailM

instance (MonadState s m, IRRep r) => MonadState s (BuilderT r m n) where
  get :: BuilderT r m n s
  get = BuilderT $ UnsafeMakeInplaceT \env decls -> do
    s <- get
    return (s, unsafeCoerceB decls, unsafeCoerceE env)

  put :: s -> BuilderT r m n ()
  put s = BuilderT $ UnsafeMakeInplaceT \env decls -> do
    put s
    return ((), unsafeCoerceB decls, unsafeCoerceE env)

liftBuilderT :: (Fallible m, EnvReader m', IRRep r) => BuilderT r m n a -> m' n (m a)
liftBuilderT cont = do
  env <- unsafeGetEnv
  Distinct <- getDistinct
  return do
    (REmpty, result) <- runInplaceT env $ runBuilderT' cont
    return result
{-# INLINE liftBuilderT #-}

liftBuilder :: (EnvReader m, IRRep r) => BuilderM r n a -> m n a
liftBuilder cont = liftM runHardFail $ liftBuilderT cont
{-# INLINE liftBuilder #-}

-- TODO: This should not fabricate Emits evidence!!
-- XXX: this uses unsafe functions in its implementations. It should be safe to
-- use, but be careful changing it.
liftEmitBuilder :: (Builder r m, SinkableE e, RenameE e)
                => BuilderM r n (e n) -> m n (e n)
liftEmitBuilder cont = do
  env <- unsafeGetEnv
  Distinct <- getDistinct
  let (result, decls, _) = runHardFail $ unsafeRunInplaceT (runBuilderT' cont) env emptyOutFrag
  Emits <- fabricateEmitsEvidenceM
  emitDecls (unsafeCoerceB $ unRNest decls) result

instance (IRRep r, Fallible m) => ScopableBuilder r (BuilderT r m) where
  buildScoped cont = BuilderT do
    Abs rdecls e <- locallyMutableInplaceT $
      runBuilderT' do
        Emits <- fabricateEmitsEvidenceM
        Distinct <- getDistinct
        cont
    return $ Abs (unRNest rdecls) e
  {-# INLINE buildScoped #-}

newtype BuilderDeclEmission (r::IR) (n::S) (l::S) = BuilderDeclEmission (Decl r n l)
instance IRRep r => ExtOutMap Env (BuilderDeclEmission r) where
  extendOutMap env (BuilderDeclEmission d) = env `extendOutMap` toEnvFrag d
  {-# INLINE extendOutMap #-}
instance IRRep r => ExtOutFrag (BuilderEmissions r) (BuilderDeclEmission r) where
  extendOutFrag rn (BuilderDeclEmission d) = RNest rn d
  {-# INLINE extendOutFrag #-}

instance (IRRep r, Fallible m) => Builder r (BuilderT r m) where
  rawEmitDecl hint ann expr = do
    ty <- getType expr
    BuilderT $ freshExtendSubInplaceT hint \b ->
      (BuilderDeclEmission $ Let b $ DeclBinding ann ty expr, binderName b)
  {-# INLINE rawEmitDecl #-}

instance (IRRep r, Fallible m) => EnvReader (BuilderT r m) where
  unsafeGetEnv = BuilderT $ getOutMapInplaceT
  {-# INLINE unsafeGetEnv #-}

instance (IRRep r, Fallible m) => EnvExtender (BuilderT r m) where
  refreshAbs ab cont = BuilderT $ refreshAbs ab \b e -> runBuilderT' $ cont b e
  {-# INLINE refreshAbs #-}

instance (SinkableV v, ScopableBuilder r m) => ScopableBuilder r (SubstReaderT v m i) where
  buildScoped cont = SubstReaderT $ ReaderT \env ->
    buildScoped $
      runReaderT (runSubstReaderT' cont) (sink env)
  {-# INLINE buildScoped #-}

instance (SinkableV v, Builder r m) => Builder r (SubstReaderT v m i) where
  rawEmitDecl hint ann expr = SubstReaderT $ lift $ emitDecl hint ann expr
  {-# INLINE rawEmitDecl #-}

instance (SinkableE e, ScopableBuilder r m) => ScopableBuilder r (OutReaderT e m) where
  buildScoped cont = OutReaderT $ ReaderT \env ->
    buildScoped do
      env' <- sinkM env
      runReaderT (runOutReaderT' cont) env'
  {-# INLINE buildScoped #-}

instance (SinkableE e, Builder r m) => Builder r (OutReaderT e m) where
  rawEmitDecl hint ann expr =
    OutReaderT $ lift $ emitDecl hint ann expr
  {-# INLINE rawEmitDecl #-}

instance (SinkableE e, ScopableBuilder r m) => ScopableBuilder r (ReaderT1 e m) where
  buildScoped cont = ReaderT1 $ ReaderT \env ->
    buildScoped do
      env' <- sinkM env
      runReaderT (runReaderT1' cont) env'
  {-# INLINE buildScoped #-}

instance (SinkableE e, Builder r m) => Builder r (ReaderT1 e m) where
  rawEmitDecl hint ann expr =
    ReaderT1 $ lift $ emitDecl hint ann expr
  {-# INLINE rawEmitDecl #-}

instance (SinkableE e, HoistableState e, Builder r m) => Builder r (StateT1 e m) where
  rawEmitDecl hint ann expr = lift11 $ emitDecl hint ann expr
  {-# INLINE rawEmitDecl #-}

instance (SinkableE e, HoistableState e, ScopableBuilder r m) => ScopableBuilder r (StateT1 e m) where
  buildScoped cont = StateT1 \s -> do
    Abs decls (e `PairE` s') <- buildScoped $ liftM toPairE $ runStateT1 cont =<< sinkM s
    let s'' = hoistState s decls s'
    return (Abs decls e, s'')
  {-# INLINE buildScoped #-}

instance (SinkableE e, HoistableState e, HoistingTopBuilder frag m)
  => HoistingTopBuilder frag (StateT1 e m) where
  emitHoistedEnv ab = lift11 $ emitHoistedEnv ab
  {-# INLINE emitHoistedEnv #-}
  canHoistToTop e = lift11 $ canHoistToTop e
  {-# INLINE canHoistToTop #-}

instance (SinkableE e, HoistingTopBuilder frag m)
  => HoistingTopBuilder frag (ReaderT1 e m) where
  emitHoistedEnv ab = lift11 $ emitHoistedEnv ab
  {-# INLINE emitHoistedEnv #-}
  canHoistToTop e = lift11 $ canHoistToTop e
  {-# INLINE canHoistToTop #-}

instance Builder r m => Builder r (MaybeT1 m) where
  rawEmitDecl hint ann expr = lift11 $ emitDecl hint ann expr
  {-# INLINE rawEmitDecl #-}

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
  :: ScopableBuilder r m
  => (forall l. (Emits l, DExt n l) => m l (Atom r l))
  -> m n (Block r n)
buildBlock cont = buildScoped (cont >>= withType) >>= computeAbsEffects >>= absToBlock

withType :: ((EnvReader m, IRRep r), HasType r e) => e l -> m l ((e `PairE` Type r) l)
withType e = do
  ty <- {-# SCC blockTypeNormalization #-} cheapNormalize =<< getType e
  return $ e `PairE` ty
{-# INLINE withType #-}

makeBlock :: IRRep r => Nest (Decl r) n l -> EffectRow r l -> Atom r l -> Type r l -> Block r n
makeBlock decls effs atom ty = Block (BlockAnn ty' effs') decls atom where
  ty' = ignoreHoistFailure $ hoist decls ty
  effs' = ignoreHoistFailure $ hoist decls effs
{-# INLINE makeBlock #-}

absToBlockInferringTypes :: (EnvReader m, IRRep r) => Abs (Nest (Decl r)) (Atom r) n -> m n (Block r n)
absToBlockInferringTypes ab = liftEnvReaderM do
  abWithEffs <-  computeAbsEffects ab
  refreshAbs abWithEffs \decls (effs `PairE` result) -> do
    ty <- cheapNormalize =<< getType result
    return $ ignoreExcept $
      absToBlock $ Abs decls (effs `PairE` (result `PairE` ty))
{-# INLINE absToBlockInferringTypes #-}

absToBlock
  :: (Fallible m, IRRep r)
  => Abs (Nest (Decl r)) (EffectRow r `PairE` (Atom r `PairE` Type r)) n -> m (Block r n)
absToBlock (Abs decls (effs `PairE` (result `PairE` ty))) = do
  let msg = "Block:" <> nest 1 (prettyBlock decls result) <> line
            <> group ("Of type:" <> nest 2 (line <> pretty ty)) <> line
            <> group ("With effects:" <> nest 2 (line <> pretty effs))
  ty' <- liftHoistExcept' (docAsStr msg) $ hoist decls ty
  effs' <- liftHoistExcept' (docAsStr msg) $ hoist decls effs
  return $ Block (BlockAnn ty' effs') decls result
{-# INLINE absToBlock #-}

makeBlockFromDecls :: (EnvReader m, IRRep r) => Abs (Nest (Decl r)) (Atom r) n -> m n (Block r n)
makeBlockFromDecls (Abs Empty result) = return $ AtomicBlock result
makeBlockFromDecls ab = liftEnvReaderM $ refreshAbs ab \decls result -> do
  ty <- getType result
  effs <- declNestEffects decls
  PairE ty' effs' <- return $ ignoreHoistFailure $ hoist decls $ PairE ty effs
  return $ Block (BlockAnn ty' effs') decls result
{-# INLINE makeBlockFromDecls #-}

buildPureLam :: (ScopableBuilder CoreIR m)
             => NameHint -> Arrow -> CType n
             -> (forall l. (Emits l, DExt n l) => AtomName CoreIR l -> m l (CAtom l))
             -> m n (CAtom n)
buildPureLam hint arr ty body = do
  buildLamGeneral hint arr ty (const $ return Pure) \v -> do
    Distinct <- getDistinct
    body v

buildLam
  :: ScopableBuilder CoreIR m
  => NameHint -> Arrow -> CType n -> EffectRow CoreIR n
  -> (forall l. (Emits l, DExt n l) => AtomName CoreIR l -> m l (CAtom l))
  -> m n (CAtom n)
buildLam hint arr ty eff body = buildLamGeneral hint arr ty (const $ sinkM eff) body

buildNullaryPi
  :: CBuilder m
  => EffectRow CoreIR n -> (forall l. DExt n l => m l (CType l)) -> m n (CType n)
buildNullaryPi effs cont =
  Pi <$> buildPi noHint PlainArrow UnitTy \_ -> do
    resultTy <- cont
    return (sink effs, resultTy)

buildLamGeneral
  :: ScopableBuilder CoreIR m
  => NameHint -> Arrow -> CType n
  -> (forall l.           DExt n l  => AtomName CoreIR l -> m l (EffectRow CoreIR l))
  -> (forall l. (Emits l, DExt n l) => AtomName CoreIR l -> m l (CAtom l))
  -> m n (CAtom n)
buildLamGeneral hint arr ty fEff fBody = do
  withFreshBinder hint ty \b -> do
    let v = binderName b
    effs <- fEff v
    body <- buildBlock $ fBody $ sink v
    return $ Lam (UnaryLamExpr b body) arr (Abs b effs)

-- Body must be an Atom because otherwise the nullary case would require
-- emitting decls into the enclosing scope.
buildPureNaryLam :: ScopableBuilder CoreIR m
                 => [Arrow] -> EmptyAbs (Nest CBinder) n
                 -> (forall l. DExt n l => [AtomName CoreIR l] -> m l (CAtom l))
                 -> m n (CAtom n)
buildPureNaryLam [] (EmptyAbs Empty) cont = do
  Distinct <- getDistinct
  cont []
buildPureNaryLam (arr:arrs) (EmptyAbs (Nest (b:>ty) rest)) cont = do
  buildPureLam (getNameHint b) arr ty \x -> do
    rest' <- applyRename (b@>x) $ EmptyAbs rest
    buildPureNaryLam arrs rest' \xs -> do
      x' <- sinkM x
      cont (x':xs)
buildPureNaryLam _ _ _ = error "impossible"

buildPi :: (Fallible1 m, CBuilder m)
        => NameHint -> Arrow -> CType n
        -> (forall l. DExt n l => AtomName CoreIR l -> m l (EffectRow CoreIR l, CType l))
        -> m n (PiType n)
buildPi hint arr ty body =
  withFreshBinder hint ty \(b:>_) -> do
    (effs, resultTy) <- body $ binderName b
    return $ PiType (b:>ty) arr effs resultTy

buildNaryPi
  :: CBuilder m
  => EmptyAbs (Nest (Binder CoreIR)) n
  -> (forall l. (Distinct l, DExt n l) => [AtomName CoreIR l] -> m l (CType l))
  -> m n (CType n)
buildNaryPi (Abs Empty UnitE) cont = do
  Distinct <- getDistinct
  cont []
buildNaryPi (Abs (Nest (b:>ty) bs) UnitE) cont = do
  Pi <$> buildPi (getNameHint b) PlainArrow ty \v -> do
    bs' <- applyRename (b@>v) $ EmptyAbs bs
    piTy <- buildNaryPi bs' \vs -> cont $ sink v : vs
    return (Pure, piTy)

buildNonDepPi :: EnvReader m => NameHint -> Arrow -> CType n -> EffectRow CoreIR n -> CType n -> m n (PiType n)
buildNonDepPi hint arr argTy effs resultTy = liftBuilder do
  argTy' <- sinkM argTy
  buildPi hint arr argTy' \_ -> do
    resultTy' <- sinkM resultTy
    effs'     <- sinkM effs
    return (effs', resultTy')

buildAbs
  :: (EnvReader m, EnvExtender m, SinkableE e, ToBinding binding c, Color c)
  => NameHint
  -> binding n
  -> (forall l. DExt n l => Name c l -> m l (e l))
  -> m n (Abs (BinderP c binding) e n)
buildAbs hint binding cont = do
  withFreshBinder hint binding \b -> do
    body <- cont $ binderName b
    return $ Abs b body

varsAsBinderNest :: (EnvReader m, IRRep r) => [AtomName r n] -> m n (EmptyAbs (Nest (Binder r)) n)
varsAsBinderNest [] = return $ EmptyAbs Empty
varsAsBinderNest (v:vs) = do
  rest <- varsAsBinderNest vs
  ty <- getType v
  Abs b (Abs bs UnitE) <- return $ abstractFreeVar v rest
  return $ EmptyAbs (Nest (b:>ty) bs)

typesAsBinderNest :: (EnvReader m, IRRep r) => [Type r n] -> m n (EmptyAbs (Nest (Binder r)) n)
typesAsBinderNest types = liftEnvReaderM $ go types
  where
    go :: forall r n. IRRep r => [Type r n] -> EnvReaderM n (EmptyAbs (Nest (Binder r)) n)
    go tys = case tys of
      [] -> return $ Abs Empty UnitE
      ty:rest -> withFreshBinder noHint ty \b -> do
        Abs bs UnitE <- go $ map sink rest
        return $ Abs (Nest b bs) UnitE

typesFromNonDepBinderNest
  :: (EnvReader m, Fallible1 m, IRRep r)
  => Nest (Binder r) n l -> m n [Type r n]
typesFromNonDepBinderNest Empty = return []
typesFromNonDepBinderNest (Nest (b:>ty) rest) = do
  Abs rest' UnitE <- return $ ignoreHoistFailure $ hoist b (Abs rest UnitE)
  tys <- typesFromNonDepBinderNest rest'
  return $ ty : tys

singletonBinderNest
  :: (EnvReader m, IRRep r)
  => NameHint -> ann n
  -> m n (EmptyAbs (Nest (BinderP (AtomNameC r) ann)) n)
singletonBinderNest hint ann = do
  Abs b _ <- return $ newName hint
  return $ EmptyAbs (Nest (b:>ann) Empty)

buildNaryAbs
  :: ( ScopableBuilder r m, SinkableE e, RenameE e, SubstE AtomSubstVal e, HoistableE e
     , BindsOneAtomName r b, BindsEnv b, RenameB b)
  => EmptyAbs (Nest b) n
  -> (forall l. DExt n l => [AtomName r l] -> m l (e l))
  -> m n (Abs (Nest b) e n)
buildNaryAbs (Abs n UnitE) body = do
  a <- liftBuilder $ buildNaryAbsRec [] n
  refreshAbs a \freshNest (ListE freshNames) ->
    Abs freshNest <$> body freshNames
{-# INLINE buildNaryAbs #-}

buildNaryAbsRec
  :: (BindsOneAtomName r b, BindsEnv b, RenameB b, IRRep r)
  => [AtomName r n] -> Nest b n l -> BuilderM r n (Abs (Nest b) (ListE (AtomName r)) n)
buildNaryAbsRec ns x = confuseGHCBuilder >>= \_ -> case x of
  Empty -> return $ Abs Empty $ ListE $ reverse ns
  Nest b bs -> do
    refreshAbs (Abs b (EmptyAbs bs)) \b' (EmptyAbs bs') -> do
      Abs bs'' ns'' <- buildNaryAbsRec (binderName b' : sinkList ns) bs'
      return $ Abs (Nest b' bs'') ns''

buildUnaryLamExpr
  :: (ScopableBuilder r m)
  => NameHint -> Type r n
  -> (forall l. (Emits l, Distinct l, DExt n l) => AtomName r l -> m l (Atom r l))
  -> m n (LamExpr r n)
buildUnaryLamExpr hint ty cont = do
  bs <- withFreshBinder hint ty \b -> return $ EmptyAbs (UnaryNest b)
  buildNaryLamExpr bs \[v] -> cont v

buildBinaryLamExpr
  :: (ScopableBuilder r m)
  => (NameHint, Type r n) -> (NameHint, Type r n)
  -> (forall l. (Emits l, Distinct l, DExt n l) => AtomName r l -> AtomName r l -> m l (Atom r l))
  -> m n (LamExpr r n)
buildBinaryLamExpr (h1,t1) (h2,t2) cont = do
  bs <- withFreshBinder h1 t1 \b1 -> withFreshBinder h2 (sink t2) \b2 ->
    return $ EmptyAbs $ BinaryNest b1 b2
  buildNaryLamExpr bs \[v1, v2] -> cont v1 v2

asNaryLam :: EnvReader m => NaryPiType CoreIR n -> Atom CoreIR n -> m n (LamExpr CoreIR n)
asNaryLam ty f = liftBuilder do
  buildNaryLamExprFromPi ty \xs ->
    naryApp (sink f) (map Var $ toList xs)

buildNonDepNaryLamExpr
  :: ScopableBuilder r m
  => [Type r n]
  -> (forall l. (Emits l, Distinct l, DExt n l) => [AtomName r l] -> m l (Atom r l))
  -> m n (LamExpr r n)
buildNonDepNaryLamExpr tys cont = do
  bs <- typesAsBinderNest tys
  buildNaryLamExpr bs cont

buildNaryLamExpr
  :: ScopableBuilder r m
  => (EmptyAbs (Nest (Binder r)) n)
  -> (forall l. (Emits l, Distinct l, DExt n l) => [AtomName r l] -> m l (Atom r l))
  -> m n (LamExpr r n)
buildNaryLamExpr (Abs bs UnitE) cont = case bs of
  Empty -> LamExpr Empty <$> buildBlock (cont [])
  Nest b rest -> do
    Abs b' (LamExpr bs' body') <- buildAbs (getNameHint b) (binderType b) \v -> do
      rest' <- applyRename (b@>v) $ EmptyAbs rest
      buildNaryLamExpr rest' \vs -> cont $ sink v : vs
    return $ LamExpr (Nest b' bs') body'

buildNaryLamExprFromPi
  :: ScopableBuilder r m
  => NaryPiType r n
  -> (forall l. (Emits l, Distinct l, DExt n l) => [AtomName r l] -> m l (Atom r l))
  -> m n (LamExpr r n)
buildNaryLamExprFromPi (NaryPiType bs _ _) cont = buildNaryLamExpr (EmptyAbs bs) cont

buildAlt
  :: ScopableBuilder r m
  => Type r n
  -> (forall l. (Distinct l, Emits l, DExt n l) => AtomName r l -> m l (Atom r l))
  -> m n (Alt r n)
buildAlt ty body = do
  buildAbs noHint ty \x ->
    buildBlock do
      Distinct <- getDistinct
      body $ sink x

buildCaseAlts :: (Emits n, ScopableBuilder r m)
  => Atom r n
  -> (forall l. DExt n l => Int -> Binder r n l -> m l a)
  -> m n [a]
buildCaseAlts scrut indexedAltBody = do
  scrutTy <- getType scrut
  altBinderTys <- caseAltsBinderTys scrutTy
  forM (enumerate altBinderTys) \(i, bTy) -> do
    withFreshBinder noHint bTy \b ->
      indexedAltBody i b

injectAltResult :: EnvReader m => [SType n] -> Int -> Alt SimpIR n -> m n (Alt SimpIR n)
injectAltResult sumTys con (Abs b body) = liftBuilder do
  buildAlt (binderType b) \v -> do
    originalResult <- emitBlock =<< applyRename (b@>v) body
    (dataResult, nonDataResult) <- fromPair originalResult
    return $ PairVal dataResult $ Con $ SumCon (sinkList sumTys) con nonDataResult

-- TODO: consider a version with nonempty list of alternatives where we figure
-- out the result type from one of the alts rather than providing it explicitly
buildCase :: (Emits n, ScopableBuilder r m)
          => Atom r n -> Type r n
          -> (forall l. (Emits l, DExt n l) => Int -> Atom r l -> m l (Atom r l))
          -> m n (Atom r n)
buildCase scrut resultTy indexedAltBody = do
  case trySelectBranch scrut of
    Just (i, arg) -> do
      Distinct <- getDistinct
      indexedAltBody i $ sink arg
    Nothing -> do
      scrutTy <- getType scrut
      altBinderTys <- caseAltsBinderTys scrutTy
      (alts, effs) <- unzip <$> forM (enumerate altBinderTys) \(i, bTy) -> do
        (Abs b' (body `PairE` eff')) <- buildAbs noHint bTy \x -> do
          blk <- buildBlock $ indexedAltBody i $ Var $ sink x
          eff <- getEffects blk
          return $ blk `PairE` eff
        return (Abs b' body, ignoreHoistFailure $ hoist b' eff')
      emitExpr $ Case scrut alts resultTy $ mconcat effs

buildEffLam
  :: ScopableBuilder r m
  => NameHint -> Type r n
  -> (forall l. (Emits l, DExt n l) => AtomName r l -> AtomName r l -> m l (Atom r l))
  -> m n (LamExpr r n)
buildEffLam hint ty body = do
  withFreshBinder noHint (TC HeapType) \h -> do
    let ty' = RefTy (Var $ binderName h) (sink ty)
    withFreshBinder hint ty' \b -> do
      let ref = binderName b
      hVar <- sinkM $ binderName h
      body' <- buildBlock $ body (sink hVar) $ sink ref
      return $ LamExpr (BinaryNest h b) body'

buildForAnn
  :: (Emits n, ScopableBuilder r m)
  => NameHint -> ForAnn -> IxType r n
  -> (forall l. (Emits l, DExt n l) => AtomName r l -> m l (Atom r l))
  -> m n (Atom r n)
buildForAnn hint ann (IxType iTy ixDict) body = do
  lam <- withFreshBinder hint iTy \b -> do
    let v = binderName b
    body' <- buildBlock $ body $ sink v
    return $ LamExpr (UnaryNest b) body'
  emitExpr $ Hof $ For ann ixDict lam

buildFor :: (Emits n, ScopableBuilder r m)
         => NameHint -> Direction -> IxType r n
         -> (forall l. (Emits l, DExt n l) => AtomName r l -> m l (Atom r l))
         -> m n (Atom r n)
buildFor hint dir ty body = buildForAnn hint dir ty body

buildMap :: (Emits n, ScopableBuilder r m)
         => Atom r n
         -> (forall l. (Emits l, DExt n l) => Atom r l -> m l (Atom r l))
         -> m n (Atom r n)
buildMap xs f = do
  TabTy (_:>ixTy) _ <- getType xs
  buildFor noHint Fwd ixTy \i ->
    tabApp (sink xs) (Var i) >>= f

unzipTab :: (Emits n, Builder r m) => Atom r n -> m n (Atom r n, Atom r n)
unzipTab tab = do
  fsts <- liftEmitBuilder $ buildMap tab getFst
  snds <- liftEmitBuilder $ buildMap tab getSnd
  return (fsts, snds)

emitRunWriter
  :: (Emits n, ScopableBuilder r m)
  => NameHint -> Type r n -> BaseMonoid r n
  -> (forall l. (Emits l, DExt n l) => AtomName r l -> AtomName r l -> m l (Atom r l))
  -> m n (Atom r n)
emitRunWriter hint accTy bm body = do
  lam <- buildEffLam hint accTy \h ref -> body h ref
  emitExpr $ Hof $ RunWriter Nothing bm lam

emitRunState
  :: (Emits n, ScopableBuilder r m)
  => NameHint -> Atom r n
  -> (forall l. (Emits l, DExt n l) => AtomName r l -> AtomName r l -> m l (Atom r l))
  -> m n (Atom r n)
emitRunState hint initVal body = do
  stateTy <- getType initVal
  lam <- buildEffLam hint stateTy \h ref -> body h ref
  emitExpr $ Hof $ RunState Nothing initVal lam

emitRunReader
  :: (Emits n, ScopableBuilder r m)
  => NameHint -> Atom r n
  -> (forall l. (Emits l, DExt n l) => AtomName r l -> AtomName r l -> m l (Atom r l))
  -> m n (Atom r n)
emitRunReader hint r body = do
  rTy <- getType r
  lam <- buildEffLam hint rTy \h ref -> body h ref
  emitExpr $ Hof $ RunReader r lam

-- === vector space (ish) type class ===

zeroAt :: (Emits n, SBuilder m) => SType n -> m n (SAtom n)
zeroAt ty = liftEmitBuilder $ go ty where
  go :: Emits n => SType n -> BuilderM SimpIR n (SAtom n)
  go = \case
   BaseTy bt  -> return $ Con $ Lit $ zeroLit bt
   ProdTy tys -> ProdVal <$> mapM go tys
   TabTy (b:>ixTy) bodyTy -> buildFor (getNameHint b) Fwd ixTy \i ->
     go =<< applyRename (b@>i) bodyTy
   _ -> unreachable
  zeroLit bt = case bt of
    Scalar Float64Type -> Float64Lit 0.0
    Scalar Float32Type -> Float32Lit 0.0
    _                  -> unreachable
  unreachable :: a
  unreachable = error $ "Missing zero case for a tangent type: " ++ pprint ty

zeroLike :: (HasType SimpIR e, SBuilder m, Emits n) => e n -> m n (SAtom n )
zeroLike x = zeroAt =<< getType x

tangentType :: EnvReader m => SType n -> m n (SType n)
tangentType ty = maybeTangentType ty >>= \case
  Just tanTy -> return tanTy
  Nothing -> error $ "can't differentiate wrt type: " ++ pprint ty

maybeTangentType :: (IRRep r, EnvReader m) => Type r n -> m n (Maybe (Type r n))
maybeTangentType ty = liftEnvReaderT $ maybeTangentType' ty

maybeTangentType' :: IRRep r => Type r n -> EnvReaderT Maybe n (Type r n)
maybeTangentType' ty = case ty of
  TabTy b bodyTy -> do
    refreshAbs (Abs b bodyTy) \b' bodyTy' -> do
      bodyTanTy <- rec bodyTy'
      return $ TabTy b' bodyTanTy
  TC con    -> case con of
    BaseType (Scalar Float64Type) -> return $ TC con
    BaseType (Scalar Float32Type) -> return $ TC con
    BaseType   _                  -> return $ UnitTy
    ProdType   tys                -> ProdTy <$> traverse rec tys
    _ -> empty
  _ -> empty
  where rec = maybeTangentType'

tangentBaseMonoidFor :: (Emits n, SBuilder m) => SType n -> m n (BaseMonoid SimpIR n)
tangentBaseMonoidFor ty = do
  zero <- zeroAt ty
  adder <- liftBuilder $ buildBinaryLamExpr (noHint, ty) (noHint, ty) \x y -> addTangent (Var x) (Var y)
  return $ BaseMonoid zero adder

addTangent :: (Emits n, SBuilder m) => SAtom n -> SAtom n -> m n (SAtom n)
addTangent x y = do
  getType x >>= \case
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

symbolicTangentTy :: (EnvReader m, Fallible1 m) => CType n -> m n (CType n)
symbolicTangentTy elTy = lookupSourceMap "SymbolicTangent" >>= \case
  Just (UTyConVar symTanName) -> do
    TyConBinding dataDefName _ <- lookupEnv symTanName
    return $ TypeCon "SymbolicTangent" dataDefName $
      DataDefParams [(PlainArrow, elTy)]
  Nothing -> throw UnboundVarErr $
    "Can't define a custom linearization with symbolic zeros: " ++
    "the SymbolicTangent type is not in scope."
  Just _ -> throw TypeErr "SymbolicTangent should name a `data` type"

symbolicTangentZero :: EnvReader m => SType n -> m n (SAtom n)
symbolicTangentZero argTy = return $ SumVal [UnitTy, argTy] 0 UnitVal

symbolicTangentNonZero :: EnvReader m => SAtom n -> m n (SType n)
symbolicTangentNonZero val = do
  ty <- getType val
  return $ SumVal [UnitTy, ty] 1 val

-- === builder versions of common top-level emissions ===

emitDataDef :: (Mut n, TopBuilder m) => DataDef n -> m n (DataDefName n)
emitDataDef dataDef@(DataDef sourceName _ _) =
  emitBinding hint $ DataDefBinding dataDef mempty
  where hint = getNameHint sourceName

updateFieldDefs :: (Mut n, TopBuilder m) => DataDefName n -> SourceName -> CAtom n -> m n ()
updateFieldDefs defName sourceName val =
  emitPartialTopEnvFrag $ mempty {fragFieldDefUpdates = toSnocList [(defName, sourceName, val)]}

emitEffectDef :: (Mut n, TopBuilder m) => EffectDef n -> m n (EffectName n)
emitEffectDef effectDef@(EffectDef name _) =
  emitBinding (getNameHint name) $ EffectBinding effectDef

emitHandlerDef :: (Mut n, TopBuilder m) => SourceName -> HandlerDef n -> m n (HandlerName n)
emitHandlerDef name handlerDef =
  emitBinding (getNameHint name) $ HandlerBinding handlerDef

emitEffectOpDef :: (Mut n, TopBuilder m) => EffectName n -> Int -> SourceName -> m n (Name EffectOpNameC n)
emitEffectOpDef effName i opName = do
  let hint = getNameHint opName
  let opDef = EffectOpDef effName (OpIdx i)
  emitBinding hint $ EffectOpBinding opDef

emitClassDef :: (Mut n, TopBuilder m) => ClassDef n -> m n (Name ClassNameC n)
emitClassDef classDef@(ClassDef name _ _ _ _) =
  emitBinding (getNameHint name) $ ClassBinding classDef

emitInstanceDef :: (Mut n, TopBuilder m) => InstanceDef n -> m n (Name InstanceNameC n)
emitInstanceDef instanceDef@(InstanceDef className _ _ _) = do
  emitBinding (getNameHint className) $ InstanceBinding instanceDef

emitDataConName :: (Mut n, TopBuilder m) => DataDefName n -> Int -> CAtom n -> m n (Name DataConNameC n)
emitDataConName dataDefName conIdx conAtom = do
  DataDef _ _ dataCons <- lookupDataDef dataDefName
  let (DataConDef name _ _ _) = dataCons !! conIdx
  emitBinding (getNameHint name) $ DataConBinding dataDefName conIdx conAtom

emitMethod
  :: (Mut n, TopBuilder m)
  => NameHint -> ClassName n -> [Bool] -> Int -> m n (Name MethodNameC n)
emitMethod hint classDef explicit idx = do
  getter <- makeMethodGetter classDef explicit idx
  f <- Var <$> emitTopLet hint PlainLet (Atom getter)
  emitBinding hint $ MethodBinding classDef idx f

makeMethodGetter :: EnvReader m => Name ClassNameC n -> [Bool] -> Int -> m n (CAtom n)
makeMethodGetter className explicit methodIdx = liftBuilder do
  className' <- sinkM className
  ClassDef sourceName _ paramBs _ _ <- getClassDef className'
  let arrows = explicit <&> \case True -> PlainArrow; False -> ImplicitArrow
  buildPureNaryLam arrows (EmptyAbs $ asPiBinders paramBs) \params -> do
    let dictTy = DictTy $ DictType sourceName (sink className') (map Var params)
    buildPureLam noHint ClassArrow dictTy \dict ->
      emitExpr $ ProjMethod (Var dict) methodIdx
  where
    asPiBinders :: Nest RolePiBinder i i' -> Nest CBinder i i'
    asPiBinders = fmapNest \(RolePiBinder b ty _ _) -> b:>ty

emitTyConName :: (Mut n, TopBuilder m) => DataDefName n -> CAtom n -> m n (Name TyConNameC n)
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

fLitLike :: (Builder r m, Emits n) => Double -> Atom r n -> m n (Atom r n)
fLitLike x t = do
  ty <- getType t
  case ty of
    BaseTy (Scalar Float64Type) -> return $ Con $ Lit $ Float64Lit x
    BaseTy (Scalar Float32Type) -> return $ Con $ Lit $ Float32Lit $ realToFrac x
    _ -> error "Expected a floating point scalar"

neg :: (Builder r m, Emits n) => Atom r n -> m n (Atom r n)
neg x = emitOp $ UnOp FNeg x

add :: (Builder r m, Emits n) => Atom r n -> Atom r n -> m n (Atom r n)
add x y = emitOp $ BinOp FAdd x y

-- TODO: Implement constant folding for fixed-width integer types as well!
iadd :: (Builder r m, Emits n) => Atom r n -> Atom r n -> m n (Atom r n)
iadd (Con (Lit l)) y | getIntLit l == 0 = return y
iadd x (Con (Lit l)) | getIntLit l == 0 = return x
iadd x@(Con (Lit _)) y@(Con (Lit _)) = return $ applyIntBinOp (+) x y
iadd x y = emitOp $ BinOp IAdd x y

mul :: (Builder r m, Emits n) => Atom r n -> Atom r n -> m n (Atom r n)
mul x y = emitOp $ BinOp FMul x y

imul :: (Builder r m, Emits n) => Atom r n -> Atom r n -> m n (Atom r n)
imul   (Con (Lit l)) y               | getIntLit l == 1 = return y
imul x                 (Con (Lit l)) | getIntLit l == 1 = return x
imul x@(Con (Lit _)) y@(Con (Lit _))                    = return $ applyIntBinOp (*) x y
imul x y = emitOp $ BinOp IMul x y

sub :: (Builder r m, Emits n) => Atom r n -> Atom r n -> m n (Atom r n)
sub x y = emitOp $ BinOp FSub x y

isub :: (Builder r m, Emits n) => Atom r n -> Atom r n -> m n (Atom r n)
isub x (Con (Lit l)) | getIntLit l == 0 = return x
isub x@(Con (Lit _)) y@(Con (Lit _)) = return $ applyIntBinOp (-) x y
isub x y = emitOp $ BinOp ISub x y

select :: (Builder r m, Emits n) => Atom r n -> Atom r n -> Atom r n -> m n (Atom r n)
select (Con (Lit (Word8Lit p))) x y = return $ if p /= 0 then x else y
select p x y = emitOp $ MiscOp $ Select p x y

div' :: (Builder r m, Emits n) => Atom r n -> Atom r n -> m n (Atom r n)
div' x y = emitOp $ BinOp FDiv x y

idiv :: (Builder r m, Emits n) => Atom r n -> Atom r n -> m n (Atom r n)
idiv x (Con (Lit l)) | getIntLit l == 1 = return x
idiv x@(Con (Lit _)) y@(Con (Lit _)) = return $ applyIntBinOp div x y
idiv x y = emitOp $ BinOp IDiv x y

irem :: (Builder r m, Emits n) => Atom r n -> Atom r n -> m n (Atom r n)
irem x y = emitOp $ BinOp IRem x y

fpow :: (Builder r m, Emits n) => Atom r n -> Atom r n -> m n (Atom r n)
fpow x y = emitOp $ BinOp FPow x y

flog :: (Builder r m, Emits n) => Atom r n -> m n (Atom r n)
flog x = emitOp $ UnOp Log x

ilt :: (Builder r m, Emits n) => Atom r n -> Atom r n -> m n (Atom r n)
ilt x@(Con (Lit _)) y@(Con (Lit _)) = return $ applyIntCmpOp (<) x y
ilt x y = emitOp $ BinOp (ICmp Less) x y

ieq :: (Builder r m, Emits n) => Atom r n -> Atom r n -> m n (Atom r n)
ieq x@(Con (Lit _)) y@(Con (Lit _)) = return $ applyIntCmpOp (==) x y
ieq x y = emitOp $ BinOp (ICmp Equal) x y

fromPair :: (Fallible1 m, EnvReader m, IRRep r) => Atom r n -> m n (Atom r n, Atom r n)
fromPair pair = do
  ~[x, y] <- getUnpacked pair
  return (x, y)

getProj :: (Builder r m, Emits n) => Int -> Atom r n -> m n (Atom r n)
getProj i x = do
  xs <- getUnpacked x
  return $ xs !! i

getFst :: Builder r m => Atom r n -> m n (Atom r n)
getFst p = fst <$> fromPair p

getSnd :: Builder r m => Atom r n -> m n (Atom r n)
getSnd p = snd <$> fromPair p

-- the rightmost index is applied first
getNaryProjRef :: (Builder r m, Emits n) => [Int] -> Atom r n -> m n (Atom r n)
getNaryProjRef [] ref = return ref
getNaryProjRef (i:is) ref = getProjRef i =<< getNaryProjRef is ref

getProjRef :: (Builder r m, Emits n) => Int -> Atom r n -> m n (Atom r n)
getProjRef i r = emitExpr $ RefOp r $ ProjRef i

-- XXX: getUnpacked must reduce its argument to enforce the invariant that
-- ProjectElt atoms are always fully reduced (to avoid type errors between two
-- equivalent types spelled differently).
getUnpacked :: (Fallible1 m, EnvReader m, IRRep r) => Atom r n -> m n [Atom r n]
getUnpacked atom = do
  atom' <- cheapNormalize atom
  ty <- getType atom'
  positions <- case ty of
    ProdTy tys  -> return $ void tys
    DepPairTy _ -> return [(), ()]
    _ -> error $ "not a product type: " ++ pprint ty
  forM (enumerate positions) \(i, _) ->
    normalizeProj (ProjectProduct i) atom'
{-# SCC getUnpacked #-}

emitUnpacked :: (Builder r m, Emits n) => Atom r n -> m n [AtomName r n]
emitUnpacked tup = do
  xs <- getUnpacked tup
  forM xs \x -> emit $ Atom x

unwrapNewtype :: CAtom n -> CAtom n
unwrapNewtype (NewtypeCon _ x) = x
unwrapNewtype x = ProjectElt UnwrapNewtype x
{-# INLINE unwrapNewtype #-}

app :: (CBuilder m, Emits n) => CAtom n -> CAtom n -> m n (CAtom n)
app x i = Var <$> emit (App x (i:|[]))

naryApp :: (CBuilder m, Emits n) => CAtom n -> [CAtom n] -> m n (CAtom n)
naryApp = naryAppHinted noHint
{-# INLINE naryApp #-}

naryTopApp :: (Builder SimpIR m, Emits n) => TopFunName n -> [SAtom n] -> m n (SAtom n)
naryTopApp f xs = emitExpr $ TopApp f xs
{-# INLINE naryTopApp #-}

naryTopAppInlined :: (Builder SimpIR m, Emits n) => TopFunName n -> [SAtom n] -> m n (SAtom n)
naryTopAppInlined f xs = do
  TopFunBinding f' <- lookupEnv f
  case f' of
    DexTopFun _ _ (LamExpr bs body) _ ->
      applySubst (bs@@>(SubstVal<$>xs)) body >>= emitBlock
    _ -> naryTopApp f xs
{-# INLINE naryTopAppInlined #-}

naryAppHinted :: (CBuilder m, Emits n)
  => NameHint -> CAtom n -> [CAtom n] -> m n (CAtom n)
naryAppHinted hint f xs = case nonEmpty xs of
  Nothing -> return f
  Just xs' -> Var <$> emitHinted hint (App f xs')

tabApp :: (Builder r m, Emits n) => Atom r n -> Atom r n -> m n (Atom r n)
tabApp x i = Var <$> emit (TabApp x (i:|[]))

naryTabApp :: (Builder r m, Emits n) => Atom r n -> [Atom r n] -> m n (Atom r n)
naryTabApp = naryTabAppHinted noHint
{-# INLINE naryTabApp #-}

naryTabAppHinted :: (Builder r m, Emits n)
  => NameHint -> Atom r n -> [Atom r n] -> m n (Atom r n)
naryTabAppHinted hint f xs = case nonEmpty xs of
  Nothing -> return f
  Just xs' -> Var <$> emitHinted hint (TabApp f xs')

indexRef :: (Builder r m, Emits n) => Atom r n -> Atom r n -> m n (Atom r n)
indexRef ref i = emitExpr $ RefOp ref $ IndexRef i

naryIndexRef :: (Builder r m, Emits n) => Atom r n -> [Atom r n] -> m n (Atom r n)
naryIndexRef ref is = foldM indexRef ref is

ptrOffset :: (Builder r m, Emits n) => Atom r n -> Atom r n -> m n (Atom r n)
ptrOffset x (IdxRepVal 0) = return x
ptrOffset x i = emitOp $ MemOp $ PtrOffset x i
{-# INLINE ptrOffset #-}

unsafePtrLoad :: (Builder r m, Emits n) => Atom r n -> m n (Atom r n)
unsafePtrLoad x = do
  body <- liftEmitBuilder $ buildBlock $ emitOp . MemOp . PtrLoad =<< sinkM x
  emitExpr $ Hof $ RunIO body

-- === index set type class ===

applyIxMethod :: (SBuilder m, Emits n) => IxDict SimpIR n -> IxMethod -> [SAtom n] -> m n (SAtom n)
applyIxMethod dict method args = case dict of
  -- These cases are use in SimpIR and they work with IdxRepVal
  IxDictRawFin n -> case method of
    Size              -> do []  <- return args; return n
    Ordinal           -> do [i] <- return args; return i
    UnsafeFromOrdinal -> do [i] <- return args; return i
  IxDictSpecialized _ d params -> do
    SpecializedDictBinding (SpecializedDict _ maybeFs) <- lookupEnv d
    Just fs <- return maybeFs
    LamExpr bs body <- return $ fs !! fromEnum method
    let args' = case method of
          Size -> params ++ [UnitVal]
          _    -> params ++ args
    emitBlock =<< applySubst (bs @@> fmap SubstVal args') body

unsafeFromOrdinal :: (SBuilder m, Emits n) => IxType SimpIR n -> Atom SimpIR n -> m n (Atom SimpIR n)
unsafeFromOrdinal (IxType _ dict) i = applyIxMethod dict UnsafeFromOrdinal [i]

ordinal :: (SBuilder m, Emits n) => IxType SimpIR n -> Atom SimpIR n -> m n (Atom SimpIR n)
ordinal (IxType _ dict) idx = applyIxMethod dict Ordinal [idx]

indexSetSize :: (SBuilder m, Emits n) => IxType SimpIR n -> m n (SAtom n)
indexSetSize (IxType _ dict) = applyIxMethod dict Size []

-- This works with `Nat` instead of `IndexRepTy` because it's used alongside
-- user-defined instances.
projectIxFinMethod :: EnvReader m => IxMethod -> CAtom n -> m n (CAtom n)
projectIxFinMethod method n = liftBuilder do
  case method of
    Size -> return n  -- result : Nat
    Ordinal -> buildPureLam noHint PlainArrow (NewtypeTyCon $ Fin n) \ix ->
      return $ unwrapNewtype (Var ix) -- result : Nat
    UnsafeFromOrdinal -> buildPureLam noHint PlainArrow NatTy \ix ->
      return $ NewtypeCon (FinCon $ sink n) (Var ix)

-- === core versions of index set type class ===

applyIxMethodCore :: (CBuilder m, Emits n) => IxDict CoreIR n -> IxMethod -> [CAtom n] -> m n (CAtom n)
applyIxMethodCore (IxDictAtom dict) method args = do
  methodImpl <- emitExpr $ ProjMethod dict $ fromEnum method
  naryApp methodImpl args
applyIxMethodCore _ _ _ = error "not implemented"

unsafeFromOrdinalCore :: (CBuilder m, Emits n) => IxType CoreIR n -> CAtom n -> m n (CAtom n)
unsafeFromOrdinalCore (IxType _ dict) i = applyIxMethodCore dict UnsafeFromOrdinal [i]

ordinalCore :: (CBuilder m, Emits n) => IxType CoreIR n -> CAtom n -> m n (CAtom n)
ordinalCore (IxType _ dict) idx = applyIxMethodCore dict Ordinal [idx]

indexSetSizeCore :: (CBuilder m, Emits n) => IxType CoreIR n -> m n (CAtom n)
indexSetSizeCore (IxType _ dict) = applyIxMethodCore dict Size []

-- === pseudo-prelude ===

-- Bool -> (Unit -> {|eff} a) -> (() -> {|eff} a) -> {|eff} a
-- XXX: the first argument is the true case, following the
-- surface-level `if ... then ... else ...`, but the order
-- is flipped in the actual `Case`, because False acts like 0.
-- TODO: consider a version that figures out the result type itself.
emitIf :: (Emits n, ScopableBuilder r m)
       => Atom r n
       -> Type r n
       -> (forall l. (Emits l, DExt n l) => m l (Atom r l))
       -> (forall l. (Emits l, DExt n l) => m l (Atom r l))
       -> m n (Atom r n)
emitIf predicate resultTy trueCase falseCase = do
  predicate' <- emitOp $ MiscOp $ ToEnum (SumTy [UnitTy, UnitTy]) predicate
  buildCase predicate' resultTy \i _ ->
    case i of
      0 -> falseCase
      1 -> trueCase
      _ -> error "should only have two cases"

emitMaybeCase :: (Emits n, ScopableBuilder r m)
              => Atom r n -> Type r n
              -> (forall l. (Emits l, DExt n l) =>             m l (Atom r l))
              -> (forall l. (Emits l, DExt n l) => Atom r l -> m l (Atom r l))
              -> m n (Atom r n)
emitMaybeCase scrut resultTy nothingCase justCase = do
  buildCase scrut resultTy \i v ->
    case i of
      0 -> nothingCase
      1 -> justCase v
      _ -> error "should be a binary scrutinee"

-- Maybe a -> a
fromJustE :: (Emits n, Builder r m) => Atom r n -> m n (Atom r n)
fromJustE x = liftEmitBuilder do
  MaybeTy a <- getType x
  emitMaybeCase x a
    (emitOp $ MiscOp $ ThrowError $ sink a)
    (return)

-- Maybe a -> Bool
isJustE :: (Emits n, Builder r m) => Atom r n -> m n (Atom r n)
isJustE x = liftEmitBuilder $
  emitMaybeCase x BoolTy (return FalseAtom) (\_ -> return TrueAtom)

-- Monoid a -> (n=>a) -> a
reduceE :: (Emits n, Builder r m) => BaseMonoid r n -> Atom r n -> m n (Atom r n)
reduceE monoid xs = liftEmitBuilder do
  TabTy (n:>ty) a <- getType xs
  a' <- return $ ignoreHoistFailure $ hoist n a
  getSnd =<< emitRunWriter noHint a' monoid \_ ref ->
    buildFor noHint Fwd (sink ty) \i -> do
      x <- tabApp (sink xs) (Var i)
      emitExpr $ RefOp (sink $ Var ref) $ MExtend (sink monoid) x

andMonoid :: (EnvReader m, IRRep r) => m n (BaseMonoid r n)
andMonoid = liftM (BaseMonoid TrueAtom) $ liftBuilder $
  buildBinaryLamExpr (noHint, BoolTy) (noHint, BoolTy) \x y ->
    emitOp $ BinOp BAnd (sink $ Var x) (Var y)

-- (a-> {|eff} b) -> n=>a -> {|eff} (n=>b)
mapE :: (Emits n, ScopableBuilder r m)
     => (forall l. (Emits l, DExt n l) => Atom r l -> m l (Atom r l))
     -> Atom r n -> m n (Atom r n)
mapE f xs = do
  TabTy (n:>ty) _ <- getType xs
  buildFor (getNameHint n) Fwd ty \i -> do
    x <- tabApp (sink xs) (Var i)
    f x

-- (n:Type) ?-> (a:Type) ?-> (xs : n=>Maybe a) : Maybe (n => a) =
catMaybesE :: (Emits n, Builder r m) => Atom r n -> m n (Atom r n)
catMaybesE maybes = do
  TabTy n (MaybeTy a) <- getType maybes
  justs <- liftEmitBuilder $ mapE isJustE maybes
  monoid <- andMonoid
  allJust <- reduceE monoid justs
  liftEmitBuilder $ emitIf allJust (MaybeTy $ TabTy n a)
    (JustAtom (sink $ TabTy n a) <$> mapE fromJustE (sink maybes))
    (return (NothingAtom $ sink $ TabTy n a))

emitWhile :: (Emits n, ScopableBuilder r m)
          => (forall l. (Emits l, DExt n l) => m l (Atom r l))
          -> m n ()
emitWhile cont = do
  body <- buildBlock cont
  void $ emit $ Hof $ While body

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

runMaybeWhile :: (Emits n, ScopableBuilder r m)
              => (forall l. (Emits l, DExt n l) => m l (Atom r l))
              -> m n (Atom r n)
runMaybeWhile body = do
  hadError <- getSnd =<< emitRunState noHint FalseAtom \_ ref -> do
    emitWhile do
      ans <- body
      emitMaybeCase ans Word8Ty
        (emit (RefOp (sink $ Var ref) $ MPut TrueAtom) >> return FalseAtom)
        (return)
    return UnitVal
  emitIf hadError (MaybeTy UnitTy)
    (return $ NothingAtom UnitTy)
    (return $ JustAtom    UnitTy UnitVal)

-- === capturing closures with telescopes ===

type ReconAbs r e = Abs (ReconBinders r) e

data ReconBinders r n l = ReconBinders
  (TelescopeType (AtomNameC r) (Type r) n)
  (Nest (NameBinder (AtomNameC r)) n l)

data TelescopeType c e n =
   DepTelescope (TelescopeType c e n) (Abs (BinderP c e) (TelescopeType c e) n)
 | ProdTelescope [e n]

instance IRRep r => GenericB (ReconBinders r) where
  type RepB (ReconBinders r) =
    PairB (LiftB (TelescopeType (AtomNameC r) (Type r)))
          (Nest (NameBinder (AtomNameC r)))
  fromB (ReconBinders x y) = PairB (LiftB x) y
  {-# INLINE fromB #-}
  toB (PairB (LiftB x) y) = ReconBinders x y
  {-# INLINE toB #-}

instance IRRep r => BindsNameList (ReconBinders r) (AtomNameC r) where
  bindNameList (ReconBinders _ bs) = bindNameList bs

instance Pretty (ReconBinders r n l) where
  pretty (ReconBinders _ ab) = pretty ab

instance IRRep r => RenameB    (ReconBinders r)
instance IRRep r => SinkableB  (ReconBinders r)
instance IRRep r => ProvesExt  (ReconBinders r)
instance IRRep r => BindsNames (ReconBinders r)
instance IRRep r => HoistableB (ReconBinders r)

instance GenericE (TelescopeType c e) where
  type RepE (TelescopeType c e) = EitherE
         (PairE (TelescopeType c e) (Abs (BinderP c e) (TelescopeType c e)))
         (ListE e)
  fromE (DepTelescope lhs ab) = LeftE (PairE lhs ab)
  fromE (ProdTelescope tys)   = RightE (ListE tys)
  {-# INLINE fromE #-}
  toE (LeftE (PairE lhs ab)) = DepTelescope lhs ab
  toE (RightE (ListE tys))   = ProdTelescope tys
  {-# INLINE toE #-}

instance (Color c, SinkableE e) => SinkableE (TelescopeType c e)
instance (Color c, SinkableE e, RenameE e) => RenameE (TelescopeType c e)
instance (Color c, ToBinding e c, SubstE AtomSubstVal e) => SubstE AtomSubstVal (TelescopeType c e)
instance (Color c, HoistableE e) => HoistableE (TelescopeType c e)

telescopicCapture
  :: (EnvReader m, HoistableE e, HoistableB b, IRRep r)
  => b n l -> e l -> m l (Atom r l, ReconAbs r e n)
telescopicCapture bs e = do
  vs <- localVarsAndTypeVars bs e
  vTys <- mapM (getType . Var) vs
  let vsTysSorted = toposortAnnVars $ zip vs vTys
  let vsSorted = map fst vsTysSorted
  ty <- liftEnvReaderM $ buildTelescopeTy vsTysSorted
  result <- buildTelescopeVal (map Var vsSorted) ty
  reconAbs <- return $ ignoreHoistFailure $ hoist bs do
    case abstractFreeVarsNoAnn vsSorted e of
      Abs bs' e' -> Abs (ReconBinders ty bs') e'
  return (result, reconAbs)

applyReconAbs
  :: (EnvReader m, Fallible1 m, SinkableE e, SubstE AtomSubstVal e, IRRep r)
  => ReconAbs r e n -> Atom r n -> m n (e n)
applyReconAbs (Abs bs result) x = do
  xs <- unpackTelescope bs x
  applySubst (bs @@> map SubstVal xs) result

buildTelescopeTy
  :: (EnvReader m, EnvExtender m, Color c, HoistableE e)
  => [AnnVar c e n] -> m n (TelescopeType c e n)
buildTelescopeTy [] = return (ProdTelescope [])
buildTelescopeTy ((v,ty):xs) = do
  rhs <- buildTelescopeTy xs
  Abs b rhs' <- return $ abstractFreeVar v rhs
  case hoist b rhs' of
    HoistSuccess rhs'' -> return $ prependTelescopeTy ty rhs''
    HoistFailure _ -> return $ DepTelescope (ProdTelescope []) (Abs (b:>ty) rhs')

prependTelescopeTy :: e n -> TelescopeType c e n -> TelescopeType c e n
prependTelescopeTy x = \case
  DepTelescope lhs rhs -> DepTelescope (prependTelescopeTy x lhs) rhs
  ProdTelescope xs -> ProdTelescope (x:xs)

buildTelescopeVal
  :: (EnvReader m, IRRep r) => [Atom r n]
  -> TelescopeType (AtomNameC r) (Type r) n -> m n (Atom r n)
buildTelescopeVal xsTop tyTop = fst <$> go tyTop xsTop where
  go :: (EnvReader m, IRRep r)
     => TelescopeType (AtomNameC r) (Type r) n ->  [Atom r n]
     -> m n (Atom r n, [Atom r n])
  go ty rest = case ty of
    ProdTelescope tys -> do
      (xs, rest') <- return $ splitAt (length tys) rest
      return (ProdVal xs, rest')
    DepTelescope ty1 (Abs b ty2) -> do
      (x1, ~(xDep : rest')) <- go ty1 rest
      ty2' <- applySubst (b@>SubstVal xDep) ty2
      (x2, rest'') <- go ty2' rest'
      let depPairTy = DepPairType b (telescopeTypeType ty2)
      return (PairVal x1 (DepPair xDep x2 depPairTy), rest'')

telescopeTypeType :: TelescopeType (AtomNameC r) (Type r) n -> Type r n
telescopeTypeType (ProdTelescope tys) = ProdTy tys
telescopeTypeType (DepTelescope lhs (Abs b rhs)) = do
  let lhs' = telescopeTypeType lhs
  let rhs' = DepPairTy (DepPairType b (telescopeTypeType rhs))
  PairTy lhs' rhs'

unpackTelescope
  :: (Fallible1 m, EnvReader m, IRRep r)
  => ReconBinders r l1 l2 -> Atom r n -> m n [Atom r n]
unpackTelescope (ReconBinders tyTop _) xTop = go tyTop xTop where
  go :: (Fallible1 m, EnvReader m, IRRep r)
     => TelescopeType c e l-> Atom r n -> m n [Atom r n]
  go ty x = case ty of
    ProdTelescope _ -> getUnpacked x
    DepTelescope ty1 (Abs _  ty2) -> do
      (x1, xPair) <- fromPair x
      (xDep, x2) <- fromPair xPair
      xs1 <- go ty1 x1
      xs2 <- go ty2 x2
      return $ xs1 ++ (xDep : xs2)

-- sorts name-annotation pairs so that earlier names may be occur free in later
-- annotations but not vice versa.
type AnnVar c e n = (Name c n, e n)
toposortAnnVars :: forall e c n.  (Color c, HoistableE e) => [AnnVar c e n] -> [AnnVar c e n]
toposortAnnVars annVars =
  let (graph, vertexToNode, _) = graphFromEdges $ map annVarToNode annVars
  in map (nodeToAnnVar . vertexToNode) $ reverse $ topSort graph
  where
    annVarToNode :: (Name c n, e n) -> (e n, Name c n, [Name c n])
    annVarToNode (v, ann) = (ann, v, nameSetToList $ freeVarsE ann)

    nodeToAnnVar :: (e n, Name c n, [Name c n]) -> (Name c n, e n)
    nodeToAnnVar (ann, v, _) = (v, ann)

-- gives a list of atom names that are free in `e`, including names mentioned in
-- the types of those names, recursively.
localVarsAndTypeVars
  :: forall m b e n l r.
     (EnvReader m, BindsNames b, HoistableE e, IRRep r)
  => b n l -> e l -> m l [AtomName r l]
localVarsAndTypeVars b e =
  transitiveClosureM varsViaType (localVars b e)
  where
    varsViaType :: AtomName r l -> m l [AtomName r l]
    varsViaType v = do
      ty <- getType $ Var v
      return $ localVars b ty

localVars :: (Color c, BindsNames b, HoistableE e) => b n l -> e l -> [Name c l]
localVars b e = nameSetToList $
  R.intersection (toNameSet (toScopeFrag b)) (freeVarsE e)

-- See Note [Confuse GHC] from Simplify.hs
-- (we use a Builder-specific name to avoid collisions, since we export everything from Builder)
confuseGHCBuilder :: IRRep r => BuilderM r n (DistinctEvidence n)
confuseGHCBuilder = getDistinct
{-# INLINE confuseGHCBuilder #-}

-- === Helpers for function evaluation over fixed-width types ===

applyIntBinOp' :: (forall a. (Eq a, Ord a, Num a, Integral a)
               => (a -> Atom r n) -> a -> a -> Atom r n) -> Atom r n -> Atom r n -> Atom r n
applyIntBinOp' f x y = case (x, y) of
  (Con (Lit (Int64Lit xv)), Con (Lit (Int64Lit yv))) -> f (Con . Lit . Int64Lit) xv yv
  (Con (Lit (Int32Lit xv)), Con (Lit (Int32Lit yv))) -> f (Con . Lit . Int32Lit) xv yv
  (Con (Lit (Word8Lit xv)), Con (Lit (Word8Lit yv))) -> f (Con . Lit . Word8Lit) xv yv
  (Con (Lit (Word32Lit xv)), Con (Lit (Word32Lit yv))) -> f (Con . Lit . Word32Lit) xv yv
  (Con (Lit (Word64Lit xv)), Con (Lit (Word64Lit yv))) -> f (Con . Lit . Word64Lit) xv yv
  _ -> error "Expected integer atoms"

applyIntBinOp :: (forall a. (Num a, Integral a) => a -> a -> a) -> Atom r n -> Atom r n -> Atom r n
applyIntBinOp f x y = applyIntBinOp' (\w -> w ... f) x y

applyIntCmpOp :: (forall a. (Eq a, Ord a) => a -> a -> Bool) -> Atom r n -> Atom r n -> Atom r n
applyIntCmpOp f x y = applyIntBinOp' (\_ -> (Con . Lit . Word8Lit . fromIntegral . fromEnum) ... f) x y

applyFloatBinOp :: (forall a. (Num a, Fractional a) => a -> a -> a) -> Atom r n -> Atom r n -> Atom r n
applyFloatBinOp f x y = case (x, y) of
  (Con (Lit (Float64Lit xv)), Con (Lit (Float64Lit yv))) -> Con $ Lit $ Float64Lit $ f xv yv
  (Con (Lit (Float32Lit xv)), Con (Lit (Float32Lit yv))) -> Con $ Lit $ Float32Lit $ f xv yv
  _ -> error "Expected float atoms"

_applyFloatUnOp :: (forall a. (Num a, Fractional a) => a -> a) -> Atom r n -> Atom r n
_applyFloatUnOp f x = applyFloatBinOp (\_ -> f) (error "shouldn't be needed") x

-- === singleton types ===

-- The following implementation should be valid:
--   isSingletonType :: EnvReader m => Type n -> m n Bool
--   isSingletonType ty =
--     singletonTypeVal ty >>= \case
--       Nothing -> return False
--       Just _  -> return True
-- But a separate implementation doesn't have to go under binders,
-- because it doesn't have to reconstruct the singleton value (which
-- may be type annotated and whose type may refer to names).

isSingletonType :: Type SimpIR n -> Bool
isSingletonType topTy = isJust $ checkIsSingleton topTy
  where
    checkIsSingleton :: Type r n -> Maybe ()
    checkIsSingleton ty = case ty of
      TabPi (TabPiType _ body) -> checkIsSingleton body
      TC (ProdType tys) -> mapM_ checkIsSingleton tys
      _ -> Nothing

singletonTypeVal :: (SBuilder m, Emits n) => Type SimpIR n -> m n (Maybe (Atom SimpIR n))
singletonTypeVal ty = do
  maybeBlock <- liftBuilderT $ buildBlock do
    ty' <- sinkM ty
    runSubstReaderT idSubst $ singletonTypeValRec ty'
  mapM emitBlock maybeBlock
{-# INLINE singletonTypeVal #-}

-- TODO: TypeCon with a single case?
singletonTypeValRec
  :: Emits o => Type SimpIR i
  -> SubstReaderT Name (BuilderT SimpIR Maybe) i o (Atom SimpIR o)
singletonTypeValRec ty = case ty of
  TabPi (TabPiType (b:>ixTy) body) -> do
    ixTy' <- renameM ixTy
    buildFor (getNameHint b) Fwd ixTy' \i ->
      extendSubst (b@>i) (singletonTypeValRec body)
  TC con -> case con of
    ProdType tys -> ProdVal <$> traverse singletonTypeValRec tys
    _            -> notASingleton
  _ -> notASingleton
  where notASingleton = fail "not a singleton type"
