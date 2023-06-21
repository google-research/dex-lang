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
import Data.Graph (graphFromEdges, topSort)
import Data.List (elemIndex)
import Data.Text.Prettyprint.Doc (Pretty (..), group, line, nest)
import Foreign.Ptr

import qualified Unsafe.Coerce as TrulyUnsafe

import Control.Category ((>>>))
import Core
import Data.Functor ((<&>))
import Err
import IRVariants
import MTL1
import Subst
import Name
import PPrint (prettyBlock)
import QueryTypePure
import Types.Core
import Types.Imp
import Types.Primitives
import Types.Source
import Util (enumerate, transitiveClosureM, bindM2, toSnocList, (...))
import Visitor

-- === Ordinary (local) builder class ===

class (EnvReader m, EnvExtender m, Fallible1 m, IRRep r)
      => Builder (r::IR) (m::MonadKind1) | m -> r where
  rawEmitDecl :: Emits n => NameHint -> LetAnn -> Expr r n -> m n (AtomVar r n)

class Builder r m => ScopableBuilder (r::IR) (m::MonadKind1) | m -> r where
  buildScoped
    :: SinkableE e
    => (forall l. (Emits l, DExt n l) => m l (e l))
    -> m n (WithDecls r e n)

type SBuilder = Builder SimpIR
type CBuilder = Builder CoreIR

type Builder2         (r::IR) (m :: MonadKind2) = forall i. Builder         r (m i)
type ScopableBuilder2 (r::IR) (m :: MonadKind2) = forall i. ScopableBuilder r (m i)

emitDecl :: (Builder r m, Emits n) => NameHint -> LetAnn -> Expr r n -> m n (AtomVar r n)
emitDecl _ _ (Atom (Var n)) = return n
emitDecl hint ann expr = rawEmitDecl hint ann expr
{-# INLINE emitDecl #-}

emit :: (Builder r m, Emits n) => Expr r n -> m n (AtomVar r n)
emit expr = emitDecl noHint PlainLet expr
{-# INLINE emit #-}

emitHinted :: (Builder r m, Emits n) => NameHint -> Expr r n -> m n (AtomVar r n)
emitHinted hint expr = emitDecl hint PlainLet expr
{-# INLINE emitHinted #-}

emitOp :: (Builder r m, IsPrimOp e, Emits n) => e r n -> m n (Atom r n)
emitOp op = Var <$> emit (PrimOp $ toPrimOp op)
{-# INLINE emitOp #-}

emitExpr :: (Builder r m, Emits n) => Expr r n -> m n (Atom r n)
emitExpr expr = Var <$> emit expr
{-# INLINE emitExpr #-}

emitHof :: (Builder r m, Emits n) => Hof r n -> m n (Atom r n)
emitHof hof = mkTypedHof hof >>= emitOp

mkTypedHof :: (EnvReader m, IRRep r) => Hof r n -> m n (TypedHof r n)
mkTypedHof hof = do
  effTy <- effTyOfHof hof
  return $ TypedHof effTy hof

emitUnOp :: (Builder r m, Emits n) => UnOp -> Atom r n -> m n (Atom r n)
emitUnOp op x = emitOp $ UnOp op x
{-# INLINE emitUnOp #-}

emitBlock :: (Builder r m, Emits n) => Block r n -> m n (Atom r n)
emitBlock (Block _ decls result) = emitDecls $ Abs decls result

emitDecls :: (Builder r m, Emits n, RenameE e, SinkableE e)
          => WithDecls r e n -> m n (e n)
emitDecls (Abs decls result) = runSubstReaderT idSubst $ emitDecls' decls result

emitDecls' :: (Builder r m, Emits o, RenameE e, SinkableE e)
           => Nest (Decl r) i i' -> e i' -> SubstReaderT Name m i o (e o)
emitDecls' Empty e = renameM e
emitDecls' (Nest (Let b (DeclBinding ann expr)) rest) e = do
  expr' <- renameM expr
  AtomVar v _ <- emitDecl (getNameHint b) ann expr'
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
    let topFrag = TopEnvFrag (toEnvFrag b') mempty mempty
    return $ Abs topFrag $ binderName b'
  emitEnv ab

updateTopEnv :: TopBuilder m => TopEnvUpdate n -> m n ()
updateTopEnv update = emitNamelessEnv $ TopEnvFrag emptyOutFrag mempty (toSnocList [update])

emitLocalModuleEnv :: TopBuilder m => ModuleEnv n -> m n ()
emitLocalModuleEnv env = emitNamelessEnv $ TopEnvFrag emptyOutFrag env mempty

emitTopLet :: (Mut n, TopBuilder m) => NameHint -> LetAnn -> Expr CoreIR n -> m n (AtomVar CoreIR n)
emitTopLet hint letAnn expr = do
  ty <- return $ getType expr
  v <- emitBinding hint $ AtomNameBinding $ LetBound (DeclBinding letAnn expr)
  return $ AtomVar v ty

emitTopFunBinding :: (Mut n, TopBuilder m) => NameHint -> TopFunDef n -> LamExpr SimpIR n -> m n (TopFunName n)
emitTopFunBinding hint def f = do
  ty <- return $ getLamExprType f
  emitBinding hint $ TopFunBinding $ DexTopFun def ty f Waiting

emitSourceMap :: TopBuilder m => SourceMap n -> m n ()
emitSourceMap sm = emitLocalModuleEnv $ mempty {envSourceMap = sm}

emitSynthCandidates :: TopBuilder m => SynthCandidates n -> m n ()
emitSynthCandidates sc = emitLocalModuleEnv $ mempty {envSynthCandidates = sc}

addInstanceSynthCandidate :: TopBuilder m => ClassName n -> InstanceName n -> m n ()
addInstanceSynthCandidate className instanceName =
  emitSynthCandidates $ SynthCandidates [] (M.singleton className [instanceName])

updateTransposeRelation :: (Mut n, TopBuilder m) => TopFunName n -> TopFunName n -> m n ()
updateTransposeRelation f1 f2 =
  updateTopEnv $ ExtendCache $ mempty { transpositionCache = eMapSingleton f1 f2 <> eMapSingleton f2 f1}

lookupLoadedModule:: EnvReader m => ModuleSourceName -> m n (Maybe (ModuleName n))
lookupLoadedModule name = do
  loadedModules <- withEnv $ envLoadedModules . topEnv
  return $ M.lookup name $ fromLoadedModules loadedModules

lookupLoadedObject :: EnvReader m => FunObjCodeName n -> m n (Maybe NativeFunction)
lookupLoadedObject name = do
  loadedObjects <- withEnv $ envLoadedObjects . topEnv
  return $ M.lookup name $ fromLoadedObjects loadedObjects

extendSpecializationCache :: TopBuilder m => SpecializationSpec n -> TopFunName n -> m n ()
extendSpecializationCache specialization f =
  updateTopEnv $ ExtendCache $ mempty { specializationCache = eMapSingleton specialization f }

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
  updateTopEnv $ ExtendCache $ mempty { linearizationCache = eMapSingleton s (toPairE fs) }

queryObjCache :: EnvReader m => TopFunName n -> m n (Maybe (FunObjCodeName n))
queryObjCache v = lookupEnv v >>= \case
  TopFunBinding (DexTopFun _ _ _ (Finished impl)) -> return $ Just $ topFunObjCode impl
  _ -> return Nothing

emitObjFile :: (Mut n, TopBuilder m) => CFunction n -> m n (FunObjCodeName n)
emitObjFile fun@CFunction{nameHint} = do
  emitBinding nameHint $ FunObjCodeBinding fun

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
      return $ Abs (TopEnvFrag (toEnvFrag b') mempty mempty) v'
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
  emitDecls $ Abs (unsafeCoerceB $ unRNest decls) result

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
    ty <- return $ getType expr
    v <- BuilderT $ freshExtendSubInplaceT hint \b ->
           (BuilderDeclEmission $ Let b $ DeclBinding ann expr, binderName b)
    return $ AtomVar v ty
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
  -> m n (WithDecls r (Block r) n)
buildBlock cont = buildScoped (cont >>= withType) >>= computeAbsEffects >>= absToBlock

buildBlockWithType
  :: ScopableBuilder r m
  => EffTy r n
  -> (forall l. (Emits l, DExt n l) => m l (Atom r l))
  -> m n (Block r n)
buildBlockWithType effTy cont = do
  Abs decls result <- buildScoped cont
  return $ Block (BlockAnn effTy) decls result

withType :: ((EnvReader m, IRRep r), HasType r e) => e l -> m l ((e `PairE` Type r) l)
withType e = return $ e `PairE` getType e
{-# INLINE withType #-}

makeBlock :: IRRep r => Nest (Decl r) n l -> EffectRow r l -> Atom r l -> Type r l -> Block r n
makeBlock decls effs atom ty = Block (BlockAnn (EffTy effs' ty')) decls atom where
  ty' = ignoreHoistFailure $ hoist decls ty
  effs' = ignoreHoistFailure $ hoist decls effs
{-# INLINE makeBlock #-}

absToBlock
  :: (Fallible m, IRRep r)
  => Abs (Nest (Decl r)) (EffectRow r `PairE` (Atom r `PairE` Type r)) n -> m (WithDecls r (Block r) n)
absToBlock (Abs decls (effs `PairE` (result `PairE` ty))) = undefined
-- TODO: figure out how to compute the possibly-decl-containing type
-- absToBlock (Abs decls (effs `PairE` (result `PairE` ty))) = do
--   let msg = "Block:" <> nest 1 (prettyBlock decls result) <> line
--             <> group ("Of type:" <> nest 2 (line <> pretty ty)) <> line
--             <> group ("With effects:" <> nest 2 (line <> pretty effs))
--   ty' <- liftHoistExcept' (docAsStr msg) $ hoist decls ty
--   effs' <- liftHoistExcept' (docAsStr msg) $ hoist decls effs
--   return $ Block (BlockAnn (EffTy effs' ty')) decls result
-- {-# INLINE absToBlock #-}

makeBlockFromDecls :: (EnvReader m, IRRep r) => Abs (Nest (Decl r)) (Atom r) n -> m n (WithDecls r (Block r) n)
makeBlockFromDecls (Abs Empty result) = undefined
-- makeBlockFromDecls (Abs Empty result) = return $ AtomicBlock result
-- makeBlockFromDecls ab = liftEnvReaderM $ refreshAbs ab \decls result -> do
--   ty <- return $ getType result
--   effs <- declNestEffects decls
--   PairE ty' effs' <- return $ ignoreHoistFailure $ hoist decls $ PairE ty effs
--   return $ Block (BlockAnn (EffTy effs' ty')) decls result
-- {-# INLINE makeBlockFromDecls #-}

buildCoreLam
  :: ScopableBuilder CoreIR m
  => CorePiType n
  -> (forall l. (Emits l, DExt n l) => [CAtomVar l] -> m l (CAtom l))
  -> m n (CoreLamExpr n)
buildCoreLam piTy@(CorePiType _ bs _) cont = do
  lam <- buildLamExpr (EmptyAbs $ fmapNest withoutExpl bs) cont
  return $ CoreLamExpr piTy lam

varsAsBinderNest :: (EnvReader m, IRRep r) => [AtomVar r n] -> m n (EmptyAbs (Nest (Binder r)) n)
varsAsBinderNest [] = return $ EmptyAbs Empty
varsAsBinderNest (v:vs) = do
  rest <- varsAsBinderNest vs
  ty <- return $ getType v
  let AtomVar v' _ = v
  Abs b (Abs bs UnitE) <- return $ abstractFreeVar v' rest
  return $ EmptyAbs (Nest (b:>ty) bs)

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

buildUnaryLamExpr
  :: (ScopableBuilder r m)
  => NameHint -> Type r n
  -> (forall l. (Emits l, Distinct l, DExt n l) => AtomVar r l -> m l (Atom r l))
  -> m n (LamExpr r n)
buildUnaryLamExpr hint ty cont = do
  bs <- withFreshBinder hint ty \b -> return $ EmptyAbs (UnaryNest (BD b Empty))
  buildLamExpr bs \[v] -> cont v

buildBinaryLamExpr
  :: (ScopableBuilder r m)
  => (NameHint, Type r n) -> (NameHint, Type r n)
  -> (forall l. (Emits l, Distinct l, DExt n l) => AtomVar r l -> AtomVar r l -> m l (Atom r l))
  -> m n (LamExpr r n)
buildBinaryLamExpr (h1,t1) (h2,t2) cont = do
  bs <- withFreshBinder h1 t1 \b1 -> withFreshBinder h2 (sink t2) \b2 ->
    return $ EmptyAbs $ BinaryNest (BD b1 Empty) (BD b2 Empty)
  buildLamExpr bs \[v1, v2] -> cont v1 v2

buildLamExpr
  :: ScopableBuilder r m
  => (EmptyAbs (Nest (BinderAndDecls r)) n)
  -> (forall l. (Emits l, Distinct l, DExt n l) => [AtomVar r l] -> m l (Atom r l))
  -> m n (LamExpr r n)
buildLamExpr (Abs bs UnitE) cont = undefined -- TODO: how to handle substitution
-- buildLamExpr (Abs bs UnitE) cont = case bs of
--   Empty -> LamExpr Empty <$> buildBlock (cont [])
--   Nest b rest -> do
--     Abs b' (LamExpr bs' body') <- buildAbs (getNameHint b) (binderType b) \v -> do
--       rest' <- applySubst (b@>SubstVal (Var v)) $ EmptyAbs rest
--       buildLamExpr rest' \vs -> cont $ sink v : vs
--     return $ LamExpr (Nest b' bs') body'

buildLamExprFromPi
  :: ScopableBuilder r m
  => PiType r n
  -> (forall l. (Emits l, Distinct l, DExt n l) => [AtomVar r l] -> m l (Atom r l))
  -> m n (LamExpr r n)
buildLamExprFromPi (PiType bs _) cont = buildLamExpr (EmptyAbs bs) cont

buildAlt
  :: ScopableBuilder r m
  => Type r n
  -> (forall l. (Distinct l, Emits l, DExt n l) => AtomVar r l -> m l (Atom r l))
  -> m n (Alt r n)
buildAlt ty body = do
  withFreshBinder noHint ty \b -> do
    Abs decls body <- buildBlock do
      Distinct <- getDistinct
      body $ sink $ binderVar b
    return $ Abs (BD b decls) body

buildCaseAlts :: (Emits n, ScopableBuilder r m)
  => Atom r n
  -> (forall l. DExt n l => Int -> Binder r n l -> m l a)
  -> m n [a]
buildCaseAlts scrut indexedAltBody = do
  scrutTy <- return $ getType scrut
  altBinderTys <- caseAltsBinderTys scrutTy
  forM (enumerate altBinderTys) \(i, bTy) -> do
    withFreshBinder noHint bTy \b ->
      indexedAltBody i b

injectAltResult :: EnvReader m => [SType n] -> Int -> Alt SimpIR n -> m n (Alt SimpIR n)
injectAltResult sumTys con (Abs b body) = liftBuilder do
  buildAlt (binderType b) \v -> do
    originalResult <- emitBlock =<< betaReduce b (Var v) body
    (dataResult, nonDataResult) <- fromPair originalResult
    return $ PairVal dataResult $ Con $ SumCon (sinkList sumTys) con nonDataResult

-- TODO: consider a version with nonempty list of alternatives where we figure
-- out the result type from one of the alts rather than providing it explicitly
buildCase' :: (Emits n, ScopableBuilder r m)
  => Atom r n -> Type r n
  -> (forall l. (Emits l, DExt n l) => Int -> Atom r l -> m l (Atom r l))
  -> m n (Expr r n)
buildCase' scrut resultTy indexedAltBody = undefined
-- buildCase' scrut resultTy indexedAltBody = do
--   case trySelectBranch scrut of
--     Just (i, arg) -> do
--       Distinct <- getDistinct
--       Atom <$> indexedAltBody i (sink arg)
--     Nothing -> do
--       scrutTy <- return $ getType scrut
--       altBinderTys <- caseAltsBinderTys scrutTy
--       (alts, effs) <- unzip <$> forM (enumerate altBinderTys) \(i, bTy) -> do
--         (Abs b' (body `PairE` eff')) <- buildAbs noHint bTy \x -> do
--           blk <- buildBlock $ indexedAltBody i $ Var $ sink x
--           eff <- return $ getEffects blk
--           return $ blk `PairE` eff
--         return (Abs b' body, ignoreHoistFailure $ hoist b' eff')
--       return $ Case scrut alts $ EffTy (mconcat effs) resultTy

buildCase :: (Emits n, ScopableBuilder r m)
  => Atom r n -> Type r n
  -> (forall l. (Emits l, DExt n l) => Int -> Atom r l -> m l (Atom r l))
  -> m n (Atom r n)
buildCase s r b = emitExprToAtom =<< buildCase' s r b

buildEffLam
  :: ScopableBuilder r m
  => NameHint -> Type r n
  -> (forall l. (Emits l, DExt n l) => AtomVar r l -> AtomVar r l -> m l (Atom r l))
  -> m n (LamExpr r n)
buildEffLam hint ty body = do
  withFreshBinder noHint (TC HeapType) \h -> do
    let ty' = RefTy (Var $ binderVar h) (sink ty)
    withFreshBinder hint ty' \b -> do
      let ref = binderVar b
      hVar <- sinkM $ binderVar h
      body' <- buildBlock $ body (sink hVar) $ sink ref
      return $ makeLamExpr (BinaryNest (BD h Empty) (BD b Empty)) body'

buildForAnn
  :: (Emits n, ScopableBuilder r m)
  => NameHint -> ForAnn -> IxType r n
  -> (forall l. (Emits l, DExt n l) => AtomVar r l -> m l (Atom r l))
  -> m n (Atom r n)
buildForAnn hint ann (IxType iTy ixDict) body = do
  lam <- withFreshBinder hint iTy \b -> do
    let v = binderVar b
    body' <- buildBlock $ body $ sink v
    return $ makeLamExpr (UnaryNest (BD b Empty)) body'
  emitHof $ For ann (IxType iTy ixDict) lam

buildFor :: (Emits n, ScopableBuilder r m)
         => NameHint -> Direction -> IxType r n
         -> (forall l. (Emits l, DExt n l) => AtomVar r l -> m l (Atom r l))
         -> m n (Atom r n)
buildFor hint dir ty body = buildForAnn hint dir ty body

buildForLike
  :: (Emits n, ScopableBuilder r m)
  => TabPiType r n
  -> (forall l. (Emits l, DExt n l) => AtomVar r l -> m l (Atom r l))
  -> m n (Atom r n)
buildForLike _ _ = undefined

buildMap :: (Emits n, ScopableBuilder r m)
         => Atom r n
         -> (forall l. (Emits l, DExt n l) => Atom r l -> m l (Atom r l))
         -> m n (Atom r n)
buildMap xs f = do
  TabPi t <- return $ getType xs
  buildForLike t \i -> tabApp (sink xs) (Var i) >>= f

unzipTab :: (Emits n, Builder r m) => Atom r n -> m n (Atom r n, Atom r n)
unzipTab tab = do
  fsts <- liftEmitBuilder $ buildMap tab getFst
  snds <- liftEmitBuilder $ buildMap tab getSnd
  return (fsts, snds)

emitRunWriter
  :: (Emits n, ScopableBuilder r m)
  => NameHint -> Type r n -> BaseMonoid r n
  -> (forall l. (Emits l, DExt n l) => AtomVar r l -> AtomVar r l -> m l (Atom r l))
  -> m n (Atom r n)
emitRunWriter hint accTy bm body = do
  lam <- buildEffLam hint accTy \h ref -> body h ref
  emitHof $ RunWriter Nothing bm lam

emitRunState
  :: (Emits n, ScopableBuilder r m)
  => NameHint -> Atom r n
  -> (forall l. (Emits l, DExt n l) => AtomVar r l -> AtomVar r l -> m l (Atom r l))
  -> m n (Atom r n)
emitRunState hint initVal body = do
  stateTy <- return $ getType initVal
  lam <- buildEffLam hint stateTy \h ref -> body h ref
  emitHof $ RunState Nothing initVal lam

emitRunReader
  :: (Emits n, ScopableBuilder r m)
  => NameHint -> Atom r n
  -> (forall l. (Emits l, DExt n l) => AtomVar r l -> AtomVar r l -> m l (Atom r l))
  -> m n (Atom r n)
emitRunReader hint r body = do
  rTy <- return $ getType r
  lam <- buildEffLam hint rTy \h ref -> body h ref
  emitHof $ RunReader r lam

emitSeq :: (Emits n, ScopableBuilder SimpIR m)
        => Direction -> IxType SimpIR n -> Atom SimpIR n -> LamExpr SimpIR n
        -> m n (Atom SimpIR n)
emitSeq d t x f = do
  op <- mkSeq d t x f
  emitExpr $ PrimOp $ DAMOp op

mkSeq :: EnvReader m
      => Direction -> IxType SimpIR n -> Atom SimpIR n -> LamExpr SimpIR n
      -> m n (DAMOp SimpIR n)
mkSeq d t x f = do
  effTy <- functionEffs f
  return $ Seq effTy d t x f

buildRememberDest :: (Emits n, ScopableBuilder SimpIR m)
  => NameHint -> SAtom n
  -> (forall l. (Emits l, Distinct l, DExt n l) => SAtomVar l -> m l (SAtom l))
  -> m n (SAtom n)
buildRememberDest hint dest cont = do
  ty <- return $ getType dest
  doit <- buildUnaryLamExpr hint ty cont
  effs <- functionEffs doit
  emitExpr $ PrimOp $ DAMOp $ RememberDest effs dest doit

-- === vector space (ish) type class ===

zeroAt :: (Emits n, SBuilder m) => SType n -> m n (SAtom n)
zeroAt ty = liftEmitBuilder $ go ty where
  go :: Emits n => SType n -> BuilderM SimpIR n (SAtom n)
  go = \case
   BaseTy bt  -> return $ Con $ Lit $ zeroLit bt
   ProdTy tys -> ProdVal <$> mapM go tys
   TabPi t -> buildForLike t \i -> go =<< typeOfTabApp (sink $ TabPi t) [Var i]
   _ -> unreachable
  zeroLit bt = case bt of
    Scalar Float64Type -> Float64Lit 0.0
    Scalar Float32Type -> Float32Lit 0.0
    _                  -> unreachable
  unreachable :: a
  unreachable = error $ "Missing zero case for a tangent type: " ++ pprint ty

zeroLike :: (HasType SimpIR e, SBuilder m, Emits n) => e n -> m n (SAtom n )
zeroLike x = zeroAt $ getType x

tangentType :: EnvReader m => SType n -> m n (SType n)
tangentType ty = maybeTangentType ty >>= \case
  Just tanTy -> return tanTy
  Nothing -> error $ "can't differentiate wrt type: " ++ pprint ty

maybeTangentType :: (IRRep r, EnvReader m) => Type r n -> m n (Maybe (Type r n))
maybeTangentType ty = liftEnvReaderT $ maybeTangentType' ty

maybeTangentType' :: IRRep r => Type r n -> EnvReaderT Maybe n (Type r n)
maybeTangentType' ty = case ty of
  TabTy d b bodyTy -> do
    refreshAbs (Abs b bodyTy) \b' bodyTy' -> do
      bodyTanTy <- rec bodyTy'
      return $ TabTy d b' bodyTanTy
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
  case getType x of
    TabPi t -> do
      liftEmitBuilder $ buildForLike t \i -> do
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
    return $ TypeCon "SymbolicTangent" symTanName $
      TyConParams [Explicit] [Type elTy]
  Nothing -> throw UnboundVarErr $
    "Can't define a custom linearization with symbolic zeros: " ++
    "the SymbolicTangent type is not in scope."
  Just _ -> throw TypeErr "SymbolicTangent should name a `data` type"

symbolicTangentZero :: EnvReader m => SType n -> m n (SAtom n)
symbolicTangentZero argTy = return $ SumVal [UnitTy, argTy] 0 UnitVal

symbolicTangentNonZero :: EnvReader m => SAtom n -> m n (SAtom n)
symbolicTangentNonZero val = do
  ty <- return $ getType val
  return $ SumVal [UnitTy, ty] 1 val

-- === builder versions of common local ops ===

fLitLike :: (Builder r m, Emits n) => Double -> Atom r n -> m n (Atom r n)
fLitLike x t = do
  ty <- return $ getType t
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

fromPair :: (Fallible1 m, Builder r m, Emits n, IRRep r) => Atom r n -> m n (Atom r n, Atom r n)
fromPair pair = do
  getUnpacked pair >>= \case
    [x, y] -> return (x, y)
    _ -> error "expected a pair"

getFst :: (Builder r m, Emits n) => Atom r n -> m n (Atom r n)
getFst p = fst <$> fromPair p

getSnd :: (Builder r m, Emits n) => Atom r n -> m n (Atom r n)
getSnd p = snd <$> fromPair p

-- the rightmost index is applied first
getNaryProjRef :: (Builder r m, Emits n) => [Projection] -> Atom r n -> m n (Atom r n)
getNaryProjRef [] ref = return ref
getNaryProjRef (i:is) ref = getProjRef i =<< getNaryProjRef is ref

getProjRef :: (Builder r m, Emits n) => Projection -> Atom r n -> m n (Atom r n)
getProjRef i r = emitOp =<< mkProjRef r i

-- XXX: getUnpacked must reduce its argument to enforce the invariant that
-- ProjectElt atoms are always fully reduced (to avoid type errors between two
-- equivalent types spelled differently).
getUnpacked :: (Fallible1 m, Builder r m, Emits n, IRRep r) => Atom r n -> m n [Atom r n]
getUnpacked atom = do
  ty <- return $ getType atom
  positions <- case ty of
    ProdTy tys  -> return $ void tys
    DepPairTy _ -> return [(), ()]
    _ -> error $ "not a product type: " ++ pprint ty
  forM (enumerate positions) \(i, _) ->
    proj (ProjectProduct i) atom
{-# SCC getUnpacked #-}

emitUnpacked :: (Builder r m, Emits n) => Atom r n -> m n [AtomVar r n]
emitUnpacked tup = do
  xs <- getUnpacked tup
  forM xs \x -> emit $ Atom x

unwrapNewtype :: (CBuilder m, Emits n) => CAtom n -> m n (CAtom n)
unwrapNewtype (NewtypeCon _ x) = return x
unwrapNewtype x = case getType x of
  NewtypeTyCon con -> do
    (_, ty) <- unwrapNewtypeType con
    emitExpr $ ProjectElt ty UnwrapNewtype x
  _ -> error "not a newtype"
{-# INLINE unwrapNewtype #-}

projectTuple :: (IRRep r, Builder r m, Emits n) => Int -> Atom r n -> m n (Atom r n)
projectTuple i x = proj (ProjectProduct i) x

projectStruct :: (CBuilder m, Emits n) => Int -> CAtom n -> m n (CAtom n)
projectStruct i x = do
  projs <- getStructProjections i (getType x)
  naryProj projs x
{-# INLINE projectStruct #-}

naryProj :: (Builder r m, Emits n) => [Projection] -> Atom r n -> m n (Atom r n)
naryProj i x = undefined
{-# INLINE naryProj #-}

proj :: (Builder r m, Emits n) => Projection -> Atom r n -> m n (Atom r n)
proj i x = undefined
{-# INLINE proj #-}

projectStructRef :: (Builder CoreIR m, Emits n) => Int -> CAtom n -> m n (CAtom n)
projectStructRef i x = do
  RefTy _ valTy <- return $ getType x
  projs <- getStructProjections i valTy
  getNaryProjRef projs x
{-# INLINE projectStructRef #-}

getStructProjections :: EnvReader m => Int -> CType n -> m n [Projection]
getStructProjections i (NewtypeTyCon (UserADTType _ tyConName _)) = do
  TyConDef _ _ ~(StructFields fields) <- lookupTyCon tyConName
  return case fields of
    [_] | i == 0    -> [UnwrapNewtype]
        | otherwise -> error "bad index"
    _ -> [ProjectProduct i, UnwrapNewtype]
getStructProjections _ _ = error "not a struct"

mkApp :: (CBuilder m, Emits n) => CAtom n -> [CAtom n] -> m n (CExpr n)
mkApp f xs = do
  et <- appEffTy (getType f) xs
  return $ App et f xs

mkTabApp :: (Builder r m, Emits n, IRRep r) => Atom r n -> [Atom r n] -> m n (Expr r n)
mkTabApp xs ixs = do
  ty <- typeOfTabApp (getType xs) ixs
  return $ TabApp ty xs ixs

mkTopApp :: (SBuilder m, Emits n) => TopFunName n -> [SAtom n] -> m n (SExpr n)
mkTopApp f xs = do
  resultTy <- typeOfTopApp f xs
  return $ TopApp resultTy f xs

mkApplyMethod :: (CBuilder m, Emits n) => CAtom n -> Int -> [CAtom n] -> m n (CExpr n)
mkApplyMethod d i xs = do
  resultTy <- typeOfApplyMethod d i xs
  return $ ApplyMethod resultTy d i xs

mkDictAtom :: (CBuilder m, Emits n) => DictExpr n -> m n (CAtom n)
mkDictAtom d = do
  ty <- typeOfDictExpr d
  return $ DictCon ty d

mkCatchException :: EnvReader m => CBlock n -> m n (Hof CoreIR n)
mkCatchException body = do
  resultTy <- makePreludeMaybeTy $ getType body
  return $ CatchException resultTy body

app :: (CBuilder m, Emits n) => CAtom n -> CAtom n -> m n (CAtom n)
app x i = mkApp x [i] >>= emitExpr

naryApp :: (CBuilder m, Emits n) => CAtom n -> [CAtom n] -> m n (CAtom n)
naryApp = naryAppHinted noHint
{-# INLINE naryApp #-}

naryTopApp :: (SBuilder m, Emits n) => TopFunName n -> [SAtom n] -> m n (SAtom n)
naryTopApp f xs = emitExpr =<< mkTopApp f xs
{-# INLINE naryTopApp #-}

naryTopAppInlined :: (Builder SimpIR m, Emits n) => TopFunName n -> [SAtom n] -> m n (SAtom n)
naryTopAppInlined f xs = do
  TopFunBinding f' <- lookupEnv f
  case f' of
    DexTopFun _ _ (LamExpr bs body) _ -> betasReduce bs xs body >>= emitBlock
    _ -> naryTopApp f xs
{-# INLINE naryTopAppInlined #-}

naryAppHinted :: (CBuilder m, Emits n)
  => NameHint -> CAtom n -> [CAtom n] -> m n (CAtom n)
naryAppHinted hint f xs = Var <$> (mkApp f xs >>= emitHinted hint)

tabApp :: (Builder r m, Emits n) => Atom r n -> Atom r n -> m n (Atom r n)
tabApp x i = mkTabApp x [i] >>= emitExpr

naryTabApp :: (Builder r m, Emits n) => Atom r n -> [Atom r n] -> m n (Atom r n)
naryTabApp = naryTabAppHinted noHint
{-# INLINE naryTabApp #-}

naryTabAppHinted :: (Builder r m, Emits n)
  => NameHint -> Atom r n -> [Atom r n] -> m n (Atom r n)
naryTabAppHinted hint f xs = do
  expr <- mkTabApp f xs
  Var <$> emitHinted hint expr

indexRef :: (Builder r m, Emits n) => Atom r n -> Atom r n -> m n (Atom r n)
indexRef ref i = emitOp =<< mkIndexRef ref i

naryIndexRef :: (Builder r m, Emits n) => Atom r n -> [Atom r n] -> m n (Atom r n)
naryIndexRef ref is = foldM indexRef ref is

ptrOffset :: (Builder r m, Emits n) => Atom r n -> Atom r n -> m n (Atom r n)
ptrOffset x (IdxRepVal 0) = return x
ptrOffset x i = emitOp $ MemOp $ PtrOffset x i
{-# INLINE ptrOffset #-}

unsafePtrLoad :: (Builder r m, Emits n) => Atom r n -> m n (Atom r n)
unsafePtrLoad x = liftEmitBuilder do
  body <- buildBlock $ emitOp . MemOp . PtrLoad =<< sinkM x
  body' <- emitDecls body
  emitHof $ RunIO body'

mkIndexRef :: (EnvReader m, Fallible1 m, IRRep r) => Atom r n -> Atom r n -> m n (PrimOp r n)
mkIndexRef ref i = do
  resultTy <- typeOfIndexRef (getType ref) i
  return $ RefOp ref $ IndexRef resultTy i

mkProjRef :: (Builder r m, Emits n, IRRep r) => Atom r n -> Projection -> m n (PrimOp r n)
mkProjRef ref i = do
  resultTy <- typeOfProjRef (getType ref) i
  return $ RefOp ref $ ProjRef resultTy i

-- === index set type class ===

applyIxMethod :: (SBuilder m, Emits n) => IxDict SimpIR n -> IxMethod -> [SAtom n] -> m n (SAtom n)
applyIxMethod dict method args = case dict of
  -- These cases are used in SimpIR and they work with IdxRepVal
  IxDictRawFin n -> case method of
    Size              -> do []  <- return args; return n
    Ordinal           -> do [i] <- return args; return i
    UnsafeFromOrdinal -> do [i] <- return args; return i
  IxDictSpecialized _ d params -> do
    SpecializedDict _ maybeFs <- lookupSpecDict d
    Just fs <- return maybeFs
    LamExpr bs body <- return $ fs !! fromEnum method
    emitBlock =<< betasReduce bs (params ++ args) body

unsafeFromOrdinal :: (SBuilder m, Emits n) => IxType SimpIR n -> Atom SimpIR n -> m n (Atom SimpIR n)
unsafeFromOrdinal (IxType _ dict) i = applyIxMethod dict UnsafeFromOrdinal [i]

ordinal :: (SBuilder m, Emits n) => IxType SimpIR n -> Atom SimpIR n -> m n (Atom SimpIR n)
ordinal (IxType _ dict) idx = applyIxMethod dict Ordinal [idx]

indexSetSize :: (SBuilder m, Emits n) => IxType SimpIR n -> m n (SAtom n)
indexSetSize (IxType _ dict) = applyIxMethod dict Size []

-- === core versions of index set type class ===

applyIxMethodCore :: (CBuilder m, Emits n) => IxMethod -> IxType CoreIR n -> [CAtom n] -> m n (CAtom n)
applyIxMethodCore method (IxType _ (IxDictAtom dict)) args = do
  emitExpr =<< mkApplyMethod dict (fromEnum method) args
applyIxMethodCore _ _ _ = error "not an ix type"

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
  MaybeTy a <- return $ getType x
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
  TabTy d b a <- return $ getType xs
  a' <- return $ ignoreHoistFailure $ hoist b a
  getSnd =<< emitRunWriter noHint a' monoid \_ ref ->
    buildFor noHint Fwd (sink $ IxType (binderType b) d) \i -> do
      x <- tabApp (sink xs) (Var i)
      emitExpr $ PrimOp $ RefOp (sink $ Var ref) $ MExtend (sink monoid) x

andMonoid :: (EnvReader m, IRRep r) => m n (BaseMonoid r n)
andMonoid = liftM (BaseMonoid TrueAtom) $ liftBuilder $
  buildBinaryLamExpr (noHint, BoolTy) (noHint, BoolTy) \x y ->
    emitOp $ BinOp BAnd (sink $ Var x) (Var y)

-- (n:Type) ?-> (a:Type) ?-> (xs : n=>Maybe a) : Maybe (n => a) =
catMaybesE :: (Emits n, Builder r m) => Atom r n -> m n (Atom r n)
catMaybesE maybes = do
  TabTy d n (MaybeTy a) <- return $ getType maybes
  justs <- liftEmitBuilder $ buildMap maybes isJustE
  monoid <- andMonoid
  allJust <- reduceE monoid justs
  liftEmitBuilder $ emitIf allJust (MaybeTy $ TabTy d n a)
    (JustAtom (sink $ TabTy d n a) <$> buildMap (sink maybes) fromJustE)
    (return (NothingAtom $ sink $ TabTy d n a))

emitWhile :: (Emits n, ScopableBuilder r m)
          => (forall l. (Emits l, DExt n l) => m l (Atom r l))
          -> m n ()
emitWhile cont = do
  body <- buildBlock cont >>= emitDecls
  void $ emitHof $ While body

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
        (emit (PrimOp $ RefOp (sink $ Var ref) $ MPut TrueAtom) >> return FalseAtom)
        (return)
    return UnitVal
  emitIf hadError (MaybeTy UnitTy)
    (return $ NothingAtom UnitTy)
    (return $ JustAtom    UnitTy UnitVal)

-- === capturing closures with telescopes ===

type ReconAbs r e = Abs (ReconBinders r) e

data ReconBinders r n l = ReconBinders
  (TelescopeType r (Type r) n)
  (Nest (NameBinder (AtomNameC r)) n l)

data TelescopeType r e n =
   DepTelescope (TelescopeType r e n) (Abs (BinderAndDecls r) (TelescopeType r e) n)
 | ProdTelescope [e n]

instance IRRep r => GenericB (ReconBinders r) where
  type RepB (ReconBinders r) =
    PairB (LiftB (TelescopeType r (Type r)))
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

instance GenericE (TelescopeType r e) where
  type RepE (TelescopeType r e) = EitherE
         (PairE (TelescopeType r e) (Abs (BinderAndDecls r) (TelescopeType r e)))
         (ListE e)
  fromE (DepTelescope lhs ab) = LeftE (PairE lhs ab)
  fromE (ProdTelescope tys)   = RightE (ListE tys)
  {-# INLINE fromE #-}
  toE (LeftE (PairE lhs ab)) = DepTelescope lhs ab
  toE (RightE (ListE tys))   = ProdTelescope tys
  {-# INLINE toE #-}

instance (IRRep r, SinkableE e) => SinkableE (TelescopeType r e)
instance (IRRep r, SinkableE e, RenameE e) => RenameE (TelescopeType r e)
instance (IRRep r, ToBinding e c, SubstE AtomSubstVal e) => SubstE AtomSubstVal (TelescopeType r e)
instance (IRRep r, HoistableE e) => HoistableE (TelescopeType r e)

telescopicCapture
  :: (Builder r m, Emits l, HoistableE e, HoistableB b, IRRep r)
  => b n l -> e l -> m l (Atom r l, ReconAbs r e n)
telescopicCapture bs e = do
  vs <- localVarsAndTypeVars bs e
  vTys <- forM vs \v -> getType <$> toAtomVar v
  let vsTysSorted = toposortAnnVars $ zip vs vTys
  let vsSorted = map fst vsTysSorted
  ty <- liftEnvReaderM $ buildTelescopeTy vsTysSorted
  valsSorted <- forM vsSorted \v -> Var <$> toAtomVar v
  result <- buildTelescopeVal valsSorted ty
  reconAbs <- return $ ignoreHoistFailure $ hoist bs do
    case abstractFreeVarsNoAnn vsSorted e of
      Abs bs' e' -> Abs (ReconBinders ty bs') e'
  return (result, reconAbs)

applyReconAbs
  :: (Builder r m, Emits n, Fallible1 m, SinkableE e, SubstE AtomSubstVal e, IRRep r)
  => ReconAbs r e n -> Atom r n -> m n (e n)
applyReconAbs (Abs bs result) x = do
  xs <- unpackTelescope bs x
  applySubst (bs @@> map SubstVal xs) result

buildTelescopeTy
  :: (EnvReader m, EnvExtender m, IRRep r)
  => [AnnVar (AtomNameC r) (Type r) n] -> m n (TelescopeType r (Type r) n)
buildTelescopeTy [] = return (ProdTelescope [])
buildTelescopeTy ((v,ty):xs) = do
  rhs <- buildTelescopeTy xs
  Abs b rhs' <- return $ abstractFreeVar v rhs
  case hoist b rhs' of
    HoistSuccess rhs'' -> return $ prependTelescopeTy ty rhs''
    HoistFailure _ -> return $ DepTelescope (ProdTelescope []) (Abs (BD (b:>ty) Empty) rhs')

prependTelescopeTy :: e n -> TelescopeType c e n -> TelescopeType c e n
prependTelescopeTy x = \case
  DepTelescope lhs rhs -> DepTelescope (prependTelescopeTy x lhs) rhs
  ProdTelescope xs -> ProdTelescope (x:xs)

buildTelescopeVal
  :: (Builder r m, Emits n, IRRep r) => [Atom r n]
  -> TelescopeType r (Type r) n -> m n (Atom r n)
buildTelescopeVal xsTop tyTop = fst <$> go tyTop xsTop where
  go :: (Builder r m, Emits n, IRRep r)
     => TelescopeType r (Type r) n ->  [Atom r n]
     -> m n (Atom r n, [Atom r n])
  go ty rest = case ty of
    ProdTelescope tys -> do
      (xs, rest') <- return $ splitAt (length tys) rest
      return (ProdVal xs, rest')
    DepTelescope ty1 (Abs b ty2) -> do
      (x1, ~(xDep : rest')) <- go ty1 rest
      ty2' <- betaReduce b xDep ty2
      (x2, rest'') <- go ty2' rest'
      let depPairTy = DepPairType ExplicitDepPair b (telescopeTypeType ty2)
      return (PairVal x1 (DepPair xDep x2 depPairTy), rest'')

telescopeTypeType :: TelescopeType r (Type r) n -> Type r n
telescopeTypeType (ProdTelescope tys) = ProdTy tys
telescopeTypeType (DepTelescope lhs (Abs b rhs)) = do
  let lhs' = telescopeTypeType lhs
  let rhs' = DepPairTy (DepPairType ExplicitDepPair b (telescopeTypeType rhs))
  PairTy lhs' rhs'

unpackTelescope
  :: (Fallible1 m, Builder r m, Emits n, IRRep r)
  => ReconBinders r l1 l2 -> Atom r n -> m n [Atom r n]
unpackTelescope (ReconBinders tyTop _) xTop = go tyTop xTop where
  go :: (Fallible1 m, Builder r m, Emits n, IRRep r)
     => TelescopeType r e l-> Atom r n -> m n [Atom r n]
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
-- the types of those names, recursively. TODO: the reason for the distinction
-- between `localVarsAndTypeVars` and `localVars` is that we used to not have
-- the types cached locally on the vars. Now we do, so we don't need it.
localVarsAndTypeVars
  :: forall m b e n l r.
     (EnvReader m, BindsNames b, HoistableE e, IRRep r)
  => b n l -> e l -> m l [AtomName r l]
localVarsAndTypeVars b e =
  transitiveClosureM varsViaType (localVars b e)
  where
    varsViaType :: AtomName r l -> m l [AtomName r l]
    varsViaType v = do
      ty <- getType <$> toAtomVar v
      return $ localVars b ty

localVars :: (Color c, BindsNames b, HoistableE e) => b n l -> e l -> [Name c l]
localVars b e = nameSetToList $ nameSetIntersection (toNameSet (toScopeFrag b)) (freeVarsE e)

-- See Note [Confuse GHC] from Simplify.hs
-- (we use a Builder-specific name to avoid collisions, since we export everything from Builder)
confuseGHCBuilder :: IRRep r => BuilderM r n (DistinctEvidence n)
confuseGHCBuilder = getDistinct
{-# INLINE confuseGHCBuilder #-}

-- === Non-emitting expression visitor ===

class Visitor m r i o => ExprVisitorNoEmits m r i o | m -> i, m -> o where
  visitExprNoEmits :: Expr r i -> m (Expr r o)

type ExprVisitorNoEmits2 m r = forall i o. ExprVisitorNoEmits (m i o) r i o

visitLamNoEmits
  :: (ExprVisitorNoEmits2 m r, IRRep r, AtomSubstReader v m, EnvExtender2 m)
  => LamExpr r i -> m i o (LamExpr r o)
visitLamNoEmits (LamExpr bs body) =
  visitBindersAndDecls bs \bs' -> LamExpr bs' <$> visitBlockNoEmits body

visitBlockNoEmits
  :: (ExprVisitorNoEmits2 m r, IRRep r, AtomSubstReader v m, EnvExtender2 m)
  => Block r i -> m i o (Block r o)
visitBlockNoEmits (Block _ decls result) = undefined
-- visitBlockNoEmits (Block _ decls result) =
--   absToBlockInferringTypes =<< visitDeclsNoEmits decls \decls' -> do
--     Abs decls' <$> visitAtom result
-- absToBlockInferringTypes :: (EnvReader m, IRRep r) => Abs (Nest (Decl r)) (Atom r) n -> m n (WithDecls r (Block r) n)
-- absToBlockInferringTypes ab = liftEnvReaderM do
--   abWithEffs <-  computeAbsEffects ab
--   refreshAbs abWithEffs \decls (effs `PairE` result) -> do
--     return $ ignoreExcept $
--       absToBlock $ Abs decls (effs `PairE` (result `PairE` getType result))
-- {-# INLINE absToBlockInferringTypes #-}

visitDeclsNoEmits
  :: (ExprVisitorNoEmits2 m r, IRRep r, AtomSubstReader v m, EnvExtender2 m)
  => Nest (Decl r) i i'
  -> (forall o'. DExt o o' => Nest (Decl r) o o' -> m i' o' a)
  -> m i o a
visitDeclsNoEmits Empty cont = getDistinct >>= \Distinct -> cont Empty
visitDeclsNoEmits (Nest (Let b (DeclBinding ann expr)) decls) cont = do
  expr' <- visitExprNoEmits expr
  withFreshBinder (getNameHint b) (getType expr') \(b':>_) -> do
    let decl' = Let b' $ DeclBinding ann expr'
    extendRenamer (b@>binderName b') do
      visitDeclsNoEmits decls \decls' ->
        cont $ Nest decl' decls'

-- === Emitting expression visitor ===

class Visitor m r i o => ExprVisitorEmits m r i o | m -> i, m -> o where
  visitExprEmits :: Emits o => Expr r i -> m (Atom r o)

type ExprVisitorEmits2 m r = forall i o. ExprVisitorEmits (m i o) r i o

liftAtomSubstBuilder :: forall tag r m n a. (IRRep r, EnvReader m) => AtomSubstBuilder tag r n n a -> m n a
liftAtomSubstBuilder cont = liftBuilder $ runSubstReaderT idSubst $ runAtomSubstBuilder cont

-- The phantom type `v` is for defining `Visitor` instances. The pattern is to
-- define a new singleton type, like `data MyTag = MyTag`.
newtype AtomSubstBuilder v r i o a =
  AtomSubstBuilder { runAtomSubstBuilder :: SubstReaderT AtomSubstVal (BuilderM r) i o a}
  deriving (MonadFail, Fallible, Functor, Applicative, Monad, ScopeReader,
            EnvReader, EnvExtender, Builder r, SubstReader AtomSubstVal,
            ScopableBuilder r)

visitLamEmits
  :: (ExprVisitorEmits2 m r, IRRep r, SubstReader AtomSubstVal m, ScopableBuilder2 r m)
  => LamExpr r i -> m i o (LamExpr r o)
visitLamEmits (LamExpr bs body) = visitBindersAndDecls bs \bs' -> makeLamExpr bs' <$>
  buildBlock (visitBlockEmits body)

makeLamExpr :: Nest (BinderAndDecls r) n l -> WithDecls r (Block r) l -> LamExpr r n
makeLamExpr = undefined

visitBlockEmits
  :: (ExprVisitorEmits2 m r, SubstReader AtomSubstVal m, EnvExtender2 m, IRRep r, Emits o)
  => Block r i -> m i o (Atom r o)
visitBlockEmits (Block _ decls result) = visitDeclsEmits decls $ visitAtom result

visitDeclsEmits
  :: (ExprVisitorEmits2 m r, SubstReader AtomSubstVal m, EnvExtender2 m, IRRep r, Emits o)
  => Nest (Decl r) i i'
  -> m i' o a
  -> m i  o a
visitDeclsEmits Empty cont = cont
visitDeclsEmits (Nest (Let b (DeclBinding _ expr)) decls) cont = do
  x <- visitExprEmits expr
  extendSubst (b@>SubstVal x) do
    visitDeclsEmits decls cont

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

-- === Querying types of partial expressions ===

sourceNameType :: (EnvReader m, Fallible1 m) => SourceName -> m n (Type CoreIR n)
sourceNameType v = do
  lookupSourceMap v >>= \case
    Nothing -> throw UnboundVarErr $ pprint v
    Just uvar -> getUVarType uvar

-- === Exposed helpers for querying types and effects ===

caseAltsBinderTys :: (Builder r m, Emits n, IRRep r) => Type r n -> m n [Type r n]
caseAltsBinderTys ty = case ty of
  SumTy types -> return types
  NewtypeTyCon t -> case t of
    UserADTType _ defName params -> do
      def <- lookupTyCon defName
      ~(ADTCons cons) <- instantiateTyConDef def params
      return [repTy | DataConDef _ _ repTy _ <- cons]
    _ -> error msg
  _ -> error msg
  where msg = "Case analysis only supported on ADTs, not on " ++ pprint ty

extendEffect :: IRRep r => Effect r n -> EffectRow r n -> EffectRow r n
extendEffect eff (EffectRow effs t) = EffectRow (effs <> eSetSingleton eff) t

getDestLamExprType :: LamExpr SimpIR n -> PiType SimpIR n
getDestLamExprType (LamExpr bsRefB body) =
  case popNest bsRefB of
    Just (PairB bs bDest) -> do
      case binderType bDest of
        RawRefTy ansTy -> do
          let resultEffs = ignoreHoistFailure $ hoist bDest $ getEffects body
          PiType bs $ EffTy resultEffs ansTy
        _ -> error "expected a reference type"
    _ -> error "expected trailing dest binder"

typeOfApp  :: (Builder r m, Emits n, IRRep r) => Type r n -> [Atom r n] -> m n (Type r n)
typeOfApp (Pi (CorePiType _ bs (EffTy _ ty))) xs = betasReduce bs xs ty
typeOfApp _ _ = error "expected a pi type"

typeOfTabApp :: (Builder r m, Emits n, IRRep r) => Type r n -> [Atom r n] -> m n (Type r n)
typeOfTabApp t [] = return t
typeOfTabApp (TabTy _ b resultTy) (i:rest) = do
  resultTy' <- betaReduce b i resultTy
  typeOfTabApp resultTy' rest
typeOfTabApp ty _ = error $ "expected a table type. Got: " ++ pprint ty

typeOfApplyMethod :: (CBuilder m, Emits n) => CAtom n -> Int -> [CAtom n] -> m n (EffTy CoreIR n)
typeOfApplyMethod d i args = do
  ty <- Pi <$> getMethodType d i
  appEffTy ty args

typeOfDictExpr :: (CBuilder m, Emits n) => DictExpr n -> m n (CType n)
typeOfDictExpr e = case e of
  InstanceDict instanceName args -> do
    InstanceDef className bs params _ <- lookupInstanceDef instanceName
    ClassDef sourceName _ _ _ _ _ <- lookupClassDef className
    ListE params' <- betasReduce bs args $ ListE params
    return $ DictTy $ DictType sourceName className params'
  InstantiatedGiven given args -> typeOfApp (getType given) args
  SuperclassProj d i -> do
    DictTy (DictType _ className params) <- return $ getType d
    ClassDef _ _ _ bs superclasses _ <- lookupClassDef className
    betasReduce bs params $ getSuperclassType REmpty superclasses i
  IxFin n -> liftM DictTy $ ixDictType $ NewtypeTyCon $ Fin n
  DataData ty -> DictTy <$> dataDictType ty

typeOfTopApp :: (SBuilder m, Emits n) => TopFunName n -> [SAtom n] -> m n (EffTy SimpIR n)
typeOfTopApp f xs = do
  PiType bs effTy <- getTypeTopFun f
  betasReduce bs xs effTy

typeOfIndexRef :: (EnvReader m, Fallible1 m, IRRep r) => Type r n -> Atom r n -> m n (Type r n)
typeOfIndexRef (TC (RefType h s)) i = do
  TabPi tabTy <- return s
  eltTy' <- instantiateTabTy tabTy i
  return $ TC $ RefType h eltTy'
typeOfIndexRef _ _ = error "expected a ref type"

typeOfProjRef :: (Builder r m, Emits n) => Type r n -> Projection -> m n (Type r n)
typeOfProjRef (TC (RefType h s)) p = do
  TC . RefType h <$> case p of
    ProjectProduct i -> do
      ~(ProdTy tys) <- return s
      return $ tys !! i
    UnwrapNewtype -> do
      case s of
        NewtypeTyCon tc -> snd <$> unwrapNewtypeType tc
        _ -> error "expected a newtype"
typeOfProjRef _ _ = error "expected a reference"

appEffTy  :: (IRRep r, Builder r m, Emits n) => Type r n -> [Atom r n] -> m n (EffTy r n)
appEffTy (Pi (CorePiType _ bs effTy)) xs = betasReduce bs xs effTy
appEffTy t _ = error $ "expected a pi type, got: " ++ pprint t

partialAppType :: (Builder r m, IRRep r, Emits n) => Type r n -> [Atom r n] -> m n (Type r n)
partialAppType (Pi (CorePiType expl bs effTy)) xs = do
  PairB bs1 bs2 <- return $ splitNestAt (length xs) bs
  betasReduce bs1 xs $ Pi $ CorePiType expl bs2 effTy
partialAppType _ _ = error "expected a pi type"

appEffects :: (Builder r m, Emits n, IRRep r) => Type r n -> [Atom r n] -> m n (EffectRow r n)
appEffects (Pi (CorePiType _ bs (EffTy effs _))) xs = betasReduce bs xs effs
appEffects _ _ = error "expected a pi type"

effTyOfHof :: (EnvReader m, IRRep r) => Hof r n -> m n (EffTy r n)
effTyOfHof hof = EffTy <$> hofEffects hof <*> typeOfHof hof

typeOfHof :: (EnvReader m, IRRep r) => Hof r n -> m n (Type r n)
typeOfHof = \case
  For _ ixTy f -> case getLamExprType f of
    PiType (UnaryNest b) (EffTy _ eltTy) -> return $ TabTy (ixTypeDict ixTy) b eltTy
    _ -> error "expected a unary pi type"
  While _ -> return UnitTy
  Linearize f _ -> case getLamExprType f of
    PiType (UnaryNest binder@(BD (_:>a) _)) (EffTy Pure b) -> do
      let b' = ignoreHoistFailure $ hoist binder b
      let fLinTy = Pi $ nonDepPiType [a] Pure b'
      return $ PairTy b' fLinTy
    _ -> error "expected a unary pi type"
  Transpose f _ -> case getLamExprType f of
    PiType (UnaryNest (BD (_:>a) _)) _ -> return a
    _ -> error "expected a unary pi type"
  RunReader _ f -> return resultTy
    where (resultTy, _) = getTypeRWSAction f
  RunWriter _ _ f -> return $ uncurry PairTy $ getTypeRWSAction f
  RunState _ _ f -> return $ PairTy resultTy stateTy
    where (resultTy, stateTy) = getTypeRWSAction f
  RunIO f -> return $ getType f
  RunInit f -> return $ getType f
  CatchException ty _ -> return ty

hofEffects :: (EnvReader m, IRRep r) => Hof r n -> m n (EffectRow r n)
hofEffects = \case
  For _ _ f     -> functionEffs f
  While body    -> return $ getEffects body
  Linearize _ _ -> return Pure  -- Body has to be a pure function
  Transpose _ _ -> return Pure  -- Body has to be a pure function
  RunReader _ f -> rwsFunEffects Reader f
  RunWriter d _ f -> maybeInit d <$> rwsFunEffects Writer f
  RunState  d _ f -> maybeInit d <$> rwsFunEffects State  f
  RunIO          f -> return $ deleteEff IOEffect        $ getEffects f
  RunInit        f -> return $ deleteEff InitEffect      $ getEffects f
  CatchException _ f -> return $ deleteEff ExceptionEffect $ getEffects f
  where maybeInit :: IRRep r => Maybe (Atom r i) -> (EffectRow r o -> EffectRow r o)
        maybeInit d = case d of Just _ -> (<>OneEffect InitEffect); Nothing -> id

deleteEff :: IRRep r => Effect r n -> EffectRow r n -> EffectRow r n
deleteEff eff (EffectRow effs t) = EffectRow (effs `eSetDifference` eSetSingleton eff) t

getMethodIndex :: EnvReader m => ClassName n -> SourceName -> m n Int
getMethodIndex className methodSourceName = do
  ClassDef _ methodNames _ _ _ _ <- lookupClassDef className
  case elemIndex methodSourceName methodNames of
    Nothing -> error $ methodSourceName ++ " is not a method of " ++ pprint className
    Just i -> return i
{-# INLINE getMethodIndex #-}

getUVarType :: EnvReader m => UVar n -> m n (CType n)
getUVarType = \case
  UAtomVar v -> getType <$> toAtomVar v
  UTyConVar   v -> getTyConNameType v
  UDataConVar v -> getDataConNameType v
  UPunVar     v -> getStructDataConType v
  UClassVar v -> do
    ClassDef _ _ _ bs _ _ <- lookupClassDef v
    let bs' = fmapNest (\(RolePiBinder _ b) -> b) bs
    return $ Pi $ CorePiType ExplicitApp bs' $ EffTy Pure TyKind
  UMethodVar  v -> getMethodNameType v
  UEffectVar   _ -> error "not implemented"
  UEffectOpVar _ -> error "not implemented"

getMethodNameType :: EnvReader m => MethodName n -> m n (CType n)
getMethodNameType v = undefined
-- getMethodNameType v = liftEnvReaderM $ lookupEnv v >>= \case
--   MethodBinding className i -> do
--     ClassDef _ _ paramNames paramBs scBinders methodTys <- lookupClassDef className
--     let paramBs' = zipWithNest paramBs paramNames \(RolePiBinder _ (WithExpl _ b)) paramName ->
--           WithExpl (Inferred paramName Unify) b
--     refreshAbs (Abs paramBs' $ Abs scBinders (methodTys !! i)) \paramBs'' (Abs scBinders' piTy) -> do
--       let paramVs = nestToList (\(WithExpl _ (BD b ds)) -> sink $ binderName b) paramBs''
--       params <- forM paramVs \v -> Var <$> toAtomVar v
--       dictTy <- DictTy <$> dictType (sink className) params
--       withFreshBinder noHint dictTy \dictB -> do
--         scDicts <- getSuperclassDicts (Var $ binderVar dictB)
--         piTy' <- withReducer $ withBetas scBinders' scDicts $ substM piTy
--         -- piTy' <- applySubst (scBinders'@@>(SubstVal<$>scDicts)) piTy
--         CorePiType appExpl methodBs effTy <- return piTy'
--         let dictBs = UnaryNest $ WithExpl (Inferred Nothing (Synth $ Partial $ succ i)) (BD dictB Empty)
--         return $ Pi $ CorePiType appExpl (paramBs'' >>> dictBs >>> methodBs) effTy

getMethodType :: (CBuilder m, Emits n) => Dict n -> Int -> m n (CorePiType n)
getMethodType dict i = do
  ~(DictTy (DictType _ className params)) <- return $ getType dict
  ClassDef _ _ _ paramBs classBs methodTys <- lookupClassDef className
  let methodTy = methodTys !! i
  superclassDicts <- getSuperclassDicts dict
  withReducer $
    withBetas paramBs params $ withBetas classBs superclassDicts $
        substM methodTy
{-# INLINE getMethodType #-}


getTyConNameType :: EnvReader m => TyConName n -> m n (Type CoreIR n)
getTyConNameType v = do
  TyConDef _ bs _ <- lookupTyCon v
  case bs of
    Empty -> return TyKind
    _ -> do
      let bs' = fmapNest (\(RolePiBinder _ b) -> b) bs
      return $ Pi $ CorePiType ExplicitApp bs' $ EffTy Pure TyKind

getDataConNameType :: EnvReader m => DataConName n -> m n (Type CoreIR n)
getDataConNameType dataCon = liftEnvReaderM do
  (tyCon, i) <- lookupDataCon dataCon
  lookupTyCon tyCon >>= \case
    tyConDef@(TyConDef tcSn _ _) ->
      buildDataConType tyConDef \paramBs ~(ADTCons dataCons) params -> do
        DataConDef _ ab _ _ <- return $ dataCons !! i
        refreshAbs ab \dataBs UnitE -> do
          let appExpl = case dataBs of Empty -> ImplicitApp
                                       _     -> ExplicitApp
          let resultTy = NewtypeTyCon $ UserADTType tcSn (sink tyCon) (sink params)
          let dataBs' = fmapNest (WithExpl Explicit) dataBs
          return $ Pi $ CorePiType appExpl (paramBs >>> dataBs') (EffTy Pure resultTy)

getStructDataConType :: EnvReader m => TyConName n -> m n (CType n)
getStructDataConType tyCon = liftEnvReaderM do
  tyConDef@(TyConDef tcSn _ _) <- lookupTyCon tyCon
  buildDataConType tyConDef \paramBs ~(StructFields fieldTys) params -> do
    let resultTy = NewtypeTyCon $ UserADTType tcSn (sink tyCon) params
    Abs dataBs resultTy' <- return $ typesAsBinderNest (map snd fieldTys) resultTy
    let dataBs' = fmapNest (WithExpl Explicit) dataBs
    return $ Pi $ CorePiType ExplicitApp (paramBs >>> dataBs') (EffTy Pure resultTy')

buildDataConType
  :: (EnvReader m, EnvExtender m)
  => TyConDef n
  -> (forall l. DExt n l => CoreBinders n l -> DataConDefs l -> TyConParams l -> m l a)
  -> m n a
buildDataConType (TyConDef _ bs _) cont = undefined
-- buildDataConType (TyConDef _ bs _) cont = do
--   bs' <- return $ forNest bs \(RolePiBinder _ (WithExpl expl b)) -> case expl of
--     Explicit -> WithExpl (Inferred Nothing Unify) b
--     _        -> WithExpl expl b
--   refreshAbs (Abs bs' UnitE) \bs'' UnitE -> do
--     let expls = nestToList (\(RolePiBinder _ b) -> getExpl b) bs
--     let vs = nestToNames bs''
--     vs' <- mapM toAtomVar vs
--     cont bs'' vs $ TyConParams expls (Var <$> vs')

makeTyConParams :: EnvReader m => TyConName n -> [CAtom n] -> m n (TyConParams n)
makeTyConParams tc params = do
  TyConDef _ paramBs _ <- lookupTyCon tc
  let expls = nestToList (\(RolePiBinder _ b) -> getExpl b) paramBs
  return $ TyConParams expls params

getDataClassName :: (Fallible1 m, EnvReader m) => m n (ClassName n)
getDataClassName = lookupSourceMap "Data" >>= \case
  Nothing -> throw CompilerErr $ "Data interface needed but not defined!"
  Just (UClassVar v) -> return v
  Just _ -> error "not a class var"

dataDictType :: (Fallible1 m, EnvReader m) => CType n -> m n (DictType n)
dataDictType ty = do
  dataClassName <- getDataClassName
  dictType dataClassName [Type ty]

getIxClassName :: (Fallible1 m, EnvReader m) => m n (ClassName n)
getIxClassName = lookupSourceMap "Ix" >>= \case
  Nothing -> throw CompilerErr $ "Ix interface needed but not defined!"
  Just (UClassVar v) -> return v
  Just _ -> error "not a class var"

dictType :: EnvReader m => ClassName n -> [CAtom n] -> m n (DictType n)
dictType className params = do
  ClassDef sourceName _ _ _ _ _ <- lookupClassDef className
  return $ DictType sourceName className params

ixDictType :: (Fallible1 m, EnvReader m) => CType n -> m n (DictType n)
ixDictType ty = do
  ixClassName <- getIxClassName
  dictType ixClassName [Type ty]

makePreludeMaybeTy :: EnvReader m => CType n -> m n (CType n)
makePreludeMaybeTy ty = do
  ~(Just (UTyConVar tyConName)) <- lookupSourceMap "Maybe"
  return $ TypeCon "Maybe" tyConName $ TyConParams [Explicit] [Type ty]

-- === computing effects ===

functionEffs :: (IRRep r, EnvReader m) => LamExpr r n -> m n (EffectRow r n)
functionEffs f = case getLamExprType f of
  PiType b (EffTy effs _) -> return $ ignoreHoistFailure $ hoist b effs

rwsFunEffects :: (IRRep r, EnvReader m) => RWS -> LamExpr r n -> m n (EffectRow r n)
rwsFunEffects rws f = undefined
-- rwsFunEffects rws f = return case getLamExprType f of
--    PiType (BinaryNest h ref) et -> do
--      let effs' = ignoreHoistFailure $ hoist ref (etEff et)
--      let hVal = Var $ AtomVar (binderName h) (TC HeapType)
--      let effs'' = deleteEff (RWSEffect rws hVal) effs'
--      ignoreHoistFailure $ hoist h effs''
--    _ -> error "Expected a binary function type"

getLamExprType :: IRRep r => LamExpr r n -> PiType r n
getLamExprType (LamExpr bs body) = PiType bs (EffTy (getEffects body) (getType body))

getTypeRWSAction :: IRRep r => LamExpr r n -> (Type r n, Type r n)
getTypeRWSAction f = case getLamExprType f of
  PiType (BinaryNest regionBinder refBinder) (EffTy _ resultTy) -> do
    case binderType refBinder of
      RefTy _ referentTy -> do
        let referentTy' = ignoreHoistFailure $ hoist regionBinder referentTy
        let resultTy' = ignoreHoistFailure $ hoist (PairB regionBinder refBinder) resultTy
        (resultTy', referentTy')
      _ -> error "expected a ref"
  _ -> error "expected a pi type"

computeAbsEffects :: (IRRep r, EnvExtender m, RenameE e)
  => Abs (Nest (Decl r)) e n -> m n (Abs (Nest (Decl r)) (EffectRow r `PairE` e) n)
computeAbsEffects it = refreshAbs it \decls result -> do
  effs <- declNestEffects decls
  return $ Abs decls (effs `PairE` result)
{-# INLINE computeAbsEffects #-}

declNestEffects :: (IRRep r, EnvReader m) => Nest (Decl r) n l -> m l (EffectRow r l)
declNestEffects decls = liftEnvReaderM $ declNestEffectsRec decls mempty
{-# INLINE declNestEffects #-}

declNestEffectsRec :: IRRep r => Nest (Decl r) n l -> EffectRow r l -> EnvReaderM l (EffectRow r l)
declNestEffectsRec Empty !acc = return acc
declNestEffectsRec n@(Nest decl rest) !acc = withExtEvidence n do
  expr <- sinkM $ declExpr decl
  acc' <- sinkM $ acc <> (getEffects expr)
  declNestEffectsRec rest acc'
  where
    declExpr :: Decl r n l -> Expr r n
    declExpr (Let _ (DeclBinding _ expr)) = expr

instantiateHandlerType :: EnvReader m => HandlerName n -> CType n -> [CAtom n] -> m n (CType n)
instantiateHandlerType _ _ _ = undefined

getSuperclassDicts :: (CBuilder m, Emits n) => CAtom n -> m n ([CAtom n])
getSuperclassDicts dict = do
  case getType dict of
    DictTy dTy -> do
      ts <- getSuperclassTys dTy
      forM (enumerate ts) \(i, t) -> return $ DictCon t $ SuperclassProj dict i
    _ -> error "expected a dict type"

getSuperclassTys :: (CBuilder m, Emits n) => DictType n -> m n [CType n]
getSuperclassTys (DictType _ className params) = do
  ClassDef _ _ _ bs superclasses _ <- lookupClassDef className
  forM [0 .. nestLength superclasses - 1] \i -> do
    withReducer $ withBetas bs params $
      substM $ getSuperclassType REmpty superclasses i

getSuperclassType :: RNest CBinderAndDecls n l -> Nest CBinderAndDecls l l' -> Int -> CType n
getSuperclassType _ Empty = error "bad index"
getSuperclassType bsAbove (Nest b bs) = \case
  0 -> ignoreHoistFailure $ hoist bsAbove $ binderType b
  i -> getSuperclassType (RNest bsAbove b) bs (i-1)

getTypeTopFun :: EnvReader m => TopFunName n -> m n (PiType SimpIR n)
getTypeTopFun f = lookupTopFun f >>= \case
  DexTopFun _ piTy _ _ -> return piTy
  FFITopFun _ iTy -> liftIFunType iTy

liftIFunType :: (IRRep r, EnvReader m) => IFunType -> m n (PiType r n)
liftIFunType (IFunType _ argTys resultTys) = liftEnvReaderM $ go argTys where
  go :: IRRep r => [BaseType] -> EnvReaderM n (PiType r n)
  go = \case
    [] -> return $ PiType Empty (EffTy (OneEffect IOEffect) resultTy)
      where resultTy = case resultTys of
              [] -> UnitTy
              [t] -> BaseTy t
              [t1, t2] -> PairTy (BaseTy t1) (BaseTy t2)
              _ -> error $ "Not a valid FFI return type: " ++ pprint resultTys
    t:ts -> withFreshBinder noHint (BaseTy t) \b -> do
      PiType bs effTy <- go ts
      return $ PiType (Nest (BD b Empty) bs) effTy

unwrapNewtypeType :: (CBuilder m, Emits n) => NewtypeTyCon n -> m n (NewtypeCon n, Type CoreIR n)
unwrapNewtypeType = \case
  Nat                   -> return (NatCon, IdxRepTy)
  Fin n                 -> return (FinCon n, NatTy)
  UserADTType sn defName params -> do
    def <- lookupTyCon defName
    ty' <- dataDefRep <$> instantiateTyConDef def params
    return (UserADTData sn defName params, ty')
  ty -> error $ "Shouldn't be projecting: " ++ pprint ty
{-# INLINE unwrapNewtypeType #-}

instantiateTyConDef :: (CBuilder m, Emits n) => TyConDef n -> TyConParams n -> m n (DataConDefs n)
instantiateTyConDef (TyConDef _ bs conDefs) (TyConParams _ xs) = do
  withReducer $ withBetas bs xs $ substM conDefs
{-# INLINE instantiateTyConDef #-}

-- Returns a representation type (type of an TypeCon-typed Newtype payload)
-- given a list of instantiated DataConDefs.
dataDefRep :: DataConDefs n -> CType n
dataDefRep (ADTCons cons) = case cons of
  [] -> error "unreachable"  -- There's no representation for a void type
  [DataConDef _ _ ty _] -> ty
  tys -> SumTy $ tys <&> \(DataConDef _ _ ty _) -> ty
dataDefRep (StructFields fields) = case map snd fields of
  [ty] -> ty
  tys  -> ProdTy tys

makeStructRepVal :: (Fallible1 m, EnvReader m) => TyConName n -> [CAtom n] -> m n (CAtom n)
makeStructRepVal tyConName args = do
  TyConDef _ _ (StructFields fields) <- lookupTyCon tyConName
  case fields of
    [_] -> case args of
      [arg] -> return arg
      _ -> error "wrong number of args"
    _ -> return $ ProdVal args

instantiateDepPairTy :: (IRRep r, EnvReader m) => DepPairType r n -> Atom r n -> m n (Type r n)
instantiateDepPairTy (DepPairType _ b rhsTy) x = undefined -- applyAbs (Abs b rhsTy) (SubstVal x)
{-# INLINE instantiateDepPairTy #-}

instantiateTabTy :: (IRRep r, EnvReader m) => TabPiType r n -> Atom r n -> m n (Type r n)
instantiateTabTy _ _ = undefined
{-# INLINE instantiateTabTy #-}

-- ==== Reducer monad ===

data ReducerTag = ReducerTag
type Reducer = AtomSubstBuilder ReducerTag

withReducer
  :: (Builder r m, Emits n) => Reducer r n n a -> m n a
withReducer = undefined

withBeta
  :: ToBinderAndDecls b r => b i i' -> Atom r o
  -> Reducer r i' o a -> Reducer r i  o a
withBeta = undefined

withBetas
  :: ToBinderAndDecls b r => Nest b i i' -> [Atom r o]
  -> Reducer r i' o a -> Reducer r i  o a
withBetas = undefined

betaReduce
  :: (Builder r m, Emits n, ToBinderAndDecls b r, SinkableE e, SubstE AtomSubstVal e,
      SinkableB b)
  => Ext h n
  => b h l -> Atom r n -> e l
  -> m n (e n)
betaReduce bs xs e = do
  Abs bs' e' <- sinkM $ Abs bs e
  withReducer $ withBeta bs' xs $ substM e'

betasReduce
  :: (Builder r m, Emits n, ToBinderAndDecls b r, SinkableE e, SubstE AtomSubstVal e, SinkableB b)
  => Ext h n
  => Nest b h l -> [Atom r n] -> e l
  -> m n (e n)
betasReduce bs xs e = do
  Abs bs' e' <- sinkM $ Abs bs e
  withReducer $ withBetas bs' xs $ substM e'
