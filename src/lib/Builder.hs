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
import Data.Foldable (fold)
import Data.Graph (graphFromEdges, topSort)
import Data.Text.Prettyprint.Doc (Pretty (..))
import Foreign.Ptr

import qualified Unsafe.Coerce as TrulyUnsafe

import Core
import Err
import IRVariants
import MTL1
import Subst
import Name
import QueryType
import Types.Core
import Types.Imp
import Types.Primitives
import Types.Source
import Util (enumerate, transitiveClosureM, bindM2, toSnocList, (...))
import Visit

-- === Ordinary (local) builder class ===

class (EnvReader m, Fallible1 m, IRRep r)
      => Builder (r::IR) (m::MonadKind1) | m -> r where
  rawEmitDecl :: Emits n => NameHint -> LetAnn -> Expr r n -> m n (AtomVar r n)

class (EnvExtender m, Builder r m) => ScopableBuilder (r::IR) (m::MonadKind1) | m -> r where
  buildScopedAndThen
    :: SinkableE e
    => (forall l. (Emits l, DExt n l) => m l (e l))
    -> (forall l.           DExt n l  => Nest (Decl r) n l -> e l -> m l a)
    -> m n a

buildScoped
 :: (ScopableBuilder r m, SinkableE e)
 => (forall l. (Emits l, DExt n l) => m l (e l))
 -> m n (Abs (Nest (Decl r)) e n)
buildScoped cont = buildScopedAndThen cont \decls body -> return $ Abs decls body

type SBuilder = Builder SimpIR
type CBuilder = Builder CoreIR

type Builder2         (r::IR) (m :: MonadKind2) = forall i. Builder         r (m i)
type ScopableBuilder2 (r::IR) (m :: MonadKind2) = forall i. ScopableBuilder r (m i)

emitDecl :: (Builder r m, Emits n) => NameHint -> LetAnn -> Expr r n -> m n (AtomVar r n)
emitDecl _ _ (Var n) = return n
emitDecl hint ann expr = rawEmitDecl hint ann expr
{-# INLINE emitDecl #-}

emit :: (Builder r m, Emits n) => Expr r n -> m n (AtomVar r n)
emit expr = emitDecl noHint PlainLet expr
{-# INLINE emit #-}

emitHinted :: (Builder r m, Emits n) => NameHint -> Expr r n -> m n (AtomVar r n)
emitHinted hint expr = emitDecl hint PlainLet expr
{-# INLINE emitHinted #-}

emitOp :: (Builder r m, IsPrimOp e, Emits n) => e r n -> m n (Atom r n)
emitOp op = AVar <$> emit (PrimOp $ toPrimOp op)
{-# INLINE emitOp #-}

emitExpr :: (Builder r m, Emits n) => Expr r n -> m n (Atom r n)
emitExpr _ = undefined -- TODO: extract as much of an atom as possible before emitting
emitExpr expr = AVar <$> emit expr
{-# INLINE emitExpr #-}

emitHof :: (Builder r m, Emits n) => Hof r n -> m n (Atom r n)
emitHof hof = mkTypedHof hof >>= emitOp

emitUnOp :: (Builder r m, Emits n) => UnOp -> Atom r n -> m n (Atom r n)
emitUnOp op x = emitOp $ UnOp op (toExpr x)
{-# INLINE emitUnOp #-}

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
  buildScopedAndThen cont1 cont2  = DoubleBuilderT do
    (ans, topDecls) <- UnsafeMakeDoubleInplaceT $
      StateT \s@(topScope, _) -> do
          (ans, topDecls) <- locallyMutableInplaceT
            (do (e, s') <- flip runStateT (topScope, emptyOutFrag) $
                   unsafeRunDoubleInplaceT $ runDoubleBuilderT' do
                     Emits <- fabricateEmitsEvidenceM
                     Distinct <- getDistinct
                     cont1
                return $ PairE e $ LiftE s')
            (\rdecls (PairE e (LiftE s')) -> do
                (ans, (_, topDecls)) <- flip runStateT s' $
                   unsafeRunDoubleInplaceT $ runDoubleBuilderT' do
                     Distinct <- getDistinct
                     cont2 (unRNest rdecls) e
                return (ans, topDecls))
          return ((ans, topDecls), s)
    unsafeEmitDoubleInplaceTHoisted topDecls
    return ans
  {-# INLINE buildScopedAndThen #-}

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
  emitHoistedEnv ab = liftSubstReaderT $ emitHoistedEnv ab
  {-# INLINE emitHoistedEnv #-}
  canHoistToTop e = liftSubstReaderT $ canHoistToTop e
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

emitTopFunBinding :: (Mut n, TopBuilder m) => NameHint -> TopFunDef n -> STopLam n -> m n (TopFunName n)
emitTopFunBinding hint def f = do
  emitBinding hint $ TopFunBinding $ DexTopFun def f Waiting

emitSourceMap :: TopBuilder m => SourceMap n -> m n ()
emitSourceMap sm = emitLocalModuleEnv $ mempty {envSourceMap = sm}

emitSynthCandidates :: TopBuilder m => SynthCandidates n -> m n ()
emitSynthCandidates sc = emitLocalModuleEnv $ mempty {envSynthCandidates = sc}

addInstanceSynthCandidate :: TopBuilder m => ClassName n -> InstanceName n -> m n ()
addInstanceSynthCandidate className instanceName =
  emitSynthCandidates $ SynthCandidates (M.singleton className [instanceName])

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
  TopFunBinding (DexTopFun _ _ (Finished impl)) -> return $ Just $ topFunObjCode impl
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
    locallyMutableInplaceT (runTopBuilderT' cont) (\d e -> return $ Abs d e)
  {-# INLINE localTopBuilder #-}

instance (SinkableV v, TopBuilder m) => TopBuilder (SubstReaderT v m i) where
  emitBinding hint binding = liftSubstReaderT $ emitBinding hint binding
  {-# INLINE emitBinding #-}
  emitEnv ab = liftSubstReaderT $ emitEnv ab
  {-# INLINE emitEnv #-}
  emitNamelessEnv bs = liftSubstReaderT $ emitNamelessEnv bs
  {-# INLINE emitNamelessEnv #-}
  localTopBuilder cont = SubstReaderT \env -> do
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
           , Catchable, CtxReader, ScopeReader, Alternative
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
  buildScopedAndThen cont1 cont2 = BuilderT $ locallyMutableInplaceT
    (runBuilderT' do
       Emits <- fabricateEmitsEvidenceM
       cont1 )
    (\rdecls e -> runBuilderT' $ cont2 (unRNest rdecls) e)
  {-# INLINE buildScopedAndThen #-}

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
  buildScopedAndThen cont1 cont2 = SubstReaderT \env ->
    buildScopedAndThen
      (runReaderT (runSubstReaderT' cont1) (sink env))
      (\d e -> runReaderT (runSubstReaderT' $ cont2 d e) (sink env))
  {-# INLINE buildScopedAndThen #-}

instance (SinkableV v, Builder r m) => Builder r (SubstReaderT v m i) where
  rawEmitDecl hint ann expr = liftSubstReaderT $ emitDecl hint ann expr
  {-# INLINE rawEmitDecl #-}

instance (SinkableE e, ScopableBuilder r m) => ScopableBuilder r (OutReaderT e m) where
  buildScopedAndThen cont1 cont2 = OutReaderT $ ReaderT \env ->
    buildScopedAndThen
      (do env' <- sinkM env
          runReaderT (runOutReaderT' cont1) env')
      (\d e -> do
          env' <- sinkM env
          runReaderT (runOutReaderT' $ cont2 d e) env')
  {-# INLINE buildScopedAndThen #-}

instance (SinkableE e, Builder r m) => Builder r (OutReaderT e m) where
  rawEmitDecl hint ann expr =
    OutReaderT $ lift $ emitDecl hint ann expr
  {-# INLINE rawEmitDecl #-}

instance (SinkableE e, ScopableBuilder r m) => ScopableBuilder r (ReaderT1 e m) where
  buildScopedAndThen cont1 cont2 = ReaderT1 $ ReaderT \env ->
    buildScopedAndThen
      (do env' <- sinkM env
          runReaderT (runReaderT1' cont1) env')
      (\d e -> do
          env' <- sinkM env
          runReaderT (runReaderT1' $ cont2 d e) env')

  {-# INLINE buildScopedAndThen #-}

instance (SinkableE e, Builder r m) => Builder r (ReaderT1 e m) where
  rawEmitDecl hint ann expr =
    ReaderT1 $ lift $ emitDecl hint ann expr
  {-# INLINE rawEmitDecl #-}

instance (DiffStateE s d, Builder r m) => Builder r (DiffStateT1 s d m) where
  rawEmitDecl hint ann expr = lift11 $ rawEmitDecl hint ann expr
  {-# INLINE rawEmitDecl #-}

instance (SinkableE e, HoistableState e, Builder r m) => Builder r (StateT1 e m) where
  rawEmitDecl hint ann expr = lift11 $ emitDecl hint ann expr
  {-# INLINE rawEmitDecl #-}

instance (SinkableE e, HoistableState e, ScopableBuilder r m) => ScopableBuilder r (StateT1 e m) where
  buildScopedAndThen cont1 cont2 = StateT1 \s1 -> do
    buildScopedAndThen
       (liftM toPairE $ runStateT1 cont1 =<< sinkM s1)
       (\decls (PairE e s2) -> do
           let s3 = hoistState s1 decls s2
           (ans, s4) <- runStateT1 (cont2 decls e) (sink s3)
           let s5 = hoistState s3 decls s4
           return (ans, s5))

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
buildBlock cont = buildScoped $ toExpr <$> cont

buildBlockExpr
  :: ScopableBuilder r m
  => (forall l. (Emits l, DExt n l) => m l (Atom r l))
  -> m n (Expr r n)
buildBlockExpr cont = mkBlockExpr =<< buildBlock cont

buildCoreLam
  :: ScopableBuilder CoreIR m
  => CorePiType n
  -> (forall l. (Emits l, DExt n l) => [CAtomVar l] -> m l (CAtom l))
  -> m n (CoreLamExpr n)
buildCoreLam piTy@(CorePiType _ _ bs _) cont = do
  lam <- buildLamExpr (EmptyAbs bs) cont
  return $ CoreLamExpr piTy lam

buildAbs
  :: (IRRep r, EnvReader m, EnvExtender m, SinkableE e, ToBinding binding (AtomNameC r))
  => NameHint
  -> binding n
  -> (forall l. DExt n l => AtomVar r l -> m l (e l))
  -> m n (Abs (BinderP (AtomNameC r) binding) e n)
buildAbs hint binding cont = do
  withFreshBinder hint binding \b -> do
    case toBinding binding of
      AtomNameBinding atombinding -> do
        ty <- sinkM $ getType atombinding
        body <- cont $ AtomVar (binderName b) ty
        return $ Abs b body
{-# INLINE buildAbs #-}

typesFromNonDepBinderNest
  :: (EnvReader m, Fallible1 m, IRRep r)
  => Nest (Binder r) n l -> m n [Type r n]
typesFromNonDepBinderNest Empty = return []
typesFromNonDepBinderNest (Nest b rest) = do
  Abs rest' UnitE <- return $ assumeConst $ Abs (UnaryNest b) $ Abs rest UnitE
  tys <- typesFromNonDepBinderNest rest'
  return $ binderType b : tys

buildUnaryLamExpr
  :: (ScopableBuilder r m)
  => NameHint -> Type r n
  -> (forall l. (Emits l, Distinct l, DExt n l) => AtomVar r l -> m l (Atom r l))
  -> m n (LamExpr r n)
buildUnaryLamExpr hint ty cont = do
  bs <- withFreshBinder hint ty \b -> return $ EmptyAbs (UnaryNest b)
  buildLamExpr bs \[v] -> cont v

buildBinaryLamExpr
  :: (ScopableBuilder r m)
  => (NameHint, Type r n) -> (NameHint, Type r n)
  -> (forall l. (Emits l, Distinct l, DExt n l) => AtomVar r l -> AtomVar r l -> m l (Atom r l))
  -> m n (LamExpr r n)
buildBinaryLamExpr (h1,t1) (h2,t2) cont = do
  bs <- withFreshBinder h1 t1 \b1 -> withFreshBinder h2 (sink t2) \b2 ->
    return $ EmptyAbs $ BinaryNest b1 b2
  buildLamExpr bs \[v1, v2] -> cont v1 v2

buildLamExpr
  :: ScopableBuilder r m
  => (EmptyAbs (Nest (Binder r)) n)
  -> (forall l. (Emits l, Distinct l, DExt n l) => [AtomVar r l] -> m l (Atom r l))
  -> m n (LamExpr r n)
buildLamExpr (Abs bs UnitE) cont = case bs of
  Empty -> LamExpr Empty <$> buildBlockExpr (cont [])
  Nest b rest -> do
    Abs b' (LamExpr bs' body') <- buildAbs (getNameHint b) (binderType b) \v -> do
      rest' <- applySubst (b@>SubstVal (Var v)) $ EmptyAbs rest
      buildLamExpr rest' \vs -> cont $ sink v : vs
    return $ LamExpr (Nest b' bs') body'

buildTopLamFromPi
  :: ScopableBuilder r m
  => PiType r n
  -> (forall l. (Emits l, Distinct l, DExt n l) => [AtomVar r l] -> m l (Atom r l))
  -> m n (TopLam r n)
buildTopLamFromPi piTy@(PiType bs _) cont =
  TopLam False piTy <$> buildLamExpr (EmptyAbs bs) cont

buildAlt
  :: ScopableBuilder r m
  => Type r n
  -> (forall l. (Distinct l, Emits l, DExt n l) => AtomVar r l -> m l (Atom r l))
  -> m n (Alt r n)
buildAlt ty body = do
  buildAbs noHint ty \x ->
    buildBlockExpr do
      Distinct <- getDistinct
      body $ sink x

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
    originalResult <- emitExpr =<< applySubst (b@>SubstVal (Var v)) body
    (dataResult, nonDataResult) <- fromPair originalResult
    return $ PairVal dataResult $ ACon $ SumCon (sinkList sumTys) con nonDataResult

-- TODO: consider a version with nonempty list of alternatives where we figure
-- out the result type from one of the alts rather than providing it explicitly
buildCase' :: (Emits n, ScopableBuilder r m)
  => Atom r n -> Type r n
  -> (forall l. (Emits l, DExt n l) => Int -> Atom r l -> m l (Atom r l))
  -> m n (Expr r n)
buildCase' scrut resultTy indexedAltBody = do
  case trySelectBranch scrut of
    Just (i, arg) -> do
      Distinct <- getDistinct
      toExpr <$> indexedAltBody i (sink arg)
    Nothing -> do
      scrutTy <- return $ getType scrut
      altBinderTys <- caseAltsBinderTys scrutTy
      (alts, effs) <- unzip <$> forM (enumerate altBinderTys) \(i, bTy) -> do
        (Abs b' (body `PairE` eff')) <- buildAbs noHint bTy \x -> do
          blk <- buildBlockExpr $ indexedAltBody i $ AVar $ sink x
          return $ blk `PairE` (getEffects blk)
        return (Abs b' body, ignoreHoistFailure $ hoist b' eff')
      return $ Case (toExpr scrut) alts $ EffTy (mconcat effs) resultTy

buildCase :: (Emits n, ScopableBuilder r m)
  => Atom r n -> Type r n
  -> (forall l. (Emits l, DExt n l) => Int -> Atom r l -> m l (Atom r l))
  -> m n (Atom r n)
buildCase s r b = emitExpr =<< buildCase' s r b

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
      body' <- buildBlockExpr $ body (sink hVar) $ sink ref
      return $ LamExpr (BinaryNest h b) body'

buildForAnn
  :: (Emits n, ScopableBuilder r m)
  => NameHint -> ForAnn -> IxType r n
  -> (forall l. (Emits l, DExt n l) => AtomVar r l -> m l (Atom r l))
  -> m n (Atom r n)
buildForAnn hint ann (IxType iTy ixDict) body = do
  lam <- withFreshBinder hint iTy \b -> do
    let v = binderVar b
    body' <- buildBlockExpr $ body $ sink v
    return $ LamExpr (UnaryNest b) body'
  emitHof $ For ann (IxType iTy ixDict) lam

buildFor :: (Emits n, ScopableBuilder r m)
         => NameHint -> Direction -> IxType r n
         -> (forall l. (Emits l, DExt n l) => AtomVar r l -> m l (Atom r l))
         -> m n (Atom r n)
buildFor hint dir ty body = buildForAnn hint dir ty body

buildMap :: (Emits n, ScopableBuilder r m)
         => Atom r n
         -> (forall l. (Emits l, DExt n l) => Atom r l -> m l (Atom r l))
         -> m n (Atom r n)
buildMap xs f = do
  TabPi t <- return $ getType xs
  buildFor noHint Fwd (tabIxType t) \i ->
    tabApp (sink xs) (AVar i) >>= f

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
  emitHof $ RunState Nothing (toExpr initVal) lam

emitRunReader
  :: (Emits n, ScopableBuilder r m)
  => NameHint -> Atom r n
  -> (forall l. (Emits l, DExt n l) => AtomVar r l -> AtomVar r l -> m l (Atom r l))
  -> m n (Atom r n)
emitRunReader hint r body = do
  rTy <- return $ getType r
  lam <- buildEffLam hint rTy \h ref -> body h ref
  emitHof $ RunReader (toExpr r) lam

emitSeq :: (Emits n, ScopableBuilder SimpIR m)
        => Direction -> IxType SimpIR n -> Atom SimpIR n -> LamExpr SimpIR n
        -> m n (Atom SimpIR n)
emitSeq d t x f = do
  op <- mkSeq d t (toExpr x) f
  emitExpr $ PrimOp $ DAMOp op

buildRememberDest :: (Emits n, ScopableBuilder SimpIR m)
  => NameHint -> SAtom n
  -> (forall l. (Emits l, Distinct l, DExt n l) => SAtomVar l -> m l (SAtom l))
  -> m n (SAtom n)
buildRememberDest hint dest cont = do
  ty <- return $ getType dest
  doit <- buildUnaryLamExpr hint ty cont
  effs <- functionEffs doit
  emitExpr $ PrimOp $ DAMOp $ RememberDest effs (toExpr dest) doit

-- === vector space (ish) type class ===

zeroAt :: (Emits n, SBuilder m) => SType n -> m n (SAtom n)
zeroAt ty = liftEmitBuilder $ go ty where
  go :: Emits n => SType n -> BuilderM SimpIR n (SAtom n)
  go = \case
   BaseTy bt  -> return $ ACon $ Lit $ zeroLit bt
   ProdTy tys -> ProdVal <$> mapM go tys
   TabPi tabPi -> buildFor (getNameHint tabPi) Fwd (tabIxType tabPi) \i ->
     go =<< instantiate (sink tabPi) [Var i]
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
  adder <- liftBuilder $ buildBinaryLamExpr (noHint, ty) (noHint, ty) \x y -> addTangent (AVar x) (AVar y)
  return $ BaseMonoid (toExpr zero) adder

addTangent :: (Emits n, SBuilder m) => SAtom n -> SAtom n -> m n (SAtom n)
addTangent x y = do
  case getType x of
    TabPi t ->
      liftEmitBuilder $ buildFor (getNameHint t) Fwd (tabIxType t) \i -> do
        bindM2 addTangent (tabApp (sink x) (AVar i)) (tabApp (sink y) (AVar i))
    TC con -> case con of
      BaseType (Scalar _) -> emitOp $ BinOp FAdd (toExpr x) (toExpr y)
      ProdType _          -> do
        xs <- getUnpacked x
        ys <- getUnpacked y
        ProdVal <$> zipWithM addTangent xs ys
      ty -> notTangent ty
    ty -> notTangent ty
    where notTangent ty = error $ "Not a tangent type: " ++ pprint ty

symbolicTangentTy :: (EnvReader m, Fallible1 m) => CType n -> m n (CType n)
symbolicTangentTy elTy = undefined
-- symbolicTangentTy elTy = lookupSourceMap "SymbolicTangent" >>= \case
--   Just (UTyConVar symTanName) -> do
--     return $ TypeCon "SymbolicTangent" symTanName $
--       TyConParams [Explicit] [Type elTy]
--   Nothing -> throw UnboundVarErr $
--     "Can't define a custom linearization with symbolic zeros: " ++
--     "the SymbolicTangent type is not in scope."
--   Just _ -> throw TypeErr "SymbolicTangent should name a `data` type"

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
    BaseTy (Scalar Float64Type) -> return $ ACon $ Lit $ Float64Lit x
    BaseTy (Scalar Float32Type) -> return $ ACon $ Lit $ Float32Lit $ realToFrac x
    _ -> error "Expected a floating point scalar"

neg :: (Builder r m, Emits n) => Atom r n -> m n (Atom r n)
neg x = emitOp $ UnOp FNeg (toExpr x)

add :: (Builder r m, Emits n) => Atom r n -> Atom r n -> m n (Atom r n)
add x y = emitOp $ BinOp FAdd (toExpr x) (toExpr y)

-- TODO: Implement constant folding for fixed-width integer types as well!
iadd :: (Builder r m, Emits n) => Atom r n -> Atom r n -> m n (Atom r n)
iadd (ACon (Lit l)) y | getIntLit l == 0 = return y
iadd x (ACon (Lit l)) | getIntLit l == 0 = return x
iadd x@(ACon (Lit _)) y@(ACon (Lit _)) = return $ applyIntBinOp (+) x y
iadd x y = emitOp $ BinOp IAdd (toExpr x) (toExpr y)

mul :: (Builder r m, Emits n) => Atom r n -> Atom r n -> m n (Atom r n)
mul x y = emitOp $ BinOp FMul (toExpr x) (toExpr y)

imul :: (Builder r m, Emits n) => Atom r n -> Atom r n -> m n (Atom r n)
imul   (ACon (Lit l)) y               | getIntLit l == 1 = return y
imul x                 (ACon (Lit l)) | getIntLit l == 1 = return x
imul x@(ACon (Lit _)) y@(ACon (Lit _))                    = return $ applyIntBinOp (*) x y
imul x y = emitOp $ BinOp IMul (toExpr x) (toExpr y)

sub :: (Builder r m, Emits n) => Atom r n -> Atom r n -> m n (Atom r n)
sub x y = emitOp $ BinOp FSub (toExpr x) (toExpr y)

isub :: (Builder r m, Emits n) => Atom r n -> Atom r n -> m n (Atom r n)
isub x (ACon (Lit l)) | getIntLit l == 0 = return x
isub x@(ACon (Lit _)) y@(ACon (Lit _)) = return $ applyIntBinOp (-) x y
isub x y = emitOp $ BinOp ISub (toExpr x) (toExpr y)

select :: (Builder r m, Emits n) => Atom r n -> Atom r n -> Atom r n -> m n (Atom r n)
select (ACon (Lit (Word8Lit p))) x y = return $ if p /= 0 then x else y
select p x y = emitOp $ MiscOp $ Select (toExpr p) (toExpr x) (toExpr y)

div' :: (Builder r m, Emits n) => Atom r n -> Atom r n -> m n (Atom r n)
div' x y = emitOp $ BinOp FDiv (toExpr x) (toExpr y)

idiv :: (Builder r m, Emits n) => Atom r n -> Atom r n -> m n (Atom r n)
idiv x (ACon (Lit l)) | getIntLit l == 1 = return x
idiv x@(ACon (Lit _)) y@(ACon (Lit _)) = return $ applyIntBinOp div x y
idiv x y = emitOp $ BinOp IDiv (toExpr x) (toExpr y)

irem :: (Builder r m, Emits n) => Atom r n -> Atom r n -> m n (Atom r n)
irem x y = emitOp $ BinOp IRem (toExpr x) (toExpr y)

fpow :: (Builder r m, Emits n) => Atom r n -> Atom r n -> m n (Atom r n)
fpow x y = emitOp $ BinOp FPow (toExpr x) (toExpr y)

flog :: (Builder r m, Emits n) => Atom r n -> m n (Atom r n)
flog x = emitOp $ UnOp Log (toExpr x)

ilt :: (Builder r m, Emits n) => Atom r n -> Atom r n -> m n (Atom r n)
ilt x@(ACon (Lit _)) y@(ACon (Lit _)) = return $ applyIntCmpOp (<) x y
ilt x y = emitOp $ BinOp (ICmp Less) (toExpr x) (toExpr y)

ieq :: (Builder r m, Emits n) => Atom r n -> Atom r n -> m n (Atom r n)
ieq x@(ACon (Lit _)) y@(ACon (Lit _)) = return $ applyIntCmpOp (==) x y
ieq x y = emitOp $ BinOp (ICmp Equal) (toExpr x) (toExpr y)

fromPair :: (Fallible1 m, EnvReader m, IRRep r) => Atom r n -> m n (Atom r n, Atom r n)
fromPair pair = do
  getUnpacked pair >>= \case
    [x, y] -> return (x, y)
    _ -> error "expected a pair"

getFst :: Builder r m => Atom r n -> m n (Atom r n)
getFst p = fst <$> fromPair p

getSnd :: Builder r m => Atom r n -> m n (Atom r n)
getSnd p = snd <$> fromPair p

-- the rightmost index is applied first
getNaryProjRef :: (Builder r m, Emits n) => [Projection] -> Atom r n -> m n (Atom r n)
getNaryProjRef [] ref = return ref
getNaryProjRef (i:is) ref = getProjRef i =<< getNaryProjRef is ref

getProjRef :: (Builder r m, Emits n) => Projection -> Atom r n -> m n (Atom r n)
getProjRef i r = emitOp =<< mkProjRef (toExpr r) i

-- XXX: getUnpacked must reduce its argument to enforce the invariant that
-- ProjectElt atoms are always fully reduced (to avoid type errors between two
-- equivalent types spelled differently).
getUnpacked :: (Fallible1 m, EnvReader m, IRRep r) => Atom r n -> m n [Atom r n]
getUnpacked atom = undefined
-- getUnpacked atom = do
--   atom' <- cheapNormalize atom
--   ty <- return $ getType atom'
--   positions <- case ty of
--     ProdTy tys  -> return $ void tys
--     DepPairTy _ -> return [(), ()]
--     _ -> error $ "not a product type: " ++ pprint ty
--   forM (enumerate positions) \(i, _) ->
--     normalizeProj (ProjectProduct i) atom'
-- {-# SCC getUnpacked #-}

getProj :: (Builder r m, Emits n) => Int -> Atom r n -> m n (Atom r n)
getProj i atom = undefined
  -- atom' <- cheapNormalize atom
  -- normalizeProj (ProjectProduct i) atom'

unwrapNewtype :: (Builder CoreIR m, Emits n) => CAtom n -> m n (CAtom n)
unwrapNewtype (ACon (NewtypeCon _ x)) = return x
unwrapNewtype x = case getType x of
  NewtypeTyCon con -> do
    (_, ty) <- unwrapNewtypeType con
    emitExpr $ ProjectElt ty UnwrapNewtype (toExpr x)
  _ -> error "not a newtype"
{-# INLINE unwrapNewtype #-}

projectTuple :: (IRRep r, EnvReader m) => Int -> Atom r n -> m n (Atom r n)
projectTuple i x = undefined
-- normalizeProj (ProjectProduct i) x
-- projectTuple i x = normalizeProj (ProjectProduct i) x

projectStruct :: EnvReader m => Int -> CAtom n -> m n (CAtom n)
projectStruct i x = undefined
-- projectStruct i x = do
--   projs <- getStructProjections i (getType x)
--   normalizeNaryProj projs x
-- {-# INLINE projectStruct #-}

projectStructRef :: (Builder CoreIR m, Emits n) => Int -> CAtom n -> m n (CAtom n)
projectStructRef i x = do
  RefTy _ valTy <- return $ getType x
  projs <- getStructProjections i valTy
  getNaryProjRef projs x
{-# INLINE projectStructRef #-}

getStructProjections :: EnvReader m => Int -> CType n -> m n [Projection]
getStructProjections i (NewtypeTyCon (UserADTType _ tyConName _)) = do
  TyConDef _ _ _ ~(StructFields fields) <- lookupTyCon tyConName
  return case fields of
    [_] | i == 0    -> [UnwrapNewtype]
        | otherwise -> error "bad index"
    _ -> [ProjectProduct i, UnwrapNewtype]
getStructProjections _ _ = error "not a struct"

app :: (CBuilder m, Emits n) => CAtom n -> CAtom n -> m n (CAtom n)
app x i = mkApp (toExpr x) [toExpr i] >>= emitExpr

naryApp :: (CBuilder m, Emits n) => CAtom n -> [CAtom n] -> m n (CAtom n)
naryApp = naryAppHinted noHint
{-# INLINE naryApp #-}

naryTopApp :: (Builder SimpIR m, Emits n) => TopFunName n -> [SAtom n] -> m n (SAtom n)
naryTopApp f xs = emitExpr =<< mkTopApp f (toExpr <$> xs)
{-# INLINE naryTopApp #-}

naryTopAppInlined :: (Builder SimpIR m, Emits n) => TopFunName n -> [SAtom n] -> m n (SAtom n)
naryTopAppInlined f xs = do
  TopFunBinding f' <- lookupEnv f
  case f' of
    DexTopFun _ lam _ -> instantiate lam (toExpr <$> xs) >>= emitExpr
    _ -> naryTopApp f xs
{-# INLINE naryTopAppInlined #-}

naryAppHinted :: (CBuilder m, Emits n)
  => NameHint -> CAtom n -> [CAtom n] -> m n (CAtom n)
naryAppHinted hint f xs = AVar <$> (mkApp (toExpr f) (toExpr <$> xs) >>= emitHinted hint)

tabApp :: (Builder r m, Emits n) => Atom r n -> Atom r n -> m n (Atom r n)
tabApp x i = mkTabApp (toExpr x) [toExpr i] >>= emitExpr

naryTabApp :: (Builder r m, Emits n) => Atom r n -> [Atom r n] -> m n (Atom r n)
naryTabApp = naryTabAppHinted noHint
{-# INLINE naryTabApp #-}

naryTabAppHinted :: (Builder r m, Emits n)
  => NameHint -> Atom r n -> [Atom r n] -> m n (Atom r n)
naryTabAppHinted hint f xs = do
  expr <- mkTabApp (toExpr f) (toExpr <$> xs)
  AVar <$> emitHinted hint expr

indexRef :: (Builder r m, Emits n) => Atom r n -> Atom r n -> m n (Atom r n)
indexRef ref i = emitOp =<< mkIndexRef (toExpr ref) (toExpr i)

naryIndexRef :: (Builder r m, Emits n) => Atom r n -> [Atom r n] -> m n (Atom r n)
naryIndexRef ref is = foldM indexRef ref is

ptrOffset :: (Builder r m, Emits n) => Atom r n -> Atom r n -> m n (Atom r n)
ptrOffset x (IdxRepVal 0) = return x
ptrOffset x i = emitOp $ MemOp $ PtrOffset (toExpr x) (toExpr i)
{-# INLINE ptrOffset #-}

unsafePtrLoad :: (Builder r m, Emits n) => Atom r n -> m n (Atom r n)
unsafePtrLoad x = emitHof $ RunIO $ PrimOp $ MemOp $ PtrLoad $ toExpr x

-- === index set type class ===

applyIxMethod :: (SBuilder m, Emits n) => IxDict SimpIR n -> IxMethod -> [SAtom n] -> m n (SAtom n)
applyIxMethod dict method args = case dict of
  -- These cases are used in SimpIR and they work with IdxRepVal
  IxDictRawFin n -> case method of
    Size              -> do []  <- return args; return n >>= emitExpr
    Ordinal           -> do [i] <- return args; return i
    UnsafeFromOrdinal -> do [i] <- return args; return i
  IxDictSpecialized _ d params -> do
    SpecializedDict _ maybeFs <- lookupSpecDict d
    Just fs <- return maybeFs
    instantiate (fs !! fromEnum method) (params ++ (toExpr <$> args)) >>= emitExpr

unsafeFromOrdinal :: (SBuilder m, Emits n) => IxType SimpIR n -> Atom SimpIR n -> m n (Atom SimpIR n)
unsafeFromOrdinal (IxType _ dict) i = applyIxMethod dict UnsafeFromOrdinal [i]

ordinal :: (SBuilder m, Emits n) => IxType SimpIR n -> Atom SimpIR n -> m n (Atom SimpIR n)
ordinal (IxType _ dict) idx = applyIxMethod dict Ordinal [idx]

indexSetSize :: (SBuilder m, Emits n) => IxType SimpIR n -> m n (SAtom n)
indexSetSize (IxType _ dict) = applyIxMethod dict Size []

-- === core versions of index set type class ===

applyIxMethodCore :: (CBuilder m, Emits n) => IxMethod -> IxType CoreIR n -> [CAtom n] -> m n (CAtom n)
applyIxMethodCore method (IxType _ (IxDictAtom dict)) args = do
  emitExpr =<< mkApplyMethod dict (fromEnum method) (toExpr <$> args)
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
  predicate' <- emitOp $ MiscOp $ ToEnum (SumTy [UnitTy, UnitTy]) (toExpr predicate)
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
  TabPi tabPi <- return $ getType xs
  let a = assumeConst tabPi
  getSnd =<< emitRunWriter noHint a monoid \_ ref ->
    buildFor noHint Fwd (sink $ tabIxType tabPi) \i -> do
      x <- toExpr <$> tabApp (sink xs) (AVar i)
      emitExpr $ PrimOp $ RefOp (sink $ Var ref) $ MExtend (sink monoid) x

assumeConst
  :: (IRRep r, HoistableE body, SinkableE body, ToBindersAbs e body r) => e n -> body n
assumeConst e = case toAbs e of Abs bs body -> ignoreHoistFailure $ hoist bs body

andMonoid :: (EnvReader m, IRRep r) => m n (BaseMonoid r n)
andMonoid = liftM (BaseMonoid (toExpr TrueAtom)) $ liftBuilder $
  buildBinaryLamExpr (noHint, BoolTy) (noHint, BoolTy) \x y ->
    emitOp $ BinOp BAnd (sink $ Var x) (Var y)

-- (a-> {|eff} b) -> n=>a -> {|eff} (n=>b)
mapE :: (Emits n, ScopableBuilder r m)
     => (forall l. (Emits l, DExt n l) => Atom r l -> m l (Atom r l))
     -> Atom r n -> m n (Atom r n)
mapE cont xs = do
  TabPi tabPi <- return $ getType xs
  buildFor (getNameHint tabPi) Fwd (tabIxType tabPi) \i -> do
    tabApp (sink xs) (AVar i) >>= cont

-- (n:Type) ?-> (a:Type) ?-> (xs : n=>Maybe a) : Maybe (n => a) =
catMaybesE :: (Emits n, Builder r m) => Atom r n -> m n (Atom r n)
catMaybesE maybes = do
  TabTy d n (MaybeTy a) <- return $ getType maybes
  justs <- liftEmitBuilder $ mapE isJustE maybes
  monoid <- andMonoid
  allJust <- reduceE monoid justs
  liftEmitBuilder $ emitIf allJust (MaybeTy $ TabTy d n a)
    (JustAtom (sink $ TabTy d n a) <$> mapE fromJustE (sink maybes))
    (return (NothingAtom $ sink $ TabTy d n a))

emitWhile :: (Emits n, ScopableBuilder r m)
          => (forall l. (Emits l, DExt n l) => m l (Atom r l))
          -> m n ()
emitWhile cont = do
  body <- buildBlockExpr cont
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
        (emit (PrimOp $ RefOp (sink $ Var ref) $ MPut (toExpr TrueAtom)) >> return FalseAtom)
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
instance (Color c, ToBinding e c, SubstE ExprSubstVal e) => SubstE ExprSubstVal (TelescopeType c e)
instance (Color c, HoistableE e) => HoistableE (TelescopeType c e)

telescopicCapture
  :: (EnvReader m, HoistableE e, HoistableB b, IRRep r)
  => b n l -> e l -> m l (Atom r l, ReconAbs r e n)
telescopicCapture bs e = undefined
-- telescopicCapture bs e = do
--   vs <- localVarsAndTypeVars bs e
--   vTys <- forM vs \v -> getType <$> toAtomVar v
--   let vsTysSorted = toposortAnnVars $ zip vs vTys
--   let vsSorted = map fst vsTysSorted
--   ty <- liftEnvReaderM $ buildTelescopeTy vsTysSorted
--   valsSorted <- forM vsSorted \v -> Var <$> toAtomVar v
--   result <- buildTelescopeVal valsSorted ty
--   reconAbs <- return $ ignoreHoistFailure $ hoist bs do
--     case abstractFreeVarsNoAnn vsSorted e of
--       Abs bs' e' -> Abs (ReconBinders ty bs') e'
--   return (result, reconAbs)

applyReconAbs
  :: (EnvReader m, Fallible1 m, SinkableE e, SubstE ExprSubstVal e, IRRep r)
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

-- buildTelescopeVal
--   :: (EnvReader m, IRRep r) => [Atom r n]
--   -> TelescopeType (AtomNameC r) (Type r) n -> m n (Atom r n)
-- buildTelescopeVal xsTop tyTop = undefined
-- buildTelescopeVal xsTop tyTop = fst <$> go tyTop xsTop where
--   go :: (EnvReader m, IRRep r)
--      => TelescopeType (AtomNameC r) (Type r) n ->  [Atom r n]
--      -> m n (Atom r n, [Atom r n])
--   go ty rest = case ty of
--     ProdTelescope tys -> do
--       (xs, rest') <- return $ splitAt (length tys) rest
--       return (ProdVal xs, rest')
--     DepTelescope ty1 (Abs b ty2) -> do
--       (x1, ~(xDep : rest')) <- go ty1 rest
--       ty2' <- applySubst (b@>SubstVal xDep) ty2
--       (x2, rest'') <- go ty2' rest'
--       let depPairTy = DepPairType ExplicitDepPair b (telescopeTypeType ty2)
--       return (PairVal x1 (DepPair xDep x2 depPairTy), rest'')

telescopeTypeType :: TelescopeType (AtomNameC r) (Type r) n -> Type r n
telescopeTypeType (ProdTelescope tys) = ProdTy tys
telescopeTypeType (DepTelescope lhs (Abs b rhs)) = do
  let lhs' = telescopeTypeType lhs
  let rhs' = DepPairTy (DepPairType ExplicitDepPair b (telescopeTypeType rhs))
  PairTy lhs' rhs'

unpackTelescope
  :: (Fallible1 m, EnvReader m, IRRep r)
  => ReconBinders r l1 l2 -> Atom r n -> m n [Expr r n]
unpackTelescope (ReconBinders tyTop _) xTop = undefined
-- unpackTelescope (ReconBinders tyTop _) xTop = go tyTop xTop where
--   go :: (Fallible1 m, EnvReader m, IRRep r)
--      => TelescopeType c e l-> Atom r n -> m n [Atom r n]
--   go ty x = case ty of
--     ProdTelescope _ -> getUnpacked x
--     DepTelescope ty1 (Abs _  ty2) -> do
--       (x1, xPair) <- fromPair x
--       (xDep, x2) <- fromPair xPair
--       xs1 <- go ty1 x1
--       xs2 <- go ty2 x2
--       return $ xs1 ++ (xDep : xs2)

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
  visitBinders bs \bs' -> LamExpr bs' <$> visitExprNoEmits body

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
  AtomSubstBuilder { runAtomSubstBuilder :: SubstReaderT ExprSubstVal (BuilderM r) i o a}
  deriving (MonadFail, Fallible, Functor, Applicative, Monad, ScopeReader,
            EnvReader, EnvExtender, Builder r, SubstReader ExprSubstVal,
            ScopableBuilder r)

visitLamEmits
  :: (ExprVisitorEmits2 m r, IRRep r, SubstReader ExprSubstVal m, ScopableBuilder2 r m)
  => LamExpr r i -> m i o (LamExpr r o)
visitLamEmits (LamExpr bs body) = visitBinders bs \bs' -> LamExpr bs' <$>
  buildBlockExpr (visitExprEmits body)

blockAsExpr :: WithDecls r (Expr r) n -> Expr r n
blockAsExpr = undefined

-- === Helpers for function evaluation over fixed-width types ===

applyIntBinOp' :: (forall a. (Eq a, Ord a, Num a, Integral a)
               => (a -> Atom r n) -> a -> a -> Atom r n) -> Atom r n -> Atom r n -> Atom r n
applyIntBinOp' f x y = case (x, y) of
  (ACon (Lit (Int64Lit xv)), ACon (Lit (Int64Lit yv))) -> f (ACon . Lit . Int64Lit) xv yv
  (ACon (Lit (Int32Lit xv)), ACon (Lit (Int32Lit yv))) -> f (ACon . Lit . Int32Lit) xv yv
  (ACon (Lit (Word8Lit xv)), ACon (Lit (Word8Lit yv))) -> f (ACon . Lit . Word8Lit) xv yv
  (ACon (Lit (Word32Lit xv)), ACon (Lit (Word32Lit yv))) -> f (ACon . Lit . Word32Lit) xv yv
  (ACon (Lit (Word64Lit xv)), ACon (Lit (Word64Lit yv))) -> f (ACon . Lit . Word64Lit) xv yv
  _ -> error "Expected integer atoms"

applyIntBinOp :: (forall a. (Num a, Integral a) => a -> a -> a) -> Atom r n -> Atom r n -> Atom r n
applyIntBinOp f x y = applyIntBinOp' (\w -> w ... f) x y

applyIntCmpOp :: (forall a. (Eq a, Ord a) => a -> a -> Bool) -> Atom r n -> Atom r n -> Atom r n
applyIntCmpOp f x y = applyIntBinOp' (\_ -> (ACon . Lit . Word8Lit . fromIntegral . fromEnum) ... f) x y

applyFloatBinOp :: (forall a. (Num a, Fractional a) => a -> a -> a) -> Atom r n -> Atom r n -> Atom r n
applyFloatBinOp f x y = case (x, y) of
  (ACon (Lit (Float64Lit xv)), ACon (Lit (Float64Lit yv))) -> ACon $ Lit $ Float64Lit $ f xv yv
  (ACon (Lit (Float32Lit xv)), ACon (Lit (Float32Lit yv))) -> ACon $ Lit $ Float32Lit $ f xv yv
  _ -> error "Expected float atoms"

_applyFloatUnOp :: (forall a. (Num a, Fractional a) => a -> a) -> Atom r n -> Atom r n
_applyFloatUnOp f x = applyFloatBinOp (\_ -> f) (error "shouldn't be needed") x
