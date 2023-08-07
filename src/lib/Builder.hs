-- Copyright 2021 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}

module Builder where

import Control.Category ((>>>))
import Control.Applicative
import Control.Monad
import Control.Monad.Reader
import Control.Monad.Writer.Strict hiding (Alt)
import Control.Monad.State.Strict (MonadState (..), StateT (..), runStateT)
import qualified Data.Map.Strict as M
import Data.List (elemIndex)
import Data.Functor ((<&>))
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
import QueryTypePure
import Types.Core
import Types.Imp
import Types.Primitives
import Types.Source hiding (fromName)
import Util
import Visit

-- === Ordinary (local) builder class ===

class (EnvReader m, EnvExtender m, Fallible1 m, IRRep r)
      => Builder (r::IR) (m::MonadKind1) | m -> r where
  rawEmitDecl :: Emits n => NameHint -> LetAnn -> Expr r n -> m n (AtomVar r n)

class Builder r m => ScopableBuilder (r::IR) (m::MonadKind1) | m -> r where
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

type BuilderEmits r m n = (IRRep r, Builder r m, Emits n)
type SBuilderEmits m n = BuilderEmits SimpIR m n
type CBuilderEmits m n = BuilderEmits CoreIR m n

emitDecl :: BuilderEmits r m n => NameHint -> LetAnn -> Expr r n -> m n (AtomVar r n)
emitDecl _ _ (Atom (Var n)) = return n
emitDecl hint ann expr = rawEmitDecl hint ann expr
{-# INLINE emitDecl #-}

emit :: BuilderEmits r m n => Expr r n -> m n (AtomVar r n)
emit expr = emitDecl noHint PlainLet expr
{-# INLINE emit #-}

emitHinted :: BuilderEmits r m n => NameHint -> Expr r n -> m n (AtomVar r n)
emitHinted hint expr = emitDecl hint PlainLet expr
{-# INLINE emitHinted #-}

emitOp :: (Builder r m, IsPrimOp e, Emits n) => e r n -> m n (Atom r n)
emitOp op = Var <$> emit (PrimOp $ toPrimOp op)
{-# INLINE emitOp #-}

emitExpr :: BuilderEmits r m n => Expr r n -> m n (Atom r n)
emitExpr expr = Var <$> emit expr
{-# INLINE emitExpr #-}

emitHof :: BuilderEmits r m n => Hof r n -> m n (Atom r n)
emitHof hof = mkTypedHof hof >>= emitOp

mkTypedHof :: BuilderEmits r m n => Hof r n -> m n (TypedHof r n)
mkTypedHof hof = do
  effTy <- effTyOfHof hof
  return $ TypedHof effTy hof

emitUnOp :: BuilderEmits r m n => UnOp -> Atom r n -> m n (Atom r n)
emitUnOp op x = emitOp $ UnOp op x
{-# INLINE emitUnOp #-}

emitBlock :: BuilderEmits r m n => Block r n -> m n (Atom r n)
emitBlock = emitDecls

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

emitExprToAtom :: BuilderEmits r m n => Expr r n -> m n (Atom r n)
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

emitTopFunBinding :: (Mut n, TopBuilder m) => NameHint -> TopFunDef n -> STopLam n -> m n (TopFunName n)
emitTopFunBinding hint def f = do
  emitBinding hint $ TopFunBinding $ DexTopFun def f Waiting

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

liftBuilder :: forall r m n a. (EnvReader m, IRRep r) => BuilderM r n a -> m n a
liftBuilder cont = liftM runHardFail $ liftBuilderT cont
{-# INLINE liftBuilder #-}

liftBuildScoped
  :: forall r m n a e. (EnvExtender m, SinkableE e, RenameE e, IRRep r)
  => (forall l. (DExt n l, Emits l) => BuilderM r l (e l))
  -> (forall l. DExt n l => Decls r n l -> e l ->  m l a)
  -> m n a
liftBuildScoped cont1 cont2 = do
  ab <- liftBuilder $ buildScoped cont1
  refreshAbs ab cont2
{-# INLINE liftBuildScoped #-}

-- TODO: This should not fabricate Emits evidence!!
-- XXX: this uses unsafe functions in its implementations. It should be safe to
-- use, but be careful changing it.
liftEmitBuilder :: (BuilderEmits r m n, SinkableE e, RenameE e)
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
  buildScopedAndThen cont1 cont2 = SubstReaderT $ ReaderT \env ->
    buildScopedAndThen
      (runReaderT (runSubstReaderT' cont1) (sink env))
      (\d e -> runReaderT (runSubstReaderT' $ cont2 d e) (sink env))
  {-# INLINE buildScopedAndThen #-}

instance (SinkableV v, Builder r m) => Builder r (SubstReaderT v m i) where
  rawEmitDecl hint ann expr = SubstReaderT $ lift $ emitDecl hint ann expr
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

instance (Builder r m) => Builder r (StreamReaderT1 a m) where
  rawEmitDecl hint ann expr =
    StreamReaderT1 $ emitDecl hint ann expr
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
buildBlock = buildScoped

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

typesFromNonDepBinderNest :: BuilderEmits r m n => Binders r n l -> m n [Type r n]
typesFromNonDepBinderNest Empty = return []
typesFromNonDepBinderNest (Nest b rest) = do
  Abs rest' UnitE <- return $ assumeConst $ Abs (UnaryNest b) $ Abs rest UnitE
  t <- binderAndDeclsType b
  ts <- typesFromNonDepBinderNest rest'
  return $ t : ts

buildUnaryLamExpr
  :: ScopableBuilder r m
  => NameHint -> Type r n
  -> (forall l. (Emits l, Distinct l, DExt n l) => AtomVar r l -> m l (Atom r l))
  -> m n (LamExpr r n)
buildUnaryLamExpr hint ty cont = do
  bs <- withFreshBinder hint ty \b -> return $ EmptyAbs (UnaryNest (PlainBD b))
  buildLamExpr bs \[v] -> cont v

buildBinaryLamExpr
  :: ScopableBuilder r m
  => (NameHint, Type r n) -> (NameHint, Type r n)
  -> (forall l. (Emits l, Distinct l, DExt n l) => AtomVar r l -> AtomVar r l -> m l (Atom r l))
  -> m n (LamExpr r n)
buildBinaryLamExpr (h1,t1) (h2,t2) cont = do
  bs <- withFreshBinder h1 t1 \b1 -> withFreshBinder h2 (sink t2) \b2 ->
    return $ EmptyAbs $ BinaryNest (PlainBD b1) (PlainBD b2)
  buildLamExpr bs \[v1, v2] -> cont v1 v2

buildLamExpr
  :: ScopableBuilder r m
  => (Abs (Binders r) any n)
  -> (forall l. (Emits l, Distinct l, DExt n l) => [AtomVar r l] -> m l (Atom r l))
  -> m n (LamExpr r n)
buildLamExpr (Abs bs _) cont =
  refreshAbs (Abs bs UnitE) \bs' UnitE -> do
    body <- buildBlock do
      vs' <- mapM sinkM $ bindersVars bs'
      cont vs'
    return $ LamExpr bs' body

buildTopLamFromPi
  :: (ScopableBuilder r m, Emits n)
  => PiType r n
  -> (forall l. (Emits l, Distinct l, DExt n l) => [AtomVar r l] -> m l (Atom r l))
  -> m n (TopLam r n)
buildTopLamFromPi piTy@(PiType bs _) cont =
  TopLam False piTy <$> buildLamExpr (EmptyAbs bs) cont

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
injectAltResult sumTys con (LamExpr b body) = liftEnvReaderM do
  refreshAbs (Abs b body) \b' body' -> do
    body'' <- liftBuilder $ buildBlock do
       originalResult <- emitBlock $ sink body'
       (dataResult, nonDataResult) <- fromPair originalResult
       return $ PairVal dataResult $ Con $ SumCon (sinkList sumTys) con nonDataResult
    return $ LamExpr b' body''

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
      Atom <$> indexedAltBody i (sink arg)
    Nothing -> do
      scrutTy <- return $ getType scrut
      altBinderTys <- caseAltsBinderTys scrutTy
      alts <- forM (enumerate altBinderTys) \(i, bTy) -> do
        buildUnaryLamExpr noHint bTy \x -> indexedAltBody i $ Var $ sink x
      effs <- caseEffs alts
      return $ Case scrut alts $ EffTy effs resultTy

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
      return $ LamExpr (BinaryNest (PlainBD h) (PlainBD b)) body'

buildForAnn
  :: (Emits n, ScopableBuilder r m)
  => NameHint -> ForAnn -> IxType r n
  -> (forall l. (Emits l, DExt n l) => AtomVar r l -> m l (Atom r l))
  -> m n (Atom r n)
buildForAnn hint ann (IxType iTy ixDict) body = do
  lam <- withFreshBinder hint iTy \b -> do
    let v = binderVar b
    body' <- buildBlock $ body $ sink v
    return $ UnaryLamExpr (PlainBD b) body'
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
  TabPi t <- headNormalize $ getType xs
  ixTy <- tabIxType t
  buildFor noHint Fwd ixTy \i ->
    tabApp (sink xs) (Var i) >>= f

tabIxType :: BuilderEmits r m n => TabPiType r n -> m n (IxType r n)
tabIxType (TabPiType d (BD decls (_:>t)) _) = do
  t' <- emitDecls $ Abs decls t
  return $ IxType t' d

unzipTab :: BuilderEmits r m n => Atom r n -> m n (Atom r n, Atom r n)
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

emitSeq :: SBuilderEmits m n
        => Direction -> IxType SimpIR n -> Atom SimpIR n -> LamExpr SimpIR n
        -> m n (Atom SimpIR n)
emitSeq d t x f = do
  op <- mkSeq d t x f
  emitExpr $ PrimOp $ DAMOp op

mkSeq :: SBuilderEmits m n
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

zeroAt :: SBuilderEmits m n => SType n -> m n (SAtom n)
zeroAt ty = liftEmitBuilder $ go ty where
  go :: Emits n => SType n -> BuilderM SimpIR n (SAtom n)
  go = \case
   BaseTy bt  -> return $ Con $ Lit $ zeroLit bt
   ProdTy tys -> ProdVal <$> mapM go tys
   TabPi tabPi -> do
     ixTy <- tabIxType tabPi
     buildFor (getNameHint tabPi) Fwd ixTy \i ->
       go =<< instantiate tabPi [Var i]
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
  TabTy d b (Abs decls bodyTy) -> do
    refreshAbs (Abs (PairB b decls) bodyTy) \(PairB b' decls') bodyTy' -> do
      bodyTanTy <- rec bodyTy'
      return $ TabTy d b' $ Abs decls' bodyTanTy
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
  headNormalize (getType x) >>= \case
    TabPi t -> do
      ixTy <- tabIxType t
      liftEmitBuilder $ buildFor (getNameHint t) Fwd ixTy \i -> do
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

fLitLike :: BuilderEmits r m n => Double -> Atom r n -> m n (Atom r n)
fLitLike x t = do
  ty <- return $ getType t
  case ty of
    BaseTy (Scalar Float64Type) -> return $ Con $ Lit $ Float64Lit x
    BaseTy (Scalar Float32Type) -> return $ Con $ Lit $ Float32Lit $ realToFrac x
    _ -> error "Expected a floating point scalar"

neg :: BuilderEmits r m n => Atom r n -> m n (Atom r n)
neg x = emitOp $ UnOp FNeg x

add :: BuilderEmits r m n => Atom r n -> Atom r n -> m n (Atom r n)
add x y = emitOp $ BinOp FAdd x y

-- TODO: Implement constant folding for fixed-width integer types as well!
iadd :: BuilderEmits r m n => Atom r n -> Atom r n -> m n (Atom r n)
iadd (Con (Lit l)) y | getIntLit l == 0 = return y
iadd x (Con (Lit l)) | getIntLit l == 0 = return x
iadd x@(Con (Lit _)) y@(Con (Lit _)) = return $ applyIntBinOp (+) x y
iadd x y = emitOp $ BinOp IAdd x y

mul :: BuilderEmits r m n => Atom r n -> Atom r n -> m n (Atom r n)
mul x y = emitOp $ BinOp FMul x y

imul :: BuilderEmits r m n => Atom r n -> Atom r n -> m n (Atom r n)
imul   (Con (Lit l)) y               | getIntLit l == 1 = return y
imul x                 (Con (Lit l)) | getIntLit l == 1 = return x
imul x@(Con (Lit _)) y@(Con (Lit _))                    = return $ applyIntBinOp (*) x y
imul x y = emitOp $ BinOp IMul x y

sub :: BuilderEmits r m n => Atom r n -> Atom r n -> m n (Atom r n)
sub x y = emitOp $ BinOp FSub x y

isub :: BuilderEmits r m n => Atom r n -> Atom r n -> m n (Atom r n)
isub x (Con (Lit l)) | getIntLit l == 0 = return x
isub x@(Con (Lit _)) y@(Con (Lit _)) = return $ applyIntBinOp (-) x y
isub x y = emitOp $ BinOp ISub x y

select :: BuilderEmits r m n => Atom r n -> Atom r n -> Atom r n -> m n (Atom r n)
select (Con (Lit (Word8Lit p))) x y = return $ if p /= 0 then x else y
select p x y = emitOp $ MiscOp $ Select p x y

div' :: BuilderEmits r m n => Atom r n -> Atom r n -> m n (Atom r n)
div' x y = emitOp $ BinOp FDiv x y

idiv :: BuilderEmits r m n => Atom r n -> Atom r n -> m n (Atom r n)
idiv x (Con (Lit l)) | getIntLit l == 1 = return x
idiv x@(Con (Lit _)) y@(Con (Lit _)) = return $ applyIntBinOp div x y
idiv x y = emitOp $ BinOp IDiv x y

irem :: BuilderEmits r m n => Atom r n -> Atom r n -> m n (Atom r n)
irem x y = emitOp $ BinOp IRem x y

fpow :: BuilderEmits r m n => Atom r n -> Atom r n -> m n (Atom r n)
fpow x y = emitOp $ BinOp FPow x y

flog :: BuilderEmits r m n => Atom r n -> m n (Atom r n)
flog x = emitOp $ UnOp Log x

ilt :: BuilderEmits r m n => Atom r n -> Atom r n -> m n (Atom r n)
ilt x@(Con (Lit _)) y@(Con (Lit _)) = return $ applyIntCmpOp (<) x y
ilt x y = emitOp $ BinOp (ICmp Less) x y

ieq :: BuilderEmits r m n => Atom r n -> Atom r n -> m n (Atom r n)
ieq x@(Con (Lit _)) y@(Con (Lit _)) = return $ applyIntCmpOp (==) x y
ieq x y = emitOp $ BinOp (ICmp Equal) x y

fromPair :: BuilderEmits r m n => Atom r n -> m n (Atom r n, Atom r n)
fromPair pair = do
  getUnpacked pair >>= \case
    [x, y] -> return (x, y)
    _ -> error "expected a pair"

getFst :: BuilderEmits r m n => Atom r n -> m n (Atom r n)
getFst p = fst <$> fromPair p

getSnd :: BuilderEmits r m n => Atom r n -> m n (Atom r n)
getSnd p = snd <$> fromPair p

-- the rightmost index is applied first
getNaryProjRef :: BuilderEmits r m n => [Projection] -> Atom r n -> m n (Atom r n)
getNaryProjRef [] ref = return ref
getNaryProjRef (i:is) ref = getProjRef i =<< getNaryProjRef is ref

getProjRef :: BuilderEmits r m n => Projection -> Atom r n -> m n (Atom r n)
getProjRef i r = emitOp =<< mkProjRef r i

getUnpacked :: BuilderEmits r m n => Atom r n -> m n [Atom r n]
getUnpacked atom = do
  let ty = getType atom
  positions <- headNormalize (getType atom) >>= \case
    ProdTy tys  -> return $ void tys
    DepPairTy _ -> return [(), ()]
    _ -> error $ "not a product type: " ++ pprint ty
  forM (enumerate positions) \(i, _) -> getProductProj i atom
{-# SCC getUnpacked #-}

getProj :: BuilderEmits r m n => Projection -> Atom r n -> m n (Atom r n)
getProj p x = case p of
  ProjectProduct i -> getProductProj i x
  UnwrapNewtype -> unwrapNewtype x

getProductProj :: BuilderEmits r m n => Int -> Atom r n -> m n (Atom r n)
getProductProj i atom = case atom of
  Con (ProdCon xs) -> return $ xs !! i
  DepPair l _ _ | i == 0 -> return l
  DepPair _ r _ | i == 1 -> return r
  RepValAtom (RepVal _ tree) -> case tree of
    Branch trees -> do
      resultTy <- getResultTy
      repValAtom $ RepVal resultTy (trees!!i)
    Leaf _ -> error "unexpected leaf"
  _ -> do
    resultTy <- getResultTy
    emitExpr $ ProjectElt resultTy (ProjectProduct i) atom
  where
    getResultTy = projType i (getType atom) atom
{-# INLINE getProj #-}

getNaryProj :: BuilderEmits r m n => [Projection] -> Atom r n -> m n (Atom r n)
getNaryProj [] atom = return atom
getNaryProj (i:is) atom = getNaryProj is atom >>= getProj i

emitUnpacked :: BuilderEmits r m n => Atom r n -> m n [AtomVar r n]
emitUnpacked tup = do
  xs <- getUnpacked tup
  forM xs \x -> emit $ Atom x

unwrapNewtype :: BuilderEmits r m n => Atom r n -> m n (Atom r n)
unwrapNewtype (NewtypeCon _ x) = return x
unwrapNewtype x = headNormalize (getType x) >>= \case
  NewtypeTyCon con -> do
    (_, ty) <- unwrapNewtypeType con
    emitExpr $ ProjectElt ty UnwrapNewtype x
  _ -> error "not a newtype"
{-# INLINE unwrapNewtype #-}

projectStruct :: CBuilderEmits m n => Int -> CAtom n -> m n (CAtom n)
projectStruct i x = do
  projs <- getStructProjections i (getType x)
  getNaryProj projs x
{-# INLINE projectStruct #-}

projectStructRef :: (Builder CoreIR m, Emits n) => Int -> CAtom n -> m n (CAtom n)
projectStructRef i x = do
  RefTy _ valTy <- headNormalize $ getType x
  projs <- getStructProjections i valTy
  getNaryProjRef projs x
{-# INLINE projectStructRef #-}

getStructProjections :: EnvReader m => Int -> CType n -> m n [Projection]
getStructProjections i (NewtypeTyCon (UserADTType _ tyConName _ _)) = do
  TyConDef _ _ _ (Abs _ ~(StructFields fields)) <- lookupTyCon tyConName
  return case fields of
    [_] | i == 0    -> [UnwrapNewtype]
        | otherwise -> error "bad index"
    _ -> [ProjectProduct i, UnwrapNewtype]
getStructProjections _ _ = error "not a struct"

mkApp :: CBuilderEmits m n => CAtom n -> [CAtom n] -> m n (CExpr n)
mkApp f xs = do
  et <- appEffTy (getType f) xs
  return $ App et f xs

mkTabApp :: BuilderEmits r m n => Atom r n -> [Atom r n] -> m n (Expr r n)
mkTabApp xs ixs = do
  ty <- typeOfTabApp (getType xs) ixs
  return $ TabApp ty xs ixs

mkTopApp :: SBuilderEmits m n => TopFunName n -> [SAtom n] -> m n (SExpr n)
mkTopApp f xs = do
  resultTy <- typeOfTopApp f xs
  return $ TopApp resultTy f xs

mkApplyMethod :: CBuilderEmits m n => CAtom n -> Int -> [CAtom n] -> m n (CExpr n)
mkApplyMethod d i xs = do
  resultTy <- typeOfApplyMethod d i xs
  return $ ApplyMethod resultTy d i xs

mkDictAtom :: CBuilderEmits m n => DictExpr n -> m n (CAtom n)
mkDictAtom d = do
  ty <- typeOfDictExpr d
  return $ DictCon ty d

mkCase :: BuilderEmits r m n => Atom r n -> Type r n -> [Alt r n] -> m n (Expr r n)
mkCase scrut resultTy alts = liftEmitBuilder do
  eff' <- caseEffs alts
  return $ Case scrut alts (EffTy eff' resultTy)

caseEffs :: BuilderEmits r m n => [Alt r n] -> m n (EffectRow r n)
caseEffs alts = liftEmitBuilder do
  fold <$> forM alts \(LamExpr b body) -> refreshAbs (Abs b body) \b' body' -> do
    Abs decls (EffTy eff _) <- buildScoped $ blockEffTy $ sink body'
    return $ ignoreHoistFailure $ hoist (PairB b' decls) eff

mkCatchException :: CBuilderEmits m n => CBlock n -> m n (Hof CoreIR n)
mkCatchException body = do
  EffTy _ bodyTy <- blockEffTy body
  resultTy <- makePreludeMaybeTy bodyTy
  return $ CatchException resultTy body

app :: CBuilderEmits m n => CAtom n -> CAtom n -> m n (CAtom n)
app x i = mkApp x [i] >>= emitExpr

naryApp :: CBuilderEmits m n => CAtom n -> [CAtom n] -> m n (CAtom n)
naryApp = naryAppHinted noHint
{-# INLINE naryApp #-}

naryTopApp :: SBuilderEmits m n => TopFunName n -> [SAtom n] -> m n (SAtom n)
naryTopApp f xs = emitExpr =<< mkTopApp f xs
{-# INLINE naryTopApp #-}

naryTopAppInlined :: (Builder SimpIR m, Emits n) => TopFunName n -> [SAtom n] -> m n (SAtom n)
naryTopAppInlined f xs = do
  TopFunBinding f' <- lookupEnv f
  case f' of
    DexTopFun _ lam _ -> instantiate lam xs
    _ -> naryTopApp f xs
{-# INLINE naryTopAppInlined #-}

naryAppHinted :: (CBuilder m, Emits n)
  => NameHint -> CAtom n -> [CAtom n] -> m n (CAtom n)
naryAppHinted hint f xs = Var <$> (mkApp f xs >>= emitHinted hint)

tabApp :: BuilderEmits r m n => Atom r n -> Atom r n -> m n (Atom r n)
tabApp x i = mkTabApp x [i] >>= emitExpr

naryTabApp :: BuilderEmits r m n => Atom r n -> [Atom r n] -> m n (Atom r n)
naryTabApp = naryTabAppHinted noHint
{-# INLINE naryTabApp #-}

naryTabAppHinted :: BuilderEmits r m n
  => NameHint -> Atom r n -> [Atom r n] -> m n (Atom r n)
naryTabAppHinted hint f xs = do
  expr <- mkTabApp f xs
  Var <$> emitHinted hint expr

indexRef :: BuilderEmits r m n => Atom r n -> Atom r n -> m n (Atom r n)
indexRef ref i = emitOp =<< mkIndexRef ref i

naryIndexRef :: BuilderEmits r m n => Atom r n -> [Atom r n] -> m n (Atom r n)
naryIndexRef ref is = foldM indexRef ref is

ptrOffset :: BuilderEmits r m n => Atom r n -> Atom r n -> m n (Atom r n)
ptrOffset x (IdxRepVal 0) = return x
ptrOffset x i = emitOp $ MemOp $ PtrOffset x i
{-# INLINE ptrOffset #-}

unsafePtrLoad :: BuilderEmits r m n => Atom r n -> m n (Atom r n)
unsafePtrLoad x = do
  body <- liftEmitBuilder $ buildBlock $ emitOp . MemOp . PtrLoad =<< sinkM x
  emitHof $ RunIO body

mkIndexRef :: BuilderEmits r m n => Atom r n -> Atom r n -> m n (PrimOp r n)
mkIndexRef ref i = do
  resultTy <- typeOfIndexRef (getType ref) i
  return $ RefOp ref $ IndexRef resultTy i

mkProjRef :: BuilderEmits r m n => Atom r n -> Projection -> m n (PrimOp r n)
mkProjRef ref i = do
  resultTy <- typeOfProjRef (getType ref) i
  return $ RefOp ref $ ProjRef resultTy i

-- === index set type class ===

applyIxMethod :: SBuilderEmits m n => IxDict SimpIR n -> IxMethod -> [SAtom n] -> m n (SAtom n)
applyIxMethod dict method args = case dict of
  -- These cases are used in SimpIR and they work with IdxRepVal
  IxDictRawFin n -> case method of
    Size              -> do []  <- return args; return n
    Ordinal           -> do [i] <- return args; return i
    UnsafeFromOrdinal -> do [i] <- return args; return i
  IxDictSpecialized _ d params -> do
    SpecializedDict _ maybeFs <- lookupSpecDict d
    Just fs <- return maybeFs
    instantiate (fs !! fromEnum method) (params ++ args)

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
fromJustE :: BuilderEmits r m n => Atom r n -> m n (Atom r n)
fromJustE x = liftEmitBuilder do
  MaybeTy a <- return $ getType x
  emitMaybeCase x a
    (emitOp $ MiscOp $ ThrowError $ sink a)
    (return)

-- Maybe a -> Bool
isJustE :: BuilderEmits r m n => Atom r n -> m n (Atom r n)
isJustE x = liftEmitBuilder $
  emitMaybeCase x BoolTy (return FalseAtom) (\_ -> return TrueAtom)

-- Monoid a -> (n=>a) -> a
reduceE :: BuilderEmits r m n => BaseMonoid r n -> Atom r n -> m n (Atom r n)
reduceE monoid xs = liftEmitBuilder do
  TabPi tabPi <- return $ getType xs
  let a = assumeConst tabPi
  getSnd =<< emitRunWriter noHint a monoid \_ ref -> do
    ixTy <- tabIxType $ sink tabPi
    buildFor noHint Fwd ixTy \i -> do
      x <- tabApp (sink xs) (Var i)
      emitExpr $ PrimOp $ RefOp (sink $ Var ref) $ MExtend (sink monoid) x

andMonoid :: BuilderEmits r m n => m n (BaseMonoid r n)
andMonoid = liftM (BaseMonoid TrueAtom) $ liftBuilder $
  buildBinaryLamExpr (noHint, BoolTy) (noHint, BoolTy) \x y ->
    emitOp $ BinOp BAnd (sink $ Var x) (Var y)

-- (a-> {|eff} b) -> n=>a -> {|eff} (n=>b)
mapE :: (Emits n, ScopableBuilder r m)
     => (forall l. (Emits l, DExt n l) => Atom r l -> m l (Atom r l))
     -> Atom r n -> m n (Atom r n)
mapE cont xs = do
  TabPi tabPi <- return $ getType xs
  ixTy <- tabIxType tabPi
  buildFor (getNameHint tabPi) Fwd ixTy \i -> do
    tabApp (sink xs) (Var i) >>= cont

-- (n:Type) ?-> (a:Type) ?-> (xs : n=>Maybe a) : Maybe (n => a) =
catMaybesE :: BuilderEmits r m n => Atom r n -> m n (Atom r n)
catMaybesE maybes = do
  TabTy d n (Abs decls (MaybeTy a)) <- return $ getType maybes
  let a' = Abs decls a
  justs <- liftEmitBuilder $ mapE isJustE maybes
  monoid <- andMonoid
  allJust <- reduceE monoid justs
  liftEmitBuilder $ emitIf allJust (MaybeTy $ TabTy d n a')
    (JustAtom (sink $ TabTy d n a') <$> mapE fromJustE (sink maybes))
    (return (NothingAtom $ sink $ TabTy d n a'))

emitWhile :: (Emits n, ScopableBuilder r m)
          => (forall l. (Emits l, DExt n l) => m l (Atom r l))
          -> m n ()
emitWhile cont = do
  body <- buildBlock cont
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

data ReconBinders r n l = ReconBinders (TelescopeType r n) (Nest (NameBinder (AtomNameC r)) n l)

data TelescopeType r n =
   DepTelescope (TelescopeType r n) (Abs (BinderAndDecls r) (WithDecls r (TelescopeType r)) n)
 | ProdTelescope [Type r n]

instance IRRep r => GenericB (ReconBinders r) where
  type RepB (ReconBinders r) =
    PairB (LiftB (TelescopeType r))
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

instance GenericE (TelescopeType r) where
  type RepE (TelescopeType r) = EitherE
         (PairE (TelescopeType r) (Abs (BinderAndDecls r) (WithDecls r (TelescopeType r))))
         (ListE (Type r))
  fromE (DepTelescope lhs ab) = LeftE (PairE lhs ab)
  fromE (ProdTelescope tys)   = RightE (ListE tys)
  {-# INLINE fromE #-}
  toE (LeftE (PairE lhs ab)) = DepTelescope lhs ab
  toE (RightE (ListE tys))   = ProdTelescope tys
  {-# INLINE toE #-}

instance IRRep r => SinkableE (TelescopeType r)
instance IRRep r => RenameE (TelescopeType r)
instance IRRep r => SubstE AtomSubstVal (TelescopeType r)
instance IRRep r => HoistableE (TelescopeType r)

telescopicCapture
  :: (Builder r m, HoistableE e, HoistableB b)
  => b n l -> e l -> m l (WithDecls r (Atom r) l, ReconAbs r e n)
telescopicCapture bs e = do
  vs <- localVarsAndTypeVars bs e
  vTys <- forM vs \v -> getType <$> toAtomVar v
  let vsTysSorted = toposortAnnVars $ zip vs vTys
  let vsSorted = map fst vsTysSorted
  ty <- liftEnvReaderM $ buildTelescopeTy vsTysSorted
  valsSorted <- forM vsSorted \v -> Var <$> toAtomVar v
  result <- liftBuilder $ buildScoped $ buildTelescopeVal (sink <$> valsSorted) (sink ty)
  reconAbs <- return $ ignoreHoistFailure $ hoist bs do
    case abstractFreeVarsNoAnn vsSorted e of
      Abs bs' e' -> Abs (ReconBinders ty bs') e'
  return (result, reconAbs)

applyReconAbs
  :: (BuilderEmits r m n, Fallible1 m, SinkableE e, SubstE AtomSubstVal e)
  => ReconAbs r e n -> Atom r n -> m n (e n)
applyReconAbs (Abs bs result) x = do
  xs <- unpackTelescope bs x
  applySubst (bs @@> map SubstVal xs) result

buildTelescopeTy
  :: (EnvReader m, EnvExtender m, IRRep r)
  => [AnnVar (AtomNameC r) (Type r) n] -> m n (TelescopeType r n)
buildTelescopeTy [] = return (ProdTelescope [])
buildTelescopeTy ((v,ty):xs) = do
  rhs <- buildTelescopeTy xs
  Abs b rhs' <- return $ abstractFreeVar v rhs
  case hoist b rhs' of
    HoistSuccess rhs'' -> return $ prependTelescopeTy ty rhs''
    HoistFailure _ -> return $ DepTelescope (ProdTelescope []) (Abs (BD Empty (b:>ty)) (Abs Empty rhs'))

prependTelescopeTy :: Type r n -> TelescopeType r n -> TelescopeType r n
prependTelescopeTy x = \case
  DepTelescope lhs rhs -> DepTelescope (prependTelescopeTy x lhs) rhs
  ProdTelescope xs -> ProdTelescope (x:xs)

buildTelescopeVal :: (BuilderEmits r m n) => [Atom r n] -> TelescopeType r n -> m n (Atom r n)
buildTelescopeVal xsTop tyTop = fst <$> go tyTop xsTop where
  go :: (BuilderEmits r m n, IRRep r)
     => TelescopeType r n ->  [Atom r n] -> m n (Atom r n, [Atom r n])
  go ty rest = case ty of
    ProdTelescope tys -> do
      (xs, rest') <- return $ splitAt (length tys) rest
      return (ProdVal xs, rest')
    DepTelescope ty1 (Abs b (Abs decls ty2)) -> do
      (x1, ~(xDep : rest')) <- go ty1 rest
      ty2' <- instantiate (Abs (PairB b decls) ty2) [xDep]
      (x2, rest'') <- go ty2' rest'
      let depPairTy = DepPairType ExplicitDepPair b (Abs decls (telescopeTypeType ty2))
      return (PairVal x1 (DepPair xDep x2 depPairTy), rest'')

telescopeTypeType :: TelescopeType r n -> Type r n
telescopeTypeType (ProdTelescope tys) = ProdTy tys
telescopeTypeType (DepTelescope lhs (Abs b (Abs decls rhs))) = do
  let lhs' = telescopeTypeType lhs
  let rhs' = DepPairTy (DepPairType ExplicitDepPair b (Abs decls (telescopeTypeType rhs)))
  PairTy lhs' rhs'

unpackTelescope
  :: BuilderEmits r m n
  => ReconBinders r l1 l2 -> Atom r n -> m n [Atom r n]
unpackTelescope (ReconBinders tyTop _) xTop = go tyTop xTop where
  go :: BuilderEmits r m n
     => TelescopeType r l-> Atom r n -> m n [Atom r n]
  go ty x = case ty of
    ProdTelescope _ -> getUnpacked x
    DepTelescope ty1 (Abs _  (Abs _ ty2)) -> do
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

-- === Helpers for traversing binders ===

-- We should only rarely need to write an explicit recursion to traverse a bunch
-- of binders. Here are some helpers for avoiding it.

traverseBindersTypes
  :: (IRRep r, EnvExtender2 m, SubstReader AtomSubstVal m, SinkableE e)
  => Binders r i i'
  -> (forall ii o'. DExt o o' => Type r o' -> m ii o' (e o'))
  -> (forall o'. DExt o o' => Binders r o o' -> [e o'] -> m i' o' a)
  -> m i o a
traverseBindersTypes Empty _ cont = getDistinct >>= \Distinct -> cont Empty []
traverseBindersTypes (Nest (BD decls b) rest) withType cont =
  substMB decls \decls' -> do
    ty' <- substM $ binderType b
    x <- withType ty'
    substMB b \b' ->
      traverseBindersTypes rest withType \rest' xs ->
        cont (Nest (BD decls' b') rest') (sink x : xs)
{-# INLINE traverseBindersTypes #-}



-- === Non-emitting expression visitor ===

class Visitor m r i o => ExprVisitorNoEmits m r i o | m -> i, m -> o where
  visitExprNoEmits :: Expr r i -> m (Expr r o)

type ExprVisitorNoEmits2 m r = forall i o. ExprVisitorNoEmits (m i o) r i o

visitLamNoEmits
  :: (ExprVisitorNoEmits2 m r, IRRep r, AtomSubstReader v m, EnvExtender2 m)
  => LamExpr r i -> m i o (LamExpr r o)
visitLamNoEmits (LamExpr bs (Abs decls result)) =
  visitBindersNoEmits bs \bs' -> LamExpr bs' <$>
    visitDeclsNoEmits decls \decls' -> Abs decls' <$> do
      visitAtom result

visitPiNoEmits
  :: (ExprVisitorNoEmits2 m r, IRRep r, FromName v, AtomSubstReader v m, EnvExtender2 m)
  => PiType r i -> m i o (PiType r o)
visitPiNoEmits (PiType bs (Abs decls effty)) = do
  visitBindersNoEmits bs \bs' -> PiType bs' <$>
    visitDeclsNoEmits decls \decls' -> Abs decls' <$> do
       visitGeneric effty

visitBindersNoEmits
  :: (ExprVisitorNoEmits2 m r, IRRep r, FromName v, AtomSubstReader v m, EnvExtender2 m)
  => Binders r i i'
  -> (forall o'. DExt o o' => Binders r o o' -> m i' o' a)
  -> m i o a
visitBindersNoEmits Empty cont = getDistinct >>= \Distinct -> cont Empty
visitBindersNoEmits (Nest (BD decls (b:>ty)) bs) cont = do
  visitDeclsNoEmits decls \decls' -> do
    ty' <- visitType ty
    withFreshBinder (getNameHint b) ty' \b' -> do
      extendRenamer (b@>binderName b') do
        visitBindersNoEmits bs \bs' ->
          cont $ Nest (BD decls' b') bs'

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
visitLamEmits (LamExpr bs body) = visitBindersEmits bs \bs' -> LamExpr bs' <$>
  buildBlock (visitBlockEmits body)

visitPiEmits
  :: (ExprVisitorEmits2 m r, IRRep r, SubstReader AtomSubstVal m, ScopableBuilder2 r m)
  => PiType r i -> m i o (PiType r o)
visitPiEmits (PiType bs (Abs decls effTy)) = visitBindersEmits bs \bs' -> PiType bs' <$>
  buildScoped (visitDeclsEmits decls $ visitGeneric effTy)

visitBindersEmits
  :: (ExprVisitorEmits2 m r, IRRep r, SubstReader AtomSubstVal m, ScopableBuilder2 r m)
  => Binders r i i'
  -> (forall o'. DExt o o' => Binders r o o' -> m i' o' a)
  -> m i o a
visitBindersEmits Empty cont = getDistinct >>= \Distinct -> cont Empty
visitBindersEmits (Nest (BD decls (b:>ty)) bs) cont = do
  buildScopedAndThen (visitDeclsEmits decls $ getSubst) \decls' subst -> withSubst subst do
    ty' <- visitType ty
    withFreshBinder (getNameHint b) ty' \b' -> do
      extendRenamer (b@>binderName b') do
        visitBindersEmits bs \bs' ->
          cont $ Nest (BD decls' b') bs'

visitBlockEmits
  :: (ExprVisitorEmits2 m r, SubstReader AtomSubstVal m, EnvExtender2 m, IRRep r, Emits o)
  => Block r i -> m i o (Atom r o)
visitBlockEmits (Abs decls result) = visitDeclsEmits decls $ visitAtom result

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

visitDeclsEmits2
  :: ( ExprVisitorEmits2 m r, ScopableBuilder2 r m
     , SubstReader AtomSubstVal m, EnvExtender2 m, IRRep r)
  => Nest (Decl r) i i'
  -> (forall o'. DExt o o' => Nest (Decl r) o o' -> m i' o' a)
  -> m i o a
visitDeclsEmits2 decls cont =
  buildScopedAndThen (visitDeclsEmits decls getSubst) \decls' subst ->
    withSubst subst $ cont decls'

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


-- === QUERYING TYPES ===

sourceNameType :: (EnvReader m, Fallible1 m) => SourceName -> m n (Type CoreIR n)
sourceNameType v = do
  lookupSourceMap v >>= \case
    Nothing -> throw UnboundVarErr $ pprint v
    Just uvar -> getUVarType uvar

-- === Exposed helpers for querying types and effects ===

caseAltsBinderTys :: BuilderEmits r m n => Type r n -> m n [Type r n]
caseAltsBinderTys ty = case ty of
  SumTy types -> return types
  NewtypeTyCon t -> case t of
    UserADTType _ defName params _ -> do
      def <- lookupTyCon defName
      ~(ADTCons cons) <- instantiateTyConDef def params
      return [repTy | DataConDef _ _ repTy _ <- cons]
    _ -> error msg
  _ -> error msg
  where msg = "Case analysis only supported on ADTs, not on " ++ pprint ty

extendEffect :: IRRep r => Effect r n -> EffectRow r n -> EffectRow r n
extendEffect eff (EffectRow effs t) = EffectRow (effs <> eSetSingleton eff) t

blockEffTy :: BuilderEmits r m n => Block r n -> m n (EffTy r n)
blockEffTy block = do  -- DECLS: this is too conservative. We need to consider hoisting decls into the type too.
  liftEnvReaderM $ refreshAbs block \decls result -> do
    effs <- declsEffects decls mempty
    return $ ignoreHoistFailure $ hoist decls $ EffTy effs $ getType result
    where
      declsEffects :: IRRep r => Nest (Decl r) n l -> EffectRow r l -> EnvReaderM l (EffectRow r l)
      declsEffects Empty !acc = return acc
      declsEffects n@(Nest (Let _ (DeclBinding _ expr)) rest) !acc = withExtEvidence n do
        expr' <- sinkM expr
        declsEffects rest $ acc <> getEffects expr'

blockEff :: BuilderEmits r m n => Block r n -> m n (EffectRow r n)
blockEff b = blockEffTy b <&> \(EffTy eff _) -> eff

blockTy :: BuilderEmits r m n => Block r n -> m n (Type r n)
blockTy b = blockEffTy b <&> \(EffTy _ t) -> t

piTypeWithoutDest :: PiType SimpIR n -> PiType SimpIR n
piTypeWithoutDest (PiType bsRefB _) =
  case popNest bsRefB of
    Just (PairB bs (BD Empty refB)) -> do
      case binderType refB of
        RawRefTy ansTy -> PiType bs $ Abs Empty $ EffTy Pure ansTy  -- XXX: we ignore the effects here
        _ -> error "expected ref type"
    _ -> error "expected trailing binder"

typeOfApp  :: BuilderEmits r m n => Type r n -> [Atom r n] -> m n (Type r n)
typeOfApp (Pi piTy) xs = withSubstReaderT $
  withInstantiated piTy xs \(EffTy _ ty) -> substM ty
typeOfApp _ _ = error "expected a pi type"

typeOfTabApp :: BuilderEmits r m n => Type r n -> [Atom r n] -> m n (Type r n)
typeOfTabApp t [] = return t
typeOfTabApp (TabPi tabTy) (i:rest) = do
  resultTy <- instantiate tabTy [i]
  typeOfTabApp resultTy rest
typeOfTabApp ty _ = error $ "expected a table type. Got: " ++ pprint ty

typeOfApplyMethod :: CBuilderEmits m n => CAtom n -> Int -> [CAtom n] -> m n (EffTy CoreIR n)
typeOfApplyMethod d i args = do
  ty <- Pi <$> getMethodType d i
  appEffTy ty args

typeOfDictExpr :: CBuilderEmits m n => DictExpr n -> m n (CType n)
typeOfDictExpr e = case e of
  InstanceDict instanceName args -> do
    instanceDef@(InstanceDef className _ _ _ _ _) <- lookupInstanceDef instanceName
    sourceName <- getSourceName <$> lookupClassDef className
    PairE (ListE params) _ <- instantiate instanceDef args
    return $ DictTy $ DictType sourceName className params
  InstantiatedGiven given args -> typeOfApp (getType given) args
  SuperclassProj d i -> do
    DictTy (DictType _ className params) <- return $ getType d
    classDef <- lookupClassDef className
    withSubstReaderT $ withInstantiated classDef params \(Abs superclasses _) -> do
      substM $ getSuperclassType REmpty superclasses i
  IxFin n -> liftM DictTy $ ixDictType $ NewtypeTyCon $ Fin n
  DataData ty -> DictTy <$> dataDictType ty

typeOfTopApp :: SBuilderEmits m n => TopFunName n -> [SAtom n] -> m n (EffTy SimpIR n)
typeOfTopApp f xs = do
  piTy <- getTypeTopFun f
  instantiate piTy xs

typeOfIndexRef :: BuilderEmits r m n => Type r n -> Atom r n -> m n (Type r n)
typeOfIndexRef (TC (RefType h s)) i = do
  TabPi tabPi <- return s
  eltTy <- instantiate tabPi [i]
  return $ TC $ RefType h eltTy
typeOfIndexRef _ _ = error "expected a ref type"

typeOfProjRef :: BuilderEmits r m n => Type r n -> Projection -> m n (Type r n)
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

appEffTy  :: BuilderEmits r m n => Type r n -> [Atom r n] -> m n (EffTy r n)
appEffTy t xs = headNormalize t >>= \case
  Pi piTy -> instantiate piTy xs
  _ -> error $ "expected a pi type, got: " ++ pprint t

partialAppType  :: BuilderEmits r m n => Type r n -> [Atom r n] -> m n (Type r n)
partialAppType (Pi (CorePiType appExpl expls bs effTy)) xs = do
  (_, expls2) <- return $ splitAt (length xs) expls
  PairB bs1 bs2 <- return $ splitNestAt (length xs) bs
  instantiate (Abs bs1 (Pi $ CorePiType appExpl expls2 bs2 effTy)) xs
partialAppType _ _ = error "expected a pi type"

effTyOfHof :: BuilderEmits r m n => Hof r n -> m n (EffTy r n)
effTyOfHof hof = EffTy <$> hofEffects hof <*> typeOfHof hof

bdType :: BuilderEmits r m n => BinderAndDecls r n l -> m n (Type r n)
bdType (BD decls (_:>ty)) = emitDecls $ Abs decls ty

typeOfHof :: BuilderEmits r m n => Hof r n -> m n (Type r n)
typeOfHof = \case
  For _ ixTy f -> getLamExprType f >>= \case
    PiType (UnaryNest b) (Abs decls (EffTy _ eltTy)) ->
      return $ TabTy (ixTypeDict ixTy) b (Abs decls eltTy)
    _ -> error "expected a unary pi type"
  While _ -> return UnitTy
  Linearize f _ -> getLamExprType f >>= \case
    PiType (UnaryNest binder) (Abs bDecls (EffTy Pure b)) -> do
      b' <- emitDecls $ ignoreHoistFailure $ hoist binder $ Abs bDecls b
      t <- bdType binder
      let fLinTy = Pi $ nonDepPiType [t] Pure b'
      return $ PairTy b' fLinTy
    _ -> error "expected a unary pi type"
  Transpose f _ -> getLamExprType f >>= \case
    PiType (UnaryNest b) _ -> bdType b
    _ -> error "expected a unary pi type"
  RunReader _ f -> do
    (resultTy, _) <- getTypeRWSAction f
    return resultTy
  RunWriter _ _ f -> uncurry PairTy <$> getTypeRWSAction f
  RunState _ _ f -> do
    (resultTy, stateTy) <- getTypeRWSAction f
    return $ PairTy resultTy stateTy
  RunIO f -> blockTy f
  RunInit f -> blockTy f
  CatchException ty _ -> return ty

hofEffects :: BuilderEmits r m n => Hof r n -> m n (EffectRow r n)
hofEffects = \case
  For _ _ f     -> functionEffs f
  While body    -> blockEff body
  Linearize _ _ -> return Pure  -- Body has to be a pure function
  Transpose _ _ -> return Pure  -- Body has to be a pure function
  RunReader _ f -> rwsFunEffects Reader f
  RunWriter d _ f -> maybeInit d <$> rwsFunEffects Writer f
  RunState  d _ f -> maybeInit d <$> rwsFunEffects State  f
  RunIO            f -> deleteEff IOEffect        <$> blockEff f
  RunInit          f -> deleteEff InitEffect      <$> blockEff f
  CatchException _ f -> deleteEff ExceptionEffect <$> blockEff f
  where maybeInit :: IRRep r => Maybe (Atom r i) -> (EffectRow r o -> EffectRow r o)
        maybeInit d = case d of Just _ -> (<>OneEffect InitEffect); Nothing -> id

deleteEff :: IRRep r => Effect r n -> EffectRow r n -> EffectRow r n
deleteEff eff (EffectRow effs t) = EffectRow (effs `eSetDifference` eSetSingleton eff) t

getMethodIndex :: EnvReader m => ClassName n -> SourceName -> m n Int
getMethodIndex className methodSourceName = do
  ClassDef _ methodNames _ _ _ _ _ <- lookupClassDef className
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
    ClassDef _ _ _ roleExpls bs _ _ <- lookupClassDef v
    return $ Pi $ CorePiType ExplicitApp (map snd roleExpls) bs $ Abs Empty $ EffTy Pure TyKind
  UMethodVar  v -> getMethodNameType v
  UEffectVar   _ -> error "not implemented"
  UEffectOpVar _ -> error "not implemented"

getMethodNameType :: EnvReader m => MethodName n -> m n (CType n)
getMethodNameType v = liftBuilder $ lookupEnv v >>= \case
  MethodBinding className i -> do
    ClassDef _ _ paramNames _ paramBs scBinders methodTys <- lookupClassDef className
    refreshAbs (Abs paramBs $ Abs scBinders (methodTys !! i)) \paramBs' absPiTy -> do
      let params = Var <$> bindersVars paramBs'
      dictTy <- DictTy <$> dictType (sink className) params
      withFreshBinder noHint dictTy \dictB -> do
        buildScopedAndThen (do
          d <- sinkM $ Var $ binderVar dictB
          scDicts <- getSuperclassDicts d
          absPiTy' <- sinkM absPiTy
          instantiate absPiTy' scDicts)
          \decls (Abs decls' piTy) -> do
            CorePiType appExpl methodExpls methodBs effTy <- return $ prependDecls (decls >>> decls') piTy
            let paramExpls = paramNames <&> \name -> Inferred name Unify
            let expls = paramExpls <> [Inferred Nothing (Synth $ Partial $ succ i)] <> methodExpls
            return $ Pi $ CorePiType appExpl expls (paramBs' >>> UnaryNest (PlainBD dictB) >>> methodBs) effTy

-- TODO: a class for this?
prependDecls :: Decls CoreIR n l -> CorePiType l -> CorePiType n
prependDecls decls (CorePiType expl expls bs (Abs decls' result)) = case bs of
  Empty -> CorePiType expl expls Empty (Abs (decls >>> decls') result)
  Nest (BD decls'' b) rest -> CorePiType expl expls (Nest (BD (decls >>> decls'') b) rest) (Abs decls' result)

getMethodType :: CBuilderEmits m n => Dict n -> Int -> m n (CorePiType n)
getMethodType dict i = liftBuilder $ withSubstReaderT do
  ~(DictTy (DictType _ className params)) <- return $ getType dict
  superclassDicts <- getSuperclassDicts dict
  classDef <- lookupClassDef className
  withInstantiated classDef params \ab -> do
    withInstantiated ab superclassDicts \(ListE methodTys) -> do
      Abs decls methodTy <- return $ methodTys !! i
      substM $ prependDecls decls methodTy

getTyConNameType :: EnvReader m => TyConName n -> m n (CType n)
getTyConNameType v = do
  TyConDef _ expls bs _ <- lookupTyCon v
  case bs of
    Empty -> return TyKind
    _ -> return $ Pi $ CorePiType ExplicitApp (snd <$> expls) bs $ Abs Empty $ EffTy Pure TyKind

getDataConNameType :: EnvReader m => DataConName n -> m n (CType n)
getDataConNameType dataCon = liftBuilder $ withSubstReaderT do
  (tyCon, i) <- lookupDataCon dataCon
  tyConDef <- lookupTyCon tyCon
  buildDataConType tyConDef \paramVs params -> do
    withInstantiated tyConDef (Var . sink <$> paramVs) \(ADTCons dataCons) -> do
      repTy <- substM $ dataDefRep $ ADTCons dataCons
      DataConDef _ ab _ _ <- substM (dataCons !! i)
      refreshAbs ab \dataBs UnitE -> do
        let appExpl = case dataBs of Empty -> ImplicitApp
                                     _     -> ExplicitApp
        let resultTy = NewtypeTyCon $ UserADTType (getSourceName tyConDef) (sink tyCon) (sink params) (sink repTy)
        let dataExpls = nestToList (const $ Explicit) dataBs
        return $ CorePiType appExpl dataExpls dataBs (Abs Empty (EffTy Pure resultTy))

getStructDataConType :: EnvReader m => TyConName n -> m n (CType n)
getStructDataConType tyCon = liftBuilder $ withSubstReaderT do
  tyConDef <- lookupTyCon tyCon
  buildDataConType tyConDef \paramVs params -> do
    withInstantiated tyConDef (Var . sink <$> paramVs) \(StructFields fields) -> do
      repTy <- substM $ dataDefRep $ StructFields fields
      fieldTys <- forM fields \(_, t) -> substM t
      let resultTy = NewtypeTyCon $ UserADTType (getSourceName tyConDef) (sink tyCon) params repTy
      Abs dataBs resultTy' <- return $ typesAsBinderNest fieldTys resultTy
      let dataExpls = nestToList (const Explicit) dataBs
      return $ CorePiType ExplicitApp dataExpls dataBs (Abs Empty (EffTy Pure resultTy'))

buildDataConType
  :: (EnvReader m, CBuilder m, ScopableBuilder CoreIR m)
  => TyConDef n
  -> (forall l. (Emits l, DExt n l) => [CAtomVar l] -> TyConParams l -> m l (CorePiType l))
  -> m n (CType n)
buildDataConType (TyConDef _ roleExpls bs _) cont = do
  let expls = snd <$> roleExpls
  expls' <- forM expls \case
    Explicit -> return $ Inferred Nothing Unify
    expl     -> return $ expl
  refreshAbs (Abs bs UnitE) \bs' UnitE -> do
    let vs = bindersVars bs'
    Abs decls piTy <- buildScoped do
      vs' <- mapM sinkM vs
      cont vs' $ TyConParams expls (Var <$> vs')
    CorePiType appExpl dataExpls dataBs resultTy <- return $ prependDecls decls piTy
    return $ Pi $ CorePiType appExpl (expls' <> dataExpls) (bs' >>> dataBs) resultTy

makeTyConParams :: EnvReader m => TyConName n -> [CAtom n] -> m n (TyConParams n)
makeTyConParams tc params = do
  TyConDef _ expls _ _ <- lookupTyCon tc
  return $ TyConParams (map snd expls) params

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
  ClassDef sourceName _ _ _ _ _ _ <- lookupClassDef className
  return $ DictType sourceName className params

ixDictType :: (Fallible1 m, EnvReader m) => CType n -> m n (DictType n)
ixDictType ty = do
  ixClassName <- getIxClassName
  dictType ixClassName [Type ty]

makePreludeMaybeTy :: EnvReader m => CType n -> m n (CType n)
makePreludeMaybeTy ty = undefined
-- makePreludeMaybeTy ty = do
--   ~(Just (UTyConVar tyConName)) <- lookupSourceMap "Maybe"
--   return $ TypeCon "Maybe" tyConName $ TyConParams [Explicit] [Type ty]

-- === computing effects ===

functionEffs :: BuilderEmits r m n => LamExpr r n -> m n (EffectRow r n)
functionEffs f = getLamExprType f >>= \case
  PiType b (Abs decls (EffTy effs _)) ->
    emitDecls $ ignoreHoistFailure $ hoist b (Abs decls effs)

rwsFunEffects :: (IRRep r, EnvReader m) => RWS -> LamExpr r n -> m n (EffectRow r n)
rwsFunEffects rws f = liftEnvReaderM $ getLamExprType f >>= \case
   PiType (BinaryNest h ref) (Abs decls et) -> do
     let effs' = ignoreHoistFailure $ hoist (PairB ref decls) (etEff et)
     refreshAbs (Abs h effs') \h' effs'' -> do
       let hVal = Var $ binderVar h'
       let effs''' = deleteEff (RWSEffect rws hVal) effs''
       return $ ignoreHoistFailure $ hoist h' effs'''
   _ -> error "Expected a binary function type"

getLamExprType :: (IRRep r, EnvReader m) => LamExpr r n -> m n (PiType r n)
getLamExprType (LamExpr bs body) = liftBuilder $
  refreshAbs (Abs bs body) \bs' body' -> do
    effTy <- buildScoped $ blockEffTy $ sink body'
    return $ PiType bs' effTy

getTypeRWSAction :: (IRRep r, EnvReader m) => LamExpr r n -> m n (Type r n, Type r n)
getTypeRWSAction f = getLamExprType f >>= \case
  PiType bs@(BinaryNest regionBinder (BD decls' refBinder)) (Abs decls (EffTy _ resultTy)) -> do
    case binderType refBinder of
      RefTy _ referentTy -> do
        let referentTy' = ignoreHoistFailure $ hoist (PairB regionBinder decls') referentTy
        let resultTy' = ignoreHoistFailure $ hoist (PairB bs decls) resultTy
        return (resultTy', referentTy')
      _ -> error "expected a ref"
  _ -> error "expected a pi type"

getSuperclassDicts :: CBuilderEmits m n => CAtom n -> m n ([CAtom n])
getSuperclassDicts dict = do
  case getType dict of
    DictTy dTy -> do
      ts <- getSuperclassTys dTy
      forM (enumerate ts) \(i, t) -> return $ DictCon t $ SuperclassProj dict i
    _ -> error "expected a dict type"

getSuperclassTys :: CBuilderEmits m n => DictType n -> m n [CType n]
getSuperclassTys (DictType _ className params) = do
  ClassDef _ _ _ _ bs superclasses _ <- lookupClassDef className
  forM [0 .. nestLength superclasses - 1] \i -> do
    instantiate (Abs bs $ getSuperclassType REmpty superclasses i) params

getSuperclassType :: RNest (BinderAndDecls CoreIR) n l -> CBinders l l' -> Int -> CType n
getSuperclassType _ Empty = error "bad index"
getSuperclassType bsAbove (Nest (BD decls b) bs) = \case
  0 -> ignoreHoistFailure $ hoist (PairB bsAbove decls) (binderType b)
  i -> getSuperclassType (RNest bsAbove (BD decls b)) bs (i-1)

getTypeTopFun :: EnvReader m => TopFunName n -> m n (PiType SimpIR n)
getTypeTopFun f = lookupTopFun f >>= \case
  DexTopFun _ (TopLam _ piTy _) _ -> return piTy
  FFITopFun _ iTy -> liftIFunType iTy

asTopLam :: (EnvReader m, IRRep r) => LamExpr r n -> m n (TopLam r n)
asTopLam lam = do
  piTy <- getLamExprType lam
  return $ TopLam False piTy lam

liftIFunType :: (IRRep r, EnvReader m) => IFunType -> m n (PiType r n)
liftIFunType (IFunType _ argTys resultTys) = liftEnvReaderM $ go argTys where
  go :: IRRep r => [BaseType] -> EnvReaderM n (PiType r n)
  go = \case
    [] -> return $ PiType Empty (Abs Empty (EffTy (OneEffect IOEffect) resultTy))
      where resultTy = case resultTys of
              [] -> UnitTy
              [t] -> BaseTy t
              [t1, t2] -> PairTy (BaseTy t1) (BaseTy t2)
              _ -> error $ "Not a valid FFI return type: " ++ pprint resultTys
    t:ts -> withFreshBinder noHint (BaseTy t) \b -> do
      PiType bs effTy <- go ts
      return $ PiType (Nest (PlainBD b) bs) effTy

-- === Data constraints ===

isData :: EnvReader m => Type CoreIR n -> m n Bool
isData ty = do
  result <- liftBuilderT $ withSubstReaderT do
    void $ buildScoped do
      checkDataLike ty
      return UnitE
  case runFallibleM result of
    Success () -> return True
    Failure _  -> return False

checkDataLike :: Emits o => Type CoreIR i -> SubstReaderT Name (BuilderT CoreIR FallibleM) i o ()
checkDataLike ty = case ty of
  TyVar _ -> notData
  TabPi (TabPiType _ b (Abs ds eltTy)) -> do
    renameBinders b \_ ->
      renameBinders ds \_ ->
        voidBuildScoped $ checkDataLike eltTy
  DepPairTy (DepPairType _ (BD ds1 b) (Abs ds2 r)) -> do
    renameBinders ds1 \_ -> do
      voidBuildScoped $ checkDataLike (binderType b)
      renameBinders b \_ ->
        renameBinders ds2 \_ ->
          voidBuildScoped $ checkDataLike r
  NewtypeTyCon nt -> do
    (_, ty') <- unwrapNewtypeType =<< renameM nt
    dropSubst $ recur ty'
  TC con -> case con of
    BaseType _       -> return ()
    ProdType as      -> mapM_ recur as
    SumType  cs      -> mapM_ recur cs
    RefType _ _      -> return ()
    HeapType         -> return ()
    _ -> notData
  _   -> notData
  where
    recur = checkDataLike
    notData = throw TypeErr $ pprint ty

voidBuildScoped
 :: (ScopableBuilder r m)
 => (forall l. (Emits l, DExt n l) => m l a) -> m n ()
voidBuildScoped body = void $ buildScoped $ body >> return UnitE

checkExtends :: (Fallible m, IRRep r) => EffectRow r n -> EffectRow r n -> m ()
checkExtends allowed (EffectRow effs effTail) = do
  let (EffectRow allowedEffs allowedEffTail) = allowed
  case effTail of
    EffectRowTail _ -> assertEq allowedEffTail effTail ""
    NoTail -> return ()
  forM_ (eSetToList effs) \eff -> unless (eff `eSetMember` allowedEffs) $
    throw CompilerErr $ "Unexpected effect: " ++ pprint eff ++
                      "\nAllowed: " ++ pprint allowed

-- === from CheapReduction ===0

repValAtom :: EnvReader m => SRepVal n -> m n (SAtom n)
repValAtom (RepVal ty tree) = case ty of
  ProdTy ts -> case tree of
    Branch trees -> ProdVal <$> mapM repValAtom (zipWith RepVal ts trees)
    _ -> malformed
  BaseTy _ -> case tree of
    Leaf x -> case x of
      ILit l -> return $ Con $ Lit l
      _ -> fallback
    _ -> malformed
  _ -> fallback
  where fallback = return $ RepValAtom $ RepVal ty tree
        malformed = error "malformed repval"
{-# INLINE repValAtom #-}

liftSimpType :: EnvReader m => SType n -> m n (CType n)
liftSimpType = \case
  BaseTy t -> return $ BaseTy t
  ProdTy ts -> ProdTy <$> mapM rec ts
  SumTy  ts -> SumTy  <$> mapM rec ts
  t -> error $ "not implemented: " ++ pprint t
  where rec = liftSimpType
{-# INLINE liftSimpType #-}

liftSimpFun :: EnvReader m => Type CoreIR n -> LamExpr SimpIR n -> m n (CAtom n)
liftSimpFun (Pi piTy) f = return $ SimpInCore $ LiftSimpFun piTy f
liftSimpFun _ _ = error "not a pi type"

depPairLeftTy :: BuilderEmits r m n => DepPairType r n -> m n (Type r n)
depPairLeftTy (DepPairType _ b _) = binderAndDeclsType b
{-# INLINE depPairLeftTy #-}

binderAndDeclsType :: BuilderEmits r m n => BinderAndDecls r n l -> m n (Type r n)
binderAndDeclsType (BD decls (_:>t)) = emitDecls $ Abs decls t

unwrapNewtypeType :: EnvReader m => NewtypeTyCon n -> m n (NewtypeCon n, Type CoreIR n)
unwrapNewtypeType = \case
  Nat                   -> return (NatCon, IdxRepTy)
  Fin n                 -> return (FinCon n, NatTy)
  UserADTType sn defName params repTy ->
    return (UserADTData sn defName params, repTy)
{-# INLINE unwrapNewtypeType #-}

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

projType :: BuilderEmits r m n => Int -> Type r n -> Atom r n -> m n (Type r n)
projType i ty x = case ty of
  ProdTy xs -> return $ xs !! i
  DepPairTy t | i == 0 -> depPairLeftTy t
  DepPairTy t | i == 1 -> do
    xFst <- getProductProj 0 x
    instantiate t [xFst]
  _ -> error $ "Can't project type: " ++ pprint ty

instantiateTyConDef :: CBuilderEmits m n => TyConDef n -> TyConParams n -> m n (DataConDefs n)
instantiateTyConDef tyConDef (TyConParams _ xs) = instantiate tyConDef xs
{-# INLINE instantiateTyConDef #-}

assumeConst
  :: (IRRep r, HoistableE body, SinkableE body, ToBindersAndDeclsAbs e body r) => e n -> body n
assumeConst e = case toAbs e of Abs bs body -> ignoreHoistFailure $ hoist bs body

arity :: (IRRep r, ToBindersAndDeclsAbs e body r) => e n -> Int
arity e = case toAbs e of Abs bs _ -> nestLength bs

tryAsConst
  :: (IRRep r, HoistableE body, SinkableE body, ToBindersAndDeclsAbs e body r) => e n -> Maybe (body n)
tryAsConst e =
  case toAbs e of
    Abs bs body -> case hoist bs body of
      HoistFailure _ -> Nothing
      HoistSuccess e' -> Just e'

instantiate
  :: ( BuilderEmits r m n, SubstE (SubstVal Atom) body, RenameE body -- TODO: shouldn't actually need RenameE
     , SinkableE body, SinkableE e, ToBindersAndDeclsAbs e body r, Ext h n)
  => e h -> [Atom r n] -> m n (body n)
instantiate e xs = do
   Abs bs result <- sinkM $ toAbs e
   runSubstReaderT idSubst $ extendSubstBD' bs (SubstVal <$> xs) $ substM result
{-# INLINE instantiate #-}

-- "lazy" subst-extending version of `instantiate`
withInstantiated
  :: ( SubstReader AtomSubstVal m, Builder2 r m, IRRep r, Emits o
     , SubstE (SubstVal Atom) body, SinkableE body, ToBindersAndDeclsAbs e body r)
  => e i -> [Atom r o]
  -> (forall i'. body i' -> m i' o a)
  -> m i o a
withInstantiated e xs cont = do
  Abs bs result <- return $ toAbs e
  extendSubstBD' bs (SubstVal <$> xs) $ cont result

extendSubstBD
 :: (SubstReader v m, SubstE v (Expr r), Builder2 r m, ToBindersAndDecls b r, IRRep r, Emits o)
 => b i i' -> [v (AtomNameC r) o] -> m i' o a -> m i o a
extendSubstBD bsTop xsTop contTop = extendSubstBD' (toBDs bsTop) xsTop contTop

extendSubstBD'
  :: (SubstReader v m, SubstE v (Expr r), Builder2 r m, IRRep r, Emits o)
  => Nest (BinderOrDecl r) ii ii' -> [v (AtomNameC r) o] -> m ii' o a -> m ii o a
extendSubstBD' Empty [] cont = cont
extendSubstBD' (Nest (LeftB b) bs) (x:xs) cont = do
  extendSubst (b@>x) $ extendSubstBD' bs xs cont
extendSubstBD' (Nest (RightB (Let b (DeclBinding _ expr))) bs) xs cont = do
  expr' <- substM expr
  AtomVar v _ <- emitDecl (getNameHint b) PlainLet expr'
  extendSubst (b@>fromName v) do
    extendSubstBD' bs xs cont
extendSubstBD' _ _ _ = error "zip error"
{-# INLINE extendSubstBD' #-}

substDecls
  :: (SubstReader v m, IRRep r, Builder2 r m, Emits o, SubstE v (Expr r))
  => Nest (Decl r) i i'
  -> m i' o a
  -> m i  o a
substDecls Empty cont = cont
substDecls (Nest (Let b (DeclBinding _ expr)) rest) cont = do
  expr' <- substM expr
  AtomVar v _ <- emitDecl (getNameHint b) PlainLet expr'
  extendSubst (b@>fromName v) do
    substDecls rest cont
{-# INLINE substDecls #-}

makeStructRepVal :: (Fallible1 m, EnvReader m) => TyConName n -> [CAtom n] -> m n (CAtom n)
makeStructRepVal tyConName args = do
  TyConDef _ _ _ (Abs _ (StructFields fields)) <- lookupTyCon tyConName
  case fields of
    [_] -> case args of
      [arg] -> return arg
      _ -> error "wrong number of args"
    _ -> return $ ProdVal args

-- === Normalizing to match-normal form ===

headNormalize :: (IRRep r, HeadNormalizable e r, EnvReader m) => e n -> m n (e n)
headNormalize e = liftBuilder $ withSubstReaderT $ headNormalize' e

class HeadNormalizable (e::E) (r::IR) | e -> r where
  headNormalize' :: e i -> SubstReaderT AtomSubstVal (BuilderM r) i o (e o)

instance IRRep r => HeadNormalizable (Type r) r where
  headNormalize' t = substM t >>= \case
    TyVar (AtomVar v ty) -> do
      lookupEnv v >>= \case
        AtomNameBinding (LetBound (DeclBinding TypeTransparent (Atom (Type t)))) ->
          dropSubst $ headNormalize t
        _ -> return $ TyVar $ AtomVar v ty
    t' -> return t'

instance IRRep r => HeadNormalizable (Atom r) r where
  headNormalize' = \case
    TypeAsAtom t -> TypeAsAtom <$> headNormalize' t
    atom -> substM atom >>= \case
      Var (AtomVar v ty) -> do
        lookupEnv v >>= \case
          AtomNameBinding (LetBound (DeclBinding TypeTransparent (Atom t))) ->
            dropSubst $ headNormalize t
          _ -> return $ Var $ AtomVar v ty
      atom' -> return atom'

instance IRRep r => HeadNormalizable (EffectRow r) r where
  headNormalize' = substM
