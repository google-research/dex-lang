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
import Data.Foldable (fold)
import Foreign.Ptr

import qualified Unsafe.Coerce as TrulyUnsafe

import CheapReduction
import Core
import Err
import MTL1
import Subst
import Name
-- import PeepholeOptimize
import PPrint
import QueryType
import Types.Core
import Types.Imp
import Types.Primitives
import Types.Source hiding (TCName (..), ConName (..))
import Types.Top
import Util (enumerate, transitiveClosureM, bindM2, toSnocList, popList)

-- temporary stub
peepholeExpr :: a -> a
peepholeExpr = id

-- === ToExpr ===

class ToExpr (e::E) where
  toExpr :: e n -> Expr n

instance ToExpr (Expr    ) where toExpr = id
instance ToExpr (Atom    ) where toExpr = Atom
instance ToExpr (Con     ) where toExpr = Atom . Con
instance ToExpr (AtomVar ) where toExpr = toExpr . toAtom
instance ToExpr (TypedHof) where toExpr = Hof

-- === Ordinary (local) builder class ===

class (EnvReader m, Fallible1 m) => Builder (m::MonadKind1) where
  rawEmitDecl :: Emits n => NameHint -> LetAnn -> Expr n -> m n (AtomVar n)

class (EnvExtender m, Builder m) => ScopableBuilder (m::MonadKind1) where
  buildScopedAndThen
    :: SinkableE e
    => (forall l. (Emits l, DExt n l) => m l (e l))
    -> (forall l.           DExt n l  => Nest Decl n l -> e l -> m l a)
    -> m n a

buildScoped
 :: (ScopableBuilder m, SinkableE e)
 => (forall l. (Emits l, DExt n l) => m l (e l))
 -> m n (Abs (Nest Decl) e n)
buildScoped cont = buildScopedAndThen cont \decls body -> return $ Abs decls body

type SBuilder = Builder
type CBuilder = Builder

type Builder2         (m :: MonadKind2) = forall i. Builder         (m i)
type ScopableBuilder2 (m :: MonadKind2) = forall i. ScopableBuilder (m i)

emitDecl :: (Builder m, Emits n) => NameHint -> LetAnn -> Expr n -> m n (AtomVar n)
emitDecl _ _ (Atom (Stuck _ (Var n))) = return n
emitDecl hint ann expr = rawEmitDecl hint ann expr
{-# INLINE emitDecl #-}

emit :: (Builder m, ToExpr e, Emits n) => e n -> m n (Atom n)
emit e = case toExpr e of
  Atom x -> return x
  Block _ block -> emitDecls block >>= emit
  expr -> do
    v <- emitDecl noHint PlainLet $ peepholeExpr expr
    return $ toAtom v
{-# INLINE emit #-}

emitUnOp :: (Builder m, Emits n) => UnOp -> Atom n -> m n (Atom n)
emitUnOp op x = emit $ PrimOp resultTy $ UnOp op x
  where resultTy = TyCon $ BaseType $ typeUnOp op $ getTypeBaseType x


emitBinOp :: (Builder m, Emits n) => BinOp -> Atom n -> Atom n -> m n (Atom n)
emitBinOp op x y = emit $ PrimOp resultTy $ BinOp op x y
  where resultTy = TyCon $ BaseType $ typeBinOp op $ getTypeBaseType x

emitRefOp :: (Builder m, Emits n) => Atom n -> RefOp (Atom n) -> m n (Atom n)
emitRefOp ref op = undefined

emitToVar :: (Builder m, ToExpr e, Emits n) => e n -> m n (AtomVar n)
emitToVar expr = emit expr >>= \case
  Stuck _ (Var v) -> return v
  atom -> emitDecl noHint PlainLet (toExpr atom)
{-# INLINE emitToVar #-}

emitDecls :: (Builder m, Emits n, RenameE e, SinkableE e)
          => WithDecls e n -> m n (e n)
emitDecls (Abs decls result) = runSubstReaderT idSubst $ go decls result where
  go :: (Builder m, Emits o, RenameE e, SinkableE e)
     => Nest Decl i i' -> e i' -> SubstReaderT Name m i o (e o)
  go Empty e = renameM e
  go (Nest (Let b (DeclBinding ann expr)) rest) e = do
    expr' <- renameM expr
    AtomVar v _ <- emitDecl (getNameHint b) ann expr'
    extendSubst (b @> v) $ go rest e

buildScopedAssumeNoDecls :: (SinkableE e, ScopableBuilder m)
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

newtype DoubleBuilderT (topEmissions::B) (m::MonadKind) (n::S) (a:: *) =
  DoubleBuilderT { runDoubleBuilderT' :: DoubleInplaceT Env topEmissions BuilderEmissions m n a }
  deriving ( Functor, Applicative, Monad, MonadFail, Fallible
           , MonadIO, Catchable, MonadReader r')

deriving instance (ExtOutMap Env frag, HoistableB frag, OutFrag frag, Fallible m)
                  => ScopeReader (DoubleBuilderT frag m)

type DoubleBuilder = DoubleBuilderT TopEnvFrag HardFailM

liftDoubleBuilderTNoEmissions
  :: (EnvReader m, Fallible m') => DoubleBuilderT UnitB m' n a -> m n (m' a)
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
     , ExtOutMap Env frag, OutFrag frag)
  => (forall l. DExt n l => DoubleBuilderT frag m' l (e l))
  -> m n (m' (Abs frag e n))
liftDoubleBuilderT cont = do
  env <- unsafeGetEnv
  Distinct <- getDistinct
  return $ runDoubleBuilderT env cont

runDoubleBuilderT
  :: ( Distinct n, Fallible m, SinkableE e, RenameE e
     , ExtOutMap Env frag, OutFrag frag)
  => Env n
  -> (forall l. DExt n l => DoubleBuilderT frag m l (e l))
  -> m (Abs frag e n)
runDoubleBuilderT env cont = do
  Abs envFrag (DoubleInplaceTResult REmpty e) <-
    runDoubleInplaceT env $ runDoubleBuilderT' cont
  return $ Abs envFrag e

instance (ExtOutMap Env f, OutFrag f, RenameB f, HoistableB f, Fallible m)
  => HoistingTopBuilder f (DoubleBuilderT f m) where
  emitHoistedEnv ab = DoubleBuilderT $ emitDoubleInplaceTHoisted ab
  {-# INLINE emitHoistedEnv #-}
  canHoistToTop e = DoubleBuilderT $ canHoistToTopDoubleInplaceT e
  {-# INLINE canHoistToTop #-}

instance (ExtOutMap Env frag, HoistableB frag, OutFrag frag, Fallible m)
          => EnvReader (DoubleBuilderT frag m) where
  unsafeGetEnv = DoubleBuilderT $ liftDoubleInplaceT $ unsafeGetEnv

instance ( RenameB frag, HoistableB frag, OutFrag frag
         , ExtOutMap Env frag, Fallible m)
        => Builder (DoubleBuilderT frag m) where
  rawEmitDecl hint ann e = DoubleBuilderT $ liftDoubleInplaceT $ runBuilderT' $ emitDecl hint ann e

instance ( RenameB frag, HoistableB frag, OutFrag frag
         , ExtOutMap Env frag, Fallible m)
         => ScopableBuilder (DoubleBuilderT frag m) where
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
instance ( RenameB frag, HoistableB frag, OutFrag frag
         , ExtOutMap Env frag, Fallible m)
         => EnvExtender (DoubleBuilderT frag m) where
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

instance (SinkableE v, HoistingTopBuilder f m) => HoistingTopBuilder f (SubstReaderT v m i) where
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
  emitBinding :: Mut n => NameHint -> Binding n -> m n (Name n)
  emitEnv :: (Mut n, SinkableE e, RenameE e) => Abs TopEnvFrag e n -> m n (e n)
  emitNamelessEnv :: TopEnvFrag n n -> m n ()
  localTopBuilder :: SinkableE e
                  => (forall l. (Mut l, DExt n l) => m l (e l))
                  -> m n (Abs TopEnvFrag e n)

emitBindingDefault :: (TopBuilder m, Mut n) => NameHint -> Binding n -> m n (Name n)
emitBindingDefault hint binding = do
  ab <- liftEnvReaderM $ withFreshBinder hint binding \b'-> do
    let topFrag = TopEnvFrag (toEnvFrag b') mempty mempty
    return $ Abs topFrag $ binderName b'
  emitEnv ab

updateTopEnv :: TopBuilder m => TopEnvUpdate n -> m n ()
updateTopEnv update = emitNamelessEnv $ TopEnvFrag emptyOutFrag mempty (toSnocList [update])

emitLocalModuleEnv :: TopBuilder m => ModuleEnv n -> m n ()
emitLocalModuleEnv env = emitNamelessEnv $ TopEnvFrag emptyOutFrag env mempty

emitTopLet :: (Mut n, TopBuilder m) => NameHint -> LetAnn -> Expr n -> m n (AtomVar n)
emitTopLet hint letAnn expr = do
  ty <- return $ getType expr
  v <- emitBinding hint $ AtomNameBinding $ LetBound (DeclBinding letAnn expr)
  return $ AtomVar v ty

emitTopFunBinding :: (Mut n, TopBuilder m) => NameHint -> TopFunDef n -> TopLam n -> m n (TopFunName n)
emitTopFunBinding hint def f = do
  emitBinding hint $ TopFunBinding $ DexTopFun def f Waiting

emitSourceMap :: TopBuilder m => SourceMap n -> m n ()
emitSourceMap sm = emitLocalModuleEnv $ mempty {envSourceMap = sm}

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

queryIxDictCache :: EnvReader m => AbsDict n -> m n (Maybe (Name n))
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
           , ScopeReader, MonadTrans1, MonadReader r
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

instance (SinkableE v, TopBuilder m) => TopBuilder (SubstReaderT v m i) where
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
           , Catchable, ScopeReader, Alternative
           , MonadWriter w, MonadReader r')

type BuilderM = BuilderT HardFailM

instance (MonadState s m) => MonadState s (BuilderT m n) where
  get :: BuilderT m n s
  get = BuilderT $ UnsafeMakeInplaceT \env decls -> do
    s <- get
    return (s, unsafeCoerceB decls, unsafeCoerceE env)

  put :: s -> BuilderT m n ()
  put s = BuilderT $ UnsafeMakeInplaceT \env decls -> do
    put s
    return ((), unsafeCoerceB decls, unsafeCoerceE env)

liftBuilderT :: (Fallible m, EnvReader m') => BuilderT m n a -> m' n (m a)
liftBuilderT cont = do
  env <- unsafeGetEnv
  Distinct <- getDistinct
  return do
    (REmpty, result) <- runInplaceT env $ runBuilderT' cont
    return result
{-# INLINE liftBuilderT #-}

liftBuilder :: (EnvReader m) => BuilderM n a -> m n a
liftBuilder cont = liftM runHardFail $ liftBuilderT cont
{-# INLINE liftBuilder #-}

-- TODO: This should not fabricate Emits evidence!!
-- XXX: this uses unsafe functions in its implementations. It should be safe to
-- use, but be careful changing it.
liftEmitBuilder :: (Builder m, SinkableE e, RenameE e)
                => BuilderM n (e n) -> m n (e n)
liftEmitBuilder cont = do
  env <- unsafeGetEnv
  Distinct <- getDistinct
  let (result, decls, _) = runHardFail $ unsafeRunInplaceT (runBuilderT' cont) env emptyOutFrag
  Emits <- fabricateEmitsEvidenceM
  emitDecls $ Abs (unsafeCoerceB $ unRNest decls) result

instance (Fallible m) => ScopableBuilder (BuilderT m) where
  buildScopedAndThen cont1 cont2 = BuilderT $ locallyMutableInplaceT
    (runBuilderT' do
       Emits <- fabricateEmitsEvidenceM
       cont1 )
    (\rdecls e -> runBuilderT' $ cont2 (unRNest rdecls) e)
  {-# INLINE buildScopedAndThen #-}

newtype BuilderDeclEmission (n::S) (l::S) = BuilderDeclEmission (Decl n l)
instance ExtOutMap Env BuilderDeclEmission where
  extendOutMap env (BuilderDeclEmission d) = env `extendOutMap` toEnvFrag d
  {-# INLINE extendOutMap #-}
instance ExtOutFrag BuilderEmissions BuilderDeclEmission where
  extendOutFrag rn (BuilderDeclEmission d) = RNest rn d
  {-# INLINE extendOutFrag #-}

instance Fallible m => Builder (BuilderT m) where
  rawEmitDecl hint ann expr = do
    ty <- return $ getType expr
    v <- BuilderT $ freshExtendSubInplaceT hint \b ->
           (BuilderDeclEmission $ Let b $ DeclBinding ann expr, binderName b)
    -- -- Debugging snippet
    -- traceM $ pprint v ++ " = " ++ pprint expr
    return $ AtomVar v ty
  {-# INLINE rawEmitDecl #-}

instance Fallible m => EnvReader (BuilderT m) where
  unsafeGetEnv = BuilderT $ getOutMapInplaceT
  {-# INLINE unsafeGetEnv #-}

instance Fallible m => EnvExtender (BuilderT m) where
  refreshAbs ab cont = BuilderT $ refreshAbs ab \b e -> runBuilderT' $ cont b e
  {-# INLINE refreshAbs #-}

instance (SinkableE v, ScopableBuilder m) => ScopableBuilder (SubstReaderT v m i) where
  buildScopedAndThen cont1 cont2 = SubstReaderT \env ->
    buildScopedAndThen
      (runReaderT (runSubstReaderT' cont1) (sink env))
      (\d e -> runReaderT (runSubstReaderT' $ cont2 d e) (sink env))
  {-# INLINE buildScopedAndThen #-}

instance (SinkableE v, Builder m) => Builder (SubstReaderT v m i) where
  rawEmitDecl hint ann expr = liftSubstReaderT $ emitDecl hint ann expr
  {-# INLINE rawEmitDecl #-}

instance (SinkableE e, ScopableBuilder m) => ScopableBuilder (ReaderT1 e m) where
  buildScopedAndThen cont1 cont2 = ReaderT1 $ ReaderT \env ->
    buildScopedAndThen
      (do env' <- sinkM env
          runReaderT (runReaderT1' cont1) env')
      (\d e -> do
          env' <- sinkM env
          runReaderT (runReaderT1' $ cont2 d e) env')

  {-# INLINE buildScopedAndThen #-}

instance (SinkableE e, Builder m) => Builder (ReaderT1 e m) where
  rawEmitDecl hint ann expr =
    ReaderT1 $ lift $ emitDecl hint ann expr
  {-# INLINE rawEmitDecl #-}

instance (DiffStateE s d, Builder m) => Builder (DiffStateT1 s d m) where
  rawEmitDecl hint ann expr = lift11 $ rawEmitDecl hint ann expr
  {-# INLINE rawEmitDecl #-}

instance (SinkableE e, HoistableState e, Builder m) => Builder (StateT1 e m) where
  rawEmitDecl hint ann expr = lift11 $ emitDecl hint ann expr
  {-# INLINE rawEmitDecl #-}

instance (SinkableE e, HoistableState e, ScopableBuilder m) => ScopableBuilder (StateT1 e m) where
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

instance Builder m => Builder (MaybeT1 m) where
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
  :: (ScopableBuilder m, HasNamesE e, ToExpr e)
  => (forall l. (Emits l, DExt n l) => m l (e l))
  -> m n (Expr n)
buildBlock cont = mkBlock =<< buildScoped cont
{-# INLINE buildBlock #-}

buildCoreLam
  :: ScopableBuilder m
  => CorePiType n
  -> (forall l. (Emits l, DExt n l) => [CAtomVar l] -> m l (CAtom l))
  -> m n (CoreLamExpr n)
buildCoreLam piTy@(CorePiType _ _ bs _) cont = do
  lam <- buildLamExpr (EmptyAbs bs) cont
  return $ CoreLamExpr piTy lam

buildAbs
  :: (EnvReader m, EnvExtender m, SinkableE e, ToBinding binding)
  => NameHint
  -> binding n
  -> (forall l. DExt n l => AtomVar l -> m l (e l))
  -> m n (Abs (BinderP binding) e n)
buildAbs hint binding cont = do
  withFreshBinder hint binding \b -> do
    case toBinding binding of
      AtomNameBinding atombinding -> do
        ty <- sinkM $ getType atombinding
        body <- cont $ AtomVar (binderName b) ty
        return $ Abs b body
{-# INLINE buildAbs #-}

typesFromNonDepBinderNest
  :: (EnvReader m, Fallible1 m)
  => Nest Binder n l -> m n [Type n]
typesFromNonDepBinderNest Empty = return []
typesFromNonDepBinderNest (Nest b rest) = do
  Abs rest' UnitE <- return $ assumeConst $ Abs (UnaryNest b) $ Abs rest UnitE
  tys <- typesFromNonDepBinderNest rest'
  return $ binderType b : tys

buildUnaryLamExpr
  :: (ScopableBuilder m)
  => NameHint -> Type n
  -> (forall l. (Emits l, Distinct l, DExt n l) => AtomVar l -> m l (Atom l))
  -> m n (LamExpr n)
buildUnaryLamExpr hint ty cont = do
  bs <- withFreshBinder hint ty \b -> return $ EmptyAbs (UnaryNest b)
  buildLamExpr bs \[v] -> cont v

buildBinaryLamExpr
  :: (ScopableBuilder m)
  => (NameHint, Type n) -> (NameHint, Type n)
  -> (forall l. (Emits l, Distinct l, DExt n l) => AtomVar l -> AtomVar l -> m l (Atom l))
  -> m n (LamExpr n)
buildBinaryLamExpr (h1,t1) (h2,t2) cont = do
  bs <- withFreshBinder h1 t1 \b1 -> withFreshBinder h2 (sink t2) \b2 ->
    return $ EmptyAbs $ BinaryNest b1 b2
  buildLamExpr bs \[v1, v2] -> cont v1 v2

buildLamExpr
  :: ScopableBuilder m
  => (EmptyAbs (Nest Binder) n)
  -> (forall l. (Emits l, Distinct l, DExt n l) => [AtomVar l] -> m l (Atom l))
  -> m n (LamExpr n)
buildLamExpr (Abs bs UnitE) cont = case bs of
  Empty -> LamExpr Empty <$> buildBlock (cont [])
  Nest b rest -> do
    Abs b' (LamExpr bs' body') <- buildAbs (getNameHint b) (binderType b) \v -> do
      rest' <- applySubst (b@>SubstVal (toAtom v)) $ EmptyAbs rest
      buildLamExpr rest' \vs -> cont $ sink v : vs
    return $ LamExpr (Nest b' bs') body'

buildTopLamFromPi
  :: ScopableBuilder m
  => PiType n
  -> (forall l. (Emits l, Distinct l, DExt n l) => [AtomVar l] -> m l (Atom l))
  -> m n (TopLam n)
buildTopLamFromPi piTy@(PiType bs _) cont =
  TopLam False piTy <$> buildLamExpr (EmptyAbs bs) cont

buildTopDestLamFromPi
  :: ScopableBuilder m
  => PiType n
  -> (forall l. (Emits l, Distinct l, DExt n l) => [AtomVar l] -> AtomVar l -> m l (Atom l))
  -> m n (TopLam n)
buildTopDestLamFromPi piTy@(PiType bs _) cont =
  TopLam True piTy <$> buildLamExpr (EmptyAbs bs) \argsAndDest -> do
    let (args, dest) = popList argsAndDest
    cont args dest

buildAlt
  :: ScopableBuilder m
  => Type n
  -> (forall l. (Distinct l, Emits l, DExt n l) => AtomVar l -> m l (Atom l))
  -> m n (Alt n)
buildAlt ty body = do
  buildAbs noHint ty \x ->
    buildBlock do
      Distinct <- getDistinct
      body $ sink x

buildCaseAlts :: (Emits n, ScopableBuilder m)
  => Atom n
  -> (forall l. DExt n l => Int -> Binder n l -> m l a)
  -> m n [a]
buildCaseAlts scrut indexedAltBody = do
  scrutTy <- return $ getType scrut
  altBinderTys <- caseAltsBinderTys scrutTy
  forM (enumerate altBinderTys) \(i, bTy) -> do
    withFreshBinder noHint bTy \b ->
      indexedAltBody i b

injectAltResult :: EnvReader m => [SType n] -> Int -> Alt n -> m n (Alt n)
injectAltResult sumTys con (Abs b body) = liftBuilder do
  buildAlt (binderType b) \v -> do
    originalResult <- emit =<< applySubst (b@>SubstVal (toAtom v)) body
    (dataResult, nonDataResult) <- fromPairReduced originalResult
    return $ toAtom $ ProdCon [dataResult, Con $ SumCon (sinkList sumTys) con nonDataResult]

-- TODO: consider a version with nonempty list of alternatives where we figure
-- out the result type from one of the alts rather than providing it explicitly
buildCase' :: (Emits n, ScopableBuilder m)
  => Atom n -> Type n
  -> (forall l. (Emits l, DExt n l) => Int -> Atom l -> m l (Atom l))
  -> m n (Expr n)
buildCase' scrut resultTy indexedAltBody = case scrut of
  Con con -> do
    SumCon _ i arg <- return con
    Distinct <- getDistinct
    Atom <$> indexedAltBody i (sink arg)
  Stuck _ _ -> do
    scrutTy <- return $ getType scrut
    altBinderTys <- caseAltsBinderTys scrutTy
    (alts, effs) <- unzip <$> forM (enumerate altBinderTys) \(i, bTy) -> do
      (Abs b' (body `PairE` eff')) <- buildAbs noHint bTy \x -> do
        blk <- buildBlock $ indexedAltBody i $ toAtom $ sink x
        return $ blk `PairE` getEffects blk
      return (Abs b' body, ignoreHoistFailure $ hoist b' eff')
    return $ Case scrut alts $ EffTy (fold effs) resultTy

buildCase :: (Emits n, ScopableBuilder m)
  => Atom n -> Type n
  -> (forall l. (Emits l, DExt n l) => Int -> Atom l -> m l (Atom l))
  -> m n (Atom n)
buildCase s r b = emit =<< buildCase' s r b

emitHof :: (Builder m, Emits n) => Hof n -> m n (Atom n)
emitHof hof = mkTypedHof hof >>= emit

mkTypedHof :: (EnvReader m) => Hof n -> m n (TypedHof n)
mkTypedHof hof = do
  effTy <- effTyOfHof hof
  return $ TypedHof effTy hof

mkFor
  :: (ScopableBuilder m)
  => NameHint -> ForAnn -> IxType n
  -> (forall l. (Emits l, DExt n l) => AtomVar l -> m l (Atom l))
  -> m n (Expr n)
mkFor hint ann (IxType iTy ixDict) body = do
  lam <- withFreshBinder hint iTy \b -> do
    let v = binderVar b
    body' <- buildBlock $ body $ sink v
    return $ LamExpr (UnaryNest b) body'
  liftM toExpr $ mkTypedHof $ For ann (IxType iTy ixDict) lam

buildFor :: (Emits n, ScopableBuilder m)
         => NameHint -> Direction -> IxType n
         -> (forall l. (Emits l, DExt n l) => AtomVar l -> m l (Atom l))
         -> m n (Atom n)
buildFor hint ann ty body = mkFor hint ann ty body >>= emit

buildMap :: (Emits n, ScopableBuilder m)
         => SAtom n
         -> (forall l. (Emits l, DExt n l) => SAtom l -> m l (SAtom l))
         -> m n (SAtom n)
buildMap xs f = do
  TabPi t <- return $ getTyCon xs
  buildFor noHint Fwd (tabIxType t) \i ->
    tabApp (sink xs) (toAtom i) >>= f

-- === vector space (ish) type class ===

emitLin :: (Builder m, ToExpr e, Emits n) => e n -> m n (Atom n)
emitLin e = case toExpr e of
  Atom x -> return x
  expr -> liftM toAtom $ emitDecl noHint LinearLet $ peepholeExpr expr
{-# INLINE emitLin #-}

emitHofLin :: (Builder m, Emits n) => Hof n -> m n (Atom n)
emitHofLin hof = mkTypedHof hof >>= emitLin
{-# INLINE emitHofLin #-}

zeroAt :: (Emits n, SBuilder m) => SType n -> m n (SAtom n)
zeroAt ty = liftEmitBuilder $ go ty where
  go :: Emits n => SType n -> BuilderM n (SAtom n)
  go (TyCon con) = case con of
    BaseType bt  -> return $ Con $ Lit $ zeroLit bt
    ProdType tys -> toAtom . ProdCon <$> mapM go tys
    TabPi tabPi -> buildFor (getNameHint tabPi) Fwd (tabIxType tabPi) \i ->
      go =<< instantiate (sink tabPi) [toAtom i]
    _ -> unreachable
  zeroLit bt = case bt of
    Scalar Float64Type -> Float64Lit 0.0
    Scalar Float32Type -> Float32Lit 0.0
    _                  -> unreachable
  unreachable :: a
  unreachable = error $ "Missing zero case for a tangent type: " ++ pprint ty

zeroLike :: (HasType e, SBuilder m, Emits n) => e n -> m n (SAtom n )
zeroLike x = zeroAt $ getType x

tangentType :: EnvReader m => SType n -> m n (SType n)
tangentType ty = maybeTangentType ty >>= \case
  Just tanTy -> return tanTy
  Nothing -> error $ "can't differentiate wrt type: " ++ pprint ty

maybeTangentType :: (EnvReader m) => Type n -> m n (Maybe (Type n))
maybeTangentType ty = liftEnvReaderT $ maybeTangentType' ty

maybeTangentType' :: Type n -> EnvReaderT Maybe n (Type n)
maybeTangentType' ty = case ty of
  TyCon con    -> case con of
    TabPi (TabPiType d b bodyTy) -> do
      refreshAbs (Abs b bodyTy) \b' bodyTy' -> do
        bodyTanTy <- rec bodyTy'
        return $ TabTy d b' bodyTanTy
    BaseType (Scalar Float64Type) -> return $ toType con
    BaseType (Scalar Float32Type) -> return $ toType con
    BaseType   _                  -> return $ UnitTy
    ProdType   tys                -> toType . ProdType <$> traverse rec tys
    _ -> empty
  _ -> empty
  where rec = maybeTangentType'

addTangent :: (Emits n, SBuilder m) => SAtom n -> SAtom n -> m n (SAtom n)
addTangent x y = do
  case getTyCon x of
    BaseType (Scalar _) -> emitBinOp FAdd x y
    ProdType _          -> do
      xs <- getUnpacked x
      ys <- getUnpacked y
      toAtom . ProdCon <$> zipWithM addTangent xs ys
    TabPi t ->
      liftEmitBuilder $ buildFor (getNameHint t) Fwd (tabIxType t) \i -> do
        bindM2 addTangent (tabApp (sink x) (toAtom i)) (tabApp (sink y) (toAtom i))
    ty -> notTangent ty
    where notTangent ty = error $ "Not a tangent type: " ++ pprint ty

symbolicTangentTy :: (EnvReader m, Fallible1 m) => CType n -> m n (CType n)
symbolicTangentTy elTy = lookupSourceMap "SymbolicTangent" >>= \case
  Just symTanName -> do
    return $ toType $ UserADTType "SymbolicTangent" symTanName $
      TyConParams [Explicit] [toAtom elTy]
  Nothing -> throwInternal $
    "Can't define a custom linearization with symbolic zeros: " ++
    "the SymbolicTangent type is not in scope."

symbolicTangentZero :: EnvReader m => SType n -> m n (SAtom n)
symbolicTangentZero argTy = return $ toAtom $ SumCon [UnitTy, argTy] 0 UnitVal

symbolicTangentNonZero :: EnvReader m => SAtom n -> m n (SAtom n)
symbolicTangentNonZero val = do
  ty <- return $ getType val
  return $ toAtom $ SumCon [UnitTy, ty] 1 val

-- === builder versions of common local ops ===

fadd :: (Builder m, Emits n) => Atom n -> Atom n -> m n (Atom n)
fadd x y = emitBinOp FAdd x y

fsub :: (Builder m, Emits n) => Atom n -> Atom n -> m n (Atom n)
fsub x y = emitBinOp FSub x y

fmul :: (Builder m, Emits n) => Atom n -> Atom n -> m n (Atom n)
fmul x y = emitBinOp FMul x y

fdiv :: (Builder m, Emits n) => Atom n -> Atom n -> m n (Atom n)
fdiv x y = emitBinOp FDiv x y

iadd :: (Builder m, Emits n) => Atom n -> Atom n -> m n (Atom n)
iadd x y = emitBinOp IAdd x y

imul :: (Builder m, Emits n) => Atom n -> Atom n -> m n (Atom n)
imul x y = emitBinOp IMul x y

fLitLike :: Double -> SAtom n -> SAtom n
fLitLike x t = case getTyCon t of
  BaseType (Scalar Float64Type) -> toAtom $ Lit $ Float64Lit x
  BaseType (Scalar Float32Type) -> toAtom $ Lit $ Float32Lit $ realToFrac x
  _ -> error "Expected a floating point scalar"

fromPair :: (Builder m, Emits n) => Atom n -> m n (Atom n, Atom n)
fromPair pair = do
  getUnpacked pair >>= \case
    [x, y] -> return (x, y)
    _ -> error "expected a pair"

-- the rightmost index is applied first
applyProjectionsRef :: (Builder m, Emits n) => [Projection] -> Atom n -> m n (Atom n)
applyProjectionsRef [] ref = return ref
applyProjectionsRef (i:is) ref = getProjRef i =<< applyProjectionsRef is ref

getProjRef :: (Builder m, Emits n) => Projection -> Atom n -> m n (Atom n)
getProjRef i = undefined -- emit =<< mkProjRef i

newUninitializedRef :: (SBuilder m, Emits o) => SType o -> m o (SAtom o)
newUninitializedRef ty = emit $ PrimOp ty $ MiscOp NewRef

-- XXX: getUnpacked must reduce its argument to enforce the invariant that
-- ProjectElt atoms are always fully reduced (to avoid type errors between two
-- equivalent types spelled differently).
getUnpacked :: (Builder m, Emits n) => Atom n -> m n [Atom n]
getUnpacked atom = forM (productIdxs atom) \i -> proj i atom
{-# SCC getUnpacked #-}

productIdxs :: Atom n -> [Int]
productIdxs atom =
  let positions = case getType atom of
        TyCon (ProdType tys)  -> void tys
        TyCon (DepPairTy _) -> [(), ()]
        ty -> error $ "not a product type: " ++ pprint ty
  in fst <$> enumerate positions

unwrapNewtype :: (Emits n, Builder m) => CAtom n -> m n (CAtom n)
unwrapNewtype (Con (NewtypeCon _ x)) = return x
unwrapNewtype x = case getType x of
  TyCon (NewtypeTyCon con) -> do
    (_, ty) <- unwrapNewtypeType con
    emit $ Unwrap ty x
  _ -> error "not a newtype"
{-# INLINE unwrapNewtype #-}

proj ::(Builder m, Emits n) => Int -> Atom n -> m n (Atom n)
proj i = \case
  Con con -> case con of
    ProdCon xs -> return $ xs !! i
    DepPair l _ _ | i == 0 -> return l
    DepPair _ r _ | i == 1 -> return r
    _ -> error "not a product"
  x -> do
    ty <- projType i x
    emit $ Project ty i x

getFst :: (Builder m, Emits n) => Atom n -> m n (Atom n)
getFst = proj 0

getSnd :: (Builder m, Emits n) => Atom n -> m n (Atom n)
getSnd = proj 1

projectStruct :: (Builder m, Emits n) => Int -> CAtom n -> m n (CAtom n)
projectStruct i x = do
  projs <- getStructProjections i (getType x)
  applyProjections projs x
{-# INLINE projectStruct #-}

projectStructRef :: (Builder m, Emits n) => Int -> CAtom n -> m n (CAtom n)
projectStructRef i x = do
  RefTy valTy <- return $ getType x
  projs <- getStructProjections i valTy
  applyProjectionsRef projs x
{-# INLINE projectStructRef #-}

getStructProjections :: EnvReader m => Int -> CType n -> m n [Projection]
getStructProjections i (TyCon (NewtypeTyCon (UserADTType _ tyConName _))) = do
  TyConDef _ _ _ ~(StructFields fields) <- lookupTyCon tyConName
  return case fields of
    [_] | i == 0    -> [UnwrapNewtype]
        | otherwise -> error "bad index"
    _ -> [ProjectProduct i, UnwrapNewtype]
getStructProjections _ _ = error "not a struct"

-- the rightmost index is applied first
applyProjections :: (Builder m, Emits n) => [Projection] -> CAtom n -> m n (CAtom n)
applyProjections [] x = return x
applyProjections (p:ps) x = do
  x' <- applyProjections ps x
  case p of
    ProjectProduct i -> proj i x'
    UnwrapNewtype    -> unwrapNewtype x'

-- the rightmost index is applied first
applyProjectionsReduced :: EnvReader m => [Projection] -> CAtom n -> m n (CAtom n)
applyProjectionsReduced [] x = return x
applyProjectionsReduced (p:ps) x = do
  x' <- applyProjectionsReduced ps x
  case p of
    ProjectProduct i -> reduceProj i x'
    UnwrapNewtype    -> reduceUnwrap x'

mkBlock :: (EnvReader m, ToExpr e) => Abs Decls e n -> m n (Expr n)
mkBlock (Abs Empty expr) = return $ toExpr expr
mkBlock (Abs decls body) = do
  let block = Abs decls (toExpr body)
  effTy <- blockEffTy block
  return $ Block effTy block

blockEffTy :: (EnvReader m) => Block n -> m n (EffTy n)
blockEffTy block = liftEnvReaderM $ refreshAbs block \decls result -> do
  effs <- declsEffects decls mempty
  return $ ignoreHoistFailure $ hoist decls $ EffTy effs $ getType result
  where
    declsEffects :: Nest Decl n l -> Effects l -> EnvReaderM l (Effects l)
    declsEffects Empty !acc = return acc
    declsEffects n@(Nest (Let _ (DeclBinding _ expr)) rest) !acc = withExtEvidence n do
      expr' <- sinkM expr
      declsEffects rest $ acc <> getEffects expr'

mkApp :: EnvReader m => CAtom n -> [CAtom n] -> m n (CExpr n)
mkApp f xs = do
  et <- appEffTy (getType f) xs
  return $ App et f xs

mkTabApp :: (EnvReader m) => Atom n -> Atom n -> m n (Expr n)
mkTabApp xs ixs = do
  ty <- typeOfTabApp (getType xs) ixs
  return $ TabApp ty xs ixs

mkProject :: (EnvReader m) => Int -> Atom n -> m n (Expr n)
mkProject i x = do
  ty <- projType i x
  return $ Project ty i x

mkTopApp :: EnvReader m => TopFunName n -> [SAtom n] -> m n (SExpr n)
mkTopApp f xs = do
  resultTy <- typeOfTopApp f xs
  return $ TopApp resultTy f xs

mkApplyMethod :: EnvReader m => CDict n -> Int -> [CAtom n] -> m n (CExpr n)
mkApplyMethod d i xs = do
  resultTy <- typeOfApplyMethod d i xs
  return $ ApplyMethod resultTy (toAtom d) i xs

mkInstanceDict :: EnvReader m => InstanceName n -> [CAtom n] -> m n (CDict n)
mkInstanceDict instanceName args = do
  instanceDef@(InstanceDef className _ _ _ _) <- lookupInstanceDef instanceName
  PairE (ListE params) _ <- instantiate instanceDef args
  ty <- toType <$> dictType className params
  return $ toDict $ InstanceDict ty instanceName args

mkCase :: (EnvReader m) => Atom n -> Type n -> [Alt n] -> m n (Expr n)
mkCase scrut resultTy alts = liftEnvReaderM do
  eff' <- undefined
  return $ Case scrut alts (EffTy eff' resultTy)

app :: (CBuilder m, Emits n) => CAtom n -> CAtom n -> m n (CAtom n)
app x i = mkApp x [i] >>= emit

naryApp :: (CBuilder m, Emits n) => CAtom n -> [CAtom n] -> m n (CAtom n)
naryApp f xs= mkApp f xs >>= emit
{-# INLINE naryApp #-}

topApp :: (Builder m, Emits n) => TopFunName n -> [SAtom n] -> m n (SAtom n)
topApp f xs = emit =<< mkTopApp f xs
{-# INLINE topApp #-}

topAppInlined :: (Builder m, Emits n) => TopFunName n -> [SAtom n] -> m n (SAtom n)
topAppInlined f xs = do
  TopFunBinding f' <- lookupEnv f
  case f' of
    DexTopFun _ lam _ -> instantiate lam xs >>= emit
    _ -> topApp f xs
{-# INLINE topAppInlined #-}

tabApp :: (Builder m, Emits n) => Atom n -> Atom n -> m n (Atom n)
tabApp x i = mkTabApp x i >>= emit

naryTabApp :: (Builder m, Emits n) => Atom n -> [Atom n] -> m n (Atom n)
naryTabApp f [] = return f
naryTabApp f (x:xs) = do
  ans <- mkTabApp f x >>= emit
  naryTabApp ans xs
{-# INLINE naryTabApp #-}

indexRef :: (Builder m, Emits n) => Atom n -> Atom n -> m n (Atom n)
indexRef ref i = emit =<< mkIndexRef ref i

naryIndexRef :: (Builder m, Emits n) => Atom n -> [Atom n] -> m n (Atom n)
naryIndexRef ref is = foldM indexRef ref is

ptrOffset :: (Builder m, Emits n) => Atom n -> Atom n -> m n (Atom n)
ptrOffset x (IdxRepVal 0) = return x
ptrOffset x i = undefined -- emit $ PtrOffset x i
{-# INLINE ptrOffset #-}

unsafePtrLoad :: (Builder m, Emits n) => Atom n -> m n (Atom n)
unsafePtrLoad x = undefined -- emit . PtrLoad =<< sinkM x

mkIndexRef :: (EnvReader m, Fallible1 m) => Atom n -> Atom n -> m n (Expr n)
mkIndexRef ref i = do
  resultTy <- typeOfIndexRef (getType ref) i
  return $ PrimOp resultTy $ RefOp ref $ IndexRef i

mkProjRef :: (EnvReader m) => Atom n -> Projection -> m n (Expr n)
mkProjRef ref i = do
  resultTy <- typeOfProjRef (getType ref) i
  return $ PrimOp resultTy $ RefOp ref $ ProjRef i

-- === index set type class ===

applyIxMethod :: (SBuilder m, Emits n) => IxDict n -> IxMethod -> [SAtom n] -> m n (SAtom n)
applyIxMethod (DictCon dict) method args = case dict of
  -- These cases are used in and they work with IdxRepVal
  IxRawFin n -> case method of
    Size              -> do []  <- return args; return n
    Ordinal           -> do [i] <- return args; return i
    UnsafeFromOrdinal -> do [i] <- return args; return i
  IxSpecialized d params -> do
    SpecializedDict _ maybeFs <- lookupSpecDict d
    Just fs <- return maybeFs
    instantiate (fs !! fromEnum method) (params ++ args) >>= emit

unsafeFromOrdinal :: (SBuilder m, Emits n) => IxType n -> Atom n -> m n (Atom n)
unsafeFromOrdinal (IxType _ dict) i = applyIxMethod dict UnsafeFromOrdinal [i]

ordinal :: (SBuilder m, Emits n) => IxType n -> Atom n -> m n (Atom n)
ordinal (IxType _ dict) idx = applyIxMethod dict Ordinal [idx]

indexSetSize :: (SBuilder m, Emits n) => IxType n -> m n (SAtom n)
indexSetSize (IxType _ dict) = applyIxMethod dict Size []

-- === core versions of index set type class ===

applyIxMethodCore :: (CBuilder m, Emits n) => IxMethod -> IxType n -> [CAtom n] -> m n (CAtom n)
applyIxMethodCore method (IxType _ dict) args =
  emit =<< mkApplyMethod dict (fromEnum method) args

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
  predicate' <- emit $ PrimOp (TyCon (SumType [UnitTy, UnitTy])) $ MiscOp (ToEnum predicate)
  buildCase predicate' resultTy \i _ ->
    case i of
      0 -> falseCase
      1 -> trueCase
      _ -> error "should only have two cases"

-- === capturing closures with telescopes ===

type ReconAbs e = Abs ReconBinders e

data ReconBinders n l = ReconBinders
  (TelescopeType Type n)
  (Nest NameBinder n l)

data TelescopeType e n =
   DepTelescope (TelescopeType e n) (Abs (BinderP e) (TelescopeType e) n)
 | ProdTelescope [e n]

instance GenericB ReconBinders where
  type RepB ReconBinders =
    PairB (LiftB (TelescopeType Type))
          (Nest NameBinder)
  fromB (ReconBinders x y) = PairB (LiftB x) y
  {-# INLINE fromB #-}
  toB (PairB (LiftB x) y) = ReconBinders x y
  {-# INLINE toB #-}

instance BindsNameList ReconBinders where
  bindNameList (ReconBinders _ bs) = bindNameList bs

instance Pretty (ReconBinders n l) where
  pretty (ReconBinders _ ab) = pretty ab

instance RenameB    ReconBinders
instance SinkableB  ReconBinders
instance ProvesExt  ReconBinders
instance BindsNames ReconBinders
instance HoistableB ReconBinders

instance GenericE (TelescopeType e) where
  type RepE (TelescopeType e) = EitherE
         (PairE (TelescopeType e) (Abs (BinderP e) (TelescopeType e)))
         (ListE e)
  fromE (DepTelescope lhs ab) = LeftE (PairE lhs ab)
  fromE (ProdTelescope tys)   = RightE (ListE tys)
  {-# INLINE fromE #-}
  toE (LeftE (PairE lhs ab)) = DepTelescope lhs ab
  toE (RightE (ListE tys))   = ProdTelescope tys
  {-# INLINE toE #-}

instance SinkableE e => SinkableE (TelescopeType e)
instance (SinkableE e, RenameE e) => RenameE (TelescopeType e)
instance (ToBinding e, SubstE AtomSubstVal e) => SubstE AtomSubstVal (TelescopeType e)
instance HoistableE e => HoistableE (TelescopeType e)

telescopicCapture
  :: (EnvReader m, HoistableE e, HoistableB b)
  => b n l -> e l -> m l (Atom l, ReconAbs e n)
telescopicCapture bs e = do
  vs <- localVarsAndTypeVars bs e
  vTys <- forM vs \v -> getType <$> toAtomVar v
  let vsTysSorted = toposortAnnVars $ zip vs vTys
  let vsSorted = map fst vsTysSorted
  ty <- liftEnvReaderM $ buildTelescopeTy vsTysSorted
  valsSorted <- forM vsSorted \v -> toAtom <$> toAtomVar v
  result <- buildTelescopeVal valsSorted ty
  reconAbs <- return $ ignoreHoistFailure $ hoist bs do
    case abstractFreeVarsNoAnn vsSorted e of
      Abs bs' e' -> Abs (ReconBinders ty bs') e'
  return (result, reconAbs)

applyReconAbs
  :: (EnvReader m, Fallible1 m, SinkableE e, SubstE AtomSubstVal e)
  => ReconAbs e n -> Atom n -> m n (e n)
applyReconAbs (Abs bs result) x = do
  xs <- unpackTelescope bs x
  applySubst (bs @@> map SubstVal xs) result

buildTelescopeTy
  :: (EnvReader m, EnvExtender m, HoistableE e)
  => [AnnVar e n] -> m n (TelescopeType e n)
buildTelescopeTy [] = return (ProdTelescope [])
buildTelescopeTy ((v,ty):xs) = do
  rhs <- buildTelescopeTy xs
  Abs b rhs' <- return $ abstractFreeVar v rhs
  case hoist b rhs' of
    HoistSuccess rhs'' -> return $ prependTelescopeTy ty rhs''
    HoistFailure _ -> return $ DepTelescope (ProdTelescope []) (Abs (b:>ty) rhs')

prependTelescopeTy :: e n -> TelescopeType e n -> TelescopeType e n
prependTelescopeTy x = \case
  DepTelescope lhs rhs -> DepTelescope (prependTelescopeTy x lhs) rhs
  ProdTelescope xs -> ProdTelescope (x:xs)

buildTelescopeVal
  :: (EnvReader m) => [Atom n] -> TelescopeType Type n -> m n (Atom n)
buildTelescopeVal xsTop tyTop = fst <$> go tyTop xsTop where
  go :: (EnvReader m)
     => TelescopeType Type n ->  [Atom n]
     -> m n (Atom n, [Atom n])
  go ty rest = case ty of
    ProdTelescope tys -> do
      (xs, rest') <- return $ splitAt (length tys) rest
      return (toAtom $ ProdCon xs, rest')
--     DepTelescope ty1 (Abs b ty2) -> do
--       (x1, ~(xDep : rest')) <- go ty1 rest
--       ty2' <- applySubst (b@>SubstVal xDep) ty2
--       (x2, rest'') <- go ty2' rest'
--       let depPairTy = DepPairType ExplicitDepPair b (telescopeTypeType ty2)
--       return (toAtom $ ProdCon [x1, toAtom $ DepPair xDep x2 depPairTy], rest'')

-- telescopeTypeType :: TelescopeType (AtomNameC r) Type n -> Type n
-- telescopeTypeType (ProdTelescope tys) = toType $ ProdType tys
-- telescopeTypeType (DepTelescope lhs (Abs b rhs)) = do
--   let lhs' = telescopeTypeType lhs
--   let rhs' = toType $ DepPairTy (DepPairType ExplicitDepPair b (telescopeTypeType rhs))
--   PairTy lhs' rhs'

unpackTelescope
  :: (Fallible1 m, EnvReader m)
  => ReconBinders l1 l2 -> Atom n -> m n [Atom n]
unpackTelescope (ReconBinders tyTop _) xTop = go tyTop xTop where
  go :: (Fallible1 m, EnvReader m)
     => TelescopeType e l-> Atom n -> m n [Atom n]
  go ty x = case ty of
    ProdTelescope _ -> getUnpackedReduced x
    DepTelescope ty1 (Abs _  ty2) -> do
      (x1, xPair) <- fromPairReduced x
      (xDep, x2) <- fromPairReduced xPair
      xs1 <- go ty1 x1
      xs2 <- go ty2 x2
      return $ xs1 ++ (xDep : xs2)

fromPairReduced :: (Fallible1 m, EnvReader m) => Atom n -> m n (Atom n, Atom n)
fromPairReduced pair = (,) <$> reduceProj 0 pair <*> reduceProj 1 pair

getUnpackedReduced :: (Fallible1 m, EnvReader m) => Atom n -> m n [Atom n]
getUnpackedReduced xs = forM (productIdxs xs) \i -> reduceProj i xs

-- sorts name-annotation pairs so that earlier names may be occur free in later
-- annotations but not vice versa.
type AnnVar e n = (Name n, e n)
toposortAnnVars :: forall e n.  (HoistableE e) => [AnnVar e n] -> [AnnVar e n]
toposortAnnVars annVars =
  let (graph, vertexToNode, _) = graphFromEdges $ map annVarToNode annVars
  in map (nodeToAnnVar . vertexToNode) $ reverse $ topSort graph
  where
    annVarToNode :: (Name n, e n) -> (e n, Name n, [Name n])
    annVarToNode (v, ann) = (ann, v, nameSetToList $ freeVarsE ann)

    nodeToAnnVar :: (e n, Name n, [Name n]) -> (Name n, e n)
    nodeToAnnVar (ann, v, _) = (v, ann)

-- gives a list of atom names that are free in `e`, including names mentioned in
-- the types of those names, recursively. TODO: the reason for the distinction
-- between `localVarsAndTypeVars` and `localVars` is that we used to not have
-- the types cached locally on the vars. Now we do, so we don't need it.
localVarsAndTypeVars
  :: forall m b e n l r.
     (EnvReader m, BindsNames b, HoistableE e)
  => b n l -> e l -> m l [AtomName l]
localVarsAndTypeVars b e =
  transitiveClosureM varsViaType (localVars b e)
  where
    varsViaType :: AtomName l -> m l [AtomName l]
    varsViaType v = do
      ty <- getType <$> toAtomVar v
      return $ localVars b ty

localVars :: (BindsNames b, HoistableE e) => b n l -> e l -> [Name l]
localVars b e = nameSetToList $ nameSetIntersection (toNameSet (toScopeFrag b)) (freeVarsE e)

-- See Note [Confuse GHC] from Simplify.hs
-- (we use a Builder-specific name to avoid collisions, since we export everything from Builder)
confuseGHCBuilder :: BuilderM n (DistinctEvidence n)
confuseGHCBuilder = getDistinct
{-# INLINE confuseGHCBuilder #-}

-- === Non-emitting expression visitor ===

class Visitor m i o => ExprVisitorNoEmits m i o | m -> i, m -> o where
  visitExprNoEmits :: Expr i -> m (Expr o)

type ExprVisitorNoEmits2 m = forall i o. ExprVisitorNoEmits (m i o) i o

visitLamNoEmits
  :: (ExprVisitorNoEmits2 m, AtomSubstReader v m, EnvExtender2 m)
  => LamExpr i -> m i o (LamExpr o)
visitLamNoEmits (LamExpr bs body) =
  visitBinders bs \bs' -> LamExpr bs' <$> visitExprNoEmits body

visitDeclsNoEmits
  :: (ExprVisitorNoEmits2 m, AtomSubstReader v m, EnvExtender2 m)
  => Nest Decl i i'
  -> (forall o'. DExt o o' => Nest Decl o o' -> m i' o' a)
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

class Visitor m i o => ExprVisitorEmits m i o | m -> i, m -> o where
  visitExprEmits :: Emits o => Expr i -> m (Atom o)

type ExprVisitorEmits2 m = forall i o. ExprVisitorEmits (m i o) i o

liftAtomSubstBuilder :: forall tag m n a. (EnvReader m) => AtomSubstBuilder tag n n a -> m n a
liftAtomSubstBuilder cont = liftBuilder $ runSubstReaderT idSubst $ runAtomSubstBuilder cont

-- The phantom type `v` is for defining `Visitor` instances. The pattern is to
-- define a new singleton type, like `data MyTag = MyTag`.
newtype AtomSubstBuilder v i o a =
  AtomSubstBuilder { runAtomSubstBuilder :: SubstReaderT AtomSubstVal BuilderM i o a}
  deriving (MonadFail, Fallible, Functor, Applicative, Monad, ScopeReader,
            EnvReader, EnvExtender, Builder, SubstReader AtomSubstVal,
            ScopableBuilder)

visitLamEmits
  :: (ExprVisitorEmits2 m, SubstReader AtomSubstVal m, ScopableBuilder2 m)
  => LamExpr i -> m i o (LamExpr o)
visitLamEmits (LamExpr bs body) = visitBinders bs \bs' -> LamExpr bs' <$>
  buildBlock (visitExprEmits body)

visitDeclsEmits
  :: (ExprVisitorEmits2 m, SubstReader AtomSubstVal m, EnvExtender2 m, Emits o)
  => Nest Decl i i'
  -> m i' o a
  -> m i  o a
visitDeclsEmits Empty cont = cont
visitDeclsEmits (Nest (Let b (DeclBinding _ expr)) decls) cont = do
  x <- visitExprEmits expr
  extendSubst (b@>SubstVal x) do
    visitDeclsEmits decls cont
