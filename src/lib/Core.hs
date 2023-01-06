-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DefaultSignatures #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- Some monads (e.g. EnvReader) and syntactic helpers for operating on CoreIR.

module Core where

import Control.Applicative
import Control.Monad.Except hiding (Except)
import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.Writer.Strict hiding (Alt)
import Control.Monad.State
import qualified Control.Monad.State.Strict as SS
import qualified Data.Map.Strict       as M

import Name
import Err
import IRVariants

import Types.Core
import Types.Imp
import Types.Primitives
import Types.Source

-- === Typeclasses for monads ===

class ScopeReader m => EnvReader (m::MonadKind1) where
  -- Unsafe because an in-place update to `n` would invalidate the env.
  unsafeGetEnv :: m n (Env n)

-- A safe version of unsafeGetEnv (thanks to SinkableE).
withEnv :: (SinkableE e, EnvReader m) => (Env n -> e n) -> m n (e n)
withEnv f = f <$> unsafeGetEnv
{-# INLINE withEnv #-}

-- Allows going under the binder with a guarantee that said binder is
-- distinct from everything else in scope, renaming if necessary.  To
-- wit, the binder in an (Abs b e n) may shadow names from the scope n
-- -- Abs makes no guarantees.  If we want to go under the binder to
-- operate on the `e`, we want to make sure it's fresh with respect to
-- the enclosing scope, which is what refreshAbs does for its
-- continuation (with DExt n l serving as proof thereof).
class (EnvReader m, Monad1 m) => EnvExtender (m::MonadKind1) where
  refreshAbs
    :: (BindsEnv b, RenameB b, RenameE e)
    => Abs b e n
    -> (forall l. DExt n l => b n l -> e l -> m l a)
    -> m n a

class Monad2 m => EnvReaderI (m::MonadKind2) where
   getEnvI :: m i o (Env i)
   getDistinctI :: m i o (DistinctEvidence i)
   withEnvI :: Distinct i' => Env i' -> m i' o a -> m i o a

type EnvReader2   (m::MonadKind2) = forall (n::S). EnvReader   (m n)
type EnvExtender2 (m::MonadKind2) = forall (n::S). EnvExtender (m n)

-- === EnvReader monad ===

newtype EnvReaderT (m::MonadKind) (n::S) (a:: *) =
  EnvReaderT {runEnvReaderT' :: ReaderT (DistinctEvidence n, Env n) m a }
  deriving ( Functor, Applicative, Monad, MonadFail
           , MonadWriter w, Fallible, Searcher, Alternative)

type EnvReaderM = EnvReaderT Identity

runEnvReaderM :: Distinct n => Env n -> EnvReaderM n a -> a
runEnvReaderM bindings m = runIdentity $ runEnvReaderT bindings m
{-# INLINE runEnvReaderM #-}

runEnvReaderT :: Distinct n => Env n -> EnvReaderT m n a -> m a
runEnvReaderT bindings cont =
  runReaderT (runEnvReaderT' cont) (Distinct, bindings)
{-# INLINE runEnvReaderT #-}

liftEnvReaderM :: EnvReader m => EnvReaderM n a -> m n a
liftEnvReaderM cont = liftM runIdentity $ liftEnvReaderT cont
{-# INLINE liftEnvReaderM #-}

liftExceptEnvReaderM :: (EnvReader m, Fallible1 m) => EnvReaderT Except n a -> m n a
liftExceptEnvReaderM cont = liftEnvReaderT cont >>= liftExcept
{-# INLINE liftExceptEnvReaderM #-}

liftEnvReaderT :: EnvReader m' => EnvReaderT m n a -> m' n (m a)
liftEnvReaderT cont = do
  env <- unsafeGetEnv
  Distinct <- getDistinct
  return $ runReaderT (runEnvReaderT' cont) (Distinct, env)
{-# INLINE liftEnvReaderT #-}

instance Monad m => EnvReader (EnvReaderT m) where
  unsafeGetEnv = EnvReaderT $ asks snd
  {-# INLINE unsafeGetEnv #-}

instance Monad m => EnvExtender (EnvReaderT m) where
  refreshAbs ab cont = EnvReaderT $ ReaderT
    \(Distinct, env) -> refreshAbsPure (toScope env) ab
       \_ b e -> do
         let env' = extendOutMap env $ toEnvFrag b
         runReaderT (runEnvReaderT' $ cont b e) (Distinct, env')
  {-# INLINE refreshAbs #-}

instance Monad m => ScopeReader (EnvReaderT m) where
  getDistinct = EnvReaderT $ asks fst
  {-# INLINE getDistinct #-}
  unsafeGetScope = toScope <$> snd <$> EnvReaderT ask
  {-# INLINE unsafeGetScope #-}

instance MonadIO m => MonadIO (EnvReaderT m n) where
  liftIO m = EnvReaderT $ lift $ liftIO m
  {-# INLINE liftIO #-}

deriving instance (Monad m, MonadState s m) => MonadState s (EnvReaderT m o)

-- === Instances for Name monads ===

instance (SinkableE e, EnvReader m)
         => EnvReader (OutReaderT e m) where
  unsafeGetEnv = OutReaderT $ lift $ unsafeGetEnv
  {-# INLINE unsafeGetEnv #-}

instance (SinkableE e, ScopeReader m, EnvExtender m)
         => EnvExtender (OutReaderT e m) where
  refreshAbs ab cont = OutReaderT $ ReaderT \env ->
    refreshAbs ab \b e -> do
      let OutReaderT (ReaderT cont') = cont b e
      env' <- sinkM env
      cont' env'
  {-# INLINE refreshAbs #-}

instance (Monad m, ExtOutMap Env decls, OutFrag decls)
         => EnvReader (InplaceT Env decls m) where
  unsafeGetEnv = getOutMapInplaceT
  {-# INLINE unsafeGetEnv #-}

instance ( Monad m
         , ExtOutMap Env d1, OutFrag d1
         , ExtOutMap Env d2, OutFrag d2)
         => EnvReader (DoubleInplaceT Env d1 d2 m) where
  unsafeGetEnv = liftDoubleInplaceT $ getOutMapInplaceT
  {-# INLINE unsafeGetEnv #-}

instance (Monad m, ExtOutMap Env decls, OutFrag decls)
         => EnvExtender (InplaceT Env decls m) where
  refreshAbs ab cont = UnsafeMakeInplaceT \env decls ->
    refreshAbsPure (toScope env) ab \_ b e -> do
      let subenv = extendOutMap env $ toEnvFrag b
      (ans, d, _) <- unsafeRunInplaceT (cont b e) subenv emptyOutFrag
      case fabricateDistinctEvidence @UnsafeS of
        Distinct -> do
          let env' = extendOutMap (unsafeCoerceE env) d
          return (ans, catOutFrags decls d, env')
  {-# INLINE refreshAbs #-}

instance ( Monad m, ExtOutMap Env d1, ExtOutMap Env d2
         , OutFrag d1, OutFrag d2, RenameB d1, HoistableB d1)
         => EnvExtender (DoubleInplaceT Env d1 d2 m) where
  refreshAbs ab cont = do
    (ans, decls) <- UnsafeMakeDoubleInplaceT do
      SS.StateT \s@(topScope, _) -> do
        (ans, (_, decls)) <- refreshAbs ab \b e -> do
          flip SS.runStateT (topScope, emptyOutFrag) $
            unsafeRunDoubleInplaceT $ cont b e
        return ((ans, decls), s)
    unsafeEmitDoubleInplaceTHoisted decls
    return ans
  {-# INLINE refreshAbs #-}


-- === Typeclasses for syntax ===

-- TODO: unify this with `HasNames` by parameterizing by the thing you bind,
-- like we do with `SubstE Name`, `SubstE AtomSubstVal`, etc?
class BindsNames b => BindsEnv (b::B) where
  toEnvFrag :: Distinct l => b n l -> EnvFrag n l

  default toEnvFrag :: (GenericB b, BindsEnv (RepB b))
                        => Distinct l => b n l -> EnvFrag n l
  toEnvFrag b = toEnvFrag $ fromB b

instance (Color c, SinkableE ann, ToBinding ann c) => BindsEnv (BinderP c ann) where
  toEnvFrag (b:>ann) = EnvFrag (RecSubstFrag (b @> toBinding ann')) Nothing
    where ann' = withExtEvidence b $ sink ann

instance (SinkableE ann, ToBinding ann AtomNameC) => BindsEnv (NonDepNest r ann) where
  toEnvFrag (NonDepNest topBs topAnns) = toEnvFrag $ zipNest topBs topAnns
    where
      zipNest :: Distinct l => Nest AtomNameBinder n l -> [ann n] -> Nest (BinderP AtomNameC ann) n l
      zipNest Empty [] = Empty
      zipNest (Nest b bs) (a:anns) = withExtEvidence b $ withSubscopeDistinct bs $
        Nest (b:>a) $ zipNest bs $ sinkList anns
      zipNest _ _ = error "Mismatched lengths in NonDepNest"

instance BindsEnv EffectBinder where
  toEnvFrag (EffectBinder effs) = EnvFrag emptyOutFrag $ Just effs

instance BindsEnv (PiBinder r) where
  toEnvFrag :: Distinct l => PiBinder r n l -> EnvFrag n l
  toEnvFrag (PiBinder b ty arr) =
    withExtEvidence b do
      let binding = toBinding $ sink $ PiBinding arr ty
      EnvFrag (RecSubstFrag $ b @> binding) (Just Pure)

instance BindsEnv (Decl r) where
  toEnvFrag (Let b binding) = toEnvFrag $ b :> binding
  {-# INLINE toEnvFrag #-}

instance BindsEnv TopEnvFrag where
  toEnvFrag = undefined

instance BindsEnv EnvFrag where
  toEnvFrag frag = frag
  {-# INLINE toEnvFrag #-}

instance BindsEnv (RolePiBinder r) where
  toEnvFrag (RolePiBinder b ty arr _) = toEnvFrag (PiBinder b ty arr)
  {-# INLINE toEnvFrag #-}

instance BindsEnv (RecSubstFrag Binding) where
  toEnvFrag frag = EnvFrag frag mempty

instance (BindsEnv b1, BindsEnv b2)
         => (BindsEnv (PairB b1 b2)) where
  toEnvFrag (PairB b1 b2) = do
    let bindings2 = toEnvFrag b2
    let ext = toExtEvidence bindings2
    withSubscopeDistinct ext do
      toEnvFrag b1 `catEnvFrags` bindings2

instance BindsEnv b => (BindsEnv (Nest b)) where
  toEnvFrag = nestToEnvFrag
  {-# INLINE toEnvFrag #-}

instance BindsEnv (LiftB e) where
  toEnvFrag (LiftB _) = EnvFrag emptyOutFrag mempty
  {-# INLINE toEnvFrag #-}

nestToEnvFragRec :: (BindsEnv b, Distinct l) => EnvFrag n h -> Nest b h l -> EnvFrag n l
nestToEnvFragRec f = \case
  Empty       -> f
  Nest b rest -> withSubscopeDistinct rest $ nestToEnvFragRec (f `catEnvFrags` toEnvFrag b) rest

nestToEnvFrag :: (BindsEnv b, Distinct l) => Nest b n l -> EnvFrag n l
nestToEnvFrag = nestToEnvFragRec emptyOutFrag
{-# NOINLINE [1] nestToEnvFrag #-}
-- The unsafeCoerceB is necessary for this rule to trigger for (>>=) of InplaceT.
-- Otherwise GHC core (on which the matching is performed) will include a coercion
-- that's impossible to match on in here.
{-# RULES
      "extendEnv * Empty"  forall env. extendEnv env (nestToEnvFrag (unsafeCoerceB Empty)) = env
  #-}

instance BindsEnv b => (BindsEnv (RNest b)) where
  toEnvFrag n = rnestToEnvFragRec n emptyOutFrag
  {-# INLINE toEnvFrag #-}

rnestToEnvFragRec :: (BindsEnv b, Distinct l) => RNest b n h -> EnvFrag h l -> EnvFrag n l
rnestToEnvFragRec n f = case n of
  REmpty       -> f
  RNest rest b -> withSubscopeDistinct f $ rnestToEnvFragRec rest (toEnvFrag b `catEnvFrags` f)

instance (BindsEnv b1, BindsEnv b2)
         => (BindsEnv (EitherB b1 b2)) where
  toEnvFrag (LeftB  b) = toEnvFrag b
  toEnvFrag (RightB b) = toEnvFrag b

instance BindsEnv UnitB where
  toEnvFrag UnitB = emptyOutFrag

instance ExtOutMap Env (Nest (Decl r)) where
  extendOutMap bindings emissions =
    bindings `extendOutMap` toEnvFrag emissions
  {-# INLINE extendOutMap #-}

instance ExtOutMap Env (RNest (Decl r)) where
  extendOutMap bindings emissions =
    bindings `extendOutMap` toEnvFrag emissions
  {-# INLINE extendOutMap #-}

instance ExtOutMap Env UnitB where
  extendOutMap bindings UnitB = bindings
  {-# INLINE extendOutMap #-}

-- === Monadic helpers ===

lookupEnv :: (Color c, EnvReader m) => Name c o -> m o (Binding c o)
lookupEnv v = withEnv $ flip lookupEnvPure v
{-# INLINE lookupEnv #-}

lookupAtomName :: EnvReader m => AtomName r n -> m n (AtomBinding r n)
lookupAtomName name = bindingToAtomBinding <$> lookupEnv name
{-# INLINE lookupAtomName #-}

lookupCustomRules :: EnvReader m => AtomName CoreIR n -> m n (Maybe (AtomRules n))
lookupCustomRules name = liftM fromMaybeE $ withEnv $
  toMaybeE . M.lookup name . customRulesMap . envCustomRules . topEnv
{-# INLINE lookupCustomRules #-}

lookupImpFun :: EnvReader m => ImpFunName n -> m n (ImpFunction n)
lookupImpFun name = lookupEnv name >>= \case ImpFunBinding f -> return f
{-# INLINE lookupImpFun #-}

lookupModule :: EnvReader m => ModuleName n -> m n (Module n)
lookupModule name = lookupEnv name >>= \case ModuleBinding m -> return m
{-# INLINE lookupModule #-}

lookupFunObjCode :: EnvReader m => FunObjCodeName n -> m n (FunObjCode, LinktimeNames n)
lookupFunObjCode name = lookupEnv name >>= \case FunObjCodeBinding obj m -> return (obj, m)
{-# INLINE lookupFunObjCode #-}

lookupDataDef :: EnvReader m => DataDefName n -> m n (DataDef n)
lookupDataDef name = lookupEnv name >>= \case DataDefBinding x -> return x
{-# INLINE lookupDataDef #-}

lookupClassDef :: EnvReader m => ClassName n -> m n (ClassDef n)
lookupClassDef name = lookupEnv name >>= \case ClassBinding x -> return x
{-# INLINE lookupClassDef #-}

lookupInstanceDef :: EnvReader m => InstanceName n -> m n (InstanceDef n)
lookupInstanceDef name = lookupEnv name >>= \case InstanceBinding x -> return x
{-# INLINE lookupInstanceDef #-}

lookupEffectDef :: EnvReader m => EffectName n -> m n (EffectDef n)
lookupEffectDef name = lookupEnv name >>= \case EffectBinding x -> return x
{-# INLINE lookupEffectDef #-}

lookupEffectOpDef :: EnvReader m => EffectOpName n -> m n (EffectOpDef n)
lookupEffectOpDef name = lookupEnv name >>= \case EffectOpBinding x -> return x
{-# INLINE lookupEffectOpDef #-}

lookupHandlerDef :: EnvReader m => HandlerName n -> m n (HandlerDef n)
lookupHandlerDef name = lookupEnv name >>= \case HandlerBinding x -> return x
{-# INLINE lookupHandlerDef #-}

lookupSourceMapPure :: SourceMap n -> SourceName -> [SourceNameDef n]
lookupSourceMapPure (SourceMap m) v = M.findWithDefault [] v m
{-# INLINE lookupSourceMapPure #-}

lookupSourceMap :: EnvReader m => SourceName -> m n (Maybe (UVar n))
lookupSourceMap sourceName = do
  sm <- withEnv $ envSourceMap . moduleEnv
  case lookupSourceMapPure sm sourceName of
    LocalVar x:_  -> return $ Just x
    [ModuleVar _ (Just x)] -> return $ Just x
    _   -> return Nothing

refreshBinders
  :: (EnvExtender m, BindsEnv b, RenameB b)
  => b n l
  -> (forall l'. DExt n l' => b n l' -> SubstFrag Name n l l' -> m l' a)
  -> m n a
refreshBinders b cont = refreshAbs (Abs b $ idSubstFrag b) cont
{-# INLINE refreshBinders #-}

withFreshBinder
  :: (Color c, EnvExtender m, ToBinding binding c)
  => NameHint -> binding n
  -> (forall l. DExt n l => NameBinder c n l -> m l a)
  -> m n a
withFreshBinder hint binding cont = do
  Abs b v <- freshNameM hint
  refreshAbs (Abs (b:>binding) v) \(b':>_) _ -> cont b'
{-# INLINE withFreshBinder #-}

withFreshBinders
  :: (Color c, EnvExtender m, ToBinding binding c)
  => [binding n]
  -> (forall l. DExt n l => Nest (BinderP c binding) n l -> [Name c l] -> m l a)
  -> m n a
withFreshBinders [] cont = do
  Distinct <- getDistinct
  cont Empty []
withFreshBinders (binding:rest) cont = do
  withFreshBinder noHint binding \b -> do
    ListE rest' <- sinkM $ ListE rest
    withFreshBinders rest' \bs vs ->
      cont (Nest (b :> binding) bs)
           (sink (binderName b) : vs)

piBinderAsBinder :: PiBinder r n l -> Binder r n l
piBinderAsBinder (PiBinder b ty _) = b:>ty

plainPiBinder :: Binder r n l -> PiBinder r n l
plainPiBinder (b:>ty) = PiBinder b ty PlainArrow

classPiBinder :: Binder r n l -> PiBinder r n l
classPiBinder (b:>ty) = PiBinder b ty ClassArrow

withAllowedEffects :: EnvExtender m => EffectRow n -> m n a -> m n a
withAllowedEffects effs cont =
  refreshAbs (Abs (EffectBinder effs) UnitE) \(EffectBinder _) UnitE ->
    cont

getLambdaDicts :: EnvReader m => m n [AtomName CoreIR n]
getLambdaDicts = do
  env <- withEnv moduleEnv
  return $ lambdaDicts $ envSynthCandidates env
{-# INLINE getLambdaDicts #-}

getInstanceDicts :: EnvReader m => ClassName n -> m n [InstanceName n]
getInstanceDicts name = do
  env <- withEnv moduleEnv
  return $ M.findWithDefault [] name $ instanceDicts $ envSynthCandidates env
{-# INLINE getInstanceDicts #-}

getAllowedEffects :: EnvReader m => m n (EffectRow n)
getAllowedEffects = withEnv $ allowedEffects . moduleEnv
{-# INLINE getAllowedEffects #-}

nonDepPiType :: ScopeReader m
             => Arrow -> Type r n -> EffectRow n -> Type r n -> m n (PiType r n)
nonDepPiType arr argTy eff resultTy =
  toConstAbs (PairE eff resultTy) >>= \case
    Abs b (PairE eff' resultTy') ->
      return $ PiType (PiBinder b argTy arr) eff' resultTy'

nonDepTabPiType :: ScopeReader m => IxType r n -> Type r n -> m n (TabPiType r n)
nonDepTabPiType argTy resultTy =
  toConstAbs resultTy >>= \case
    Abs b resultTy' -> return $ TabPiType (b:>argTy) resultTy'

considerNonDepPiType :: PiType r n -> Maybe (Arrow, Type r n, EffectRow n, Type r n)
considerNonDepPiType (PiType (PiBinder b argTy arr) eff resultTy) = do
  HoistSuccess (PairE eff' resultTy') <- return $ hoist b (PairE eff resultTy)
  return (arr, argTy, eff', resultTy')

fromNonDepPiType :: (ScopeReader m, MonadFail1 m)
                 => Arrow -> Type r n -> m n (Type r n, EffectRow n, Type r n)
fromNonDepPiType arr ty = do
  Pi (PiType (PiBinder b argTy arr') eff resultTy) <- return ty
  unless (arr == arr') $ fail "arrow type mismatch"
  HoistSuccess (PairE eff' resultTy') <- return $ hoist b (PairE eff resultTy)
  return $ (argTy, eff', resultTy')

fromNonDepTabType :: (ScopeReader m, MonadFail1 m) => Type r n -> m n (IxType r n, Type r n)
fromNonDepTabType ty = do
  TabPi (TabPiType (b :> ixTy) resultTy) <- return ty
  HoistSuccess resultTy' <- return $ hoist b resultTy
  return (ixTy, resultTy')

nonDepDataConTys :: DataConDef r n -> Maybe [Type r n]
nonDepDataConTys (DataConDef _ repTy idxs) =
  case repTy of
    ProdTy tys | length idxs == length tys -> Just tys
    _ -> Nothing

infixr 1 ?-->
infixr 1 -->
infixr 1 --@

(?-->) :: HasCore r => ScopeReader m => Type r n -> Type r n -> m n (Type r n)
a ?--> b = Pi <$> nonDepPiType ImplicitArrow a Pure b

(-->) :: HasCore r => ScopeReader m => Type r n -> Type r n -> m n (Type r n)
a --> b = Pi <$> nonDepPiType PlainArrow a Pure b

(--@) :: ScopeReader m => HasCore r => Type r n -> Type r n -> m n (Type r n)
a --@ b = Pi <$> nonDepPiType LinArrow a Pure b

(==>) :: ScopeReader m => IxType r n -> Type r n -> m n (Type r n)
a ==> b = TabPi <$> nonDepTabPiType a b

-- These `fromNary` functions traverse a chain of unary structures (LamExpr,
-- TabLamExpr, PiType, respectively) up to the given maxDepth, and return the
-- discovered binders packed as the nary structure (NaryLamExpr or NaryPiType),
-- including a count of how many binders there were.
-- - If there are no binders, return Nothing.
-- - If there are more than maxDepth binders, only return maxDepth of them, and
--   leave the others in the unary structure.
-- - The `exact` versions only succeed if at least maxDepth binders were
--   present, in which case exactly maxDepth binders are packed into the nary
--   structure.  Excess binders, if any, are still left in the unary structures.
blockEffects :: Block r n -> EffectRow n
blockEffects (Block blockAnn _ _) = case blockAnn of
  NoBlockAnn -> Pure
  BlockAnn _ eff -> eff

lamExprToAtom :: HasCore r => LamExpr r n -> Arrow -> Maybe (EffAbs r n) -> Atom r n
lamExprToAtom lam@(UnaryLamExpr b block) arr maybeEffAbs = Lam lam arr effAbs
  where effAbs = case maybeEffAbs of
          Just e -> e
          Nothing -> Abs b $ blockEffects block
lamExprToAtom _ _ _ = error "not a unary lambda expression"

naryLamExprToAtom :: HasCore r => LamExpr r n -> [Arrow] -> Atom r n
naryLamExprToAtom lam@(LamExpr (Nest b bs) body) (arr:arrs) = case bs of
  Empty -> lamExprToAtom lam arr Nothing
  _ -> do
    let rest = naryLamExprToAtom (LamExpr bs body) arrs
    Lam (UnaryLamExpr b (AtomicBlock rest)) arr (Abs b Pure)
naryLamExprToAtom _ _ = error "unexpected nullary lambda expression"

-- first argument is the number of args expected
fromNaryLamExact :: Int -> Atom r n -> Maybe (LamExpr r n)
fromNaryLamExact exactDepth _ | exactDepth <= 0 = error "expected positive number of args"
fromNaryLamExact exactDepth lam = do
  (realDepth, naryLam) <- fromNaryLam exactDepth lam
  guard $ realDepth == exactDepth
  return naryLam

fromNaryLam :: Int -> Atom r n -> Maybe (Int, LamExpr r n)
fromNaryLam maxDepth | maxDepth <= 0 = error "expected positive number of args"
fromNaryLam maxDepth = \case
  Lam (LamExpr (Nest b Empty) body) _ (Abs _ effs) ->
    extend <|> (Just (1, LamExpr (Nest b Empty) body))
    where
      extend = case (effs, body) of
        (Pure, AtomicBlock lam) | maxDepth > 1 -> do
          (d, LamExpr bs body2) <- fromNaryLam (maxDepth - 1) lam
          return $ (d + 1, LamExpr (Nest b bs) body2)
        _ -> Nothing
  _ -> Nothing

fromNaryTabLam :: Int -> Atom r n -> Maybe (Int, LamExpr r n)
fromNaryTabLam maxDepth | maxDepth <= 0 = error "expected positive number of args"
fromNaryTabLam maxDepth = \case
  (TabLam (TabLamExpr (b:>IxType ty _) body)) ->
    extend <|> (Just $ (1, LamExpr (Nest (b:>ty) Empty) body))
    where
      extend = case body of
        AtomicBlock lam | maxDepth > 1 -> do
          (d, LamExpr (Nest b2 bs2) body2) <- fromNaryTabLam (maxDepth - 1) lam
          return $ (d + 1, LamExpr (Nest (b:>ty) (Nest b2 bs2)) body2)
        _ -> Nothing
  _ -> Nothing

-- first argument is the number of args expected
fromNaryTabLamExact :: Int -> Atom r n -> Maybe (LamExpr r n)
fromNaryTabLamExact exactDepth _ | exactDepth <= 0 = error "expected positive number of args"
fromNaryTabLamExact exactDepth lam = do
  (realDepth, naryLam) <- fromNaryTabLam exactDepth lam
  guard $ realDepth == exactDepth
  return naryLam

fromNaryForExpr :: Int -> Expr r n -> Maybe (Int, LamExpr r n)
fromNaryForExpr maxDepth | maxDepth <= 0 = error "expected positive number of args"
fromNaryForExpr maxDepth = \case
  Hof (For _ _ (UnaryLamExpr b body)) ->
    extend <|> (Just $ (1, LamExpr (Nest b Empty) body))
    where
      extend = do
        expr <- exprBlock body
        guard $ maxDepth > 1
        (d, LamExpr bs body2) <- fromNaryForExpr (maxDepth - 1) expr
        return (d + 1, LamExpr (Nest b bs) body2)
  _ -> Nothing

-- first argument is the number of args expected
fromNaryPiType :: Int -> Type r n -> Maybe (NaryPiType r n)
fromNaryPiType n _ | n <= 0 = error "expected positive number of args"
fromNaryPiType 1 ty = case ty of
  Pi (PiType b effs resultTy) -> Just $ NaryPiType (Nest b Empty) effs resultTy
  _ -> Nothing
fromNaryPiType n (Pi (PiType b1 Pure piTy)) = do
  NaryPiType (Nest b2 bs) effs resultTy <- fromNaryPiType (n-1) piTy
  Just $ NaryPiType (Nest b1 (Nest b2 bs)) effs resultTy
fromNaryPiType _ _ = Nothing

mkConsListTy :: [Type r n] -> Type r n
mkConsListTy = foldr PairTy UnitTy

mkConsList :: [Atom r n] -> Atom r n
mkConsList = foldr PairVal UnitVal

fromConsListTy :: Fallible m => Type r n -> m [Type r n]
fromConsListTy ty = case ty of
  UnitTy         -> return []
  PairTy t rest -> (t:) <$> fromConsListTy rest
  _              -> throw CompilerErr $ "Not a pair or unit: " ++ show ty

-- ((...((ans & x{n}) & x{n-1})... & x2) & x1) -> (ans, [x1, ..., x{n}])
fromLeftLeaningConsListTy :: Fallible m => Int -> Type r n -> m (Type r n, [Type r n])
fromLeftLeaningConsListTy depth initTy = go depth initTy []
  where
    go 0        ty xs = return (ty, reverse xs)
    go remDepth ty xs = case ty of
      PairTy lt rt -> go (remDepth - 1) lt (rt : xs)
      _ -> throw CompilerErr $ "Not a pair: " ++ show xs

fromConsList :: Fallible m => Atom r n -> m [Atom r n]
fromConsList xs = case xs of
  UnitVal        -> return []
  PairVal x rest -> (x:) <$> fromConsList rest
  _              -> throw CompilerErr $ "Not a pair or unit: " ++ show xs

type BundleDesc = Int  -- length

bundleFold :: a -> (a -> a -> a) -> [a] -> (a, BundleDesc)
bundleFold emptyVal pair els = case els of
  []  -> (emptyVal, 0)
  [e] -> (e, 1)
  h:t -> (pair h tb, td + 1)
    where (tb, td) = bundleFold emptyVal pair t

mkBundleTy :: [Type r n] -> (Type r n, BundleDesc)
mkBundleTy = bundleFold UnitTy PairTy

mkBundle :: [Atom r n] -> (Atom r n, BundleDesc)
mkBundle = bundleFold UnitVal PairVal

trySelectBranch :: Atom r n -> Maybe (Int, Atom r n)
trySelectBranch e = case e of
  SumVal _ i value -> Just (i, value)
  Con (SumAsProd _ (TagRepVal tag) vals) -> Just (i, vals !! i)
    where i = fromIntegral tag
  NewtypeCon con e' | isSumCon con -> trySelectBranch e'
  _ -> Nothing

freeAtomVarsList :: HoistableE e => e n -> [Name AtomNameC n]
freeAtomVarsList = freeVarsList

freshNameM :: (Color c, EnvReader m)
           => NameHint -> m n (Abs (NameBinder c) (Name c) n)
freshNameM hint = do
  scope    <- toScope <$> unsafeGetEnv
  Distinct <- getDistinct
  return $ withFresh hint scope \b -> Abs b (binderName b)
{-# INLINE freshNameM #-}

type AtomNameMap = NameMap AtomNameC
