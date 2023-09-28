-- Copyright 2022 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module Subst where

import Control.Applicative
import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.State.Strict
import Data.Functor ((<&>))

import Name
import MTL1
import IRVariants
import Types.Core
import Types.Imp
import Core
import QueryTypePure
import qualified RawName as R
import Err
import PPrint

-- === SubstReader class ===

class (SinkableV v, Monad2 m) => SubstReader (v::V) (m::MonadKind2) | m -> v where
   getSubst :: m i o (Subst v i o)
   withSubst :: Subst v i' o -> m i' o a -> m i o a

lookupSubstM :: (Color c, SubstReader v m) => Name c i -> m i o (v c o)
lookupSubstM name = (!name) <$> getSubst

dropSubst :: (SubstReader v m, FromName v) => m o o a -> m i o a
dropSubst cont = withSubst idSubst cont
{-# INLINE dropSubst #-}

withVoidSubst :: (SubstReader v m, FromName v) => m VoidS o a -> m i o a
withVoidSubst cont = withSubst (newSubst absurdNameFunction) cont
{-# INLINE withVoidSubst #-}

extendSubst :: SubstReader v m => SubstFrag v i i' o -> m i' o a -> m i o a
extendSubst frag cont = do
  env <- (<>>frag) <$> getSubst
  withSubst env cont
{-# INLINE extendSubst #-}

-- XXX: this only (monadically) visits each name once, even if a name has
-- multiple occurrences. So don't use it to count occurrences or anything like
-- that! It's not deliberate. It's just an accident of the implementation, where
-- we gather the (de-duplicated) free names and then traverse them. At some
-- point we may add a monadic traversal to `Subst{E,B}`, which would actually
-- visit each occurrence.
traverseNames
  :: forall v e m i o.
     (SubstE v e, HoistableE e, SinkableE e, FromName v, EnvReader m)
  => (forall c. Color c => Name c i -> m o (v c o))
  -> e i -> m o (e o)
traverseNames f e = do
  let vs = freeVarsE e
  m <- flip R.traverseWithKey (fromNameSet vs) \rawName (SubstItem d c _) ->
    interpretColor c \(ColorProxy :: ColorProxy c) -> do
      v' <- f (UnsafeMakeName rawName :: Name c i)
      return $ SubstItem d c (unsafeCoerceVC v')
  fmapNamesM (applyTraversed m) e
{-# INLINE traverseNames #-}

applyTraversed :: FromName v
               => RawNameMap (SubstItem v n) -> Name c i -> v c n
applyTraversed m = \((UnsafeMakeName v) :: Name c i) -> case R.lookup v m of
    Just item -> unsafeFromSubstItem item
    Nothing -> fromName $ (UnsafeMakeName v :: Name c o)

fmapNames :: (SubstE v e, Distinct o)
          => Env o -> (forall c. Color c => Name c i -> v c o) -> e i -> e o
fmapNames env f e = substE (env, newSubst f) e
{-# INLINE fmapNames #-}

fmapNamesM :: (SubstE v e, SinkableE e, EnvReader m)
          => (forall c. Color c => Name c i -> v c o)
          -> e i -> m o (e o)
fmapNamesM f e = do
  env <- unsafeGetEnv
  Distinct <- getDistinct
  return $ substE (env, newSubst f) e
{-# INLINE fmapNamesM #-}

-- === type classes for traversing names ===

class FromName v => SubstE (v::V) (e::E) where
  -- TODO: can't make an alias for these constraints because of impredicativity
  substE :: Distinct o => (Env o, Subst v i o) -> e i -> e o

  default substE :: (GenericE e, SubstE v (RepE e), Distinct o)
                 => (Env o, Subst v i o) -> e i -> e o
  substE env e = toE $ substE env (fromE e)

class (FromName v, SinkableB b) => SubstB (v::V) (b::B) where
  substB
    :: Distinct o
    => (Env o, Subst v i o)
    -> b i i'
    -> (forall o'. Distinct o' => (Env o', Subst v i' o') -> b o o' -> a)
    -> a

  default substB
    :: (GenericB b, SubstB v (RepB b))
    => Distinct o
    => (Env o, Subst v i o)
    -> b i i'
    -> (forall o'. Distinct o' => (Env o', Subst v i' o') -> b o o' -> a)
    -> a
  substB env b cont =
    substB env (fromB b) \env' b' ->
      cont env' $ toB b'

class ( FromName substVal, SinkableV v
      , forall c. Color c => SubstE substVal (v c))
      => SubstV (substVal::V) (v::V)

instance ( forall r. IRRep r => SinkableE (atom r)
         , forall r. IRRep r => RenameE (atom r)) => RenameV (SubstVal atom)

instance (Color c, forall r. IRRep r => RenameE (atom r)) => RenameE (SubstVal atom c) where
  renameE (_, env) (Rename name) = Rename $ env ! name
  renameE (scope, env) (SubstVal atom) = SubstVal $ renameE (scope, env) atom

substM :: (SubstReader v m, EnvReader2 m, SinkableE e, SubstE v e, FromName v)
       => e i -> m i o (e o)
substM e = do
  subst <- getSubst
  substM' subst e
{-# INLINE substM #-}

substM' :: (EnvReader m, SinkableE e, SubstE v e, FromName v)
       => Subst v i o -> e i -> m o (e o)
substM' subst e = do
  case tryApplyIdentitySubst subst e of
    Just e' -> return $ e'
    Nothing -> do
      env <- unsafeGetEnv
      Distinct <- getDistinct
      return $ fmapNames env (subst!) e
{-# INLINE substM' #-}

fromConstAbs :: (BindsNames b, HoistableE e) => Abs b e n -> HoistExcept (e n)
fromConstAbs (Abs b e) = hoist b e

-- === rename-only substitutions ===

extendRenamer :: (SubstReader v m, FromName v) => SubstFrag Name i i' o -> m i' o r -> m i o r
extendRenamer frag = extendSubst (fmapSubstFrag (const fromName) frag)

applyRename
  :: (ScopeReader m, RenameE e, SinkableE e)
  => Ext h o => SubstFrag Name h i o -> e i -> m o (e o)
applyRename substFrag x = do
  Distinct <- getDistinct
  scope <- unsafeGetScope
  let subst = sink idSubst <>> substFrag
  case tryApplyIdentitySubst subst x of
    Just x' -> return x'
    Nothing -> return $ renameE (scope, newSubst (subst!)) x
{-# INLINE applyRename #-}

renameM
  :: (SubstReader Name m, ScopeReader2 m, SinkableE e, RenameE e)
  => e i -> m i o (e o)
renameM e = do
  env <- getSubst
  case tryApplyIdentitySubst env e of
    Just e' -> return $ e'
    Nothing -> do
      WithScope scope env' <- addScope env
      sinkM $ renameE (scope, newSubst (env'!)) e
{-# INLINE renameM #-}

renameBinders
  :: (EnvExtender2 m, SubstReader Name m, RenameB b, BindsEnv b)
  => b i i'
  -> (forall o'. DExt o o' => b o o' -> m i' o' a)
  -> m i o a
renameBinders b cont = do
  ab <- renameM $ Abs b $ idSubstFrag b
  refreshAbs ab \b' subst -> extendSubst subst $ cont b'
{-# INLINE renameBinders #-}

-- === various convenience utilities ===

applySubstFragPure :: (SubstE v e, SinkableE e, SinkableV v, FromName v, Ext h o, Distinct o)
                   => Env o -> SubstFrag v h i o -> e i -> e o
applySubstFragPure env substFrag x = do
  let fullSubst = sink idSubst <>> substFrag
  applySubstPure env fullSubst x

applySubstPure :: (SubstE v e, SinkableE e, SinkableV v, FromName v, Distinct o)
               => Env o -> Subst v i o -> e i -> e o
applySubstPure env subst x = do
  case tryApplyIdentitySubst subst x of
    Just x' -> x'
    Nothing -> fmapNames env (subst !) x

applySubst :: (EnvReader m, SubstE v e, SinkableE e, SinkableV v, FromName v)
           => Ext h o
           => SubstFrag v h i o -> e i -> m o (e o)
applySubst substFrag x = do
  Distinct <- getDistinct
  env <- unsafeGetEnv
  return $ applySubstFragPure env substFrag x
{-# INLINE applySubst #-}

applyAbs :: ( SinkableV v, SinkableE e
            , FromName v, EnvReader m, BindsOneName b c, SubstE v e)
         => Abs b e n -> v c n -> m n (e n)
applyAbs (Abs b body) x = applySubst (b@>x) body
{-# INLINE applyAbs #-}

applyNaryAbs :: ( SinkableV v, FromName v, EnvReader m, BindsNameList b c, SubstE v e
                , SubstB v b, SinkableE e)
             => Abs b e n -> [v c n] -> m n (e n)
applyNaryAbs (Abs bs body) xs = applySubst (bs @@> xs) body
{-# INLINE applyNaryAbs #-}

substBinders
  :: ( SinkableV v, SubstV v v, EnvExtender2 m, FromName v
     , SubstReader v m, SubstB v b, RenameV v, RenameB b, BindsEnv b)
  => b i i'
  -> (forall o'. DExt o o' => b o o' -> m i' o' a)
  -> m i o a
substBinders b cont = do
  substBindersFrag b \subst b' -> extendSubst subst $ cont b'
{-# INLINE substBinders #-}

substBindersFrag
  :: ( SinkableV v, SubstV v v, EnvExtender2 m, FromName v
     , SubstReader v m, SubstB v b, RenameV v, RenameB b, BindsEnv b)
  => b i i'
  -> (forall o'. DExt o o' => SubstFrag v i i' o' -> b o o' -> m i o' a)
  -> m i o a
substBindersFrag b cont = do
  ab <- substM $ Abs b $ idSubstFrag b
  refreshAbs ab \b' subst -> cont subst b'
{-# INLINE substBindersFrag #-}

-- === atom subst vals ===

data SubstVal (atom::IR->E) (c::C) (n::S) where
  SubstVal :: IRRep r => atom r n -> SubstVal atom (AtomNameC r) n
  Rename   :: Name c n -> SubstVal atom c n
type AtomSubstVal = SubstVal Atom

type family IsAtomName (c::C) where
  IsAtomName (AtomNameC r) = True
  IsAtomName _             = False

instance (Color c, IsAtomName c ~ False) => SubstE (SubstVal atom) (Name c) where
  substE (_, env) v = case env ! v of Rename v' -> v'

instance FromName (SubstVal atom) where
  fromName = Rename
  {-# INLINE fromName #-}

class ToSubstVal (v::V) (atom::IR->E) where
  toSubstVal :: v c n -> SubstVal atom c n

instance ToSubstVal (Name::V) (atom::IR->E) where
  toSubstVal = Rename

instance ToSubstVal (SubstVal atom) atom where
  toSubstVal = id

type AtomSubstReader v m = (SubstReader v m, FromName v, ToSubstVal v Atom)

atomSubstM :: (AtomSubstReader v m, EnvReader2 m, SinkableE e, SubstE AtomSubstVal e)
           => e i -> m i o (e o)
atomSubstM e = do
  subst <- getSubst
  let subst' = asAtomSubstValSubst subst
  substM' subst' e

asAtomSubstValSubst :: ToSubstVal v Atom => Subst v i o -> Subst AtomSubstVal i o
asAtomSubstValSubst subst = newSubst \v -> toSubstVal (subst ! v)

-- === SubstReaderT transformer ===

newtype SubstReaderT (v::V) (m::MonadKind1) (i::S) (o::S) (a:: *) =
  SubstReaderT' { runSubstReaderT' :: ReaderT (Subst v i o) (m o) a }

pattern SubstReaderT :: (Subst v i o -> m o a) -> SubstReaderT v m i o a
pattern SubstReaderT f = SubstReaderT' (ReaderT f)

runSubstReaderT :: Subst v i o -> SubstReaderT v m i o a -> m o a
runSubstReaderT env m = runReaderT (runSubstReaderT' m) env
{-# INLINE runSubstReaderT #-}

instance (forall n. Functor (m n)) => Functor (SubstReaderT v m i o) where
  fmap f (SubstReaderT' m) = SubstReaderT' $ fmap f m
  {-# INLINE fmap #-}

instance Monad1 m => Applicative (SubstReaderT v m i o) where
  pure   = SubstReaderT' . pure
  {-# INLINE pure #-}
  liftA2 f (SubstReaderT' x) (SubstReaderT' y) = SubstReaderT' $ liftA2 f x y
  {-# INLINE liftA2 #-}
  (SubstReaderT' f) <*> (SubstReaderT' x) = SubstReaderT' $ f <*> x
  {-# INLINE (<*>) #-}

instance (forall n. Monad (m n)) => Monad (SubstReaderT v m i o) where
  return = SubstReaderT' . return
  {-# INLINE return #-}
  (SubstReaderT' m) >>= f = SubstReaderT' (m >>= (runSubstReaderT' . f))
  {-# INLINE (>>=) #-}

deriving instance (Monad1 m, MonadFail1   m) => MonadFail   (SubstReaderT v m i o)
deriving instance (Monad1 m, Alternative1 m) => Alternative (SubstReaderT v m i o)
deriving instance Fallible1  m => Fallible  (SubstReaderT v m i o)
deriving instance Catchable1 m => Catchable (SubstReaderT v m i o)
deriving instance CtxReader1 m => CtxReader (SubstReaderT v m i o)

type ScopedSubstReader (v::V) = SubstReaderT v (ScopeReaderT Identity) :: MonadKind2

liftSubstReaderT :: Monad1 m => m o a -> SubstReaderT v m i o a
liftSubstReaderT m = SubstReaderT' $ lift m
{-# INLINE liftSubstReaderT #-}

runScopedSubstReader :: Distinct o => Scope o -> Subst v i o
                   -> ScopedSubstReader v i o a -> a
runScopedSubstReader scope env m =
  runIdentity $ runScopeReaderT scope $ runSubstReaderT env m
{-# INLINE runScopedSubstReader #-}

withSubstReaderT :: FromName v => SubstReaderT v m n n a -> m n a
withSubstReaderT = runSubstReaderT idSubst
{-# INLINE withSubstReaderT #-}

instance (SinkableV v, Monad1 m) => SubstReader v (SubstReaderT v m) where
  getSubst = SubstReaderT' ask
  {-# INLINE getSubst #-}
  withSubst env (SubstReaderT' cont) = SubstReaderT' $ withReaderT (const env) cont
  {-# INLINE withSubst #-}

instance (SinkableV v, ScopeReader m) => ScopeReader (SubstReaderT v m i) where
  unsafeGetScope = liftSubstReaderT unsafeGetScope
  {-# INLINE unsafeGetScope #-}
  getDistinct = liftSubstReaderT getDistinct
  {-# INLINE getDistinct #-}

instance (SinkableV v, EnvReader m) => EnvReader (SubstReaderT v m i) where
  unsafeGetEnv = liftSubstReaderT unsafeGetEnv
  {-# INLINE unsafeGetEnv #-}

instance (SinkableV v, ScopeReader m, EnvExtender m)
         => EnvExtender (SubstReaderT v m i) where
  refreshAbs ab cont = SubstReaderT \subst ->
    refreshAbs ab \b e -> do
      subst' <- sinkM subst
      let SubstReaderT cont' = cont b e
      cont' subst'
  {-# INLINE refreshAbs #-}

instance MonadDiffState1 m s d => MonadDiffState1 (SubstReaderT v m i) s d where
  withDiffState s m =
    SubstReaderT \subst -> do
      withDiffState s $ runSubstReaderT subst m

  updateDiffStateM d = liftSubstReaderT $ updateDiffStateM d
  getDiffState = liftSubstReaderT getDiffState

type SubstEnvReaderM v = SubstReaderT v EnvReaderM :: MonadKind2

liftSubstEnvReaderM
  :: forall v m n a. (EnvReader m, FromName v)
  => SubstEnvReaderM v n n a
  -> m n a
liftSubstEnvReaderM cont = liftEnvReaderM $ runSubstReaderT idSubst $ cont
{-# INLINE liftSubstEnvReaderM #-}

instance (SinkableV v, ScopeReader m, ScopeExtender m)
         => ScopeExtender (SubstReaderT v m i) where
  refreshAbsScope ab cont = SubstReaderT \env ->
    refreshAbsScope ab \b e -> do
      let SubstReaderT cont' = cont b e
      env' <- sinkM env
      cont' env'

instance (SinkableV v, MonadIO1 m) => MonadIO (SubstReaderT v m i o) where
  liftIO m = liftSubstReaderT $ liftIO m
  {-# INLINE liftIO #-}

instance (Monad1 m, MonadState (s o) (m o)) => MonadState (s o) (SubstReaderT v m i o) where
  state = liftSubstReaderT . state
  {-# INLINE state #-}

instance (Monad1 m, MonadReader (r o) (m o)) => MonadReader (r o) (SubstReaderT v m i o) where
  ask = SubstReaderT $ const ask
  {-# INLINE ask #-}
  local r (SubstReaderT' (ReaderT f)) = SubstReaderT \env -> local r $ f env
  {-# INLINE local #-}

-- === instances ===

instance (forall r. IRRep r => SinkableE (atom r)) => SinkableV (SubstVal atom)
instance (forall r. IRRep r => SinkableE (atom r)) => SinkableE (SubstVal atom c) where
  sinkingProofE fresh substVal = case substVal of
    Rename name  -> Rename   $ sinkingProofE fresh name
    SubstVal val -> SubstVal $ sinkingProofE fresh val

instance (SubstB v b, SubstE v e) => SubstE v (Abs b e) where
  substE env (Abs b body) = do
    substB env b \env' b' -> Abs b' $ substE env' body

instance ( BindsNames b1, SubstB v b1
         , BindsNames b2, SubstB v b2
         , SinkableV v, FromName v)
         => SubstB v (PairB b1 b2) where
  substB env (PairB b1 b2) cont =
    substB env b1 \env' b1' ->
      substB env' b2 \env'' b2' ->
        cont env'' $ PairB b1' b2'

instance (SinkableE e, SubstE v e) => SubstB v (LiftB e) where
  substB env@(_, subst) (LiftB e) cont = case tryApplyIdentitySubst subst e of
    Just e' -> cont env $ LiftB e'
    Nothing -> cont env $ LiftB $ substE env e
  {-# INLINE substB #-}

instance (SubstB v b1, SubstB v b2) => SubstB v (EitherB b1 b2) where
  substB env (LeftB b) cont =
    substB env b \env' b' ->
      cont env' $ LeftB b'
  substB env (RightB b) cont =
    substB env b \env' b' ->
      cont env' $ RightB b'

instance (Color c, SinkableE ann, SubstE v ann, SinkableV v, ToBinding ann c)
         => SubstB v (BinderP c ann) where
  substB (env, subst) (b:>ty) cont = do
    let ty' = substE (env, subst) ty
    withFresh (getNameHint b) (toScope env) \bRaw -> do
      let b' = bRaw:>ty'
      let env' = env `extendOutMap` toEnvFrag b'
      let UnsafeMakeName bn  = binderName b
      let UnsafeMakeName bn' = binderName b'
      let subst' = case subst of
                   UnsafeMakeIdentitySubst | bn == bn' -> UnsafeMakeIdentitySubst
                   _ -> sink subst <>> b @> (fromName $ binderName b')
      cont (env', subst') b'

instance (BindsNames b, SubstB v b, SinkableV v)
         => SubstB v (Nest b) where
  substB env (Nest b bs) cont =
    substB env b \env' b' ->
      substB env' bs \env'' bs' ->
        cont env'' $ Nest b' bs'
  substB env Empty cont = cont env Empty

instance FromName v => SubstE v UnitE where
  substE _ UnitE = UnitE

instance SubstB v b => SubstB v (WithAttrB a b) where
  substB env (WithAttrB x b) cont =
    substB env b \env' b' -> cont env' $ WithAttrB x b'

instance (Traversable f, SubstE v e) => SubstE v (ComposeE f e) where
  substE env (ComposeE xs) = ComposeE $ fmap (substE env) xs

instance (SubstE v e1, SubstE v e2) => SubstE v (PairE e1 e2) where
  substE env (PairE x y) = PairE (substE env x) (substE env y)

instance (SubstE v e1, SubstE v e2) => SubstE v (EitherE e1 e2) where
  substE env (LeftE  x) = LeftE  $ substE env x
  substE env (RightE x) = RightE $ substE env x

instance FromName v => SubstE v VoidE where
  substE _ _ = error "impossible"

instance FromName v => SubstE v (LiftE a) where
  substE _ (LiftE x) = LiftE x

instance SubstE v e => SubstE v (ListE e) where
  substE env (ListE xs) = ListE $ map (substE env) xs

instance SubstE v e => SubstE v (RListE e) where
  substE env (RListE xs) = RListE $ fmap (substE env) xs

instance SubstE v e => SubstE v (NonEmptyListE e) where
  substE env (NonEmptyListE xs) = NonEmptyListE $ fmap (substE env) xs

instance (p ~ True => SubstE v e, FromName v) => SubstE v (WhenE p e) where
  substE (scope, subst) (WhenE e) = WhenE $ substE (scope, subst) e

instance (r ~ r' => SubstE v e, FromName v) => SubstE v (WhenIRE r r' e) where
  substE (scope, subst) (WhenIRE e) = WhenIRE $ substE (scope, subst) e

instance SubstV substVal v => SubstE substVal (SubstFrag v i i') where
   substE env frag = fmapSubstFrag (\_ val -> substE env val) frag

instance SubstV substVal v => SubstE substVal (Subst v i) where
  substE env = \case
    Subst f frag -> Subst (\n -> substE env (f n)) $ substE env frag
    UnsafeMakeIdentitySubst
      -> Subst (\n -> substE env (fromName $ unsafeCoerceE n)) emptyInFrag

instance (SubstE v e0, SubstE v e1, SubstE v e2,
          SubstE v e3, SubstE v e4, SubstE v e5,
          SubstE v e6, SubstE v e7)
            => SubstE v (EitherE8 e0 e1 e2 e3 e4 e5 e6 e7) where
  substE env = \case
    Case0 e -> Case0 $ substE env e
    Case1 e -> Case1 $ substE env e
    Case2 e -> Case2 $ substE env e
    Case3 e -> Case3 $ substE env e
    Case4 e -> Case4 $ substE env e
    Case5 e -> Case5 $ substE env e
    Case6 e -> Case6 $ substE env e
    Case7 e -> Case7 $ substE env e
  {-# INLINE substE #-}

toAtomVar :: (EnvReader m,  IRRep r) => AtomName r n -> m n (AtomVar r n)
toAtomVar v = do
  ty <- getType <$> lookupAtomName v
  return $ AtomVar v ty

bindersToVars :: (EnvReader m,  IRRep r) => Nest (Binder r) n' n -> m n [AtomVar r n]
bindersToVars bs = do
  withExtEvidence bs do
    Distinct <- getDistinct
    mapM toAtomVar $ nestToNames bs

bindersToAtoms :: (EnvReader m,  IRRep r) => Nest (Binder r) n' n -> m n [Atom r n]
bindersToAtoms bs = liftM (Var <$>) $ bindersToVars bs

newtype SubstVisitor i o a = SubstVisitor { runSubstVisitor :: Reader (Env o, Subst AtomSubstVal i o) a }
        deriving (Functor, Applicative, Monad, MonadReader (Env o, Subst AtomSubstVal i o))

substV :: (Distinct o, SubstE AtomSubstVal e) => e i -> SubstVisitor i o (e o)
substV x = ask <&> \env -> substE env x

instance Distinct o => NonAtomRenamer (SubstVisitor i o) i o where
  renameN = substV

instance (Distinct o, IRRep r) => Visitor (SubstVisitor i o) r i o where
  visitType = substV
  visitAtom = substV
  visitLam  = substV
  visitPi   = substV

instance Color c => SubstE AtomSubstVal (AtomSubstVal c) where
  substE (_, env) (Rename name) = env ! name
  substE env (SubstVal val) = SubstVal $ substE env val

instance SubstV (SubstVal Atom) (SubstVal Atom) where

instance IRRep r => SubstE AtomSubstVal (Atom r) where
  substE es@(env, subst) = \case
    Var (AtomVar v ty) -> case subst!v of
      Rename v' -> Var $ AtomVar v' (substE es ty)
      SubstVal x -> x
    SimpInCore x   -> SimpInCore (substE es x)
    atom -> runReader (runSubstVisitor $ visitAtomPartial atom) es

instance IRRep r => SubstE AtomSubstVal (Type r) where
  substE es@(env, subst) = \case
    ty -> runReader (runSubstVisitor $ visitTypePartial ty) es

instance SubstE AtomSubstVal SimpInCore

instance IRRep r => SubstE AtomSubstVal (EffectRow r) where
  substE env (EffectRow effs tailVar) = do
    let effs' = eSetFromList $ map (substE env) (eSetToList effs)
    let tailEffRow = case tailVar of
          NoTail -> EffectRow mempty NoTail
          EffectRowTail (AtomVar v _) -> case snd env ! v of
            Rename        v'  -> do
              let v'' = runEnvReaderM (fst env) $ toAtomVar v'
              EffectRow mempty (EffectRowTail v'')
            SubstVal (Var v') -> EffectRow mempty (EffectRowTail v')
            SubstVal (Eff r)  -> r
            _ -> error "Not a valid effect substitution"
    extendEffRow effs' tailEffRow

instance IRRep r => SubstE AtomSubstVal (Effect r)

instance SubstE AtomSubstVal SpecializationSpec where
  substE env (AppSpecialization (AtomVar f _) ab) = do
    let f' = case snd env ! f of
               Rename v -> runEnvReaderM (fst env) $ toAtomVar v
               SubstVal (Var v) -> v
               _ -> error "bad substitution"
    AppSpecialization f' (substE env ab)

instance SubstE AtomSubstVal EffectDef
instance SubstE AtomSubstVal EffectOpType
instance SubstE AtomSubstVal IExpr
instance IRRep r => SubstE AtomSubstVal (RepVal r)
instance SubstE AtomSubstVal TyConParams
instance SubstE AtomSubstVal DataConDef
instance IRRep r => SubstE AtomSubstVal (BaseMonoid r)
instance IRRep r => SubstE AtomSubstVal (DAMOp r)
instance IRRep r => SubstE AtomSubstVal (TypedHof r)
instance IRRep r => SubstE AtomSubstVal (Hof r)
instance IRRep r => SubstE AtomSubstVal (TC r)
instance IRRep r => SubstE AtomSubstVal (Con r)
instance IRRep r => SubstE AtomSubstVal (MiscOp r)
instance IRRep r => SubstE AtomSubstVal (VectorOp r)
instance IRRep r => SubstE AtomSubstVal (MemOp r)
instance IRRep r => SubstE AtomSubstVal (PrimOp r)
instance IRRep r => SubstE AtomSubstVal (RefOp r)
instance IRRep r => SubstE AtomSubstVal (EffTy r)
instance IRRep r => SubstE AtomSubstVal (Expr r)
instance IRRep r => SubstE AtomSubstVal (GenericOpRep const r)
instance SubstE AtomSubstVal InstanceBody
instance SubstE AtomSubstVal DictType
instance SubstE AtomSubstVal DictExpr
instance IRRep r => SubstE AtomSubstVal (LamExpr r)
instance SubstE AtomSubstVal CorePiType
instance SubstE AtomSubstVal CoreLamExpr
instance IRRep r => SubstE AtomSubstVal (TabPiType r)
instance IRRep r => SubstE AtomSubstVal (PiType r)
instance IRRep r => SubstE AtomSubstVal (DepPairType r)
instance SubstE AtomSubstVal SolverBinding
instance IRRep r => SubstE AtomSubstVal (DeclBinding r)
instance IRRep r => SubstB AtomSubstVal (Decl r)
instance SubstE AtomSubstVal NewtypeTyCon
instance IRRep r => SubstE AtomSubstVal (PureExpr r)
instance SubstE AtomSubstVal NewtypeCon
instance IRRep r => SubstE AtomSubstVal (IxDict r)
instance IRRep r => SubstE AtomSubstVal (IxType r)
instance SubstE AtomSubstVal DataConDefs

-- === traversable terms ===

class Monad m => NonAtomRenamer m i o | m -> i, m -> o where
  renameN :: (IsAtomName c ~ False, Color c) => Name c i -> m (Name c o)

class NonAtomRenamer m i o => Visitor m r i o | m -> i, m -> o where
  visitType :: Type r i -> m (Type r o)
  visitAtom :: Atom r i -> m (Atom r o)
  visitLam  :: LamExpr r i -> m (LamExpr r o)
  visitPi   :: PiType  r i -> m (PiType  r o)

class VisitGeneric (e:: E) (r::IR) | e -> r where
  visitGeneric :: Visitor m r i o => e i -> m (e o)

type Visitor2 (m::MonadKind2) r = forall i o . Visitor (m i o) r i o

instance VisitGeneric (Atom    r) r where visitGeneric = visitAtom
instance VisitGeneric (Type    r) r where visitGeneric = visitType
instance VisitGeneric (LamExpr r) r where visitGeneric = visitLam
instance VisitGeneric (PiType  r) r where visitGeneric = visitPi

visitBlock :: Visitor m r i o => Block r i -> m (Block r o)
visitBlock b = visitGeneric (LamExpr Empty b) >>= \case
  LamExpr Empty b' -> return b'
  _ -> error "not a block"

visitAlt :: Visitor m r i o => Alt r i -> m (Alt r o)
visitAlt (Abs b body) = do
  visitGeneric (LamExpr (UnaryNest b) body) >>= \case
    LamExpr (UnaryNest b') body' -> return $ Abs b' body'
    _ -> error "not an alt"

traverseOpTerm
  :: (GenericOp e, Visitor m r i o, OpConst e r ~ OpConst e r)
  => e r i -> m (e r o)
traverseOpTerm e = traverseOp e visitGeneric visitGeneric visitGeneric

visitAtomDefault
  :: (IRRep r, Visitor (m i o) r i o, AtomSubstReader v m, EnvReader2 m)
  => Atom r i -> m i o (Atom r o)
visitAtomDefault atom = case atom of
  Var _          -> atomSubstM atom
  SimpInCore _   -> atomSubstM atom
  _ -> visitAtomPartial atom

visitTypeDefault
  :: (IRRep r, Visitor (m i o) r i o, AtomSubstReader v m, EnvReader2 m)
  => Type r i -> m i o (Type r o)
visitTypeDefault = \case
  x -> visitTypePartial x

visitPiDefault
  :: (Visitor2 m r, IRRep r, FromName v, AtomSubstReader v m, EnvExtender2 m)
  => PiType r i -> m i o (PiType r o)
visitPiDefault (PiType bs effty) = do
  visitBinders bs \bs' -> do
    effty' <- visitGeneric effty
    return $ PiType bs' effty'

visitBinders
  :: (Visitor2 m r, IRRep r, FromName v, AtomSubstReader v m, EnvExtender2 m)
  => Nest (Binder r) i i'
  -> (forall o'. DExt o o' => Nest (Binder r) o o' -> m i' o' a)
  -> m i o a
visitBinders Empty cont = getDistinct >>= \Distinct -> cont Empty
visitBinders (Nest (b:>ty) bs) cont = do
  ty' <- visitType ty
  withFreshBinder (getNameHint b) ty' \b' -> do
    extendRenamer (b@>binderName b') do
      visitBinders bs \bs' ->
        cont $ Nest b' bs'

-- XXX: This doesn't handle the `Var`, `ProjectElt`, `SimpInCore` cases. These
-- should be handled explicitly beforehand. TODO: split out these cases under a
-- separate constructor, perhaps even a `hole` paremeter to `Atom` or part of
-- `IR`.
visitAtomPartial :: (IRRep r, Visitor m r i o) => Atom r i -> m (Atom r o)
visitAtomPartial = \case
  Var _          -> error "Not handled generically"
  SimpInCore _   -> error "Not handled generically"
  Con con -> Con <$> visitGeneric con
  PtrVar t v -> PtrVar t <$> renameN v
  DepPair x y t -> do
    x' <- visitGeneric x
    y' <- visitGeneric y
    ~(DepPairTy t') <- visitGeneric $ DepPairTy t
    return $ DepPair x' y' t'
  Lam lam   -> Lam     <$> visitGeneric lam
  Eff eff   -> Eff     <$> visitGeneric eff
  DictCon t d -> DictCon <$> visitType t <*> visitGeneric d
  NewtypeCon con x -> NewtypeCon <$> visitGeneric con <*> visitGeneric x
  TypeAsAtom t -> TypeAsAtom <$> visitGeneric t
  RepValAtom repVal -> RepValAtom <$> visitGeneric repVal

-- XXX: This doesn't handle the `TyVar` or `ProjectEltTy` cases. These should be
-- handled explicitly beforehand.
visitTypePartial :: (IRRep r, Visitor m r i o) => Type r i -> m (Type r o)
visitTypePartial = \case
  NewtypeTyCon t -> NewtypeTyCon <$> visitGeneric t
  Pi           t -> Pi           <$> visitGeneric t
  TabPi        t -> TabPi        <$> visitGeneric t
  TC           t -> TC           <$> visitGeneric t
  DepPairTy    t -> DepPairTy    <$> visitGeneric t
  DictTy       t -> DictTy       <$> visitGeneric t

instance IRRep r => VisitGeneric (Expr r) r where
  visitGeneric = \case
    TopApp et v xs -> TopApp <$> visitGeneric et <*> renameN v <*> mapM visitGeneric xs
    TabApp t tab xs -> TabApp <$> visitType t <*> visitGeneric tab <*> mapM visitGeneric xs
    -- TODO: should we reuse the original effects? Whether it's valid depends on
    -- the type-preservation requirements for a visitor. We should clarify what
    -- those are.
    Case x alts effTy -> do
      x' <- visitGeneric x
      alts' <- mapM visitAlt alts
      effTy' <- visitGeneric effTy
      return $ Case x' alts' effTy'
    Atom x -> Atom <$> visitGeneric x
    TabCon Nothing t xs -> TabCon Nothing <$> visitGeneric t <*> mapM visitGeneric xs
    TabCon (Just (WhenIRE d)) t xs -> TabCon <$> (Just . WhenIRE <$> visitGeneric d) <*> visitGeneric t <*> mapM visitGeneric xs
    PrimOp op -> PrimOp <$> visitGeneric op
    App et fAtom xs -> App <$> visitGeneric et <*> visitGeneric fAtom <*> mapM visitGeneric xs
    ApplyMethod et m i xs -> ApplyMethod <$> visitGeneric et <*> visitGeneric m <*> pure i <*> mapM visitGeneric xs

instance IRRep r => VisitGeneric (PrimOp r) r where
  visitGeneric = \case
    UnOp     op x   -> UnOp  op <$> visitGeneric x
    BinOp    op x y -> BinOp op <$> visitGeneric x <*> visitGeneric y
    MemOp        op -> MemOp    <$> visitGeneric op
    VectorOp     op -> VectorOp     <$> visitGeneric op
    MiscOp       op -> MiscOp       <$> visitGeneric op
    Hof          op -> Hof          <$> visitGeneric op
    DAMOp        op -> DAMOp        <$> visitGeneric op
    RefOp r op  -> RefOp <$> visitGeneric r <*> traverseOp op visitGeneric visitGeneric visitGeneric

instance IRRep r => VisitGeneric (TypedHof r) r where
  visitGeneric (TypedHof eff hof) = TypedHof <$> visitGeneric eff <*> visitGeneric hof

instance IRRep r => VisitGeneric (Hof r) r where
  visitGeneric = \case
    For ann d lam -> For ann <$> visitGeneric d <*> visitGeneric lam
    RunReader x body -> RunReader <$> visitGeneric x <*> visitGeneric body
    RunWriter dest bm body -> RunWriter <$> mapM visitGeneric dest <*> visitGeneric bm <*> visitGeneric body
    RunState  dest s body ->  RunState  <$> mapM visitGeneric dest <*> visitGeneric s <*> visitGeneric body
    While          b -> While          <$> visitBlock b
    RunIO          b -> RunIO          <$> visitBlock b
    RunInit        b -> RunInit        <$> visitBlock b
    CatchException t b -> CatchException <$> visitType t <*> visitBlock b
    Linearize      lam x -> Linearize <$> visitGeneric lam <*> visitGeneric x
    Transpose      lam x -> Transpose <$> visitGeneric lam <*> visitGeneric x

instance IRRep r => VisitGeneric (BaseMonoid r) r where
  visitGeneric (BaseMonoid x lam) = BaseMonoid <$> visitGeneric x <*> visitGeneric lam

instance IRRep r => VisitGeneric (DAMOp r) r where
  visitGeneric = \case
    Seq eff dir d x lam -> Seq <$> visitGeneric eff <*> pure dir <*> visitGeneric d <*> visitGeneric x <*> visitGeneric lam
    RememberDest eff x lam -> RememberDest <$> visitGeneric eff <*> visitGeneric x <*> visitGeneric lam
    AllocDest t -> AllocDest <$> visitGeneric t
    Place x y -> Place  <$> visitGeneric x <*> visitGeneric y
    Freeze x  -> Freeze <$> visitGeneric x

instance IRRep r => VisitGeneric (Effect r) r where
  visitGeneric = \case
    RWSEffect rws h    -> RWSEffect rws <$> visitGeneric h
    ExceptionEffect    -> pure ExceptionEffect
    IOEffect           -> pure IOEffect
    InitEffect         -> pure InitEffect

instance IRRep r => VisitGeneric (EffectRow r) r where
  visitGeneric (EffectRow effs tailVar) = do
    effs' <- eSetFromList <$> mapM visitGeneric (eSetToList effs)
    tailEffRow <- case tailVar of
      NoTail -> return $ EffectRow mempty NoTail
      EffectRowTail v -> visitGeneric (Var v) <&> \case
        Var v' -> EffectRow mempty (EffectRowTail v')
        Eff r  -> r
        _ -> error "Not a valid effect substitution"
    return $ extendEffRow effs' tailEffRow

instance VisitGeneric DictExpr CoreIR where
  visitGeneric = \case
    InstantiatedGiven x xs -> InstantiatedGiven <$> visitGeneric x <*> mapM visitGeneric xs
    SuperclassProj x i     -> SuperclassProj <$> visitGeneric x <*> pure i
    InstanceDict v xs      -> InstanceDict <$> renameN v <*> mapM visitGeneric xs
    IxFin x                -> IxFin <$> visitGeneric x
    DataData t             -> DataData <$> visitGeneric t

instance VisitGeneric NewtypeCon CoreIR where
  visitGeneric = \case
    UserADTData sn t params -> UserADTData sn <$> renameN t <*> visitGeneric params
    NatCon -> return NatCon
    FinCon x -> FinCon <$> visitGeneric x

instance VisitGeneric NewtypeTyCon CoreIR where
  visitGeneric = \case
    Nat -> return Nat
    Fin x -> Fin <$> visitGeneric x
    EffectRowKind -> return EffectRowKind
    UserADTType n v params -> UserADTType n <$> renameN v <*> visitGeneric params

instance VisitGeneric (PureExpr r) r where
  visitGeneric (PureExpr block) = do
    visitGeneric (LamExpr Empty block) >>= \case
      LamExpr Empty block' -> return $ PureExpr block'
      _ -> error "not a block"

instance VisitGeneric TyConParams CoreIR where
  visitGeneric (TyConParams expls xs) = TyConParams expls <$> mapM visitGeneric xs

instance IRRep r => VisitGeneric (IxDict r) r where
  visitGeneric = \case
    IxDictAtom   x -> IxDictAtom   <$> visitGeneric x
    IxDictRawFin x -> IxDictRawFin <$> visitGeneric x
    IxDictSpecialized t v xs -> IxDictSpecialized <$> visitGeneric t <*> renameN v <*> mapM visitGeneric xs

instance IRRep r => VisitGeneric (IxType r) r where
  visitGeneric (IxType t d) = IxType <$> visitType t <*> visitGeneric d

instance VisitGeneric DictType CoreIR where
  visitGeneric (DictType n v xs) = DictType n <$> renameN v <*> mapM visitGeneric xs

instance VisitGeneric CoreLamExpr CoreIR where
  visitGeneric (CoreLamExpr t lam) = CoreLamExpr <$> visitGeneric t <*> visitGeneric lam

instance VisitGeneric CorePiType CoreIR where
  visitGeneric (CorePiType app expl bs effty) = do
    PiType bs' effty' <- visitGeneric $ PiType bs effty
    return $ CorePiType app expl bs' effty'

instance IRRep r => VisitGeneric (TabPiType r) r where
  visitGeneric (TabPiType d b eltTy) = do
    d' <- visitGeneric d
    visitGeneric (PiType (UnaryNest b) (EffTy Pure eltTy)) <&> \case
      PiType (UnaryNest b') (EffTy Pure eltTy') -> TabPiType d' b' eltTy'
      _ -> error "not a table pi type"

instance IRRep r => VisitGeneric (DepPairType r) r where
  visitGeneric (DepPairType expl b ty) = do
    visitGeneric (PiType (UnaryNest b) (EffTy Pure ty)) <&> \case
      PiType (UnaryNest b') (EffTy Pure ty') -> DepPairType expl b' ty'
      _ -> error "not a dependent pair type"

instance VisitGeneric (RepVal SimpIR) SimpIR where
  visitGeneric (RepVal ty tree) = RepVal <$> visitGeneric ty <*> mapM renameIExpr tree
    where renameIExpr = \case
            ILit l -> return $ ILit l
            IVar    v t -> IVar    <$> renameN v <*> pure t
            IPtrVar v t -> IPtrVar <$> renameN v <*> pure t

instance IRRep r => VisitGeneric (DeclBinding r) r where
  visitGeneric (DeclBinding ann expr) = DeclBinding ann <$> visitGeneric expr

instance IRRep r => VisitGeneric (EffTy r) r where
  visitGeneric (EffTy eff ty) =
    EffTy <$> visitGeneric eff <*> visitGeneric ty

instance VisitGeneric DataConDefs CoreIR where
  visitGeneric = \case
    ADTCons cons -> ADTCons <$> mapM visitGeneric cons
    StructFields defs -> do
      let (names, tys) = unzip defs
      tys' <- mapM visitGeneric tys
      return $ StructFields $ zip names tys'

instance VisitGeneric DataConDef CoreIR where
  visitGeneric (DataConDef sn (Abs bs UnitE) repTy ps) = do
    PiType bs' _  <- visitGeneric $ PiType bs $ EffTy Pure UnitTy
    repTy' <- visitGeneric repTy
    return $ DataConDef sn (Abs bs' UnitE) repTy' ps

instance VisitGeneric (Con      r) r where visitGeneric = traverseOpTerm
instance VisitGeneric (TC       r) r where visitGeneric = traverseOpTerm
instance VisitGeneric (MiscOp   r) r where visitGeneric = traverseOpTerm
instance VisitGeneric (VectorOp r) r where visitGeneric = traverseOpTerm
instance VisitGeneric (MemOp    r) r where visitGeneric = traverseOpTerm
