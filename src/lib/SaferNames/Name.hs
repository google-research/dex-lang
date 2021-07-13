-- Copyright 2021 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module SaferNames.Name (
  Name (..), RawName, S (..), Env (..), (!), (<>>), (<.>), NameBinder (..),
  Scope, ScopeFrag, NameTraversal (..), lookupNameTraversal, newEnv,
  E, B, HasNamesE (..), HasNamesB (..), BindsNames (..),
  BindsOneName (..), BindsNameList (..),
  Abs (..), Nest (..), NestPair (..),
  UnitE (..), VoidE, PairE (..), MaybeE (..), ListE (..),
  EitherE (..), LiftE (..), EqE, EqB,
  fromConstAbs, toConstAbs, PrettyE, PrettyB, ShowE, ShowB,
  SubstReader (..), SubstReaderT, SubstReaderM, runSubstReaderT, runSubstReaderM,
  ScopeReader (..), ScopeReaderT, ScopeReaderM, runScopeReaderT, runScopeReaderM,
  MonadKind, MonadKind1, MonadKind2,
  Monad1, Monad2, MonadErr1, MonadErr2, MonadFail1, MonadFail2,
  idSubst, applySubst, applyAbs, applyNaryAbs,
  ZipSubstEnv (..), MonadZipSubst (..), alphaEqTraversable,
  checkAlphaEq, AlphaEq, AlphaEqE (..), AlphaEqB (..), IdE (..), ConstE (..),
  InjectableE (..), InjectableB (..), dropSubst, lookupSubstM, Ext (..),
  lookupScope, lookupScopeM, withFreshM, extendSubst, inject, injectM, withDistinct,
  EmptyAbs, pattern EmptyAbs, SubstVal (..), SubstE (..), SubstB (..)) where

import Prelude hiding (id, (.))
import Control.Category
import Control.Monad.Except hiding (Except)
import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.Writer.Strict
import Data.Dynamic
import Data.Text.Prettyprint.Doc  hiding (nest)
import GHC.Exts (Constraint)

import SaferNames.NameCore
import Util (zipErr)
import Err

-- === environments and scopes ===

-- Env is like `NameMap` but it doesn't hold the full set of names, so you can
-- make one from an ordinary function. It's effcicently extensible using
-- an `EnvFrag`.
data Env (v::E->E) (i::S) (o::S) where
  Env :: (forall s. Name s i -> v s o)  -- fallback function
      -> NameMap v (i:=>:i') o          -- names first lookup up here
      -> Env v i' o

newtype EnvFrag (v::E->E) (i::S) (i'::S) (o::S) =
  EnvFrag (NameMap v (i:=>:i') o)

-- Scopes carry
--    1. The full set of names (suitable for generating fresh names)
--    2. A no-shadowing guarantee (via `Distinct`)
--    3. The payload associated with each name's static data parameter
data Scope (n::S) where
  Scope :: Distinct n => NameMap IdE n n -> Scope n

data ScopeFrag (n::S) (l::S) where
  ScopeFrag :: Distinct l => NameMap IdE (n:=>:l) l -> ScopeFrag n l

newEnv :: (forall s. Name s i -> v s o) -> Env v i o
newEnv f = Env f emptyNameMap

infixl 9 !
(!) :: Env v i o -> Name s i -> v s o
(!) (Env f frag) name =
  case lookupEnvFrag (EnvFrag frag) name of
    Left name' -> f name'
    Right val -> val

infixl 1 <>>
(<>>) :: Env v i o -> EnvFrag v i i' o -> Env v i' o
(<>>) (Env f frag) (EnvFrag frag') = Env f $ concatNameMaps frag frag'

infixl 1 <.>
(<.>) :: EnvFrag v i1 i2 o -> EnvFrag v i2 i3 o -> EnvFrag v i1 i3 o
(<.>) (EnvFrag env) (EnvFrag env') = EnvFrag (concatNameMaps env env')

emptyEnvFrag :: EnvFrag v i i o
emptyEnvFrag = EnvFrag emptyNameMap

lookupEnvFrag :: EnvFrag v i i' o -> Name s i' -> Either (Name s i) (v s o)
lookupEnvFrag (EnvFrag m) name =
  case projectName (nameMapNames m) name of
    Left  name' -> Left name'
    Right name' -> Right $ lookupNameMap m name'

lookupScope :: Scope n -> Name s n -> s n
lookupScope (Scope m) v = fromIdE $ lookupNameMap m v

appendScope :: Scope n -> ScopeFrag n l -> Scope l
appendScope (Scope m1) (ScopeFrag m2) =
  Scope $ extendNameMap (injectNames (nameMapNames m2) m1) m2

-- === common scoping patterns ===

data Abs (binder::B) (body::E) (n::S) where
  Abs :: binder n l -> body l -> Abs binder body n

data NestPair (b1::B) (b2::B) (n::S) (l::S) where
  NestPair :: b1 n l -> b2 l l' -> NestPair b1 b2 n l'

data Nest (binder::B) (n::S) (l::S) where
  Nest  :: binder n h -> Nest binder h l -> Nest binder n l
  Empty ::                                  Nest binder n n

type EmptyAbs b = Abs b UnitE :: E
pattern EmptyAbs :: b n l -> EmptyAbs b n
pattern EmptyAbs bs = Abs bs UnitE

-- === Injections and projections ===

newtype Ext (n::S) (l::S) = ExtVal { fromExtVal :: NameSet (n:=>:l) }

instance Category Ext where
  id = ExtVal emptyNameSetFrag
  ext1 . ext2 = ExtVal $ concatNameSets (fromExtVal ext2) (fromExtVal ext1)

class BindsNames (b :: B) where
  toExtVal :: b n l -> Ext n l

instance BindsNames Ext where
  toExtVal = id

toNameSet :: BindsNames b => b n l -> NameSet (n:=>:l)
toNameSet b = fromExtVal $ toExtVal b

inject :: BindsNames b => InjectableE e => Distinct l => b n l -> e n -> e l
inject ext x = injectNames (toNameSet ext) x

-- like inject, but uses the ScopeReader monad for its `Distinct` proof
injectM :: ScopeReader m => BindsNames b => InjectableE e => b n l -> e n -> m l (e l)
injectM b e = withDistinct $ return $ inject b e

-- This may become expensive. It traverses the body of the Abs to check for
-- leaked variables.
fromConstAbs :: ScopeReader m => MonadErr1 m => BindsNames b => HasNamesE e
             => Abs b e n -> m n (e n)
fromConstAbs (Abs b e) = do
  let t = newNameTraversal \name ->
             case projectName (toNameSet b) name of
               Left name' -> return name'
               Right _    -> throw EscapedNameErr (pprint name)
  scope <- askScope
  liftEither $ traverseNamesE scope t e

-- TODO: seems silly to have to have the static annotation here. I think we need
-- to have a finer-grained scope reader class hierarchy so we're not forced to
-- supply static information when it's not needed.
toConstAbs :: InjectableE s => Typeable s => ScopeReader m => HasNamesE e
           => s n -> e n -> m n (Abs (NameBinder s) e n)
toConstAbs ann body =
  withFreshM ann \b -> do
    body' <- injectM b body
    return $ Abs b body'

-- === type classes for traversing names ===

-- NameTraversal is logically equivalent to this:
--    type NameTraversal m i o = forall s. Name s i -> m (Name s o)
-- But, as an optimization, we represent it as a composition of an ordinary
-- monadic function and a renaming env. This is just so that we can efficiently
-- extend it. The composition hides the intermediate name space `hidded`,
-- just as `(.) :: (b -> c) -> (a -> b) -> (a -> c)` hides `b`.
data NameTraversal m i o where
  NameTraversal :: (forall s. Name s hidden -> m (Name s o))
                -> EnvFrag Name hidden i o
                -> NameTraversal m i o

class InjectableE e => HasNamesE (e::E) where
  traverseNamesE :: Monad m => Scope o -> NameTraversal m i o -> e i -> m (e o)

class (BindsNames b, InjectableB b) => HasNamesB (b::B) where
  traverseNamesB :: Scope o
                 -> NameTraversal m i o
                 -> b i i'
                 -> (forall o'. Scope o' -> NameTraversal m i' o' -> b o o' -> m a)
                 -> m a

lookupNameTraversal :: Typeable s => Monad m
                    => NameTraversal m i o -> Name s i -> m (Name s o)
lookupNameTraversal (NameTraversal f env) name =
  case lookupEnvFrag env name of
    Left  name' -> f name'
    Right name' -> return name'

newNameTraversal :: (forall s. Name s i -> m (Name s o)) -> NameTraversal m i o
newNameTraversal f = NameTraversal f emptyEnvFrag

-- === type class for substitutions ===

-- Only alllows non-trivial substitution with names that match the parameter
-- `sMatch`. For example, this lets us substitute ordinary variables in Core
-- with Atoms, while ensuring that things like data def names only get renamed.
data SubstVal (sMatch::E) (atom::E) (s::E) (n::S) where
  SubstVal :: atom n   -> SubstVal s      atom s n
  Rename   :: Name s n -> SubstVal sMatch atom s n

class SubstE (v::E->E) (e::E) where
  substE :: SubstReader v m => e i -> m i o (e o)

class BindsNames b => SubstB (v::E->E) (b::B) where
  substB :: SubstReader v  m
         => b i i'
         -> (forall o'. b o o' -> m i' o' a)
         -> m i o a

-- === various E-kind and B-kind versions of standard containers and classes ===

type PrettyE  e = (forall (n::S)       . Pretty (e n  )) :: Constraint
type PrettyB b  = (forall (n::S) (l::S). Pretty (b n l)) :: Constraint

type ShowE e = (forall (n::S)       . Show (e n  )) :: Constraint
type ShowB b = (forall (n::S) (l::S). Show (b n l)) :: Constraint

type EqE e = (forall (n::S)       . Eq (e n  )) :: Constraint
type EqB b = (forall (n::S) (l::S). Eq (b n l)) :: Constraint

data UnitE (n::S) = UnitE deriving (Show, Eq)
data VoidE (n::S)

data PairE (e1::E) (e2::E) (n::S) = PairE (e1 n) (e2 n)
     deriving (Show, Eq)

data EitherE (e1::E) (e2::E) (n::S) = LeftE (e1 n) | RightE (e2 n)
     deriving (Show, Eq)

data MaybeE (e::E) (n::S) = JustE (e n) | NothingE
     deriving (Show, Eq)

data ListE (e::E) (n::S) = ListE { fromListE :: [e n] }
     deriving (Show, Eq)

data LiftE (a:: *) (n::S) = LiftE { fromLiftE :: a }
     deriving (Show, Eq)

-- The identity function at `E`
newtype IdE (e::E) (n::S) = IdE { fromIdE :: e n }

-- The constant function at `E`
newtype ConstE (const::E) (ignored::E) (n::S) = ConstE (const n)

-- === various convenience utilities ===

infixr 7 @>
class BindsOneName (b::B) (s::E) | b -> s where
  (@>) :: b i i' -> v s o -> EnvFrag v i i' o
  binderName :: b i i' -> Name s i'

instance BindsNames (NameBinder s) where
  toExtVal b = ExtVal $ singletonNameSet b

instance BindsOneName (NameBinder s) s where
  b @> x = EnvFrag (singletonNameMap b x)
  binderName = nameBinderName

infixr 7 @@>
class BindsNameList (b::B) (s::E) | b -> s where
  (@@>) :: b i i' -> [v s o] -> EnvFrag v i i' o

instance BindsOneName b s => BindsNameList (Nest b) s where
  (@@>) Empty [] = emptyEnvFrag
  (@@>) (Nest b rest) (x:xs) = b@>x <.> rest@@>xs
  (@@>) _ _ = error "length mismatch"

idSubst :: Typeable e => Typeable s => Env (SubstVal s e) n n
idSubst = newEnv Rename

applySubst :: ScopeReader m => SubstE v e => Env v i o -> e i -> m o (e o)
applySubst env x = do
  scope <- askScope
  return $ runSubstReaderM scope env $ substE x

applyAbs :: Typeable s => Typeable val
         => ScopeReader m
         => BindsOneName b s => SubstE (SubstVal s val) e
         => Abs b e n -> val n -> m n (e n)
applyAbs (Abs b body) x = applySubst (idSubst <>> (b@>SubstVal x)) body

applyNaryAbs :: Typeable s => Typeable val
             => ScopeReader m
             => BindsNameList b s
             => SubstE (SubstVal s val) e
             => SubstB (SubstVal s val) b
             => Abs b e n -> [val n] -> m n (e n)
applyNaryAbs (Abs bs body) xs = applySubst (idSubst <>> (bs @@> map SubstVal xs)) body

-- === versions of monad constraints with scope params ===

type MonadKind  =           * -> *
type MonadKind1 =      S -> * -> *
type MonadKind2 = S -> S -> * -> *

type Monad1 (m :: MonadKind1) = forall (n::S)        . Monad (m n  )
type Monad2 (m :: MonadKind2) = forall (n::S) (l::S) . Monad (m n l)

type MonadErr1 (m :: MonadKind1) = forall (n::S)        . MonadErr (m n  )
type MonadErr2 (m :: MonadKind2) = forall (n::S) (l::S) . MonadErr (m n l)

type MonadFail1 (m :: MonadKind1) = forall (n::S)        . MonadFail (m n  )
type MonadFail2 (m :: MonadKind2) = forall (n::S) (l::S) . MonadFail (m n l)

-- === scope reader monad ===

class Monad1 m => ScopeReader (m::MonadKind1) where
  askScope :: m n (Scope n)
  extendScope :: ScopeFrag n l -> m l a -> m n a

type ScopeReader2 (m::MonadKind2) = forall (n::S). ScopeReader (m n)

newtype ScopeReaderT (m:: * -> *) (n::S) (a:: *) =
  ScopeReaderT { runScopeReaderT' :: ReaderT (Scope n) m a}
  deriving (Functor, Applicative, Monad)

type ScopeReaderM = ScopeReaderT Identity

runScopeReaderT :: Monad m => Scope n -> ScopeReaderT m n a -> m a
runScopeReaderT scope m = runReaderT (runScopeReaderT' m) scope

runScopeReaderM :: Scope n -> ScopeReaderM n a -> a
runScopeReaderM scope m = runIdentity $ runScopeReaderT scope m

lookupScopeM :: Typeable s => ScopeReader m => Name s n -> m n (s n)
lookupScopeM v = flip lookupScope v <$> askScope

withDistinct :: ScopeReader m => (Distinct n => m n a) -> m n a
withDistinct cont = askScope >>= \case Scope _ -> cont

-- === subst monad ===

-- `SubstReader m => m v i o a` gives you access to a substitution mapping
-- input-names, `Name s i`, to result values, `v s o`.
class ScopeReader2 m => SubstReader (v::E->E) (m::MonadKind2) | m -> v where
  askSubst :: m i o (Env v i o)
  withSubst :: Env v i' o -> m i' o a -> m i o a

-- we could have `m::MP` but it's more work and we don't need it
newtype SubstReaderT (m:: * -> *) (v::E -> E) (i::S) (o::S) (a:: *) =
  SubstReaderT { runSubstReaderT' :: ReaderT (Scope o, Env v i o) m a }
  deriving (Functor, Applicative, Monad)

type SubstReaderM = SubstReaderT Identity

runSubstReaderT :: Scope o -> Env v i o -> SubstReaderT m v i o a -> m a
runSubstReaderT bindings env m = runReaderT (runSubstReaderT' m) (bindings, env)

runSubstReaderM :: Scope o -> Env v i o -> SubstReaderM v i o a -> a
runSubstReaderM scope env m = runIdentity $ runSubstReaderT scope env m

instance MonadError e m => MonadError e (SubstReaderT m v i o) where
  throwError e = SubstReaderT $ throwError e
  catchError (SubstReaderT m) f = SubstReaderT $ catchError m $ runSubstReaderT' . f

instance MonadFail m => MonadFail (SubstReaderT m v i o) where
  fail s = SubstReaderT $ fail s

instance Monad m => ScopeReader (SubstReaderT m v i) where
  askScope = SubstReaderT $ asks fst
  extendScope scopeFrag@(ScopeFrag m) (SubstReaderT (ReaderT f)) =
    SubstReaderT $ ReaderT \(scope, subst) ->
    f (appendScope scope scopeFrag, injectNames (nameMapNames m) subst)

instance Monad m => SubstReader v (SubstReaderT m v) where
  askSubst = SubstReaderT $ asks snd
  withSubst subst (SubstReaderT (ReaderT f)) =
    SubstReaderT $ ReaderT \(scope, _) -> f (scope, subst)

extendSubst :: SubstReader v m
            => EnvFrag v i i' o -> m i' o a -> m i o a
extendSubst frag cont = do
  env <- askSubst
  withSubst (env <>> frag) cont

dropSubst :: SubstReader (SubstVal sMatch atom) m => Typeable sMatch => Typeable atom
          => m o o a
          -> m i o a
dropSubst cont = withSubst idSubst cont

withFreshM :: ScopeReader m => Typeable s => InjectableE s
           => s o
           -> (forall o'. NameBinder s o o' -> m o' a)
           -> m o a
withFreshM ann cont = do
  scope <- askScope
  case scope of
    Scope m ->
      withFresh (nameMapNames m) \b' -> do
        let ann' = inject b' ann
        extendScope (ScopeFrag (singletonNameMap b' (IdE ann'))) $
          cont b'

lookupSubstM :: SubstReader v m => Name s i -> m i o (v s o)
lookupSubstM name = (!name) <$> askSubst

-- === alpha-renaming-invariant equality checking ===

type AlphaEq e = AlphaEqE e  :: Constraint

checkAlphaEq :: AlphaEqE e => MonadErr1 m => ScopeReader m
             => e n -> e n -> m n ()
checkAlphaEq e1 e2 = do
  scope <- askScope
  liftEither $ runReaderT (runZipSubstM $ alphaEqE e1 e2) (idZipSubstEnv scope)

data ZipSubstEnv i1 i2 o = ZipSubstEnv
  { zSubst1 :: Env Name i1 o
  , zSubst2 :: Env Name i2 o
  , zScope  :: Scope o }

class AlphaEqE (e::E) where
  alphaEqE :: MonadZipSubst m => e i1 -> e i2 -> m i1 i2 o ()

class AlphaEqB (b::B) where
  withAlphaEqB :: MonadZipSubst m => b i1 i1' -> b i2 i2'
               -> (forall o'. m i1' i2' o' a)
               ->             m i1  i2  o  a

-- TODO: consider generalizing this to something that can also handle e.g.
-- unification and type checking with some light reduction
class (forall i1 i2 o. MonadErr (m i1 i2 o), forall i1 i2 o. MonadFail (m i1 i2 o))
      => MonadZipSubst (m :: S -> S -> S -> * -> *) where
  askZipSubstEnv :: m i1 i2 o (ZipSubstEnv i1 i2 o)
  withZipSubstEnv :: ZipSubstEnv i1' i2' o'
             -> m i1' i2' o' a
             -> m i1  i2  o  a

newtype ZipSubstM i1 i2 o a =
  ZipSubstM { runZipSubstM :: (ReaderT (ZipSubstEnv i1 i2 o) Except a) }
  deriving (Functor, Applicative, Monad, MonadFail)

instance MonadError Err (ZipSubstM i1 i2 o) where
  throwError e = ZipSubstM $ throwError e
  catchError (ZipSubstM m) f = ZipSubstM $ catchError m $ runZipSubstM . f

instance MonadZipSubst ZipSubstM where
  askZipSubstEnv = ZipSubstM ask
  withZipSubstEnv env (ZipSubstM m) = ZipSubstM $ lift $ runReaderT m env

idZipSubstEnv :: Scope n -> ZipSubstEnv n n n
idZipSubstEnv scope = ZipSubstEnv (newEnv id) (newEnv id) scope

alphaEqTraversable :: (AlphaEqE e, Traversable f, Eq (f ()))
                   => MonadZipSubst m
                   => f (e i1) -> f (e i2) -> m i1 i2 o ()
alphaEqTraversable f1 f2 = do
  let (struct1, vals1) = splitTraversable f1
  let (struct2, vals2) = splitTraversable f2
  unless (struct1 == struct2) zipErr
  zipWithM_ alphaEqE vals1 vals2
  where
    splitTraversable :: Traversable f => f a -> (f (), [a])
    splitTraversable xs = runWriter $ forM xs \x -> tell [x]

instance Typeable s => AlphaEqE (Name s) where
  alphaEqE v1 v2 = do
    ZipSubstEnv env1 env2 _ <- askZipSubstEnv
    if env1!v1 == env2!v2
      then return ()
      else zipErr

instance AlphaEqB b => AlphaEqB (Nest b) where
  withAlphaEqB Empty Empty cont = cont
  withAlphaEqB (Nest b1 rest1) (Nest b2 rest2) cont =
    withAlphaEqB b1 b2 $ withAlphaEqB rest1 rest2 $ cont
  withAlphaEqB _ _ _ = zipErr

instance (AlphaEqB b1, AlphaEqB b2) => AlphaEqB (NestPair b1 b2) where
  withAlphaEqB (NestPair a1 b1) (NestPair a2 b2) cont =
    withAlphaEqB a1 a2 $ withAlphaEqB b1 b2 $ cont

instance (AlphaEqB b, AlphaEqE e) => AlphaEqE (Abs b e) where
  alphaEqE (Abs b1 e1) (Abs b2 e2) = withAlphaEqB b1 b2 $ alphaEqE e1 e2

instance AlphaEqE UnitE where
  alphaEqE UnitE UnitE = return ()

instance (AlphaEqE e1, AlphaEqE e2) => AlphaEqE (PairE e1 e2) where
  alphaEqE (PairE a1 b1) (PairE a2 b2) = alphaEqE a1 a2 >> alphaEqE b1 b2

-- === instances ===

instance InjectableE (Env v i) where
  injectionProofE = undefined

instance InjectableB ScopeFrag where
  injectionProofB _ _ _ = undefined

instance Typeable s => HasNamesE (Name s) where
  traverseNamesE _ t name = lookupNameTraversal t name

instance (InjectableB b, InjectableE e) => InjectableE (Abs b e) where
  injectionProofE = undefined

instance (HasNamesB b, HasNamesE e) => HasNamesE (Abs b e) where
  traverseNamesE s t (Abs b body) = do
    traverseNamesB s t b \s' t' b' ->
      Abs b' <$> traverseNamesE s' t' body

instance (SubstB v b, SubstE v e) => SubstE v (Abs b e) where
  substE (Abs b body) = substB b \b' -> Abs b' <$> substE body

instance SubstB v b => SubstB v (Nest b) where
  substB Empty cont = cont Empty
  substB (Nest b r) cont = substB b \b' -> substB r \r' -> cont $ Nest b' r'

instance (BindsNames b1, BindsNames b2) => BindsNames (NestPair b1 b2) where
  toExtVal (NestPair b1 b2) = toExtVal b1 >>> toExtVal b2

instance (InjectableB b1, InjectableB b2) => InjectableB (NestPair b1 b2) where
  injectionProofB _ _ _ = undefined

instance (HasNamesB b1, HasNamesB b2) => HasNamesB (NestPair b1 b2) where
  traverseNamesB s t (NestPair b1 b2) cont =
    traverseNamesB s t b1 \s' t' b1' ->
      traverseNamesB s' t' b2 \s'' t'' b2' ->
        cont s'' t'' (NestPair b1' b2')

instance (SubstB v b1, SubstB v b2) => SubstB v (NestPair b1 b2) where
  substB (NestPair b1 b2) cont =
    substB b1 \b1' ->
      substB b2 \b2' ->
        cont $ NestPair b1' b2'

instance BindsNames b => BindsNames (Nest b) where
  toExtVal Empty = id
  toExtVal (Nest b rest) = toExtVal b >>> toExtVal rest

instance InjectableB b => InjectableB (Nest b) where
  injectionProofB _ _ _ = undefined

instance HasNamesB b => HasNamesB (Nest b) where
  traverseNamesB s t nest cont = case nest of
    Empty -> cont s t Empty
    Nest b rest ->
      traverseNamesB s t b \s' t' b' ->
        traverseNamesB s' t' rest \s'' t'' rest' ->
          cont s'' t'' $ Nest b' rest'

instance InjectableE UnitE where
  injectionProofE = undefined

instance HasNamesE UnitE where
  traverseNamesE _ _ UnitE = return UnitE

instance SubstE v UnitE where
  substE UnitE = return UnitE

instance InjectableE e => InjectableE (IdE e) where
  injectionProofE = undefined

instance HasNamesE e => HasNamesE (IdE e) where
  traverseNamesE = undefined

instance (InjectableE e1, InjectableE e2) => InjectableE (PairE e1 e2) where
  injectionProofE = undefined

instance (HasNamesE e1, HasNamesE e2) => HasNamesE (PairE e1 e2) where
  traverseNamesE s env (PairE x y) =
    PairE <$> traverseNamesE s env x <*> traverseNamesE s env y

instance (SubstE v e1, SubstE v e2) => SubstE v (PairE e1 e2) where
  substE (PairE x y) = PairE <$> substE x <*> substE y

instance InjectableE e => InjectableE (ListE e) where
  injectionProofE = undefined

instance HasNamesE e => HasNamesE (ListE e) where
  traverseNamesE s env (ListE xs) = ListE <$> mapM (traverseNamesE s env) xs

instance SubstE v e => SubstE v (ListE e) where
  substE (ListE xs) = ListE <$> mapM substE xs

instance (forall n' l. Show (b n' l), forall n'. Show (body n')) => Show (Abs b body n) where
  show (Abs b body) = "(Abs " <> show b <> " " <> show body <> ")"

instance (forall n' l'. Show (b n' l')) => Show (Nest b n l) where
  show Empty = ""
  show (Nest b rest) = "(Nest " <> show b <> " in " <> show rest <> ")"

instance (PrettyB b) => Pretty (Nest b n l) where
  pretty _ = "TODO"

instance (PrettyB b, PrettyE e) => Pretty (Abs b e n) where
  pretty _ = "TODO"

instance Pretty a => Pretty (LiftE a n) where
  pretty (LiftE x) = pretty x
