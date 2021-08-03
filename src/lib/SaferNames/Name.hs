-- Copyright 2021 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module SaferNames.Name (
  Name (..), RawName, S (..), Env (..), (<.>), NameBinder (..),
  EnvReader (..), EnvExtender (..), Renamer (..),
  ScopeReader (..), ScopeExtender (..), BindingsReader (..), BindingsExtender (..),
  Scope, ScopeFrag, SubstE (..), SubstB (..),
  E, B, HasNamesE, HasNamesB, BindsNames (..),
  BindsOneName (..), BindsNameList (..),
  Abs (..), Nest (..), NestPair (..),
  UnitE (..), VoidE, PairE (..), MaybeE (..), ListE (..),
  EitherE (..), LiftE (..), EqE, EqB,
  fromConstAbs, toConstAbs, PrettyE, PrettyB, ShowE, ShowB,
  ScopeReaderT (..), BindingsReaderT (..), EnvReaderT (..),
  MonadKind, MonadKind1, MonadKind2,
  Monad1, Monad2, MonadErr1, MonadErr2, MonadFail1, MonadFail2,
  BindingsReader2, BindingsExtender2,
  applyAbs, applyNaryAbs,
  ZipEnvReader (..), alphaEqTraversable,
  checkAlphaEq, AlphaEq, AlphaEqE (..), AlphaEqB (..), IdE (..), ConstE (..),
  InjectableE (..), InjectableB (..), Ext (..), InjectionCoercion,
  lookupBindings, lookupBindingsVal, withFreshM, inject, injectM, withDistinct,
  EmptyAbs, pattern EmptyAbs, SubstVal (..),
  NameGen (..), NameGenT (..), SubstGen (..), SubstGenT (..),
  liftSG, traverseNestSG) where

import Prelude hiding (id, (.))
import Control.Category
import Control.Monad.Except hiding (Except)
import Control.Monad.Reader
import Control.Monad.Writer.Strict
import Data.Dynamic
import Data.Text.Prettyprint.Doc  hiding (nest)
import GHC.Exts (Constraint)

import SaferNames.NameCore
import Util (zipErr, onFst, onSnd)
import Err

-- === environments and scopes ===

-- Scopes carry
--    1. The full set of names (suitable for generating fresh names)
--    2. A no-shadowing guarantee (via `Distinct`)
data Scope (n::S) where
  Scope :: Distinct n => NameSet n -> Scope n

data ScopeFrag (n::S) (l::S) where
  ScopeFrag :: Distinct l => NameSet (n:=>:l) -> ScopeFrag n l

-- Bindings are Scopes that additionally carry static information associated with names
data Bindings (n::S) where
  Bindings :: Distinct n => NameMap IdE n n -> Bindings n

data BindingsFrag (n::S) (l::S) where
  BindingsFrag :: Distinct l => NameMap IdE (n:=>:l) l -> BindingsFrag n l

-- Env is like `NameMap` but it doesn't hold the full set of names, so you can
-- make one from an ordinary function. It's effcicently extensible using
-- an `EnvFrag`.
data Env (v::E->E) (i::S) (o::S) where
  Env :: (forall s. Name s hidden -> v s o)  -- fallback function
      -> NameMap v (hidden:=>:i) o           -- names first looked up here
      -> Env v i o

newtype EnvFrag (v::E->E) (i::S) (i'::S) (o::S) =
  EnvFrag (NameMap v (i:=>:i') o)

newEnv :: (forall s. Name s i -> v s o) -> Env v i o
newEnv f = Env f emptyNameMap

voidEnv :: Env v VoidS o
voidEnv = newEnv absurdNameFunction

-- === monadic type classes for reading and extending envs and scopes ===

class Monad1 m => ScopeReader (m::MonadKind1) where
  getScope :: m n (Scope n)

class Monad1 m => ScopeExtender (m::MonadKind1) where
  extendScope :: ScopeFrag n l -> m l r -> m n r

class (Monad1 m, ScopeReader m) => BindingsReader (m::MonadKind1) where
  getBindings :: m n (Bindings n)

class BindingsExtender (m::MonadKind1) where
  extendBindings :: BindingsFrag n l -> m l r -> m n r

class Monad2 m => EnvReader (v::E->E) (m::MonadKind2) | m -> v where
  lookupEnv :: Name s i -> m i o (v s o)

class Monad2 m => EnvExtender (v::E->E) (m::MonadKind2) | m -> v where
  extendEnv :: EnvFrag v i i' o -> m i' o r -> m i o r

class Monad2 m => Renamer (m::MonadKind2) where
  withEmptyRenamer :: m o o r -> m i o r
  extendRenamer :: EnvFrag Name i i' o -> m i' o r -> m i o r

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

instance BindsNames ScopeFrag where
  toExtVal (ScopeFrag s) = ExtVal s

instance BindsNames BindingsFrag where
  toExtVal (BindingsFrag m) = ExtVal $ nameMapNames m

toNameSet :: BindsNames b => b n l -> NameSet (n:=>:l)
toNameSet b = fromExtVal $ toExtVal b

inject :: BindsNames b => InjectableE e => Distinct l => b n l -> e n -> e l
inject ext x = injectNames (toNameSet ext) x

-- like inject, but uses the ScopeReader monad for its `Distinct` proof
injectM :: ScopeReader m => BindsNames b => InjectableE e => b n l -> e n -> m l (e l)
injectM b e = withDistinct $ return $ inject b e

withDistinct :: ScopeReader m => (Distinct n => m n a) -> m n a
withDistinct cont = do
  Scope _ <- getScope
  cont

traverseNames :: (Monad m, HasNamesE e)
              => Scope o -> (forall s. Name s i -> m (Name s o)) -> e i -> m (e o)
traverseNames scope f e =
  flip runReaderT scope $
    runScopeReaderT $
      flip runReaderT (newNameTraverserEnv f) $
         runNameTraverserT $
           substE e

-- This may become expensive. It traverses the body of the Abs to check for
-- leaked variables.
fromConstAbs :: (ScopeReader m, MonadErr1 m, BindsNames b, HasNamesE e)
             => Abs b e n -> m n (e n)
fromConstAbs (Abs b e) = do
  scope <- getScope
  liftEither $ traverseNames scope (tryProjectName $ toNameSet b) e

tryProjectName :: MonadErr m => NameSet (n:=>:l) -> Name s l -> m (Name s n)
tryProjectName names name =
  case projectName names name of
    Left name' -> return name'
    Right _    -> throw EscapedNameErr (pprint name)

toConstAbs :: (Typeable s, InjectableE s, InjectableE e, ScopeReader m, ScopeExtender m)
           => e n -> m n (Abs (NameBinder s) e n)
toConstAbs body =
  withFreshM \b -> do
    body' <- injectM b body
    return $ Abs b body'

-- === type classes for traversing names ===

class SubstE (v::E->E) (e::E) where
  -- TODO: can't make an alias for these constraints because of impredicativity
  substE :: ( ScopeReader2 m, ScopeExtender2 m , EnvReader v m, Renamer m)
         => e i -> m i o (e o)

class SubstB (v::E->E) (b::B) where
  substB :: ( ScopeReader2 m, ScopeExtender2 m , EnvReader v m, Renamer m)
         => b i i'
         -> SubstGenT m i i' (b o) o

type HasNamesE = SubstE Name
type HasNamesB = SubstB Name

instance Typeable s => SubstE Name (Name s) where
  substE name = lookupEnv name

instance (InjectableE s, Typeable s) => SubstB v (NameBinder s) where
  substB b = SubstGenT do
    Scope names <- getScope
    withFresh names \b' -> do
      let frag = ScopeFrag $ singletonNameSet b'
      return $ Abs frag $ PairE (b @> binderName b') b'

withSubstB :: (SubstB v b, ScopeReader2 m, ScopeExtender2 m , EnvReader v m, Renamer m)
           => b i i'
           -> (forall o'. b o o' -> m i' o' r)
           -> m i o r
withSubstB b cont = do
  Abs scopeFrag (PairE substFrag b') <- runSubstGenT $ substB b
  extendScope scopeFrag $ extendRenamer substFrag $ cont b'

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

-- -- === various convenience utilities ===

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


applySubst :: (ScopeReader m, SubstE (SubstVal s val) e, Typeable val, InjectableE val)
           => EnvFrag (SubstVal s val) o i o -> e i -> m o (e o)
applySubst substFrag x = do
  scope <- getScope
  return $
    flip runReader scope $ runScopeReaderT $
      flip runReaderT voidEnv $ runEnvReaderT $
        withEmptyRenamer $ extendEnv substFrag $ substE x

applyAbs :: ( Typeable s, InjectableE s, Typeable val, InjectableE val
            , ScopeReader m, BindsOneName b s, SubstE (SubstVal s val) e)
         => Abs b e n -> val n -> m n (e n)
applyAbs (Abs b body) x = applySubst (b@>SubstVal x) body

applyNaryAbs :: ( Typeable s, InjectableE s, Typeable val, InjectableE val
                , ScopeReader m, BindsNameList b s, SubstE (SubstVal s val) e
                , SubstB (SubstVal s val) b)
             => Abs b e n -> [val n] -> m n (e n)
applyNaryAbs (Abs bs body) xs = applySubst (bs @@> map SubstVal xs) body

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

lookupBindingsVal :: Bindings n -> Name s n -> s n
lookupBindingsVal (Bindings m) v = fromIdE $ lookupNameMap m v

lookupBindings :: Typeable s => BindingsReader m => Name s n -> m n (s n)
lookupBindings v = flip lookupBindingsVal v <$> getBindings

appendScope :: Scope n -> ScopeFrag n l -> Scope l
appendScope (Scope s1) (ScopeFrag s2) =
  Scope $ extendNameSet s1 s2

appendBindings :: Bindings n -> BindingsFrag n l -> Bindings l
appendBindings (Bindings m1) (BindingsFrag m2) =
  Bindings $ extendNameMap (injectNames (nameMapNames m2) m1) m2

bindingsAsScope :: Bindings n -> Scope n
bindingsAsScope (Bindings m) = Scope $ nameMapNames m

bindingsFragAsScopeFrag :: BindingsFrag n l -> ScopeFrag n l
bindingsFragAsScopeFrag (BindingsFrag m) = ScopeFrag $ nameMapNames m


-- TODO: we ought to make `ScopeFrag` a category, but it's tricky because
-- we require the `Distinct` constraint to make the identity fragment.
emptyScopeFrag :: Distinct n => ScopeFrag n n
emptyScopeFrag = ScopeFrag emptyNameSetFrag

concatScopeFrags :: ScopeFrag n1 n2 -> ScopeFrag n2 n3 -> ScopeFrag n1 n3
concatScopeFrags (ScopeFrag s1) (ScopeFrag s2) = ScopeFrag $ concatNameSets s1 s2

infixl 9 !
(!) :: Env v i o -> Name s i -> v s o
(!) (Env f frag) name =
  case lookupEnvFrag (EnvFrag frag) name of
    Left name' -> f name'
    Right val -> val

infixl 1 <>>
(<>>) :: Env v i o -> EnvFrag v i i' o -> Env v i' o
(<>>) (Env f frag) (EnvFrag frag') = Env f $ concatNameMaps frag frag'

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

type ScopeReader2      (m::MonadKind2) = forall (n::S). ScopeReader      (m n)
type ScopeExtender2    (m::MonadKind2) = forall (n::S). ScopeExtender    (m n)

type BindingsReader2   (m::MonadKind2) = forall (n::S). BindingsReader   (m n)
type BindingsExtender2 (m::MonadKind2) = forall (n::S). BindingsExtender (m n)

-- -- === subst monad ===

-- Only alllows non-trivial substitution with names that match the parameter
-- `sMatch`. For example, this lets us substitute ordinary variables in Core
-- with Atoms, while ensuring that things like data def names only get renamed.
data SubstVal (sMatch::E) (atom::E) (s::E) (n::S) where
  SubstVal :: atom n   -> SubstVal s      atom s n
  Rename   :: Name s n -> SubstVal sMatch atom s n

withFreshM :: (ScopeReader m, ScopeExtender m, Typeable s, InjectableE s)
           => (forall o'. NameBinder s o o' -> m o' a)
           -> m o a
withFreshM cont = do
  Scope m <- getScope
  withFresh m \b' -> do
    extendScope (ScopeFrag (singletonNameSet b')) $
      cont b'

-- -- === alpha-renaming-invariant equality checking ===

type AlphaEq e = AlphaEqE e  :: Constraint

-- TODO: consider generalizing this to something that can also handle e.g.
-- unification and type checking with some light reduction
class ( forall i1 i2 o. Monad (m i1 i2 o)
      , forall i1 i2 o. MonadErr (m i1 i2 o)
      , forall i1 i2 o. MonadFail (m i1 i2 o)
      , forall i1 i2.   ScopeReader (m i1 i2)
      , forall i1 i2.   ScopeExtender (m i1 i2))
      => ZipEnvReader (m :: S -> S -> S -> * -> *) where
  lookupZipEnvFst :: Name s i1 -> m i1 i2 o (Name s o)
  lookupZipEnvSnd :: Name s i2 -> m i1 i2 o (Name s o)

  extendZipEnvFst :: EnvFrag Name i1 i1' o -> m i1' i2  o r -> m i1 i2 o r
  extendZipEnvSnd :: EnvFrag Name i2 i2' o -> m i1  i2' o r -> m i1 i2 o r

  withEmptyZipEnv :: m o o o a -> m i1 i2 o a

class AlphaEqE (e::E) where
  alphaEqE :: ZipEnvReader m => e i1 -> e i2 -> m i1 i2 o ()

class AlphaEqB (b::B) where
  withAlphaEqB :: ZipEnvReader m => b i1 i1' -> b i2 i2'
               -> (forall o'. m i1' i2' o' a)
               ->             m i1  i2  o  a

checkAlphaEq :: (AlphaEqE e, MonadErr1 m, ScopeReader m)
             => e n -> e n -> m n ()
checkAlphaEq e1 e2 = do
  scope <- getScope
  liftEither $
    flip runReaderT scope $ runScopeReaderT $
      flip runReaderT (voidEnv, voidEnv) $ runZipEnvReaderT $
        withEmptyZipEnv $ alphaEqE e1 e2

instance Typeable s => AlphaEqE (Name s) where
  alphaEqE v1 v2 = do
    v1' <- lookupZipEnvFst v1
    v2' <- lookupZipEnvSnd v2
    unless (v1' == v2') zipErr

instance (InjectableE s, Typeable s) => AlphaEqB (NameBinder s) where
  withAlphaEqB b1 b2 cont = do
    withFreshM \b -> do
      let v = binderName b
      extendZipEnvFst (b1@>v) $ extendZipEnvSnd (b2@>v) $ cont

alphaEqTraversable :: (AlphaEqE e, Traversable f, Eq (f ()), ZipEnvReader m)
                   => f (e i1) -> f (e i2) -> m i1 i2 o ()
alphaEqTraversable f1 f2 = do
  let (struct1, vals1) = splitTraversable f1
  let (struct2, vals2) = splitTraversable f2
  unless (struct1 == struct2) zipErr
  zipWithM_ alphaEqE vals1 vals2
  where
    splitTraversable :: Traversable f => f a -> (f (), [a])
    splitTraversable xs = runWriter $ forM xs \x -> tell [x]

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

-- === ScopeReaderT transformer ===

newtype ScopeReaderT (m::MonadKind) (n::S) (a:: *) =
  ScopeReaderT {runScopeReaderT :: ReaderT (Scope n) m a}
  deriving (Functor, Applicative, Monad, MonadError err, MonadFail)

instance Monad m => ScopeReader (ScopeReaderT m) where
  getScope = ScopeReaderT ask

instance Monad m => ScopeExtender (ScopeReaderT m) where
  extendScope frag (ScopeReaderT m) =
    ScopeReaderT $ withReaderT (\scope -> appendScope scope frag) m

instance Monad m => BindingsExtender (ScopeReaderT m) where
  extendBindings frag = extendScope (bindingsFragAsScopeFrag frag)

-- === BindingsReaderT transformer ===

newtype BindingsReaderT (m::MonadKind) (n::S) (a:: *) =
  BindingsReaderT {runBindingsReaderT :: ReaderT (Bindings n) m a }
  deriving (Functor, Applicative, Monad, MonadError err, MonadFail)

instance Monad m => BindingsReader (BindingsReaderT m) where
  getBindings = BindingsReaderT ask

instance Monad m => BindingsExtender (BindingsReaderT m) where
  extendBindings frag (BindingsReaderT m) =
    BindingsReaderT $ withReaderT (\scope -> appendBindings scope frag) m

instance Monad m => ScopeReader (BindingsReaderT m) where
  getScope = bindingsAsScope <$> getBindings

-- === EnvReaderT transformer ===

newtype EnvReaderT (v::E->E) (m::MonadKind1) (i::S) (o::S) (a:: *) =
  EnvReaderT { runEnvReaderT :: ReaderT (Env v i o) (m o) a }
  deriving (Functor, Applicative, Monad, MonadError err, MonadFail)

instance Monad1 m => EnvReader v (EnvReaderT v m) where
  lookupEnv name = EnvReaderT $ (! name) <$> ask

instance Monad1 m => EnvExtender v (EnvReaderT v m) where
  extendEnv frag (EnvReaderT cont) =
    EnvReaderT $ withReaderT (\env -> env <>> frag) cont

instance Monad1 m => Renamer (EnvReaderT (SubstVal s val) m) where
  withEmptyRenamer (EnvReaderT cont) = EnvReaderT $ withReaderT (const $ newEnv Rename) cont
  extendRenamer (EnvFrag frag) (EnvReaderT cont) =
    EnvReaderT $ withReaderT (<>>frag') cont
    where frag' = EnvFrag $ fmapNameMap (\_ v -> Rename v) frag

instance Monad1 m => Renamer (EnvReaderT Name m) where
  withEmptyRenamer (EnvReaderT cont) = EnvReaderT $ withReaderT (const $ newEnv id) cont
  extendRenamer frag (EnvReaderT cont) =
    EnvReaderT $ withReaderT (<>>frag) cont

instance ScopeReader m => ScopeReader (EnvReaderT v m i) where
  getScope = EnvReaderT $ lift getScope

instance BindingsReader m => BindingsReader (EnvReaderT v m i) where
  getBindings = EnvReaderT $ lift getBindings

-- The rest are boilerplate but this one is a bit interesting. When we extend
-- the scope we have to inject the env, `Env i o` into the new scope, to become
-- `Env i oNew `
instance (InjectableV v, ScopeReader m, ScopeExtender m)
         => ScopeExtender (EnvReaderT v m i) where
  extendScope frag (EnvReaderT (ReaderT cont)) = EnvReaderT $ ReaderT \env ->
    extendScope frag do
      env' <- injectM frag env
      cont env'

instance (InjectableV v, ScopeReader m, BindingsExtender m)
         => BindingsExtender (EnvReaderT v m i) where
  extendBindings frag (EnvReaderT (ReaderT cont)) = EnvReaderT $ ReaderT \env ->
    extendBindings frag do
      env' <- injectM frag env
      cont env'

-- === ZipEnvReaderT transformer ===

newtype ZipEnvReaderT (m::MonadKind1) (i1::S) (i2::S) (o::S) (a:: *) =
  ZipEnvReaderT { runZipEnvReaderT :: ReaderT (ZipEnv i1 i2 o) (m o) a }
  deriving (Functor, Applicative, Monad, MonadError err, MonadFail)

type ZipEnv i1 i2 o = (Env Name i1 o, Env Name i2 o)

instance ScopeReader m => ScopeReader (ZipEnvReaderT m i1 i2) where
  getScope = ZipEnvReaderT $ lift getScope

instance (ScopeReader m, ScopeExtender m)
         => ScopeExtender (ZipEnvReaderT m i1 i2) where
  extendScope frag (ZipEnvReaderT (ReaderT cont)) =
    ZipEnvReaderT $ ReaderT \(env1, env2) -> do
      extendScope frag do
        env1' <- injectM frag env1
        env2' <- injectM frag env2
        cont (env1', env2')

instance (Monad1 m, ScopeReader m, ScopeExtender m, MonadErr1 m, MonadFail1 m)
         => ZipEnvReader (ZipEnvReaderT m) where

  lookupZipEnvFst v = ZipEnvReaderT $ (!v) <$> fst <$> ask
  lookupZipEnvSnd v = ZipEnvReaderT $ (!v) <$> snd <$> ask

  extendZipEnvFst frag (ZipEnvReaderT cont) = ZipEnvReaderT $ withReaderT (onFst (<>>frag)) cont
  extendZipEnvSnd frag (ZipEnvReaderT cont) = ZipEnvReaderT $ withReaderT (onSnd (<>>frag)) cont

  withEmptyZipEnv (ZipEnvReaderT cont) =
    ZipEnvReaderT $ withReaderT (const (newEnv id, newEnv id)) cont

-- === Name traverser ===

-- Similar to `EnvReaderT Name`, but lookup up a name may produce effects. We
-- use this, with `Either Err`, for projecting expressions into a shallower name
-- space.

data NameTraverserEnv (m::MonadKind) (i::S) (o::S) where
  NameTraverserEnv :: (forall s. Name s hidden -> m (Name s o))  -- fallback function (with effects)
                   -> NameMap Name (hidden:=>:i) o               -- names first looked up here
                   -> NameTraverserEnv m i o

newNameTraverserEnv :: (forall s. Name s i -> m (Name s o)) -> NameTraverserEnv m i o
newNameTraverserEnv f = NameTraverserEnv f emptyNameMap

extendNameTraverserEnv :: NameTraverserEnv m i o -> EnvFrag Name i i' o -> NameTraverserEnv m i' o
extendNameTraverserEnv (NameTraverserEnv f frag) (EnvFrag frag') =
  NameTraverserEnv f (concatNameMaps frag frag')

newtype NameTraverserT (m::MonadKind) (i::S) (o::S) (a:: *) =
  NameTraverserT {
    runNameTraverserT ::
        ReaderT (NameTraverserEnv m i o) (ScopeReaderT m o) a}
  deriving (Functor, Applicative, Monad, MonadError err, MonadFail)

instance InjectableE (NameTraverserEnv m i) where
  injectionProofE _ _ = undefined

instance Monad m => ScopeReader (NameTraverserT m i) where
  getScope = NameTraverserT $ lift $ getScope

instance Monad m => ScopeExtender (NameTraverserT m i) where
  extendScope frag (NameTraverserT (ReaderT cont)) = NameTraverserT $ ReaderT \env ->
    extendScope frag do
      env' <- injectM frag env
      cont env'

instance Monad m => Renamer (NameTraverserT m) where
  withEmptyRenamer (NameTraverserT cont) =
    NameTraverserT $ withReaderT (const $ newNameTraverserEnv return) cont
  extendRenamer frag (NameTraverserT cont) =
    NameTraverserT $ withReaderT (`extendNameTraverserEnv` frag) cont

instance Monad m => EnvReader Name (NameTraverserT m) where
  lookupEnv name = NameTraverserT do
    env <- ask
    lift $ ScopeReaderT $ lift $ lookupNameTraversalEnv env name

lookupNameTraversalEnv :: Monad m => NameTraverserEnv m i o -> Name s i -> m (Name s o)
lookupNameTraversalEnv (NameTraverserEnv f frag) name =
  case lookupEnvFrag (EnvFrag frag) name of
    Left name' -> f name'
    Right val -> return val

-- === monadish thing for computations that produce names ===

class NameGen (m :: E -> S -> *) where
  returnG :: e n -> m e n
  bindG   :: m e n -> (forall l. e l -> m e' l) -> m e' n

newtype NameGenT (m::MonadKind1) (e::E) (n::S) =
  NameGenT { runNameGenT :: m n (Abs ScopeFrag e n) }

instance (ScopeReader m, ScopeExtender m, Monad1 m) => NameGen (NameGenT m) where
  returnG e = NameGenT $ do
    withDistinct do
      let frag = ScopeFrag emptyNameSetFrag
      return (Abs frag e)
  bindG (NameGenT m) f = NameGenT do
    Abs s  e  <- m
    Abs s' e' <- extendScope s $ runNameGenT $ f e
    return $ Abs (concatScopeFrags s s') e'

-- === monadish thing for computations that produce names and substitutions ===

-- TODO: Here we actually just want an indexed monad `m :: S -> S -> * -> *`
-- with a bind like `>>>= :: m i i' a -> (a -> m i' i'' b) -> m i i'' b`. But we
-- also want it to be an instance of `NameGen`, so we end up with all this
-- `forall o' ...` business. Can we separate them better?
-- TODO: Is this whole thing just getting too silly? Maybe it wouldn't be the
-- end of the world if we were forced to sprinkle some explicit recursive helper
-- functions in our passes instead of trying to treat everything as some
-- generalized traversal.
class (forall i. NameGen (m i i)) => SubstGen (m :: S -> S -> E -> S -> *) where
  returnSG :: e o -> m i i e o
  bindSG   :: m i i' e o -> (forall o'. e o' -> m i' i'' e' o') -> m i i'' e' o

traverseNestSG :: SubstGen m
               => (forall ii ii' oo. b ii ii' -> m ii ii' (b oo) oo)
               -> Nest b i i'
               -> m i i' (Nest b o) o
traverseNestSG _ Empty = returnSG Empty
traverseNestSG f (Nest b bs) =
  f b `bindSG` \b' ->
    traverseNestSG f bs `bindSG` \bs' ->
      returnSG $ Nest b' bs'

newtype SubstGenT (m::MonadKind2) (i::S) (i'::S) (e::E) (o::S) =
  SubstGenT { runSubstGenT :: m i o (Abs ScopeFrag (PairE (EnvFrag Name i i') e) o) }

instance (ScopeReader2 m, ScopeExtender2 m, Renamer m, Monad2 m)
         => NameGen (SubstGenT m i i) where
  returnG = returnSG
  bindG = bindSG

instance (ScopeReader2 m, ScopeExtender2 m, Renamer m, Monad2 m)
         => SubstGen (SubstGenT m) where
  returnSG e = SubstGenT $ withDistinct do
    return (Abs emptyScopeFrag (PairE emptyEnvFrag e))
  bindSG (SubstGenT m) f = SubstGenT do
    Abs s (PairE env e) <- m
    extendScope s $ extendRenamer env do
      Abs s' (PairE env' e') <- runSubstGenT $ f e
      envInj <- extendScope s' $ injectM s' env
      return $ Abs (concatScopeFrags s s') $ PairE (envInj <.> env')  e'

liftSG :: ScopeReader2 m => m i o a -> (a -> SubstGenT m i i' e o) -> SubstGenT m i i' e o
liftSG m cont = SubstGenT do
  ans <- m
  runSubstGenT $ cont ans

-- === instances ===

instance InjectableV v => InjectableE (Env v i) where
  injectionProofE fresh (Env f m) =
    Env (\name -> withNameClasses name $ injectionProofE fresh $ f name)
        (injectionProofE fresh m)

instance InjectableV v => InjectableE (EnvFrag v i i') where
  injectionProofE fresh (EnvFrag m) = EnvFrag (injectionProofE fresh m)

instance InjectableE atom => InjectableE (SubstVal (sMatch::E) (atom::E) (s::E)) where
  injectionProofE fresh substVal = case substVal of
    Rename name  -> Rename   $ injectionProofE fresh name
    SubstVal val -> SubstVal $ injectionProofE fresh val

instance (InjectableB b, InjectableE e) => InjectableE (Abs b e) where
  injectionProofE fresh (Abs b body) =
    injectionProofB fresh b \fresh' b' ->
      Abs b' (injectionProofE fresh' body)

instance (SubstB v b, SubstE v e) => SubstE v (Abs b e) where
  substE (Abs b body) = do
    withSubstB b \b' -> Abs b' <$> substE body

instance (BindsNames b1, BindsNames b2) => BindsNames (NestPair b1 b2) where
  toExtVal (NestPair b1 b2) = toExtVal b1 >>> toExtVal b2

instance (InjectableB b1, InjectableB b2) => InjectableB (NestPair b1 b2) where
  injectionProofB fresh (NestPair b1 b2) cont =
    injectionProofB fresh b1 \fresh' b1' ->
      injectionProofB fresh' b2 \fresh'' b2' ->
        cont fresh'' (NestPair b1' b2')

instance (SubstB v b1, SubstB v b2) => SubstB v (NestPair b1 b2) where
  substB (NestPair b1 b2) =
    substB b1 `bindSG` \b1' ->
      substB b2 `bindSG` \b2' ->
        returnSG $ NestPair b1' b2'

instance BindsNames b => BindsNames (Nest b) where
  toExtVal Empty = id
  toExtVal (Nest b rest) = toExtVal b >>> toExtVal rest

instance InjectableB b => InjectableB (Nest b) where
  injectionProofB fresh Empty cont = cont fresh Empty
  injectionProofB fresh (Nest b rest) cont =
    injectionProofB fresh b \fresh' b' ->
      injectionProofB fresh' rest \fresh'' rest' ->
        cont fresh'' (Nest b' rest')

instance SubstB v b => SubstB v (Nest b) where
  substB nest = case nest of
    Empty -> returnSG Empty
    Nest b rest ->
      substB b `bindSG` \b' ->
        substB rest `bindSG` \rest' ->
          returnSG $ Nest b' rest'

instance InjectableE UnitE where
  injectionProofE _ UnitE = UnitE

instance SubstE v UnitE where
  substE UnitE = return UnitE

instance InjectableE e => InjectableE (IdE e) where
  injectionProofE fresh (IdE e) = IdE $ injectionProofE fresh e

instance SubstE v e => SubstE v (IdE e) where
  substE (IdE e) = IdE <$> substE e

instance (InjectableE e1, InjectableE e2) => InjectableE (PairE e1 e2) where
  injectionProofE fresh (PairE e1 e2) =
    PairE (injectionProofE fresh e1) (injectionProofE fresh e2)

instance (SubstE v e1, SubstE v e2) => SubstE v (PairE e1 e2) where
  substE (PairE x y) =
    PairE <$> substE x <*> substE y

instance InjectableE e => InjectableE (ListE e) where
  injectionProofE fresh (ListE xs) = ListE $ map (injectionProofE fresh) xs

instance SubstE v e => SubstE v (ListE e) where
  substE (ListE xs) = ListE <$> mapM substE xs

instance (forall n' l. Show (b n' l), forall n'. Show (body n')) => Show (Abs b body n) where
  show (Abs b body) = "(Abs " <> show b <> " " <> show body <> ")"

instance (forall n' l'. Show (b n' l')) => Show (Nest b n l) where
  show Empty = ""
  show (Nest b rest) = "(Nest " <> show b <> " in " <> show rest <> ")"

instance (PrettyB b) => Pretty (Nest b n l) where
  pretty Empty = ""
  pretty (Nest b rest) = "(Nest " <> pretty b <> " in " <> pretty rest <> ")"

instance (PrettyB b, PrettyE e) => Pretty (Abs b e n) where
  pretty (Abs b body) = "(Abs " <> pretty b <> " " <> pretty body <> ")"

instance Pretty a => Pretty (LiftE a n) where
  pretty (LiftE x) = pretty x

instance Pretty (UnitE n) where
  pretty UnitE = ""
