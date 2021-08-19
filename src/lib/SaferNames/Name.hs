-- Copyright 2021 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE EmptyCase #-}

module SaferNames.Name (
  Name (..), RawName, S (..), C (..), Env, (<.>), EnvFrag (..), NameBinder (..),
  EnvReader (..), EnvGetter (..), EnvExtender (..),
  Renamer (..), Distinct, WithDistinct (..),
  NameFunction (..), emptyNameFunction,
  WithScopeFrag (..), WithScopeSubstFrag (..),
  ScopeReader (..), ScopeExtender (..),
  Scope, ScopeFrag (..), SubstE (..), SubstB (..),
  E, B, V, HasNamesE, HasNamesB, BindsNames (..), RecEnvFrag (..),
  BindsOneName (..), BindsNameList (..), NameColorRep (..),
  Abs (..), Nest (..), PairB (..), UnitB (..),
  IsVoidS (..), UnitE (..), VoidE, PairE (..), ListE (..), ComposeE (..),
  EitherE (..), LiftE (..), EqE, EqB, OrdE, OrdB,
  EitherB (..), BinderP (..),
  LiftB, pattern LiftB,
  MaybeE, pattern JustE, pattern NothingE, MaybeB, pattern JustB, pattern NothingB,
  fromConstAbs, toConstAbs, PrettyE, PrettyB, ShowE, ShowB,
  runScopeReaderT, ScopeReaderT (..), EnvReaderT (..),
  MonadKind, MonadKind1, MonadKind2,
  Monad1, Monad2, MonadErr1, MonadErr2, MonadFail1, MonadFail2,
  ScopeReader2, ScopeExtender2,
  applyAbs, applyNaryAbs, ZipEnvReader (..), alphaEqTraversable,
  checkAlphaEq, AlphaEq, AlphaEqE (..), AlphaEqB (..), ConstE (..),
  InjectableE (..), InjectableB (..), InjectableV, InjectionCoercion,
  withFreshM, withFreshLike, inject, injectM, (!), (<>>), emptyEnv, envAsScope,
  EmptyAbs, pattern EmptyAbs, SubstVal (..), lookupEnv,
  NameGen (..), fmapG, NameGenT (..), SubstGen (..), SubstGenT (..), withSubstB,
  liftSG, forEachNestItem, forEachNestItemSG, substM, ScopedEnvReader, liftScopedEnvReader,
  HasNameHint (..), NameHint, HasNameColor (..), CommonHint (..), NameColor (..),
  GenericE (..), GenericB (..), ColorsEqual (..), ColorsNotEqual (..),
  EitherE1, EitherE2, EitherE3, EitherE4, EitherE5,
  pattern Case0, pattern Case1, pattern Case2, pattern Case3, pattern Case4
  ) where

import Prelude hiding (id, (.))
import Control.Category
import Control.Monad.Identity
import Control.Monad.Except hiding (Except)
import Control.Monad.Reader
import Control.Monad.Writer.Strict
import Data.String (fromString)
import Data.Text.Prettyprint.Doc  hiding (nest)
import GHC.Exts (Constraint)
import GHC.Generics (Generic (..), Rep)
import Data.Store (Store)

import SaferNames.NameCore
import Util (zipErr, onFst, onSnd)
import Err

-- === environments and scopes ===

data NameFunction v i o where
  NameFunction
    :: (forall c. Name c hidden -> v c o)
    -> EnvFrag v hidden i o
    -> NameFunction v i o

newNameFunction :: (forall c. Name c i -> v c o) -> NameFunction v i o
newNameFunction f = NameFunction f emptyEnv

emptyNameFunction :: NameFunction v VoidS o
emptyNameFunction = newNameFunction absurdNameFunction

-- === monadic type classes for reading and extending envs and scopes ===

data WithDistinct e n where
  Distinct :: Distinct n => e n -> WithDistinct e n

class Monad1 m => ScopeReader (m::MonadKind1) where
  getScope :: m n (WithDistinct Scope n)

class ScopeReader m => ScopeExtender (m::MonadKind1) where
  extendScope :: Distinct l => ScopeFrag n l -> m l r -> m n r

class Monad2 m => EnvReader (v::V) (m::MonadKind2) | m -> v where
   lookupEnvM :: Name c i -> m i o (v c o)

class EnvReader v m => EnvGetter (v::V) (m::MonadKind2) | m -> v where
   getEnv :: m i o (NameFunction v i o)

class Monad2 m => EnvExtender (v::V) (m::MonadKind2) | m -> v where
  extendEnv :: EnvFrag v i i' o -> m i' o r -> m i o r

class Monad2 m => Renamer (m::MonadKind2) where
  dropSubst :: m o o r -> m i o r
  extendRenamer :: EnvFrag Name i i' o -> m i' o r -> m i o r

-- === common scoping patterns ===

data Abs (binder::B) (body::E) (n::S) where
  Abs :: binder n l -> body l -> Abs binder body n
deriving instance (ShowB b, ShowE e) => Show (Abs b e n)

data BinderP (b::B) (ann::E) (n::S) (l::S) =
  (:>) (b n l) (ann n)
  deriving (Show, Generic)

type EmptyAbs b = Abs b UnitE :: E
pattern EmptyAbs :: b n l -> EmptyAbs b n
pattern EmptyAbs bs = Abs bs UnitE

-- wraps an EnvFrag as a kind suitable for SubstB instances etc
newtype RecEnvFrag (v::V) n l = RecEnvFrag { fromRecEnvFrag :: EnvFrag v n l l }

-- Proof object that a given scope is void
data IsVoidS n where
  IsVoidS :: IsVoidS VoidS

-- === Injections and projections ===

class BindsNames (b :: B) where
  toScopeFrag :: b n l -> ScopeFrag n l

  default toScopeFrag :: (GenericB b, BindsNames (RepB b)) => b n l -> ScopeFrag n l
  toScopeFrag b = toScopeFrag $ fromB b

instance BindsNames ScopeFrag where
  toScopeFrag s = s

inject :: BindsNames b => InjectableE e => Distinct l => b n l -> e n -> e l
inject ext x = injectNames (toScopeFrag ext) x

-- like inject, but uses the ScopeReader monad for its `Distinct` proof
injectM :: ScopeReader m => BindsNames b => InjectableE e => b n l -> e n -> m l (e l)
injectM b e = do
  Distinct _ <- getScope
  return $ inject b e

traverseNames :: (Monad m, HasNamesE e)
              => Distinct o => Scope o -> (forall c. Name c i -> m (Name c o)) -> e i -> m (e o)
traverseNames scope f e =
  runScopeReaderT scope $
    flip runReaderT (newNameTraverserEnv f) $
       runNameTraverserT $
         substE e

-- This may become expensive. It traverses the body of the Abs to check for
-- leaked variables.
fromConstAbs :: (ScopeReader m, MonadErr1 m, BindsNames b, HasNamesE e)
             => Abs b e n -> m n (e n)
fromConstAbs (Abs b e) = do
  Distinct scope <- getScope
  liftEither $ traverseNames scope (tryProjectName $ toScopeFrag b) e

tryProjectName :: MonadErr m => ScopeFrag n l -> Name c l -> m (Name c n)
tryProjectName names name =
  case projectName names name of
    Left name' -> return name'
    Right _    -> throw EscapedNameErr (pprint name)

toConstAbs :: (InjectableE e, ScopeReader m)
           => NameColorRep c -> e n -> m n (Abs (NameBinder c) e n)
toConstAbs rep body = do
  Distinct scope <- getScope
  withFresh ("ignore"::NameHint) rep scope \b -> do
    return $ Abs b $ inject b body

-- === type classes for traversing names ===

class SubstE (v::V) (e::E) where
  -- TODO: can't make an alias for these constraints because of impredicativity
  substE :: ( ScopeReader2 m, ScopeExtender2 m , EnvReader v m, Renamer m)
         => e i -> m i o (e o)

  default substE :: ( GenericE e, SubstE v (RepE e)
                    , ScopeReader2 m, ScopeExtender2 m , EnvReader v m, Renamer m )
                 => e i -> m i o (e o)
  substE e = toE <$> substE (fromE e)

class SubstB (v::V) (b::B) where
  substB :: ( ScopeReader2 m, ScopeExtender2 m , EnvReader v m, Renamer m)
         => b i i'
         -> SubstGenT m i i' (b o) o

  default substB :: ( GenericB b, SubstB v (RepB b)
                    , ScopeReader2 m, ScopeExtender2 m , EnvReader v m, Renamer m)
                  => b i i'
                  -> SubstGenT m i i' (b o) o
  substB b = substB (fromB b) `bindSG` \b' -> returnSG $ toB b'

type HasNamesE = SubstE Name
type HasNamesB = SubstB Name

instance SubstE Name (Name c) where
  substE name = lookupEnvM name

instance SubstB v (NameBinder c) where
  substB b = SubstGenT do
    Distinct names <- getScope
    let rep = getNameColorRep $ nameBinderName b
    withFresh (getNameHint b) rep names \b' -> do
      let frag = singletonScope b'
      return $ WithScopeSubstFrag frag (b @> binderName b') b'


-- Like SubstE, but with fewer requirements for the monad
substM :: ( InjectableE val, EnvGetter (SubstVal s val) m
          , ScopeReader2 m, SubstE (SubstVal s val) e)
       => e i -> m i o (e o)
substM e = liftScopedEnvReader $ substE e

withSubstB :: (SubstB v b, ScopeReader2 m, ScopeExtender2 m , EnvReader v m, Renamer m)
           => b i i'
           -> (forall o'. b o o' -> m i' o' r)
           -> m i o r
withSubstB b cont = do
  WithScopeSubstFrag scopeFrag substFrag b' <- runSubstGenT $ substB b
  extendScope scopeFrag $ extendRenamer substFrag $ cont b'

-- === various E-kind and B-kind versions of standard containers and classes ===

type PrettyE  e = (forall (n::S)       . Pretty (e n  )) :: Constraint
type PrettyB b  = (forall (n::S) (l::S). Pretty (b n l)) :: Constraint

type ShowE e = (forall (n::S)       . Show (e n  )) :: Constraint
type ShowB b = (forall (n::S) (l::S). Show (b n l)) :: Constraint

type EqE e = (forall (n::S)       . Eq (e n  )) :: Constraint
type EqB b = (forall (n::S) (l::S). Eq (b n l)) :: Constraint

type OrdE e = (forall (n::S)       . Ord (e n  )) :: Constraint
type OrdB b = (forall (n::S) (l::S). Ord (b n l)) :: Constraint

data UnitE (n::S) = UnitE
     deriving (Show, Eq, Generic)

data VoidE (n::S)
     deriving (Generic)

data PairE (e1::E) (e2::E) (n::S) = PairE (e1 n) (e2 n)
     deriving (Show, Eq, Generic)

data EitherE (e1::E) (e2::E) (n::S) = LeftE (e1 n) | RightE (e2 n)
     deriving (Show, Eq, Generic)

newtype ListE (e::E) (n::S) = ListE { fromListE :: [e n] }
        deriving (Show, Eq, Generic)

newtype LiftE (a:: *) (n::S) = LiftE { fromLiftE :: a }
        deriving (Show, Eq, Generic)

newtype ComposeE (f :: * -> *) (e::E) (n::S) =
  ComposeE (f (e n))
  deriving (Show, Eq, Generic)

data UnitB (n::S) (l::S) where
  UnitB :: UnitB n n
deriving instance Show (UnitB n l)

data PairB (b1::B) (b2::B) (n::S) (l::S) where
  PairB :: b1 n l' -> b2 l' l -> PairB b1 b2 n l
deriving instance (ShowB b1, ShowB b2) => Show (PairB b1 b2 n l)

data EitherB (b1::B) (b2::B) (n::S) (l::S) =
   LeftB  (b1 n l)
 | RightB (b2 n l)
   deriving (Show, Eq, Generic)

-- The constant function of kind `V`
newtype ConstE (const::E) (ignored::C) (n::S) = ConstE (const n)
        deriving (Show, Eq, Generic)

type MaybeE e = EitherE e UnitE

pattern JustE :: e n -> MaybeE e n
pattern JustE e = LeftE e

pattern NothingE :: MaybeE e n
pattern NothingE = RightE UnitE

type MaybeB b = EitherB b UnitB

pattern JustB :: b n l -> MaybeB b n l
pattern JustB b = LeftB b

pattern NothingB :: MaybeB b n n
pattern NothingB = RightB UnitB

type LiftB (e::E) = BinderP UnitB e :: B

pattern LiftB :: e n -> LiftB e n n
pattern LiftB e = UnitB :> e

-- -- === various convenience utilities ===

infixr 7 @>
class BindsOneName (b::B) (c::C) | b -> c where
  (@>) :: b i i' -> v c o -> EnvFrag v i i' o
  binderName :: b i i' -> Name c i'

instance BindsNames (NameBinder c) where
  toScopeFrag b = singletonScope b

instance BindsOneName (NameBinder c) c where
  b @> x = singletonEnv b x
  binderName = nameBinderName

instance BindsOneName b c => BindsOneName (BinderP b ann) c where
  (b:>_) @> x = b @> x
  binderName (b:>_) = binderName b

infixr 7 @@>
class BindsNameList (b::B) (c::C) | b -> c where
  (@@>) :: b i i' -> [v c o] -> EnvFrag v i i' o

instance BindsOneName b c => BindsNameList (Nest b) c where
  (@@>) Empty [] = emptyEnv
  (@@>) (Nest b rest) (x:xs) = b@>x <.> rest@@>xs
  (@@>) _ _ = error "length mismatch"

applySubst :: (ScopeReader m, SubstE (SubstVal c val) e, InjectableE val)
           => EnvFrag (SubstVal c val) o i o -> e i -> m o (e o)
applySubst substFrag x = do
  Distinct scope <- getScope
  return $ runIdentity $ runScopeReaderT scope $
    flip runReaderT (emptyNameFunction) $ runEnvReaderT $
      dropSubst $ extendEnv substFrag $ substE x

applyAbs :: (InjectableE val , ScopeReader m, BindsOneName b c, SubstE (SubstVal c val) e)
         => Abs b e n -> val n -> m n (e n)
applyAbs (Abs b body) x = applySubst (b@>SubstVal x) body

applyNaryAbs :: ( InjectableE val, ScopeReader m, BindsNameList b c, SubstE (SubstVal c val) e
                , SubstB (SubstVal c val) b)
             => Abs b e n -> [val n] -> m n (e n)
applyNaryAbs (Abs bs body) xs = applySubst (bs @@> map SubstVal xs) body

infixl 9 !
(!) :: NameFunction v i o -> Name c i -> v c o
(!) (NameFunction f env) name =
  case lookupEnvFragProjected env name of
    Left name' -> f name'
    Right val -> val

infixl 1 <>>
(<>>) :: NameFunction v i o -> EnvFrag v i i' o -> NameFunction v i' o
(<>>) (NameFunction f frag) frag' = NameFunction f $ frag <.> frag'

lookupEnvFragProjected :: EnvFrag v i i' o -> Name c i' -> Either (Name c i) (v c o)
lookupEnvFragProjected m name =
  case projectName (envAsScope m) name of
    Left  name' -> Left name'
    Right name' -> Right $ lookupEnvFrag m name'

forEachNestItem :: Monad m
                => Nest b i i'
                -> (forall ii ii'. b ii ii' -> m (b' ii ii'))
                -> m (Nest b' i i')
forEachNestItem Empty _ = return Empty
forEachNestItem (Nest b rest) f = Nest <$> f b <*> forEachNestItem rest f

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

-- === subst monad ===

-- Only alllows non-trivial substitution with names that match the parameter
-- `cMatch`. For example, this lets us substitute ordinary variables in Core
-- with Atoms, while ensuring that things like data def names only get renamed.
data SubstVal (cMatch::C) (atom::E) (c::C) (n::S) where
  SubstVal :: atom n   -> SubstVal c      atom c n
  Rename   :: Name c n -> SubstVal cMatch atom c n

withFreshM :: (ScopeReader m, ScopeExtender m, HasNameHint hint)
           => hint
           -> NameColorRep c
           -> (forall o'. NameBinder c o o' -> m o' a)
           -> m o a
withFreshM hint rep cont = do
  Distinct m <- getScope
  withFresh (getNameHint hint) rep m \b' -> do
    extendScope (singletonScope b') $
      cont b'

withFreshLike
  :: (ScopeReader m, ScopeExtender m, HasNameHint hint, HasNameColor hint c)
  => hint
  -> (forall o'. NameBinder c o o' -> m o' a)
  -> m o a
withFreshLike hint cont =
  withFreshM (getNameHint hint) (getNameColor hint) cont

data ColorsEqual (a::C) (b::C) where
  ColorsEqual :: ColorsEqual a a

class ColorsNotEqual a b where
  notEqProof :: ColorsEqual a b -> r

instance (ColorsNotEqual cMatch c)
         => (SubstE (SubstVal cMatch atom) (Name c)) where
  substE name = do
    substVal <- lookupEnvM name
    case substVal of
      Rename name' -> return name'
      SubstVal _ -> notEqProof (ColorsEqual :: ColorsEqual c cMatch)

instance ColorsNotEqual AtomNameC DataDefNameC where notEqProof = \case
instance ColorsNotEqual AtomNameC ClassNameC   where notEqProof = \case

-- === alpha-renaming-invariant equality checking ===

type AlphaEq e = AlphaEqE e  :: Constraint

-- TODO: consider generalizing this to something that can also handle e.g.
-- unification and type checking with some light reduction
class ( forall i1 i2 o. Monad (m i1 i2 o)
      , forall i1 i2 o. MonadErr (m i1 i2 o)
      , forall i1 i2 o. MonadFail (m i1 i2 o)
      , forall i1 i2.   ScopeReader (m i1 i2)
      , forall i1 i2.   ScopeExtender (m i1 i2))
      => ZipEnvReader (m :: S -> S -> S -> * -> *) where
  lookupZipEnvFst :: Name c i1 -> m i1 i2 o (Name c o)
  lookupZipEnvSnd :: Name c i2 -> m i1 i2 o (Name c o)

  extendZipEnvFst :: EnvFrag Name i1 i1' o -> m i1' i2  o r -> m i1 i2 o r
  extendZipEnvSnd :: EnvFrag Name i2 i2' o -> m i1  i2' o r -> m i1 i2 o r

  withEmptyZipEnv :: m o o o a -> m i1 i2 o a

class AlphaEqE (e::E) where
  alphaEqE :: ZipEnvReader m => e i1 -> e i2 -> m i1 i2 o ()

  default alphaEqE :: (GenericE e, AlphaEqE (RepE e), ZipEnvReader m)
                   => e i1 -> e i2 -> m i1 i2 o ()
  alphaEqE e1 e2 = fromE e1 `alphaEqE` fromE e2

class AlphaEqB (b::B) where
  withAlphaEqB :: ZipEnvReader m => b i1 i1' -> b i2 i2'
               -> (forall o'. m i1' i2' o' a)
               ->             m i1  i2  o  a

  default withAlphaEqB :: (GenericB b, AlphaEqB (RepB b), ZipEnvReader m)
                       => b i1 i1' -> b i2 i2'
                       -> (forall o'. m i1' i2' o' a)
                       ->             m i1  i2  o  a
  withAlphaEqB b1 b2 cont = withAlphaEqB (fromB b1) (fromB b2) $ cont

checkAlphaEq :: (AlphaEqE e, MonadErr1 m, ScopeReader m)
             => e n -> e n -> m n ()
checkAlphaEq e1 e2 = do
  Distinct scope <- getScope
  liftEither $
    runScopeReaderT scope $
      flip runReaderT (emptyNameFunction, emptyNameFunction) $ runZipEnvReaderT $
        withEmptyZipEnv $ alphaEqE e1 e2

instance AlphaEqE (Name c) where
  alphaEqE v1 v2 = do
    v1' <- lookupZipEnvFst v1
    v2' <- lookupZipEnvSnd v2
    unless (v1' == v2') zipErr

instance AlphaEqB (NameBinder c) where
  withAlphaEqB b1 b2 cont = do
    withFreshLike b1 \b -> do
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

instance (AlphaEqB b1, AlphaEqB b2) => AlphaEqB (PairB b1 b2) where
  withAlphaEqB (PairB a1 b1) (PairB a2 b2) cont =
    withAlphaEqB a1 a2 $ withAlphaEqB b1 b2 $ cont

instance (AlphaEqB b, AlphaEqE e) => AlphaEqE (Abs b e) where
  alphaEqE (Abs b1 e1) (Abs b2 e2) = withAlphaEqB b1 b2 $ alphaEqE e1 e2

instance (AlphaEqB b, AlphaEqE ann) => AlphaEqB (BinderP b ann) where
  withAlphaEqB (b1:>ann1) (b2:>ann2) cont = do
    alphaEqE ann1 ann2
    withAlphaEqB b1 b2 $ cont

instance AlphaEqE UnitE where
  alphaEqE UnitE UnitE = return ()

instance (AlphaEqE e1, AlphaEqE e2) => AlphaEqE (PairE e1 e2) where
  alphaEqE (PairE a1 b1) (PairE a2 b2) = alphaEqE a1 a2 >> alphaEqE b1 b2

instance (AlphaEqE e1, AlphaEqE e2) => AlphaEqE (EitherE e1 e2) where
  alphaEqE (LeftE  e1) (LeftE  e2) = alphaEqE e1 e2
  alphaEqE (RightE e1) (RightE e2) = alphaEqE e1 e2
  alphaEqE (LeftE  _ ) (RightE _ ) = zipErr
  alphaEqE (RightE _ ) (LeftE  _ ) = zipErr

-- === ScopeReaderT transformer ===

newtype ScopeReaderT (m::MonadKind) (n::S) (a:: *) =
  ScopeReaderT {runScopeReaderT' :: ReaderT (WithDistinct Scope n) m a}
  deriving (Functor, Applicative, Monad, MonadError err, MonadFail)

runScopeReaderT :: Distinct n => Scope n -> ScopeReaderT m n a -> m a
runScopeReaderT scope m = flip runReaderT (Distinct scope) $ runScopeReaderT' m

instance Monad m => ScopeReader (ScopeReaderT m) where
  getScope = ScopeReaderT ask

instance Monad m => ScopeExtender (ScopeReaderT m) where
  extendScope frag (ScopeReaderT m) = ScopeReaderT $ withReaderT
    (\(Distinct scope) -> Distinct (scope >>> frag)) m

-- === EnvReaderT transformer ===

newtype EnvReaderT (v::V) (m::MonadKind1) (i::S) (o::S) (a:: *) =
  EnvReaderT { runEnvReaderT :: ReaderT (NameFunction v i o) (m o) a }
  deriving (Functor, Applicative, Monad, MonadError err, MonadFail)

type ScopedEnvReader (v::V) = EnvReaderT v (ScopeReaderT Identity) :: MonadKind2

-- lets you call SubstE etc from a monad that lets you read the scope but not
-- extend it (or at least, not extend it without more information, like
-- bindings).
liftScopedEnvReader :: (EnvGetter v m, ScopeReader2 m)
                    => ScopedEnvReader (v::V) i o a
                    -> m i o a
liftScopedEnvReader m = do
  env <- getEnv
  Distinct scope <- getScope
  return $
    runIdentity $ runScopeReaderT scope $
      flip runReaderT env $
        runEnvReaderT $ m

instance Monad1 m => EnvReader v (EnvReaderT v m) where
  lookupEnvM name = EnvReaderT $ (! name) <$> ask

instance Monad1 m => EnvExtender v (EnvReaderT v m) where
  extendEnv frag (EnvReaderT cont) =
    EnvReaderT $ withReaderT (\env -> env <>> frag) cont

instance Monad1 m => Renamer (EnvReaderT (SubstVal s val) m) where
  dropSubst (EnvReaderT cont) =
    EnvReaderT $ withReaderT (const $ newNameFunction Rename) cont
  extendRenamer frag (EnvReaderT cont) =
    EnvReaderT $ withReaderT (<>>frag') cont
    where frag' = fmapEnvFrag (\_ v -> Rename v) frag

instance Monad1 m => Renamer (EnvReaderT Name m) where
  dropSubst (EnvReaderT cont) =
    EnvReaderT $ withReaderT (const $ newNameFunction id) cont
  extendRenamer frag (EnvReaderT cont) =
    EnvReaderT $ withReaderT (<>>frag) cont

instance Monad1 m => EnvGetter v (EnvReaderT v m) where
  getEnv = EnvReaderT ask

instance ScopeReader m => ScopeReader (EnvReaderT v m i) where
  getScope = EnvReaderT $ lift getScope

-- The rest are boilerplate but this one is a bit interesting. When we extend
-- the scope we have to inject the env, `Env i o` into the new scope, to become
-- `Env i oNew `
instance (InjectableV v, ScopeReader m, ScopeExtender m)
         => ScopeExtender (EnvReaderT v m i) where
  extendScope frag (EnvReaderT (ReaderT cont)) = EnvReaderT $ ReaderT \env ->
    extendScope frag do
      env' <- injectM frag env
      cont env'

-- === ZipEnvReaderT transformer ===

newtype ZipEnvReaderT (m::MonadKind1) (i1::S) (i2::S) (o::S) (a:: *) =
  ZipEnvReaderT { runZipEnvReaderT :: ReaderT (ZipEnv i1 i2 o) (m o) a }
  deriving (Functor, Applicative, Monad, MonadError err, MonadFail)

type ZipEnv i1 i2 o = (NameFunction Name i1 o, NameFunction Name i2 o)

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
    ZipEnvReaderT $ withReaderT (const (newNameFunction id, newNameFunction id)) cont

-- === Name traverser ===

-- Similar to `EnvReaderT Name`, but lookup up a name may produce effects. We
-- use this, with `Either Err`, for projecting expressions into a shallower name
-- space.

data NameTraverserEnv (m::MonadKind) (i::S) (o::S) where
  NameTraverserEnv :: (forall s. Name s hidden -> m (Name s o))  -- fallback function (with effects)
                   -> EnvFrag Name hidden i o                    -- names first looked up here
                   -> NameTraverserEnv m i o

newNameTraverserEnv :: (forall s. Name s i -> m (Name s o)) -> NameTraverserEnv m i o
newNameTraverserEnv f = NameTraverserEnv f emptyEnv

extendNameTraverserEnv :: NameTraverserEnv m i o -> EnvFrag Name i i' o -> NameTraverserEnv m i' o
extendNameTraverserEnv (NameTraverserEnv f frag) frag' =
  NameTraverserEnv f $ frag <.> frag'

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
  dropSubst (NameTraverserT cont) =
    NameTraverserT $ withReaderT (const $ newNameTraverserEnv return) cont
  extendRenamer frag (NameTraverserT cont) =
    NameTraverserT $ withReaderT (`extendNameTraverserEnv` frag) cont

instance Monad m => EnvReader Name (NameTraverserT m) where
  lookupEnvM name = NameTraverserT do
    env <- ask
    lift $ ScopeReaderT $ lift $ lookupNameTraversalEnv env name

lookupNameTraversalEnv :: Monad m => NameTraverserEnv m i o -> Name c i -> m (Name c o)
lookupNameTraversalEnv (NameTraverserEnv f frag) name =
  case lookupEnvFragProjected frag name of
    Left name' -> f name'
    Right val -> return val

-- === monadish thing for computations that produce names ===

class NameGen (m :: E -> S -> *) where
  returnG :: e n -> m e n
  bindG   :: m e n -> (forall l. e l -> m e' l) -> m e' n

fmapG :: NameGen m => (forall l. e1 l -> e2 l) -> m e1 n -> m e2 n
fmapG f e = e `bindG` (returnG . f)

data WithScopeFrag (e::E) (n::S) where
  WithScopeFrag :: Distinct l => ScopeFrag n l -> e l -> WithScopeFrag e n

newtype NameGenT (m::MonadKind1) (e::E) (n::S) =
  NameGenT { runNameGenT :: m n (WithScopeFrag e n) }

instance (ScopeReader m, ScopeExtender m, Monad1 m) => NameGen (NameGenT m) where
  returnG e = NameGenT $ do
    Distinct _ <- getScope
    return (WithScopeFrag id e)
  bindG (NameGenT m) f = NameGenT do
    WithScopeFrag s  e  <- m
    WithScopeFrag s' e' <- extendScope s $ runNameGenT $ f e
    return $ WithScopeFrag (s >>> s') e'

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

forEachNestItemSG :: SubstGen m
               => Nest b i i'
               -> (forall ii ii' oo. b ii ii' -> m ii ii' (b' oo) oo)
               -> m i i' (Nest b' o) o
forEachNestItemSG Empty _ = returnSG Empty
forEachNestItemSG (Nest b bs) f =
  f b `bindSG` \b' ->
    forEachNestItemSG bs f `bindSG` \bs' ->
      returnSG $ Nest b' bs'

data WithScopeSubstFrag (i::S) (i'::S) (e::E) (o::S) where
  WithScopeSubstFrag :: Distinct o'
                     => ScopeFrag o o' -> EnvFrag Name i i' o' -> e o'
                     -> WithScopeSubstFrag i i' e o

newtype SubstGenT (m::MonadKind2) (i::S) (i'::S) (e::E) (o::S) =
  SubstGenT { runSubstGenT :: m i o (WithScopeSubstFrag i i' e o)}

instance (ScopeReader2 m, ScopeExtender2 m, Renamer m, Monad2 m)
         => NameGen (SubstGenT m i i) where
  returnG = returnSG
  bindG = bindSG

instance (ScopeReader2 m, ScopeExtender2 m, Renamer m, Monad2 m)
         => SubstGen (SubstGenT m) where
  returnSG e = SubstGenT $ do
    Distinct _ <- getScope
    return (WithScopeSubstFrag id emptyEnv e)
  bindSG (SubstGenT m) f = SubstGenT do
    WithScopeSubstFrag s env e <- m
    extendScope s $ extendRenamer env do
      WithScopeSubstFrag s' env' e' <- runSubstGenT $ f e
      envInj <- extendScope s' $ injectM s' env
      return $ WithScopeSubstFrag (s >>> s') (envInj <.> env')  e'

liftSG :: ScopeReader2 m => m i o a -> (a -> SubstGenT m i i' e o) -> SubstGenT m i i' e o
liftSG m cont = SubstGenT do
  ans <- m
  runSubstGenT $ cont ans

-- === name hints ===

type NameHint = RawName

class HasNameHint a where
  getNameHint :: a -> NameHint

instance HasNameHint (Name s n) where
  getNameHint = getRawName

instance HasNameHint (NameBinder s n l) where
  getNameHint = getRawName . binderName

instance HasNameHint RawName where
  getNameHint = id

instance HasNameHint String where
  getNameHint = fromString

data CommonHint =
   IgnoreHint
 | GenHint

instance HasNameHint CommonHint where
  getNameHint hint = case hint of
    IgnoreHint -> "_"
    GenHint    -> "v"

-- === getting name colors ===

class HasNameColor a c | a -> c where
  getNameColor :: a -> NameColorRep c

instance HasNameColor (Name c n) c where
  getNameColor = getNameColorRep

instance HasNameColor (NameBinder c n l) c where
  getNameColor b = getNameColorRep $ nameBinderName b

-- === instances ===

instance InjectableV v => InjectableE (NameFunction v i) where
  injectionProofE fresh (NameFunction f m) =
    NameFunction (\name -> injectionProofE fresh $ f name)
                 (injectionProofE fresh m)

instance InjectableE atom => InjectableE (SubstVal (cMatch::C) (atom::E) (c::C)) where
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

instance (BindsNames b1, BindsNames b2) => BindsNames (PairB b1 b2) where
  toScopeFrag (PairB b1 b2) = toScopeFrag b1 >>> toScopeFrag b2

instance (InjectableB b1, InjectableB b2) => InjectableB (PairB b1 b2) where
  injectionProofB fresh (PairB b1 b2) cont =
    injectionProofB fresh b1 \fresh' b1' ->
      injectionProofB fresh' b2 \fresh'' b2' ->
        cont fresh'' (PairB b1' b2')

instance (SubstB v b1, SubstB v b2) => SubstB v (PairB b1 b2) where
  substB (PairB b1 b2) =
    substB b1 `bindSG` \b1' ->
      substB b2 `bindSG` \b2' ->
        returnSG $ PairB b1' b2'

instance (InjectableB b, InjectableE ann) => InjectableB (BinderP b ann) where
  injectionProofB fresh (b:>ann) cont = do
    let ann' = injectionProofE fresh ann
    injectionProofB fresh b \fresh' b' ->
      cont fresh' $ b':>ann'

instance (SubstB v b, SubstE v ann) => SubstB v (BinderP b ann) where
   substB (b:>ann) =
      substE ann `liftSG` \ann' ->
      substB b   `bindSG` \b' ->
      returnSG $ b':>ann'

instance BindsNames b => BindsNames (BinderP b ann) where
  toScopeFrag (b:>_) = toScopeFrag b

instance BindsNames b => BindsNames (Nest b) where
  toScopeFrag Empty = id
  toScopeFrag (Nest b rest) = toScopeFrag b >>> toScopeFrag rest

instance SubstB v b => SubstB v (Nest b) where
  substB nest = forEachNestItemSG nest substB

instance InjectableE UnitE where
  injectionProofE _ UnitE = UnitE

instance SubstE v UnitE where
  substE UnitE = return UnitE

instance (Functor f, InjectableE e) => InjectableE (ComposeE f e) where
  injectionProofE fresh (ComposeE xs) = ComposeE $ fmap (injectionProofE fresh) xs

instance (Traversable f, SubstE v e) => SubstE v (ComposeE f e) where
  substE (ComposeE xs) = ComposeE <$> mapM substE xs

-- alternatively we could use Zippable, but we'd want to be able to derive it
-- (e.g. via generic) for the many-armed cases like PrimOp.
instance (Traversable f, Eq (f ()), AlphaEq e) => AlphaEqE (ComposeE f e) where
  alphaEqE (ComposeE xs) (ComposeE ys) = alphaEqTraversable xs ys

instance InjectableB UnitB where
  injectionProofB fresh UnitB cont = cont fresh UnitB

instance BindsNames UnitB where
  toScopeFrag UnitB = id

instance SubstB v UnitB where
  substB UnitB = returnSG UnitB

instance InjectableE const => InjectableE (ConstE const ignored) where
  injectionProofE fresh (ConstE e) = ConstE $ injectionProofE fresh e

instance InjectableE VoidE where
  injectionProofE _ _ = error "impossible"

instance AlphaEqE VoidE where
  alphaEqE _ _ = error "impossible"

instance SubstE v VoidE where
  substE _ = error "impossible"

instance (InjectableE e1, InjectableE e2) => InjectableE (PairE e1 e2) where
  injectionProofE fresh (PairE e1 e2) =
    PairE (injectionProofE fresh e1) (injectionProofE fresh e2)

instance (SubstE v e1, SubstE v e2) => SubstE v (PairE e1 e2) where
  substE (PairE x y) =
    PairE <$> substE x <*> substE y

instance (InjectableE e1, InjectableE e2) => InjectableE (EitherE e1 e2) where
  injectionProofE fresh (LeftE  e) = LeftE  (injectionProofE fresh e)
  injectionProofE fresh (RightE e) = RightE (injectionProofE fresh e)

instance (SubstE v e1, SubstE v e2) => SubstE v (EitherE e1 e2) where
  substE (LeftE  x) = LeftE  <$> substE x
  substE (RightE x) = RightE <$> substE x

instance InjectableE e => InjectableE (ListE e) where
  injectionProofE fresh (ListE xs) = ListE $ map (injectionProofE fresh) xs

instance AlphaEqE e => AlphaEqE (ListE e) where
  alphaEqE (ListE xs) (ListE ys)
    | length xs == length ys = mapM_ (uncurry alphaEqE) (zip xs ys)
    | otherwise              = zipErr

instance InjectableE (LiftE a) where
  injectionProofE _ (LiftE x) = LiftE x

instance SubstE v (LiftE a) where
  substE (LiftE x) = return $ LiftE x

instance Eq a => AlphaEqE (LiftE a) where
  alphaEqE (LiftE x) (LiftE y) = unless (x == y) zipErr

instance SubstE v e => SubstE v (ListE e) where
  substE (ListE xs) = ListE <$> mapM substE xs

instance (PrettyB b, PrettyE e) => Pretty (Abs b e n) where
  pretty (Abs b body) = "(Abs " <> pretty b <> " " <> pretty body <> ")"

instance Pretty a => Pretty (LiftE a n) where
  pretty (LiftE x) = pretty x

instance Pretty (UnitE n) where
  pretty UnitE = ""

instance ( Generic (b UnsafeS UnsafeS)
         , Generic (body UnsafeS) )
         => Generic (Abs b body n) where
  type Rep (Abs b body n) = Rep (b UnsafeS UnsafeS, body UnsafeS)
  from (Abs b body) = from (unsafeCoerceB b, unsafeCoerceE body)
  to rep = Abs (unsafeCoerceB b) (unsafeCoerceE body)
    where (b, body) = to rep

instance ( Generic (b1 UnsafeS UnsafeS)
         , Generic (b2 UnsafeS UnsafeS) )
         => Generic (PairB b1 b2 n l) where
  type Rep (PairB b1 b2 n l) = Rep (b1 UnsafeS UnsafeS, b2 UnsafeS UnsafeS)
  from (PairB b1 b2) = from (unsafeCoerceB b1, unsafeCoerceB b2)
  to rep = PairB (unsafeCoerceB b1) (unsafeCoerceB b2)
    where (b1, b2) = to rep

instance ( Store   (b UnsafeS UnsafeS), Store   (body UnsafeS)
         , Generic (b UnsafeS UnsafeS), Generic (body UnsafeS) )
         => Store (Abs b body n)
instance ( Store   (b1 UnsafeS UnsafeS), Store   (b2 UnsafeS UnsafeS)
         , Generic (b1 UnsafeS UnsafeS), Generic (b2 UnsafeS UnsafeS) )
         => Store (PairB b1 b2 n l)

instance BindsNames (RecEnvFrag v) where
  toScopeFrag env = envAsScope $ fromRecEnvFrag env

-- Traversing a recursive set of bindings is a bit tricky because we have to do
-- two passes: first we rename the binders, then we go and subst the payloads.
instance (forall s. SubstE substVal (v s)) => SubstB substVal (RecEnvFrag v) where
  substB (RecEnvFrag env) = SubstGenT do
    WithScopeSubstFrag s r pairs <- runSubstGenT $ forEachNestItemSG (toEnvPairs env)
       \(EnvPair b x) -> substB b `bindSG` \b' -> returnSG (EnvPair b' x)
    extendScope s $ extendRenamer r do
      pairs' <- forEachNestItem pairs \(EnvPair b x) -> EnvPair b <$> substE x
      return $ WithScopeSubstFrag s r $ RecEnvFrag $ fromEnvPairs pairs'

instance (forall c. SubstE substVal (v c)) => SubstE substVal (EnvVal v) where
  substE = undefined

instance Store (UnitE n)
instance Store (VoidE n)
instance (Store (e1 n), Store (e2 n)) => Store (PairE   e1 e2 n)
instance (Store (e1 n), Store (e2 n)) => Store (EitherE e1 e2 n)
instance Store (e n) => Store (ListE  e n)
instance Store a => Store (LiftE a n)
instance Store (const n) => Store (ConstE const ignored n)
instance (Store (b n l), Store (ann n)) => Store (BinderP b ann n l)

type EE = EitherE

type EitherE1 e0             = EE e0 VoidE
type EitherE2 e0 e1          = EE e0 (EE e1 VoidE)
type EitherE3 e0 e1 e2       = EE e0 (EE e1 (EE e2 VoidE))
type EitherE4 e0 e1 e2 e3    = EE e0 (EE e1 (EE e2 (EE e3 VoidE)))
type EitherE5 e0 e1 e2 e3 e4 = EE e0 (EE e1 (EE e2 (EE e3 (EE e4 VoidE))))

pattern Case0 :: e0 n -> EE e0 rest n
pattern Case0 e = LeftE e

pattern Case1 :: e1 n -> EE e0 (EE e1 rest) n
pattern Case1 e = RightE (LeftE e)

pattern Case2 :: e2 n -> EE e0 (EE e1 (EE e2 rest)) n
pattern Case2 e = RightE (RightE (LeftE e))

pattern Case3 :: e3 n -> EE e0 (EE e1 (EE e2 (EE e3 rest))) n
pattern Case3 e = RightE (RightE (RightE (LeftE e)))

pattern Case4 :: e4 n ->  EE e0 (EE e1 (EE e2 (EE e3 (EE e4 rest)))) n
pattern Case4 e = RightE (RightE (RightE (RightE (LeftE e))))
