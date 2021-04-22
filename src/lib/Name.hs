-- Copyright 2021 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE UndecidableInstances #-}

module Name (Name, RawName (..), Tag, EnvFrag (..), Env, envFragLookup, envLookup,
             PlainBinder (..), PlainBinderList, getRawSourceName, fromRawSourceName,
             VoidNS, SourceNS, SourceName, pattern SourceBinder, pattern SourceName,
             Ext (..), RecEnvFrag (..), RecEnv, Fresh (..), unsafeCoerceNames,
             withFresh, Scope, AlphaEq (..), NameTraversal (..),
             EmptyNest, NameSet, HasNames (..), BindsNames (..), BindsOneName (..),
             BindsNameList (..), fmapEnvFrag, HasNamesEnvFrag (..), HasNamesEnv,
             liftNames, lowerNames, liftEnvNames, RenameEnv, RenameEnvFrag,
             binderName, Abs (..), Nest (..), toNest, getRawName,
             NameHint, withTempScope, freeNames, fmapNames, foldMapNames,
             unitScope, unitName, voidScope, voidEnv, FreshAbs (..), freshenAbs,
             AnnBinderP (..), AnnBinderListP (..), binderAnn, extendRecEnv,
             fromNest, coerceToSourceNS, coerceToSourceNS2, newNameTraversal,
             fmapFresh, SubstVal (..), applyRename, renamerLookup, MonadBuilderP (..),
             BuilderPT (..), withManyFresh, fmapNestToList, NestPair (..),
             withTraverseFreeNamesBinders, extendLiftNameTraversal) where

-- TODO: use a custom prelude to avoid this in every file
import Prelude hiding ((.), id)
import Control.Category
import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer.Strict
import qualified Data.Map.Strict as M
import qualified Data.Set        as S
import Data.String
import qualified Data.Text as T
import Unsafe.Coerce
import Data.Text.Prettyprint.Doc  hiding (nest)

import HigherKinded
import qualified LazyMap as LM

type Tag = T.Text
data RawName = RawName Tag Int
               deriving (Show, Eq, Ord)

data Name n = UnsafeMakeName RawName
              deriving (Show, Eq, Ord)

-- `EnvFrag a n l` is a function `Name l -> Either (Name n) a`, along with
-- the set of names for which that function gives the `Right` case.
data EnvFrag a n l = UnsafeMakeEnvFrag (LM.LazyMap RawName a)
type Env a = EnvFrag a VoidNS  :: * -> *

-- There should only be one `Scope n` for any `n`
type ScopeFrag = EnvFrag ()  :: * -> * -> *
type Scope     = Env     ()  :: * -> *

-- There's a common sort of Env whose payload is `e n` with `HasNames e`. Such
-- an env could have a HasNames instance, and used in a `FreshAbs` and so on.
-- The renaming env and the atom subst env are two examples. But there's no way
-- to have an env type that both accepts an arbitrary payload, `a`, and also has
-- a kind suitable for `HasNames`. So it seems we have to use a newtype.
-- TODO: `EnvFrag (e o) i i'` is covariant in both `i` and `o`. Do we
--       need three different newtype wrappers to handle all the cases (i, o, i+o)?
newtype HasNamesEnvFrag e i i' o = HasNamesEnv { fromHasNamesEnv :: EnvFrag (e o) i i' }
type HasNamesEnv e = HasNamesEnvFrag e VoidNS

instance Category (EnvFrag a) where
  id = UnsafeMakeEnvFrag mempty
  UnsafeMakeEnvFrag m1 . UnsafeMakeEnvFrag m2 = UnsafeMakeEnvFrag $ m1 <> m2

envFragLookup :: EnvFrag a n l -> Name l -> Either (Name n) a
envFragLookup (UnsafeMakeEnvFrag m) (UnsafeMakeName name) =
  case LM.lookup name m of
    Just x -> Right x
    Nothing -> Left $ UnsafeMakeName name

fmapEnvFrag :: (a -> b) -> EnvFrag a n l -> EnvFrag b n l
fmapEnvFrag f (UnsafeMakeEnvFrag m) = UnsafeMakeEnvFrag $ fmap f m

traverseEnvFrag :: Applicative m => (a -> m b) -> EnvFrag a n l -> m (EnvFrag b n l)
traverseEnvFrag f (UnsafeMakeEnvFrag m) = UnsafeMakeEnvFrag <$> traverse f m

envPairs :: EnvFrag a n l -> (PlainBinderList n l, [a])
envPairs (UnsafeMakeEnvFrag m) = do
  let (names, vals) = unzip $ LM.assocs m
  (unsafeMakePlainBinderList names, vals)

unsafeMakePlainBinderList :: [RawName] -> PlainBinderList n l
unsafeMakePlainBinderList names = case names of
  [] -> unsafeCoerce Empty
  (name:rest) -> Nest (UnsafeMakeBinder name) $ unsafeMakePlainBinderList rest

data PlainBinder n l where
  UnsafeMakeBinder :: RawName -> PlainBinder n l
  Ignore           :: PlainBinder n n

-- `Ext n l` is a proof that `l` is a *fresh* extension of `n`
data Ext n l = UnsafeMakeExt
instance Category Ext where
  id    = UnsafeMakeExt
  _ . _ = UnsafeMakeExt

withFresh :: Scope n -> (forall l. Ext n l -> PlainBinder n l -> Name l -> a) -> a
withFresh (UnsafeMakeEnvFrag scope) cont =
  cont UnsafeMakeExt (UnsafeMakeBinder freshName) (UnsafeMakeName freshName)
  where freshName = freshRawName "v" (LM.keysSet scope)

freshRawName :: Tag -> S.Set RawName -> RawName
freshRawName tag usedNames = RawName tag nextNum
  where
    nextNum = case S.lookupLT (RawName tag bigInt) usedNames of
                Just (RawName tag' i)
                  | tag' /= tag -> 0
                  | i < bigInt  -> i + 1
                  | otherwise   -> error "Ran out of numbers!"
                Nothing -> 0
    bigInt = (10::Int) ^ (9::Int)  -- TODO: consider a real sentinel value

binderName :: PlainBinder n l -> Maybe (Name l)
binderName Ignore = Nothing
binderName (UnsafeMakeBinder name) = Just $ UnsafeMakeName name

-- useful for printing etc
getRawName :: Name n -> RawName
getRawName (UnsafeMakeName name) = name

-- slightly safer than raw `unsafeCoerce` because it requires `HasNames`
unsafeCoerceNames :: HasNames e => e i -> e o
unsafeCoerceNames = unsafeCoerce

unsafeCoerceNamesBinders :: BindsNames b => b n l -> b n' l'
unsafeCoerceNamesBinders = unsafeCoerce

unsafeCoerceNamesEnv :: EnvFrag a n l -> EnvFrag a n' l'
unsafeCoerceNamesEnv (UnsafeMakeEnvFrag env) = UnsafeMakeEnvFrag env

-- === free variable traversal ===

type RenameEnv     i    o = EnvFrag (Name o) o i
type RenameEnvFrag i i' o = EnvFrag (Name o) i i'

data NameTraversal m i o where
  NameTraversal :: (Name i -> m (Name o)) -> RenameEnvFrag i i' o -> NameTraversal m i' o

-- XXX: In addition to the methods, a `HasNames` instance is also used as a
-- proof that the `n` parameter is truly phantom, so that it doesn't affect the
-- runtime representation and can be cast arbitrarily by `unsafeCastNames`.
-- It should therefore satisfy:
--   traverseFreeNames scope (pure . liftName ext) x = unsafeCoerceNames x
--   (see implementation of `liftNames :: HasNames e => Ext n l -> e n -> e l`)
class HasNames (e :: * -> *) where
  traverseFreeNames
    :: Monad m
    => Scope o
    -> NameTraversal m i o
    -> e i
    -> m (e o)

class BindsNames (b :: * -> * -> *) where
  traverseFreeNamesBinders
    :: Monad m
    => Scope o
    -> NameTraversal m i o
    -> b i i'
    -> m (Fresh b i i' o)

  asScopeFrag :: b n l -> ScopeFrag n l

-- variant with the common extension built in
withTraverseFreeNamesBinders
  :: BindsNames b => Monad m
  =>             Scope o  -> NameTraversal m i  o  -> b i i'
  -> (forall o'. Scope o' -> NameTraversal m i' o' -> b o o' -> m a)
  -> m a
withTraverseFreeNamesBinders s t b cont =
  traverseFreeNamesBinders s t b >>= \case
    Fresh ext b' renamer -> do
      let t' = extendLiftNameTraversal ext t renamer
      let s' = extendScope s b'
      cont s' t' b'

infixr 7 @>
-- really, at most one name
class BindsNames b => BindsOneName (b :: * -> * -> *) where
  (@>) :: b i i' -> a -> EnvFrag a i i'

infixr 7 @@>
class BindsNames b => BindsNameList (b :: * -> * -> *) where
  (@@>) :: b i i' -> [a] -> EnvFrag a i i'

class HasNames e => AlphaEq (e :: * -> *) where
  alphaEq :: Scope n -> e n -> e n -> Bool

liftNames :: HasNames e => Ext n l -> e n -> e l
-- This is the reference implementation. `unsafeCoerce` is an optimization, and
-- should behave the same, up to alpha renaming.
--   liftNames _ x = fmapFreeNames scope (pure . liftName ext) x
liftNames _ x = unsafeCoerceNames x

-- Makes a temporary scope by querying the free variables of an expression. We
-- should try to avoid using this, since we normally have the actual scope
-- available and we can avoid the work of traversing the expression.
withTempScope :: HasNames e => e n
              -> (forall l. Ext l n -> Scope l -> e l -> a) -> a
withTempScope e cont = do
  let freeRawNames = foldMapNames (S.singleton . getRawName) e
  let rawScope = LM.fromList $ map (,()) $ S.toList freeRawNames
  cont UnsafeMakeExt (UnsafeMakeEnvFrag rawScope) (unsafeCoerceNames e)

-- === convenience utilities using safe API ===

data Abs (binder :: * -> * -> *) (body :: * -> *) (n :: *) where
  Abs :: binder n l -> body l -> Abs binder body n

data Nest (binder :: * -> * -> * ) (n :: *) (l :: *) where
 Nest  :: binder n h -> Nest binder h i -> Nest binder n i
 Empty ::                                  Nest binder n n

data NestPair (b1 :: * -> * -> *) (b2 :: * -> * -> *) n l where
  NestPair :: b1 n l -> b2 l l' -> NestPair b1 b2 n l'

type PlainBinderList = Nest PlainBinder

envLookup :: Env a i -> Name i -> a
envLookup env name = case envFragLookup env name of
  Left _ -> error "Impossible! `Name VoidNS`s don't exist."
  Right x -> x

type EmptyNest (binder :: * -> * -> *) = Abs (Nest binder) UnitH :: * -> *

type NameHint = RawName

type NameSet n = S.Set (Name n)

lowerName :: EnvFrag a n l -> Name l -> Maybe (Name n)
lowerName ef name = case envFragLookup ef name of
   Left name' -> Just name'
   Right _ -> Nothing

-- TODO: use `Except` instead of `Maybe` to provide a more informative error
lowerNames :: HasNames e => Scope n -> EnvFrag a n l -> e l -> Maybe (e n)
lowerNames scope frag expr = traverseFreeNames scope t expr
  where t = newNameTraversal $ lowerName frag

fmapNames :: HasNames e => Scope b -> (Name a -> Name b) -> e a -> e b
fmapNames scope f xs = runIdentity $ traverseFreeNames scope t xs
  where t = newNameTraversal $ pure . f

foldMapNames :: (HasNames e, Monoid a) => (Name n -> a) -> e n -> a
foldMapNames f e = execWriter $ traverseFreeNames unitScope t e
  where t = newNameTraversal \name -> tell (f name) >> return unitName

freeNames :: HasNames e => e n -> NameSet n
freeNames e = foldMapNames S.singleton e

refreshBinders :: BindsNames b => Scope n -> b n l -> Fresh b n l n
refreshBinders scope b = runIdentity $ traverseFreeNamesBinders scope t b
  where t = NameTraversal return id

liftEnvNames :: HasNames e => Ext n l -> EnvFrag (e o) i i' -> EnvFrag (e l) i i'
liftEnvNames = unsafeCoerce

liftNameTraversal :: Ext o o' -> NameTraversal m i o -> NameTraversal m i o'
liftNameTraversal = unsafeCoerce

extendNameTraversal :: NameTraversal m i o -> RenameEnvFrag i i' o -> NameTraversal m i' o
extendNameTraversal (NameTraversal f frag) frag' = NameTraversal f $ frag >>> frag'

extendLiftNameTraversal :: Ext o o' -> NameTraversal m i o -> RenameEnvFrag i i' o' -> NameTraversal m i' o'
extendLiftNameTraversal ext t frag = extendNameTraversal (liftNameTraversal ext t) frag

-- variant of `Abs` whose binder is fresh wrt the outer scope.
-- XXX: don't implement `HasNames` for this! -- the fmap-coerce equivalence
-- won't hold.
data FreshAbs b e n where
  FreshAbs :: Ext n l -> b n l -> e l -> FreshAbs b e n

data Fresh b i i' o where
  Fresh :: Ext o o' -> b o o' -> RenameEnvFrag i i' o' -> Fresh b i i' o

fmapFresh :: (forall o'. b1 o o' -> b2 o o') -> Fresh b1 i i' o -> Fresh b2 i i' o
fmapFresh f (Fresh ext b renamer) = Fresh ext (f b) renamer

freshenAbs :: (BindsNames b, HasNames e) => Scope n -> Abs b e n -> FreshAbs b e n
freshenAbs scope (Abs b body) =
  case refreshBinders scope b of
    Fresh ext b' renamer ->
      let subst name = case envFragLookup renamer name of
                         Left name' -> liftNames ext name'
                         Right name' -> name'
      in FreshAbs ext b' $ fmapNames (extendScope scope b') subst body

renamerLookup :: RenameEnv i o -> Name i -> Name o
renamerLookup frag name = case envFragLookup frag name of
  Left  name' -> name'
  Right name' -> name'

applyRename :: HasNames e => Scope o -> RenameEnv i o -> e i -> e o
applyRename scope renamer x = fmapNames scope (renamerLookup renamer) x

-- TODO: use name hints `[RawName]` instead of `[()]`
withManyFresh :: Scope n -> [()] -> (forall l. Ext n l -> PlainBinderList n l -> [Name l] -> a) -> a
withManyFresh _ _ _ = undefined

-- data DeferredSubst (e :: * -> *) (n :: *) where
--   DeferredSubst :: RenameEnv l n -> e l -> DeferredSubst e n

-- forceDeferredSubst :: HasNames e => Scope n -> DeferredSubst e n -> e n
-- forceDeferredSubst scope (DeferredSubst env x) = fmapNames scope (envLookup env) x

infixl 7 :>
data AnnBinderP     (b :: * -> * -> *) (ann :: * -> *) n l = (:>) (b n l) (ann n) deriving (Show)
data AnnBinderListP (b :: * -> * -> *) (ann :: * -> *) n l = (:>>) (Nest b n l) [ann n]

binderAnn :: AnnBinderP b ann n l -> ann n
binderAnn (_:>ann) = ann

newtype RecEnvFrag e n l = RecEnvFrag { fromRecEnvFrag :: (EnvFrag (e l) n l) }
type RecEnv e = RecEnvFrag e VoidNS :: * -> *

extendRecEnv :: HasNames e => Ext n l -> RecEnv e n -> RecEnvFrag e n l -> RecEnv e l
extendRecEnv ext env env' =
  RecEnvFrag $ liftEnvNames ext (fromRecEnvFrag env) >>> fromRecEnvFrag env'

extendScope :: BindsNames b => Scope n -> b n l -> Scope l
extendScope scope b = scope >>> asScopeFrag b

newNameTraversal :: (Name i -> m (Name o)) -> NameTraversal m i o
newNameTraversal f = NameTraversal f id

data SubstVal e n = SubstVal (e n) | Rename (Name n)

fmapNestToList :: (forall n' l'. b n' l' -> a) ->  Nest b n l -> [a]
fmapNestToList f Empty = []
fmapNestToList f (Nest b rest) = f b : fmapNestToList f rest


-- NameMap and NameMapH are much more like an ordinary map, with no special
-- invariants maintained. `<>` is right-biased, like Env but unlike Data.Map
data NameMap a n = NameMap (M.Map (Name n) a)

data NameMapH e n = NameMap (M.Map (Name n) (e n))


-- === monad that updates name sets "in place" ===

-- XXX: it should only gives you access to things that are covariant in `n`.

newtype BuilderPT d m n a =
  UnsafeBuilderPT (StateT (RecEnv d n, [Name n]) m a)
  deriving (Functor, Applicative, Monad)

-- TODO: consider making this the fundamental `MonadBuilder` emit operation:
--   emitGeneral :: (BindsNames b, MonadBuilder m b n, HasNames e)
--               => Abs b e -> m (e n)
-- The challenge is figuring how how to handle the in-scope binding data.
-- Maybe if we have names parameterized by their static payloads we'll
-- be able to handle scope payloads automatically.
class (HasNames d, Monad m) => MonadBuilderP d n m | m -> d, m -> n where
  riskyGetBindings :: m (RecEnv d n)
  emitGeneral :: d n -> m (Name n)
  -- TODO: more foralls
  scopedGeneral :: HasNames e => m (e n) -> m (WithDeclsP d e n)

type WithDeclsP d = Abs (Nest (AnnBinderP PlainBinder d))

-- TODO: more foralls
runBuilderPT :: (HasNames d, Monad m)
                  => RecEnv d n -> BuilderPT d m n (e n) -> m (WithDeclsP d e n)
runBuilderPT bindings (UnsafeBuilderPT m) = do
  (result, (bindings, orderedNames)) <- runStateT m (bindings, [])
  return $ Abs (unsafeMakeDecls bindings orderedNames) result

instance (HasNames d, Monad m) => MonadBuilderP d n (BuilderPT d m n) where
  riskyGetBindings = UnsafeBuilderPT $ gets fst
  emitGeneral ann = UnsafeBuilderPT do
    (bindings, orderedNames) <- get
    withFresh (asScopeFrag bindings) \_ b name -> do
      let bindings' = RecEnvFrag $ unsafeCoerceNamesEnv $ fromRecEnvFrag bindings >>> b @> ann
      let orderedNames' = orderedNames <> [unsafeCoerceNames name]
      put (bindings', orderedNames')
      return $ unsafeCoerceNames name
  scopedGeneral = undefined

-- Not actually unsafe exactly. It's more that if you have a list `[b n n]` then
-- you're in already in unsafe land.
unsafeMakeDecls :: HasNames d => RecEnv d n -> [Name n] -> Nest (AnnBinderP PlainBinder d) n n
unsafeMakeDecls = undefined
-- unsafeToNest [] = Empty
-- unsafeToNest (b:rest) = Nest b $ unsafeToNest rest

instance MonadBuilderP d n m => MonadBuilderP d n (ReaderT r m) where
  riskyGetBindings = undefined
  emitGeneral = undefined
  scopedGeneral = undefined

-- === special name spaces ===

-- Used for source names, which don't obey any invariants
data SourceNS where
type RawSourceName = Tag

type SourceName = Name SourceNS

pattern SourceBinder :: Name SourceNS -> PlainBinder SourceNS SourceNS
pattern SourceBinder name <- ((\(UnsafeMakeBinder name) -> SourceName name) -> name)
  where SourceBinder (UnsafeMakeName name) = UnsafeMakeBinder name

pattern SourceName :: RawName -> Name SourceNS
pattern SourceName name = UnsafeMakeName name

getRawSourceName :: Name SourceNS -> RawSourceName
getRawSourceName (UnsafeMakeName (RawName name 0)) = name
getRawSourceName (UnsafeMakeName (RawName _ _)) =
  error "nonzero counter for a source name shouldn't happen"

fromRawSourceName :: RawSourceName -> Name SourceNS
fromRawSourceName name = UnsafeMakeName (RawName name 0)

toNest :: [b SourceNS SourceNS] -> Nest b SourceNS SourceNS
toNest [] = Empty
toNest (b:bs) = Nest b $ toNest bs

fromNest :: Nest b SourceNS SourceNS -> [b SourceNS SourceNS]
fromNest = undefined

-- This is safe because there are no restrictions on source names.
-- The inteded use is for printing
coerceToSourceNS :: HasNames e => e n -> e SourceNS
coerceToSourceNS = unsafeCoerce

coerceToSourceNS2 :: BindsNames b => b n l -> b SourceNS SourceNS
coerceToSourceNS2 = unsafeCoerce

-- Name space with no inhabitants
data VoidNS where

voidScope :: Scope VoidNS
voidScope = id

voidEnv :: Env a VoidNS
voidEnv = id

-- Name space with one inhabitant
data UnitNS where

unitRawName :: RawName
unitRawName  = "TheOneName"

unitName :: Name UnitNS
unitName = UnsafeMakeName unitRawName

unitBinder :: PlainBinder VoidNS UnitNS
unitBinder = UnsafeMakeBinder unitRawName

unitScope :: Scope UnitNS
unitScope = unitBinder @> ()

-- === instances ===

instance HasNames Name where
  traverseFreeNames _ (NameTraversal f frag) name =
    case envFragLookup frag name of
      Left  name' -> f name'
      Right name' -> return name'

instance (BindsNames b, HasNames e) => HasNames (Abs b e) where
  traverseFreeNames s t (Abs b body) = do
    withTraverseFreeNamesBinders s t b \s' t' b' ->
      Abs b' <$> traverseFreeNames s' t' body

instance BindsNames PlainBinder where
  traverseFreeNamesBinders scope _ b = return $ case b of
    Ignore -> Fresh id Ignore id
    UnsafeMakeBinder _ -> withFresh scope \ext b' name' ->
                            Fresh ext b' (b@>name')
  asScopeFrag b = b @> ()

instance (BindsNames b1, BindsNames b2) => BindsNames (NestPair b1 b2) where
  traverseFreeNamesBinders scope _ b = undefined
  asScopeFrag b = undefined

instance BindsOneName PlainBinder where
  (@>) b x = case b of
    Ignore -> id
    UnsafeMakeBinder name -> UnsafeMakeEnvFrag $ LM.singleton name x

instance BindsOneName b => BindsNameList (Nest b) where
  (@@>) Empty [] = id
  (@@>) (Nest b rest) (x:xs) = b@>x >>> (rest@@>xs)
  (@@>) _ _ = error "length mismatch"

instance BindsNames b => BindsNames (Nest b) where
  traverseFreeNamesBinders scope t nest = case nest of
    Empty -> return $ Fresh id Empty id
    Nest b rest -> do
      traverseFreeNamesBinders scope t b >>= \case
        Fresh ext b' renamer -> do
          let t' = extendLiftNameTraversal ext t renamer
          let scope' = extendScope scope b'
          traverseFreeNamesBinders scope' t' rest >>= \case
            Fresh ext' rest' renamer' -> do
              let renamer'' = liftEnvNames ext' renamer >>> renamer'
              return $ Fresh (ext >>> ext') (Nest b' rest') renamer''

  asScopeFrag nest = case nest of
    Empty -> id
    Nest b rest -> asScopeFrag b >>> asScopeFrag rest

instance BindsNames (EnvFrag a) where
  traverseFreeNamesBinders scope t env = do
    let (bs, vals) = envPairs env
    traverseFreeNamesBinders scope t bs >>= \case
      Fresh ext bs' renamer ->
        return $ Fresh ext (bs' @@> vals) renamer

  -- TODO: extract the names more directly for efficiency?
  asScopeFrag frag = fmapEnvFrag (const ()) frag

instance HasNames e => BindsNames (RecEnvFrag e) where
  traverseFreeNamesBinders scope t (RecEnvFrag frag) =
    traverseFreeNamesBinders scope t frag >>= \case
      Fresh ext frag' renamer -> do
        let t' = extendLiftNameTraversal ext t renamer
        let scope' = extendScope scope frag'
        frag'' <- liftM fromHasNamesEnv $ traverseFreeNames scope' t' $ HasNamesEnv frag'
        return $ Fresh ext (RecEnvFrag frag'') renamer

  asScopeFrag (RecEnvFrag frag) = asScopeFrag frag

instance HasNames e => HasNames (HasNamesEnvFrag e i i') where
  traverseFreeNames scope traversal (HasNamesEnv frag) =
    HasNamesEnv <$> traverseEnvFrag (traverseFreeNames scope traversal) frag

instance (HasNames e1, HasNames e2) => HasNames (PairH e1 e2) where
  traverseFreeNames scope env (PairH x y) =
    PairH <$> traverseFreeNames scope env x <*> traverseFreeNames scope env y

instance (Traversable f, HasNames e) => HasNames (H f e) where
  traverseFreeNames scope env (H xs) = H <$> traverse (traverseFreeNames scope env) xs

instance IsString RawName where
  fromString s = RawName (fromString s) 0

instance Show (PlainBinder n l) where
  show Ignore = "_"
  show (UnsafeMakeBinder v) = show v

instance (forall n' l. Show (b n' l), forall n'. Show (body n')) => Show (Abs b body n) where
  show (Abs b body) = "(Abs " <> show b <> " " <> show body <> ")"

instance (forall n' l'. Show (b n' l')) => Show (Nest b n l) where
  show Empty = ""
  show (Nest b rest) = "(Nest " <> show b <> " in " <> show rest <> ")"

instance (BindsNames b, HasNames ann) => BindsNames (AnnBinderP b ann) where
  traverseFreeNamesBinders scope t (b:>ann) = do
    ann' <- traverseFreeNames scope t ann
    traverseFreeNamesBinders scope t b >>= \case
      Fresh ext b' frag -> return $ Fresh ext (b':>ann') frag

  asScopeFrag (b:>_) = asScopeFrag b

instance (BindsOneName b, HasNames ann) => BindsOneName (AnnBinderP b ann) where
  (b:>_) @> x = b @> x

instance HasNames (LiftH a) where
  traverseFreeNames s t (LiftH x) = return $ LiftH x

instance Pretty (Name n) where
  pretty name = pretty $ show name

instance Pretty (PlainBinder n l) where
  pretty = undefined

instance (PrettyH2 b, PrettyH ann) => Pretty (AnnBinderP b ann n l) where
  pretty = undefined

instance (PrettyH2 b) => Pretty (Nest b n l) where
  pretty _ = undefined --  pretty $ toList xs

instance (PrettyH2 b, PrettyH e) => Pretty (Abs b e n) where
  pretty _ = undefined
