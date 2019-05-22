{-# LANGUAGE OverloadedStrings #-}

module Env (Env, envLookup, isin, envNames, envPairs, envDelete,
            envSubset, (!), (%>), (@>), GenBinder (..), bind, bindFold,
            bindWith, binderVars, binderVar, binderAnn, extendWith,
            freshenBinder, freshenBinders, addAnnot, replaceAnnot,
            bindRecZip, lookupSubst) where

import Data.Traversable
import qualified Data.Map.Strict as M
import Control.Applicative (liftA)
import Control.Monad.Reader
import Data.Text.Prettyprint.Doc

import Util
import Fresh
import Record

newtype Env a = Env (M.Map Name a)  deriving (Show, Eq, Ord)
data GenBinder a = Bind Name a
                 | Ignore a  deriving (Show, Eq, Ord)

infixr 7 %>

(%>) :: Name -> a -> GenBinder a
name %> annot = Bind name annot

envLookup :: Env a -> Name -> Maybe a
envLookup (Env m) v = M.lookup v m

envNames :: Env a -> [Name]
envNames (Env m) = M.keys m

envPairs :: Env a -> [(Name, a)]
envPairs (Env m) = M.toAscList m

lookupSubst :: Name -> Env Name -> Name
lookupSubst v (Env m) = M.findWithDefault v v m

envDelete :: Name -> Env a -> Env a
envDelete v (Env m) = Env (M.delete v m)

envSubset :: [Name] -> Env a -> Env a
envSubset vs (Env m) = Env $ M.intersection m (M.fromList [(v,()) | v <- vs])

isin :: Name -> Env a -> Bool
isin v env = case envLookup env v of Just _  -> True
                                     Nothing -> False

(!) :: Env a -> Name -> a
env ! v = case envLookup env v of
  Just x -> x
  Nothing -> error $ "Lookup of " ++ show v
                       ++ " in " ++ show (envNames env) ++ " failed"

infixr 7 @>

(@>) :: Name -> a -> Env a
k @> v = Env $ M.singleton k v

-- return a list to allow for underscore binders
binderVars :: GenBinder a -> [Name]
binderVars (Bind v _) = [v]
binderVars (Ignore _) = []

binderVar :: GenBinder a -> Maybe Name
binderVar (Bind v _) = Just v
binderVar (Ignore _) = Nothing

binderAnn :: GenBinder a -> a
binderAnn (Bind _ x) = x
binderAnn (Ignore x) = x

bind :: GenBinder a -> Env a
bind (Bind v x) = v @> x
bind (Ignore _) = mempty

bindWith :: GenBinder a -> b -> Env (a, b)
bindWith b y = bind $ fmap (\x -> (x,y)) b

bindFold :: Foldable f => f (GenBinder a) -> Env a
bindFold bs = foldMap bind bs

bindRecZip :: RecTreeZip t => RecTree (GenBinder a) -> t -> Env (a, t)
bindRecZip bs t = foldMap (uncurry bindWith) (recTreeZip bs t)

addAnnot :: GenBinder a -> b -> GenBinder (a, b)
addAnnot b y = fmap (\x -> (x, y)) b

replaceAnnot :: GenBinder a -> b -> GenBinder b
replaceAnnot b y = fmap (const y) b

extendWith :: (MonadReader env m, Monoid env) => env -> m a -> m a
extendWith env m = local (env <>) m

freshenBinder :: MonadFreshR m =>
                 GenBinder a -> (Env Name -> GenBinder a -> m b) -> m b
freshenBinder b cont = do
  scope <- askFresh
  let (b', (scope', subst)) = runEnvM (freshenBinderEnvM b) (scope, mempty)
  localFresh (scope' <>) (cont subst b')

freshenBinders :: (Traversable f, MonadFreshR m) =>
                 f (GenBinder a) -> (Env Name -> f (GenBinder a) -> m b) -> m b
freshenBinders pat cont = do
  scope <- askFresh
  let (pat', (scope', subst)) =
        runEnvM (traverse freshenBinderEnvM pat) (scope, mempty)
  localFresh (scope' <>) (cont subst pat')

freshenBinderEnvM :: GenBinder a -> EnvM (FreshScope, Env Name) (GenBinder a)
freshenBinderEnvM (Ignore x) = return (Ignore x)
freshenBinderEnvM (Bind v x) = do
  (scope, _) <- askEnv
  let v' = rename v scope
  addEnv (newScope v', v@>v')
  return (v' %> x)

instance Functor Env where
  fmap = fmapDefault

instance Foldable Env where
  foldMap = foldMapDefault

instance Traversable Env where
  traverse f (Env m) = liftA Env (traverse f m)


instance Semigroup (Env a) where
  Env m <> Env m' = Env (m <> m')

instance Monoid (Env a) where
  mempty = Env mempty
  mappend = (<>)

instance Pretty a => Pretty (Env a) where
  pretty (Env m) = pretty (M.toAscList m)

instance Pretty a => Pretty (GenBinder a) where
  pretty (Bind v x) = pretty v   <> "::" <> pretty x
  pretty (Ignore x) = "_ ::" <> pretty x

instance Functor GenBinder where
  fmap = fmapDefault

instance Foldable GenBinder where
  foldMap = foldMapDefault

instance Traversable GenBinder where
  traverse f (Bind v x) = fmap (Bind v) (f x)
  traverse f (Ignore x) = fmap Ignore   (f x)
