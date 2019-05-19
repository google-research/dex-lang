module Env (Env, envLookup, isin, envNames, envPairs, envDelete,
            envSubset, (!), (@>), GenBinder (..), bind, bindFold,
            binderVars, binderVar, binderVal, extendWith,
            addAnnot, replaceAnnot) where

import Data.Traversable
import qualified Data.Map.Strict as M
import Control.Applicative (liftA)
import Control.Monad.Reader
import Data.Text.Prettyprint.Doc

import Fresh

newtype Env a = Env (M.Map Name a)  deriving (Show, Eq, Ord)
data GenBinder a = Bind Name a  deriving (Show, Eq, Ord)

envLookup :: Env a -> Name -> Maybe a
envLookup (Env m) v = M.lookup v m

envNames :: Env a -> [Name]
envNames (Env m) = M.keys m

envPairs :: Env a -> [GenBinder a]
envPairs (Env m) = map (uncurry Bind) (M.toAscList m)

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

binderVar :: GenBinder a -> Name
binderVar (Bind v _) = v

binderVal :: GenBinder a -> a
binderVal (Bind _ x) = x

bind :: GenBinder a -> Env a
bind (Bind v x) = v @> x

bindFold :: Foldable f => f (GenBinder a) -> Env a
bindFold bs = foldMap bind bs

addAnnot :: GenBinder a -> b -> GenBinder (a, b)
addAnnot b y = fmap (\x -> (x, y)) b

replaceAnnot :: GenBinder a -> b -> GenBinder b
replaceAnnot b y = fmap (const y) b

extendWith :: (MonadReader env m, Monoid env) => env -> m a -> m a
extendWith env m = local (env <>) m

instance Functor (Env) where
  fmap = fmapDefault

instance Foldable (Env) where
  foldMap = foldMapDefault

instance Traversable (Env) where
  traverse f (Env m) = liftA Env (traverse f m)


instance Semigroup (Env a) where
  Env m <> Env m' = Env (m <> m')

instance Monoid (Env a) where
  mempty = Env mempty
  mappend = (<>)

instance Pretty a => Pretty (Env a) where
  pretty (Env m) = pretty ( M.toAscList m)

instance Functor GenBinder where
  fmap = fmapDefault

instance Foldable GenBinder where
  foldMap = foldMapDefault

instance Traversable GenBinder where
  traverse f (Bind v x) = fmap (Bind v) (f x)
