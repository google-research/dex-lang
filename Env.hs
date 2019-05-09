module Env (Env, envLookup, newEnv, addV, addVs, isin,
            envNames, envPairs, envDelete, envSubset, (!)) where

import Data.Traversable
import qualified Data.Map.Strict as M
import Control.Applicative (liftA)
import Data.Foldable (toList)
import Data.Text.Prettyprint.Doc

import Fresh

newtype Env a = Env (M.Map Name a)  deriving (Show, Eq, Ord)

newEnv :: Traversable f => f (Name, a) -> Env a
newEnv xs = Env (M.fromList (toList xs))

addV :: (Name, a) -> Env a -> Env a
addV (v, x) (Env m) = Env (M.insert v x m)

addVs :: Traversable f => f (Name, a) -> Env a -> Env a
addVs xs (Env m) = Env m' -- use foldl to traverse patterns left-to-right
  where m' = foldl (flip $ uncurry M.insert) m xs

envLookup :: Env a -> Name -> Maybe a
envLookup (Env m) v = M.lookup v m

envNames :: Env a -> [Name]
envNames (Env m) = M.keys m

envPairs :: Env a -> [(Name, a)]
envPairs (Env m) = M.toAscList m

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
