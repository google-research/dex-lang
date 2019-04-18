module Env (Env, envLookup, newEnv, addV, addVs, isin,
            envVars, envPairs, envDelete, (!)) where

import Data.Semigroup
import Data.Traversable
import qualified Data.Map.Strict as M
import Control.Applicative (liftA)
import Fresh

newtype Env a = Env (M.Map Var a)  deriving (Show, Eq, Ord)

newEnv :: [(Var, a)] -> Env a
newEnv xs = Env (M.fromList xs)

addV :: (Var, a) -> Env a -> Env a
addV (v, x) (Env m) = Env (M.insert v x m)

addVs :: Traversable f => f (Var, a) -> Env a -> Env a
addVs xs (Env m) = Env m'
  where m' = foldr (uncurry M.insert) m xs

envLookup :: Env a -> Var -> Maybe a
envLookup (Env m) v = M.lookup v m

envVars :: Env a -> [Var]
envVars (Env m) = M.keys m

envPairs :: Env a -> [(Var, a)]
envPairs (Env m) = M.toAscList m

envDelete :: Var -> Env a -> Env a
envDelete v (Env m) = Env (M.delete v m)

isin :: Var -> Env a -> Bool
isin v env = case envLookup env v of Just _  -> True
                                     Nothing -> False

(!) :: Env a -> Var -> a
env ! v = case envLookup env v of
  Just x -> x
  Nothing -> error $ "Lookup of " ++ show v ++ " failed"

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
