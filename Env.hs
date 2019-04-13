module Env (Env (..), envLookup, newEnv, addLocal, addLocals, addTop,
            isin, (!), locals) where

import Data.List (elemIndex)
import Data.Semigroup
import Data.Traversable
import qualified Data.Map.Strict as M
import Control.Applicative (liftA, liftA2, liftA3)
import Fresh

data Env a = Env (M.Map Var a) (M.Map Var a) deriving (Show, Eq, Ord)

newEnv :: [(Var, a)] -> Env a
newEnv xs = Env (M.fromList xs) mempty

addTop :: Var -> a -> Env a -> Env a
addTop v x (Env top local) = Env (M.insert v x top) local

locals :: Env a -> [(Var, a)]
locals (Env _ local) = M.toAscList local

addLocal :: (Var, a) -> Env a -> Env a
addLocal (v, x) (Env top local) = Env top (M.insert v x local)

addLocals :: Traversable f => f (Var, a) -> Env a -> Env a
addLocals xs (Env top local) = Env top local'
  where local' = foldr (uncurry M.insert) local xs

envLookup :: Env a -> Var -> Maybe a
envLookup (Env top local) v =
  case M.lookup v local of
    Just x -> Just x
    Nothing -> M.lookup v top

isin :: Var -> Env a -> Bool
isin v env = case envLookup env v of Just _  -> True
                                     Nothing -> False

(!) :: Env a -> Var -> a
env ! v = case envLookup env v of
  Just x -> x
  Nothing -> error ("Lookup of " ++ show v ++ " failed! This is a compiler bug")

instance Functor (Env) where
  fmap = fmapDefault

instance Foldable (Env) where
  foldMap = foldMapDefault

instance Traversable (Env) where
  traverse f (Env fenv xs) = liftA2 Env (traverse f fenv) (traverse f xs)


instance Semigroup (Env a) where
  Env m1 m2 <> Env m1' m2' = Env (m1 <> m1') (m2 <> m2')

instance Monoid (Env a) where
  mempty = Env mempty mempty
  mappend = (<>)
