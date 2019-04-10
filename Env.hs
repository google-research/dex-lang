module Env (Env (..), Var (..), VarName, TempVar, envLookup,
            newEnv, addLocal, addLocals, addTop, isin, (!), locals) where

-- module Env (Env (..), GVar (..), VarName (..), ExVar,
--             newEnv, addFVar, addBVar, addBVars,
--             envDiff, isin, (!), fVars, bVars, toDeBruijn, numBound) where

import Data.List (elemIndex)
import Data.Semigroup
import Data.Traversable
import qualified Data.Map.Strict as M
import Control.Applicative (liftA, liftA2, liftA3)

data Env a = Env (M.Map VarName a) (M.Map Var a)
                    deriving (Show, Eq, Ord)

type TempVar = Int
type VarName = String
data Var = TempVar TempVar
         | NamedVar VarName
         | BoundVar Int    deriving (Eq, Ord)

newEnv :: [(VarName, a)] -> Env a
newEnv xs = undefined -- Env (M.fromList xs) []

addTop :: String -> a -> Env a -> Env a
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
    Nothing -> case v of
                 NamedVar s -> M.lookup s top
                 _ -> Nothing

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

instance Show Var where
  show v = case v of
    TempVar n -> "#" ++ show n
    NamedVar name -> name
    BoundVar n -> "BV" ++ show n
