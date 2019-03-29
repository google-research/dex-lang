module Env (Env (..), GVar (..), VarName (..),
            newEnv, addFVar, addBVar, addBVars,
            envDiff, isin, (!), fVars, bVars, toDeBruijn, numBound) where

import Data.List (elemIndex)
import Data.Semigroup
import Data.Traversable
import qualified Data.Map.Strict as M
import Control.Applicative (liftA, liftA2, liftA3)

data Env i a = Env (M.Map VarName a) [a]  deriving (Show, Eq, Ord)
data GVar i = FV VarName
            | BV Int
               deriving (Show, Eq, Ord)

data VarName = TempVar Int
             | NamedVar String  deriving (Show, Eq, Ord)

newEnv :: [(VarName, a)] -> Env i a
newEnv xs = Env (M.fromList xs) []

addFVar :: VarName -> a -> Env i a -> Env i a
addFVar k v (Env fvs bvs)= Env (M.insert k v fvs) bvs

addBVar :: a -> Env i a -> Env i a
addBVar x (Env fvs bvs) = Env fvs (x:bvs)

addBVars :: [a] -> Env i a -> Env i a
addBVars = flip $ foldr addBVar

envDiff ::Env i a -> Env i b -> Env i a
envDiff (Env fvs1 _) (Env fvs2 _) = Env (M.difference fvs1 fvs2) []

fVars :: Env i a -> [VarName]
fVars (Env fvs _) = M.keys fvs

bVars :: Env i a -> [a]
bVars (Env _ bvs) = bvs

numBound :: Env i a -> Int
numBound (Env _ bvs) = length bvs

isin :: GVar i -> Env (GVar i) a -> Bool
isin i (Env fvs bvs) = case i of
  FV s -> case M.lookup s fvs of
            Just _  -> True
            Nothing -> False
  BV i -> i < length bvs

(!) :: Env (GVar i) a -> GVar i -> a
(Env fvs bvs) ! i = case i of
  FV s -> case M.lookup s fvs of
            Just x -> x
            Nothing -> error ("Lookup of " ++ show s ++
                              " in env " ++ show (M.keys fvs) ++
                              " failed! This is a compiler bug")
  BV i -> if i < length(bvs)
            then bvs !! i
            else error "Env lookup index too large"

toDeBruijn :: [VarName]->  GVar i -> GVar i
toDeBruijn vs (FV v) = case elemIndex v vs of Just i  -> BV i
                                              Nothing -> FV v
toDeBruijn vs (BV i) = BV i

instance Functor (Env i) where
  fmap = fmapDefault

instance Foldable (Env i) where
  foldMap = foldMapDefault

instance Traversable (Env i) where
  traverse f (Env fenv xs) = liftA2 Env (traverse f fenv) (traverse f xs)

instance Semigroup (Env i a) where
  Env m1 xs1 <> Env m2 xs2 = Env (m1 <> m2) (xs1 <> xs2)

instance Monoid (Env i a) where
  mempty = Env mempty []
  mappend = (<>)
