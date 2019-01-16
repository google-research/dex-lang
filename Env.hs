module Env (Env, FreeEnv (..), Var (..),
            newFreeEnv, emptyEnv, extendEnv, catEnv, isin,
            (!!), envFromFree, updateFreeEnv) where

import Prelude hiding ((!!))
import qualified Prelude as P
import qualified Data.Map.Strict as M

data FreeEnv a = FreeEnv (M.Map String a)   deriving (Show, Eq, Ord)
data Env i a = Env (FreeEnv a) [a]          deriving (Show, Eq, Ord)
data Var i = FV String | BV Int             deriving (Show, Eq, Ord)

newFreeEnv :: [(String, a)] -> FreeEnv a
newFreeEnv = FreeEnv . M.fromList

envFromFree :: FreeEnv a -> Env i a
envFromFree env = Env env []

emptyEnv :: Env i a
emptyEnv = envFromFree (newFreeEnv [])

extendEnv :: Env i a -> a -> Env i a
extendEnv (Env fvs bvs) x = Env fvs (x:bvs)

catEnv :: Env i a -> [a] -> Env i a
catEnv (Env fvs bvs) xs = Env fvs (xs ++ bvs)

updateFreeEnv :: FreeEnv a -> String -> a -> FreeEnv a
updateFreeEnv (FreeEnv m) k v = FreeEnv $ M.insert k v m

isin :: Var i -> Env (Var i) a -> Bool
isin i (Env (FreeEnv fvs) bvs) = case i of
  FV s -> case M.lookup s fvs of
            Just _ -> True
            Nothing -> False
  BV i -> i < length bvs

(!!) :: Env (Var i) a -> Var i -> a
(Env (FreeEnv fvs) bvs) !! i = case i of
  FV s -> case M.lookup s fvs of Just x -> x
  BV i -> bvs P.!! i

instance Functor (Env i) where
  fmap f (Env (FreeEnv m) xs) = Env (FreeEnv (fmap f m)) (map f xs)
