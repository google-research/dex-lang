module Env (Env, FreeEnv (..), Var (..), VarName,
            newFreeEnv, emptyEnv, emptyFreeEnv, extendEnv, catEnv, isin,
            (!!), envFromFree, envFromFrees, updateFreeEnv, freeEnvToList) where

import Prelude hiding ((!!))
import qualified Prelude as P
import qualified Data.Map.Strict as M

type VarName = String
data FreeEnv a = FreeEnv (M.Map VarName a)  deriving (Show, Eq, Ord)
data Env i a = Env (FreeEnv a) [a]          deriving (Show, Eq, Ord)
data Var i = FV VarName | BV Int            deriving (Show, Eq, Ord)

newFreeEnv :: [(String, a)] -> FreeEnv a
newFreeEnv = FreeEnv . M.fromList

freeEnvToList :: FreeEnv a -> [(String, a)]
freeEnvToList (FreeEnv m) = M.toList m

envFromFree :: FreeEnv a -> Env i a
envFromFree env = Env env []

envFromFrees :: FreeEnv a -> FreeEnv a -> Env i a
envFromFrees (FreeEnv m1) (FreeEnv m2) = Env (FreeEnv $ M.union m2 m1) []

emptyFreeEnv :: FreeEnv a
emptyFreeEnv = newFreeEnv []

emptyEnv :: Env i a
emptyEnv = envFromFree emptyFreeEnv

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
  FV s -> case M.lookup s fvs of
            Just x -> x
            Nothing -> error ("Lookup of " ++ show s ++
                              " failed! This is a compiler bug")
  BV i -> bvs P.!! i

instance Functor (Env i) where
  fmap f (Env fenv xs) = Env (fmap f fenv) (map f xs)

instance Functor FreeEnv where
  fmap f (FreeEnv m) = FreeEnv (fmap f m)
