{-# LANGUAGE GADTs #-}
-- module TypedInterpreter where

import qualified Data.Map.Strict as M

type Table a b = M.Map a b

data Term = Lit Int
          | Var Int deriving (Show)

data TTerm e t where
  TLit :: Int -> TTerm e Int
  TVar :: TVar e t -> TTerm e t

data TVar e t where
  Zero ::             TVar (t , e) t
  Succ :: TVar e t -> TVar (t', e) t

data Ty t where
  IntType :: Ty Int
  ArrType :: Ty a -> Ty b -> Ty (a -> b)
  TabType :: Ty a -> Ty b -> Ty (Table a b)

data Typed a where
  Typed :: Ty t -> a t -> Typed a

data Env e where
  Nil  :: Env ()
  Cons :: Ty t -> Env e -> Env (t, e)

data ValEnv e where
  VNil  :: ValEnv ()
  VCons :: t -> ValEnv e -> ValEnv (t, e)

lookupVal :: TVar e t -> ValEnv e -> t
lookupVal Zero (VCons x _) = x
lookupVal (Succ n) (VCons _ env) = lookupVal n env

lookupType :: Int -> Env e -> Typed (TVar e)
lookupType 0 (Cons t _) = Typed t Zero
lookupType n (Cons _ env) = case lookupType (n-1) env of
                              Typed t v -> Typed t (Succ v)

typeExpr :: Term -> Env e -> Maybe (Typed (TTerm e))
typeExpr expr env =
  case expr of
  Lit x -> return $ Typed IntType (TLit x)
  Var v -> return $ case lookupType v env of
                       Typed t v -> Typed t (TVar v)


eval :: TTerm e t -> ValEnv e -> t
eval expr env = case expr of
  TVar v -> lookupVal v env
  TLit x -> x

evalt :: Typed (TTerm e) -> ValEnv e-> String
evalt (Typed t expr) env =
  let v = eval expr env
  in case t of
    IntType -> show v


tenv = Cons IntType Nil
venv = VCons 5 VNil

expr = Var 0
texpr = case typeExpr expr tenv of
          Just e -> e
val = evalt texpr venv

main :: IO ()
main = do
  print $ val
