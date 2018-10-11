{-# LANGUAGE GADTs #-}

module Interpreter (Expr (..), BinOpName (..), evalClosed) where

import qualified Data.Map.Strict as Map
import qualified BMap as BMap

data Expr = BinOp BinOpName Expr Expr
          | Lit Integer
          | Var VarName
          | Let VarName Expr Expr
          | Lam VarName Expr
          | App Expr Expr
          | IdxComp IdxVarName Expr
          | Get Expr IdxVarName
          deriving (Show)

data TExpr env ienv t where
  TLit  :: Integer -> TExpr env ienv Integer
  TVar  :: TVar env t -> TExpr env ienv t
  TLet  :: TExpr env ienv a -> TExpr (a, env) ienv b -> TExpr env ienv b
  TLam  :: TExpr (a,env) ienv b -> TExpr env ienv (a -> b)
  TApp  :: TExpr env ienv (a -> b) -> TExpr env ienv a -> TExpr env ienv b
  TComp :: TExpr env (i, ienv) t -> TExpr env ienv t
  TGet  :: TExpr env ienv t -> IVar ienv -> TExpr env ienv t
  TBinOp:: BinOpName -> TExpr env ienv Integer -> TExpr env ienv Integer
                                               -> TExpr env ienv Integer

data TVar env t where
  VZ :: TVar (t, env) t  -- s/env/()/ ?
  VS :: TVar env t -> TVar (a, env) t

data IVar ienv where
  IVZ :: IVar ((), env)
  IVS :: IVar env -> IVar ((), env)

-- typeEvalShow :: Expr -> String
-- typeEvalShow = undefined


evalTyped :: env -> ienv -> TExpr env ienv t -> t
evalTyped _ _ (TLit x) = x
evalTyped env _ (TVar v) = lookp v env
-- evalTyped env _ (TVar v) = lookp v env

lookp :: TVar env t -> env -> t
lookp = undefined



-- typeExpr :: Expr -> TExpr env ienv t
-- typeExpr (Lit x) = TLit x
-- typeExpr (Lit x) = TLit x




data BinOpName = Add | Mul | Sub | Div deriving (Show)

data Val = IntVal Integer
         | LamVal Env IdxEnv VarName Expr
         | MapVal ValMap  deriving (Show)

type ValMap = BMap.BMap Key Val
type Key = Int
type VarName = String
type IdxVarName = String
type Env = Map.Map VarName Val
type IdxEnv = [IdxVarName]


evalGet :: IdxVarName -> IdxEnv -> Val -> Val
evalGet iv (cur_iv:rest) (MapVal m)
     | iv == cur_iv = let f = MapVal . promoteKey (length rest) . unMapVal
                      in  zipIdxs $ BMap.map f m
     | otherwise = MapVal $ BMap.map (evalGet iv rest) m


unMapVal :: Val -> ValMap
unMapVal (MapVal m) = m

promoteKey :: Int -> ValMap -> ValMap
promoteKey 0 x = undefined
promoteKey 1 x = transpose x
promoteKey n x = transpose $ valMapMap (promoteKey (n-1)) x

transpose :: ValMap -> ValMap
transpose (BMap.Dict m) = undefined
transpose (BMap.Broadcast v) = case v of
   MapVal v' -> BMap.map (MapVal . BMap.Broadcast)   v'


valMapMap :: (ValMap -> ValMap) -> ValMap -> ValMap
valMapMap f m = let f' x' = case x' of MapVal m' -> MapVal (f m')
                in BMap.map f' m

getFromVal :: Key -> Val -> Maybe Val
getFromVal k (MapVal v) = BMap.lookup k v

zipIdxs :: ValMap -> Val
zipIdxs (BMap.Dict m) = MapVal . BMap.Dict $ Map.mapMaybeWithKey getFromVal m
zipIdxs (BMap.Broadcast v) = v


-- evalGet (Dict v) iv [] = error "empty index environment"
-- evalGet (Broadcast v) iv (curIEnv:[]) | iv == curIEnv = v

-- evalGet (Dict (MapVal (Broadcast v)) iv (curIEnv:[]) | iv == curIEnv =

eval :: Expr -> Env -> IdxEnv -> Val
eval (Lit c) _ ienv = lift (length ienv) (IntVal c)
eval (Var v) env _ = case Map.lookup v env of
                     Just val -> val
                     Nothing -> error $ "Undefined variable: " ++ show v
eval (BinOp b e1 e2) env ienv = let v1 = eval e1 env ienv
                                    v2 = eval e2 env ienv
                                in evalBinOp b v1 v2
eval (Let v bound body) env ienv = let boundVal = eval bound env ienv
                                       newEnv = Map.insert v boundVal env
                                   in eval body newEnv ienv
eval (Lam v body) env ienv = LamVal env ienv v body
eval (App fexpr arg) env ienv = let f = eval fexpr env ienv
                                    x = eval arg env ienv
                                in evalApp f x
eval (IdxComp iv body) env ienv = eval body (Map.map (lift 0) env) (iv:ienv)
eval (Get e iv) env ienv = let v = eval e env ienv
                           in evalGet iv ienv v

dummyVal :: Val
dummyVal = (MapVal . BMap.fromList) [(0, IntVal 10), (1, IntVal 20)]

emptyEnv :: Env
emptyEnv = Map.fromList [("d", dummyVal)]


lift :: Int -> Val -> Val
lift 0 v = v
lift n v = lift (n - 1) (MapVal (BMap.Broadcast v))

evalApp :: Val -> Val -> Val
evalApp (LamVal env ienv v body) x = eval body (Map.insert v x env) ienv
evalApp (MapVal f) (MapVal x) = MapVal $ BMap.intersectionWith evalApp f x

evalClosed :: Expr -> Val
evalClosed e = eval e emptyEnv []

evalBinOp :: BinOpName -> Val -> Val -> Val
evalBinOp b (IntVal v1) (IntVal v2) = IntVal $ evalBinOpFun b v1 v2
evalBinOp b (MapVal m1) (MapVal m2) =
    MapVal $ BMap.intersectionWith (evalBinOp b) m1 m2

evalBinOpFun Add = (+)
evalBinOpFun Mul = (*)
evalBinOpFun Sub = (-)
