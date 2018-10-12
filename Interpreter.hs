{-# LANGUAGE GADTs #-}

module Interpreter (Expr (..), BinOpName (..), evalClosed) where

import qualified Data.Map.Strict as Map
import qualified Table as Table


data Expr = BinOp BinOpName Expr Expr
          | Lit Int
          | Var Int
          | Lam Expr
          | App Expr Expr
          | IdxComp Expr
          | Get Expr Int
          deriving (Show)

data BinOpName = Add | Mul | Sub | Div deriving (Show)
data UnOpName = Iota deriving (Show)

-- example:
-- index env depth : how many dynamically enclosing indices do we have
-- index env:  (5, [0, 2])
-- rank: 4
    --                     1   0  --rank---
-- table indices: [... * * * * * | * * * * ]
-- ienv :: list of

data Val = TableVal (Table.Table Int Int) Rank
         | LamVal Env IEnv Expr
         | UnOp UnOpName  deriving (Show)

type IEnv = (Int, [Int]) -- depth, and positions of in-scope indices
type Env = [Val]
type Rank = Int

eval :: Expr -> Env -> IEnv -> Val
eval (Lit c) _ (d, _) = TableVal (Table.scalar c) 0
eval (Var v) env (d, _) = env !! v
eval (BinOp b e1 e2) env ienv = let v1 = eval e1 env ienv
                                    v2 = eval e2 env ienv
                                in case (v1, v2) of
     ((TableVal t1 r1), (TableVal t2 r2)) | r1 == r2 ->
           TableVal (Table.map2 (binOpFun b) t1 t2) r1

eval (Lam body) env ienv = LamVal env ienv body
eval (App fexpr arg) env ienv =
    let f = eval fexpr env ienv
        x = eval arg env ienv
        (d, _) = ienv
    in case f of
        LamVal env' (_, idxs) body -> eval body (x:env') (d, idxs)

eval (IdxComp body) env (d, idxs) = let ienv' = ((d + 1), d:idxs) in
                                    case eval body env ienv' of
                                      TableVal t r -> TableVal t (r + 1)
eval (Get e i) env ienv = let (_, idxs) = ienv
                              i' = idxs !! i
                          in case eval e env ienv of
              TableVal t r -> TableVal (Table.diag t (r - 1) (r + i')) (r - 1)

binOpFun :: BinOpName -> Int -> Int -> Int
binOpFun Add = (+)
binOpFun Mul = (*)
binOpFun Sub = (-)

builtinEnv = [UnOp Iota]

evalClosed :: Expr -> Val
evalClosed e = eval e builtinEnv (0, [])


-- ienv
-- rank
-- which indices point to what

-- unMapVal :: Val -> ValMap
-- unMapVal (MapVal m) = m

-- promoteKey :: Int -> ValMap -> ValMap
-- promoteKey 0 x = undefined
-- promoteKey 1 x = transpose x
-- promoteKey n x = transpose $ valMapMap (promoteKey (n-1)) x

-- transpose :: ValMap -> ValMap
-- transpose (BMap.Dict m) = undefined
-- transpose (BMap.Broadcast v) = case v of
--    MapVal v' -> BMap.map (MapVal . BMap.Broadcast)   v'


-- valMapMap :: (ValMap -> ValMap) -> ValMap -> ValMap
-- valMapMap f m = let f' x' = case x' of MapVal m' -> MapVal (f m')
--                 in BMap.map f' m

-- getFromVal :: Key -> Val -> Maybe Val
-- getFromVal k (MapVal v) = BMap.lookup k v

-- zipIdxs :: ValMap -> Val
-- zipIdxs (BMap.Dict m) = MapVal . BMap.Dict $ Map.mapMaybeWithKey getFromVal m
-- zipIdxs (BMap.Broadcast v) = v


-- -- evalGet (Dict v) iv [] = error "empty index environment"
-- -- evalGet (Broadcast v) iv (curIEnv:[]) | iv == curIEnv = v

-- -- evalGet (Dict (MapVal (Broadcast v)) iv (curIEnv:[]) | iv == curIEnv =


-- dummyVal :: Val
-- dummyVal = (MapVal . BMap.fromList) [(0, IntVal 10), (1, IntVal 20)]

-- emptyEnv :: Env
-- emptyEnv = Map.fromList [("d", dummyVal)]


-- lift :: Int -> Val -> Val
-- lift 0 v = v
-- lift n v = lift (n - 1) (MapVal (BMap.Broadcast v))

-- evalApp :: Val -> Val -> Val
-- evalApp (LamVal env ienv v body) x = eval body (Map.insert v x env) ienv
-- evalApp (MapVal f) (MapVal x) = MapVal $ BMap.intersectionWith evalApp f x




-- -- typed experiments

-- -- data TExpr env ienv t where
-- --   TLit  :: Int -> TExpr env ienv Int
-- --   TVar  :: TVar env t -> TExpr env ienv t
-- --   TLet  :: TExpr env ienv a -> TExpr (a, env) ienv b -> TExpr env ienv b
-- --   TLam  :: TExpr (a,env) ienv b -> TExpr env ienv (a -> b)
-- --   TApp  :: TExpr env ienv (a -> b) -> TExpr env ienv a -> TExpr env ienv b
-- --   TComp :: TExpr env (i, ienv) t -> TExpr env ienv t
-- --   TGet  :: TExpr env ienv t -> IVar ienv -> TExpr env ienv t
-- --   TBinOp:: BinOpName -> TExpr env ienv Int -> TExpr env ienv Int
-- --                                                -> TExpr env ienv Int
-- -- data TVar env t where
-- --   VZ :: TVar (t, env) t  -- s/env/()/ ?
-- --   VS :: TVar env t -> TVar (a, env) t

-- -- data IVar ienv where
-- --   IVZ :: IVar ((), env)
-- --   IVS :: IVar env -> IVar ((), env)

-- -- typeEvalShow :: Expr -> String
-- -- typeEvalShow = undefined

-- -- evalTyped :: env -> ienv -> TExpr env ienv t -> t
-- -- evalTyped _ _ (TLit x) = x
-- -- evalTyped env _ (TVar v) = lookp v env
-- -- -- evalTyped env _ (TVar v) = lookp v env

-- -- lookp :: TVar env t -> env -> t
-- -- lookp = undefined

-- -- typeExpr :: Expr -> TExpr env ienv t
-- -- typeExpr (Lit x) = TLit x
-- -- typeExpr (Lit x) = TLit x
