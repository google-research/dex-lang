{-# LANGUAGE GADTs #-}

module Interpreter (Expr (..), BinOpName (..), binOpIdx, evalClosed) where

import qualified Data.Map.Strict as Map
import qualified Table as Table

data Expr = Lit Int
          | Var Int
          | Lam Expr
          | App Expr Expr
          | IdxComp Expr
          | Get Expr Int
              deriving (Show)

-- example:
-- index env depth : how many dynamically enclosing indices do we have
-- index env:  (5, [0, 2])
-- rank: 4
    --                     1   0  --rank---
-- table indices: [... * * * * * | * * * * ]
-- ienv :: list of

data Val = TV (Table.Table Int Int) Rank
         | LamVal Env IEnv Expr
         | Builtin BuiltinName [Val]  deriving (Show)

data BinOpName = Add | Mul | Sub | Div  deriving (Show)

data BuiltinName = BinOp BinOpName
                 | Iota
                 | Reduce  deriving (Show)

type IEnv = (Int, [Int]) -- depth, and positions of in-scope indices
type Env = [Val]
type Rank = Int

eval :: Expr -> Env -> IEnv -> Val
eval (Lit c) _ (d, _) = TV (Table.fromScalar c) 0
eval (Var v) env (d, _) = env !! v
eval (Lam body) env ienv = LamVal env ienv body
eval (App fexpr arg) env ienv =
    let f = eval fexpr env ienv
        x = eval arg env ienv
        (d, _) = ienv
    in case f of
        LamVal env' (_, idxs) body -> eval body (x:env') (d, idxs)
        Builtin name vs -> let args = x:vs
                           in if length args < numArgs name
                                then Builtin name args
                                else evalBuiltin name (reverse args)

eval (IdxComp body) env (d, idxs) = let ienv' = ((d + 1), d:idxs) in
                                    case eval body env ienv' of
                                      TV t r -> TV t (r + 1)
eval (Get e i) env ienv = let (_, idxs) = ienv
                              i' = idxs !! i
                          in case eval e env ienv of
              TV t r -> TV (Table.diag t (r - 1) (r + i')) (r - 1)


numArgs :: BuiltinName -> Int
numArgs (BinOp _) = 2
numArgs Iota      = 1

evalBuiltin :: BuiltinName -> [Val] -> Val
evalBuiltin (BinOp b) (TV t1 0 : TV t2 0 : []) =
    TV (Table.map2 (binOpFun b) t1 t2) 0
evalBuiltin Iota (TV t 0 : []) = TV (Table.iota t) 1

binOpFun :: BinOpName -> Int -> Int -> Int
binOpFun Add = (+)
binOpFun Mul = (*)
binOpFun Sub = (-)

builtinEnv = [ Builtin Iota []
             , Builtin (BinOp Add) []
             , Builtin (BinOp Mul) []
             , Builtin (BinOp Sub) []
             , Builtin (BinOp Div) []
             ]

binOpIdx :: BinOpName -> Int
binOpIdx b = case b of Add -> 0 ; Mul -> 1;
                       Sub -> 2 ; Div -> 3

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
