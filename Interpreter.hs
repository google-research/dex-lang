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

data Val = TV (Table.Table Int Int) Rank
         | LamVal Env IEnv Expr
         | Builtin BuiltinName [Val]

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

-- example:
-- index env depth : how many *dynamically* enclosing indices do we have
-- index env:  (5, [0, 2])
-- rank: 4
    --                     1   0  --rank---
-- table indices: [... * * * * * | * * * * ]

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
             , Builtin (BinOp Div) [] ]

binOpIdx :: BinOpName -> Int
binOpIdx b = case b of Add -> 0 ; Mul -> 1;
                       Sub -> 2 ; Div -> 3

evalClosed :: Expr -> Val
evalClosed e = eval e builtinEnv (0, [])

instance Show Val where
  show (TV t r) = Table.printTable r t
  show (LamVal _ _ _) = "<lambda>"
  show (Builtin _ _ ) = "<builtin>"
