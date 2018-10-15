{-# LANGUAGE GADTs #-}

module Interpreter (Expr (..), BinOpName (..), binOpIdx, evalClosed) where

import qualified Data.Map.Strict as Map
import qualified Table as T

data Expr = Lit Int
          | Var Int
          | Lam Expr
          | App Expr Expr
          | IdxComp Expr
          | Get Expr Int
              deriving (Show)

data Val = TV (T.Table Int Int) Depth
         | LamVal Env IEnv Expr
         | Builtin BuiltinName [Val]

data BinOpName = Add | Mul | Sub | Div  deriving (Show)

data BuiltinName = BinOp BinOpName
                 | Iota
                 | Reduce  deriving (Show)

type IEnv = (Depth, [Int]) -- depth, and positions of in-scope indices
type Env = [Val]
type Depth = Int

eval :: Expr -> Env -> IEnv -> Val
eval (Lit c) _   (depth, _) = lift depth $ TV (T.fromScalar c) 0
eval (Var v) env (depth, _) = lift depth $ env !! v
eval (Lam body) env ienv = LamVal env ienv body
eval (App fexpr arg) env ienv =
    let f = eval fexpr env ienv
        x = eval arg env ienv
    in case f of
        LamVal env' ienv' body -> eval body (x:env') ienv'
        Builtin name vs -> let args = x:vs
                           in if length args < numArgs name
                                then Builtin name args
                                else evalBuiltin name (reverse args)
eval (IdxComp body) env (d, idxs) = let ienv = ((d + 1), d:idxs) in
                                    case eval body env ienv of
                                      TV t d -> TV t (d-1)
eval (Get e i) env ienv = let (_, idxs) = ienv
                              i' = idxs !! i
                          in case eval e env ienv of
                              TV t d -> TV (T.diag i' d t) d

-- example:
-- index env depth : how many *dynamically* enclosing indices do we have
-- index env:  (5, [0, 2])
-- rank: 4
    --                     1   0  --rank---
-- table indices: [... * * * * * | * * * * ]
-- |<--rank->|<--env indices -->|
-- [ * * * * |                    ...]

lift :: Int -> Val -> Val
lift d (TV t d') = TV (T.insert d' (d - d') t) d
lift d (LamVal env (_, idxs) body) = LamVal env (d, idxs) body
lift d (Builtin name args) = Builtin name (map (lift d) args)

numArgs :: BuiltinName -> Int
numArgs (BinOp _) = 2
numArgs Iota      = 1

evalBuiltin :: BuiltinName -> [Val] -> Val
evalBuiltin (BinOp b) (TV t1 d : TV t2 d' : []) | d == d' =
    TV (T.map2 (binOpFun b) t1 t2) d
evalBuiltin Iota (TV t d : []) = TV (T.iota t) d


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
  show (TV t _) = T.printTable t
  show (LamVal _ _ _) = "<lambda>"
  show (Builtin _ _ ) = "<builtin>"
