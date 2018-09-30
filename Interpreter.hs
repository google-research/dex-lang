module Interpreter (Expr (..), BinOpName (..), evalClosed) where

import qualified Data.Map.Strict as Map
import qualified Data.Array as A

data Expr = BinOp BinOpName Expr Expr
          | Lit Integer
          | Var VarName
          | Let VarName Expr Expr
          | Lam VarName Expr
          | App Expr Expr
          | Arr IdxVarName Expr
          | Get Expr IdxVarName
          deriving (Show)

data BinOpName = Add | Mul | Sub | Div deriving (Show)

data Val = IntVal Integer
         | LamVal Env VarName Expr
         | ArrayVal Array deriving (Show)

type VarName = String
type IdxVarName = String

type Env = Map.Map VarName Val

eval :: Expr -> Env -> Val
eval (BinOp b e1 e2) env = IntVal $ case (eval e1 env, eval e2 env) of
                                     (IntVal v1, IntVal v2) -> evalBinOp b v1 v2
eval (Lit c) _ = IntVal c
eval (Var v) env = case Map.lookup v env of
                     Just val -> val
                     Nothing -> error $ "Undefined variable: " ++ show v
eval (Let v bound body) env = let boundVal = eval bound env
                                  newEnv = Map.insert v boundVal env
                              in eval body newEnv
eval (Lam v body) env = LamVal env v body
eval (App f arg) env = case eval f env of
  LamVal closureEnv v body ->
    let argVal = eval arg env
    in eval body (Map.insert v argVal env)

evalClosed :: Expr -> Val
evalClosed e = eval e Map.empty

evalBinOp :: BinOpName -> Integer -> Integer -> Integer
evalBinOp Add = (+)
evalBinOp Mul = (*)
evalBinOp Sub = (-)

-- -------------------- vector operations --------------------

type DType   = Int
type Shape   = ([Int], Map.Map IdxVarName Int)
type Strides = ([Int], Map.Map IdxVarName Int)
data Array = Array Shape Strides (A.Array Int DType)

instance Show Array where
  show (Array shape _ _) = "<array>"

-- vlen :: Array -> Int
-- vlen (Array shape _ _) = foldr (*) 1 shape

toList :: Array -> [DType]
toList = undefined

fromList :: Shape -> [DType] -> Array
fromList = undefined

binop :: (DType -> DType -> DType) -> Array -> Array -> Array
binop f x y = let (Array shape _ _) = x
              in fromList shape $ zipWith f (toList x) (toList y)
