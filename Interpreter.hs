module Interpreter (Expr (..), Env, BinOpName (..), evalClosed,
                    Val, eval, builtinEnv) where

import qualified Data.Map.Strict as Map
import Util
import qualified Table as T

data Expr = Lit Int
          | Var Int
          | Lam Expr
          | App Expr Expr
          | For Expr
          | Get Expr Int
              deriving (Show)

data Val = IntVal Depth (T.Table Int Int)
         | LamVal Env IEnv Expr
         | Builtin BuiltinName [Val]

data BinOpName = Add | Mul | Sub | Div  deriving (Show, Eq)

type IEnv = (Depth, [Int])
type Env = [Val]
type Depth = Int



eval :: Expr -> Env -> IEnv -> Val
eval (Lit c) _   (d, _) = (composeN d lift) $ IntVal 0 (T.fromScalar c)
eval (Var v) env ienv = env !! v
eval (Lam body) env ienv = LamVal env ienv body
eval (App fexpr arg) env ienv = let f = eval fexpr env ienv
                                    x = eval arg env ienv
                                in evalApp f x
eval (For body) env (d, idxs) = let ienv = (d+1, d:idxs)
                                    env' = map lift env
                                in lower $ eval body env' ienv
eval (Get e i) env ienv = let (_, idxs) = ienv
                              i' = idxs!!i
                              x = eval e env ienv
                          in contract i' x

contract :: Int -> Val -> Val
contract i (IntVal d t) = IntVal d $ T.diag i d t
contract i (LamVal env ienv body) = LamVal (map (contract i) env) ienv body
contract i (Builtin name args) = Builtin name (map (contract i) args)

lift :: Val -> Val
lift (IntVal d t) = IntVal (d+1) $ T.insert d t
lift (LamVal env (d,idxs) body) = LamVal (map lift env) (d+1, idxs) body
lift (Builtin name args) = Builtin name (map lift args)

lower :: Val -> Val
lower (IntVal d t) = IntVal (d-1) t
lower (LamVal env (d,idxs) body) = LamVal (map lower env) (d-1, idxs) body
lower (Builtin name args) = Builtin name (map lower args)

data BuiltinName = BinOp BinOpName
                 | Iota
                 | Reduce deriving (Show)

numArgs :: BuiltinName -> Int
numArgs (BinOp _) = 2
numArgs Iota      = 1
numArgs Reduce    = 3

evalApp :: Val -> Val -> Val
evalApp (LamVal env ienv body) x = eval body (x:env) ienv
evalApp (Builtin name vs) x = let args = x:vs
                              in if length args < numArgs name
                                   then Builtin name args
                                   else evalBuiltin name (reverse args)

evalBuiltin :: BuiltinName -> [Val] -> Val
evalBuiltin (BinOp b) [IntVal d t1 , IntVal d' t2] | d == d' =
    let f x y = T.fromScalar $ binOpFun b (T.toScalar x) (T.toScalar y)
    in IntVal d (T.mapD2 d f t1 t2)
evalBuiltin Iota [IntVal d t] = IntVal d (T.mapD d T.iota t)


evalBuiltin Reduce (f : IntVal d z : IntVal d' t: []) | d == d' =
    let f' x y = case evalApp (evalApp f (IntVal d x)) (IntVal d y)
                 of IntVal d t -> t
    in IntVal d (T.reduceD d f' z t)

binOpFun :: BinOpName -> Int -> Int -> Int
binOpFun Add = (+)
binOpFun Mul = (*)
binOpFun Sub = (-)

builtinEnv = [ Builtin Iota []
             , Builtin Reduce []
             , Builtin (BinOp Add) []
             , Builtin (BinOp Mul) []
             , Builtin (BinOp Sub) []
             , Builtin (BinOp Div) [] ]

evalClosed :: Expr -> Val
evalClosed e = eval e builtinEnv (0, [])

instance Show Val where
  show (IntVal _ t) = T.printTable t
  show (LamVal _ _ _) = "<lambda>"
  show (Builtin _ _ ) = "<builtin>"
