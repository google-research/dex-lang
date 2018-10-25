module Interpreter (evalExpr, initValEnv, ValEnv, Val (..)) where

import qualified Table as T
import Syntax
import Util
import qualified Parser

data Val = IntVal Depth (T.Table Int Int)
         | LamVal ValEnv IEnv Expr
         | Builtin BuiltinName [Val]

type IEnv = (Depth, [Int])
type ValEnv = [Val]
type Depth = Int
type Env = (ValEnv, IEnv)

evalExpr :: Expr -> ValEnv -> Val
evalExpr expr env = eval expr (env, (0, []))

initValEnv :: ValEnv
initValEnv = let builtinNames = [Iota, Reduce,
                                 BinOp Add, BinOp Sub,
                                 BinOp Mul, BinOp Div]
             in [Builtin b [] | b <- builtinNames]

eval :: Expr -> Env -> Val
eval expr env =
  let (venv, ienv) = env
      (d, idxs) = ienv
  in case expr of
    Lit c          -> composeN d lift $ IntVal 0 (T.fromScalar c)
    Var v          -> venv !! v
    Let bound body -> let x = eval bound env
                      in eval body ((x:venv),ienv)
    Lam body       -> LamVal venv ienv body
    App fexpr arg  -> let f = eval fexpr env
                          x = eval arg env
                      in evalApp f x
    For body       -> let ienv' = (d+1, d:idxs)
                          venv' = map lift venv
                      in lower $ eval body (venv',ienv')
    Get e i        -> let i' = idxs!!i
                          x = eval e env
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

data BinOpName = Add | Mul | Sub | Div  deriving (Show, Eq)

numArgs :: BuiltinName -> Int
numArgs x = case x of
  BinOp _ -> 2
  Iota    -> 1
  Reduce  -> 3

evalApp :: Val -> Val -> Val
evalApp (LamVal env ienv body) x = eval body ((x:env), ienv)
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
    let f' x y = case evalApp (evalApp f (IntVal 0 x)) (IntVal 0 y)
                 of IntVal 0 t -> t
    in IntVal d (T.reduceD d f' z t)

binOpFun :: BinOpName -> Int -> Int -> Int
binOpFun Add = (+)
binOpFun Mul = (*)
binOpFun Sub = (-)

instance Show Val where
  show (IntVal _ t) = T.printTable t
  show (LamVal _ _ _) = "<lambda>"
  show (Builtin _ _ ) = "<builtin>"
