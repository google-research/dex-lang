module LinearA where

import Data.List (intercalate)
import Prelude hiding (lookup)
import qualified Data.Map.Strict as M
import Data.Map.Strict ((!))

type Var = String
data MixedType = MixedType [Type] [Type]
data Type = FloatType | TupleType [Type]
data Expr = Ret [Var] [Var]
          | LetMixed     [Var] [Var] Expr Expr
          | LetUnpack    [Var]       Var  Expr
          | LetUnpackLin [Var]       Var  Expr
          | App FuncName [Var] [Var]
          -- Additional non-linear expressions
          | Var Var
          | Lit Float
          | Tuple [Expr]
          | UnOp  UnOp  Expr
          | BinOp BinOp Expr Expr
          -- Additional linear expressions
          | LVar Var
          | LTuple [Expr]
          | LAdd   Expr Expr
          | LScale Expr Expr
          | LZero  [Var]
          | Dup  Expr
          | Drop Expr
data UnOp  = Sin | Cos | Exp
data BinOp = Add | Mul

type FuncName = String
data FuncDef = FuncDef [Var] [Var] MixedType Expr
data Program = Program (M.Map FuncName FuncDef)

data Value = FloatVal Float | TupleVal [Value]
             deriving Eq
data Result = Result [Value] [Value]
              deriving Eq

instance Show Value where
  show (FloatVal f) = show f
  show (TupleVal vs) = "(" ++ intercalate ", " (show <$> vs) ++ ")"
instance Show Result where
  show (Result vs linVs) = "(" ++ intercalate ", " (show <$> vs) ++ "; "
                               ++ intercalate ", " (show <$> linVs) ++ ")"

-------------------- Evaluation --------------------

type EvalEnv = M.Map Var Value
eval :: Program -> EvalEnv -> Expr -> Result
eval prog@(Program defs) env expr = case expr of
  Ret nonlin lin -> Result ((env !) <$> nonlin) ((env !) <$> lin)
  LetMixed vs linVs e1 e2 -> do
    let Result vals linVals = eval prog env e1
    let env' = envExt env (vs ++ linVs) (vals ++ linVals)
    eval prog env' e2
  LetUnpack vs v e -> do
    let TupleVal vals = env ! v
    let env' = envExt env vs vals
    eval prog env' e
  LetUnpackLin vs v e -> do
    let TupleVal vals = env ! v
    let env' = envExt env vs vals
    eval prog env' e
  App funcName args linArgs -> do
    let FuncDef formals linFormals _ funcExpr = defs ! funcName
    let argVals = (env !) <$> args
    let linArgVals = (env !) <$> linArgs
    let appEnv = envExt mempty (formals ++ linFormals) (argVals ++ linArgVals)
    eval prog appEnv funcExpr
  -- Nonlinear expressions
  Var v     -> result $ env ! v
  Lit f     -> result $ FloatVal f
  Tuple es  -> result $ TupleVal $ fromResult . eval prog env <$> es
  UnOp op e -> do
    let Result [FloatVal x] [] = eval prog env e
    result $ FloatVal $ f x
    where
      f = case op of
        Sin -> sin
        Cos -> cos
        Exp -> exp
  BinOp op le re -> do
    let Result [FloatVal lv] [] = eval prog env le
    let Result [FloatVal rv] [] = eval prog env re
    result $ FloatVal $ f lv rv
    where
      f = case op of
        Add -> (+)
        Mul -> (*)
  -- Linear expressions
  LVar v -> linResult $ env ! v
  LTuple es -> linResult $ TupleVal $ fromLinResult . eval prog env <$> es
  LAdd le re -> do
    let Result [] [FloatVal lv] = eval prog env le
    let Result [] [FloatVal rv] = eval prog env re
    linResult $ FloatVal $ lv + rv
  LScale se le -> do
    let Result [FloatVal sv] [] = eval prog env se
    let Result [] [FloatVal lv] = eval prog env le
    linResult $ FloatVal $ sv * lv
  LZero _ -> linResult $ FloatVal 0
  Dup   e -> do
    let Result [] [v] = eval prog env e
    Result [] [v, v]
  Drop  _ -> Result [] []
  where
    envExt :: EvalEnv -> [Var] -> [Value] -> EvalEnv
    envExt env vs vals = foldl (\env (k, v) -> M.insert k v env) env $ zip vs vals

    result :: Value -> Result
    result v = Result [v] []

    fromResult :: Result -> Value
    fromResult (Result [v] []) = v
    fromResult _ = error "Unexpected result type"

    linResult :: Value -> Result
    linResult v = Result [] [v]

    fromLinResult :: Result -> Value
    fromLinResult (Result [] [v]) = v
    fromLinResult _ = error "Unexpected result type"
