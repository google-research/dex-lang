module Builtins (initEnv, Env (..), consEnv) where

import qualified Data.Map.Strict as M

import Interpreter
import Typer
import Lower

a = TypeVar 0
b = TypeVar 1
int = BaseType IntType

data Env = Env { varEnv  :: VarEnv
               , typeEnv :: TypeEnv
               , valEnv  :: ValEnv }

initEnv :: Env
initEnv = Env { varEnv  = map name builtins
              , typeEnv = map ty builtins
              , valEnv  = [ Builtin (BuiltinVal numArgs name evalFun) []
                            | BuiltinSpec name ty numArgs evalFun <- builtins ]}

builtins = [ binOp "add" (+)
           , binOp "sub" (-)
           , binOp "mul" (*)
           , BuiltinSpec "reduce" reduceType 3 reduceEval
           , BuiltinSpec "iota" iotaType 1 iotaEval
           ]

consEnv :: (String, ClosedType, Val) -> Env -> Env
consEnv (var, ty, val) env =
  Env { varEnv  = var : varEnv  env
      , typeEnv = ty  : typeEnv env
      , valEnv  = val : valEnv  env }

data BuiltinSpec = BuiltinSpec { name    :: String
                               , ty      :: ClosedType
                               , numArgs :: Int
                               , evalFun :: [Val] -> Val }

infixr 1 -->
infixr 2 ==>
(-->) = ArrType
(==>) = TabType


binOp :: String -> (Int -> Int -> Int) -> BuiltinSpec
binOp name binOpFun = BuiltinSpec name binOpType 2 binOpEval
  where
     binOpEval [IntVal x, IntVal y] = IntVal $ binOpFun x y
     binOpType = Forall 0 $ int --> int --> int

reduceType = Forall 2 $ (b --> b --> b) --> b --> (a ==> b) --> b
reduceEval [f, z, TabVal m] = let f' x y = evalApp (evalApp f x) y
                              in foldr f' z (M.elems m)

iotaType = Forall 0 $ int --> int ==> int
iotaEval [IntVal n] = tabVal [(IntVal i, IntVal i) | i <- [0..(n-1)]]


-- initEnv = unzip3 [ add, sub, mul, div
--                  , iota, reduce]
-- -- initEnv :: Env
-- -- initEnv = Env { varEnv  = initVarEnv
-- --               , typeEnv = initTypeEnv
-- --               , valEnv  = initValEnv }


-- consEnv :: (String, ClosedType, Val) -> Env -> Env
-- consEnv (var, ty, val) env =
--   Env { varEnv  = var : varEnv  env
--       , typeEnv = ty  : typeEnv env
--       , valEnv  = val : valEnv  env }

-- evalBuiltin (BinOp b) [IntVal x, IntVal y] = IntVal $ binOpFun b x y
-- data BuiltinName = BinOp BinOpName
--                  | Iota
--                  | Reduce deriving (Show, Eq, Ord)

-- data BinOpName = Add | Mul | Sub | Div  deriving (Show, Eq, Ord)

-- numArgs :: BuiltinName -> Int
-- numArgs x = case x of
--   BinOp _ -> 2
--   Iota    -> 1
--   Reduce  -> 3

-- binOpFun :: BinOpName -> Int -> Int -> Int
-- binOpFun Add = (+)
-- binOpFun Mul = (*)
-- binOpFun Sub = (-)
--   "iota", "reduce", "add", "sub", "mul", "div"
--              , "exp", "log", "sqrt", "pow"]

-- ("iota"  , 
--      , ("reduce", Forall 2 $ (b --> b --> b) --> b --> (a ==> b) --> b , reduceImpl)
--      -- reduce
--      , binOp, binOp, binOp, binOp]

-- evalBuiltin :: BuiltinName -> [Val] -> Val
-- evalBuiltin Reduce [f, z, TabVal m] = let f' x y = evalApp (evalApp f x) y
--                                       in foldr f' z (M.elems m)

