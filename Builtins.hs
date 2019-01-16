module Builtins (initEnv, Env (..)) where

import qualified Data.Map.Strict as M

import Interpreter
import qualified Syntax as S
import Typer
import Lower
import Env hiding (Env)

data Env = Env { varEnv  :: FreeEnv ()
               , typeEnv :: FreeEnv Type
               , valEnv  :: FreeEnv Val }

initEnv :: Env
initEnv = Env
  { varEnv  = newFreeEnv [(name b, ()) | b <- builtins]
  , typeEnv = newFreeEnv [(name b, ty b) | b <- builtins]
  , valEnv  = newFreeEnv [(name b, Builtin (BuiltinVal numArgs name' evalFun) [])
                         | b@(BuiltinSpec name' ty numArgs evalFun) <- builtins ]}

builtins = [ binOp "add" (+)
           , binOp "sub" (-)
           , binOp "mul" (*)
           , binOp "pow" (^)
           , realUnOp "exp" exp
           , realUnOp "log" log
           , realUnOp "sqrt" sqrt
           , realUnOp "sin" sin
           , realUnOp "cos" cos
           , realUnOp "tan" tan
           , BuiltinSpec "reduce" reduceType 3 reduceEval
           , BuiltinSpec "iota" iotaType 1 iotaEval
           ]

data BuiltinSpec = BuiltinSpec { name    :: String
                               , ty      :: S.SigmaType
                               , numArgs :: Int
                               , evalFun :: [Val] -> Val }

a = TypeVar (BV 0)
b = TypeVar (BV 1)
int = BaseType IntType
real = BaseType RealType

infixr 1 -->
infixr 2 ==>
(-->) = ArrType
(==>) = TabType

binOp :: String -> (Int -> Int -> Int) -> BuiltinSpec
binOp name f = BuiltinSpec name ty 2 f'
  where
     f' [IntVal x, IntVal y] = IntVal $ f x y
     ty = int --> int --> int

realUnOp :: String -> (Float -> Float) -> BuiltinSpec
realUnOp name f = BuiltinSpec name ty 1 f'
  where
     f' [RealVal x] = RealVal $ f x
     ty = real --> real

reduceType = Forall 2 $ (b --> b --> b) --> b --> (a ==> b) --> b
reduceEval [f, z, TabVal m] = let f' x y = evalApp (evalApp f x) y
                              in foldr f' z (M.elems m)

iotaType = int --> int ==> int
iotaEval [IntVal n] = tabVal [(IntVal i, IntVal i) | i <- [0..(n-1)]]
