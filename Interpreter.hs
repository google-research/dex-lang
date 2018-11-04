module Interpreter (evalExpr, initValEnv, showVal, ValEnv, Val (..), IdxVal (..)) where

import qualified Data.Map.Strict as M
import Data.List (sortOn)
import Text.PrettyPrint.Boxes

import Syntax
import Util
import Typer

data Val = IntVal Int
         | TabVal (M.Map (Maybe IdxVal) Val)
         | LamVal Env Expr
         | Builtin BuiltinName [Val]  deriving (Eq, Show)

data IdxVal = IntIdxVal  Int
            | RealIdxVal Float
            | StrIdxVal  String
                deriving (Eq, Ord, Show)

type IEnv = Int
type ValEnv = [Val]
type Env = (ValEnv, IEnv)

evalExpr :: Expr -> ValEnv -> Val
evalExpr expr env = eval expr (env, 0)

initValEnv :: ValEnv
initValEnv = let builtinNames = [Iota, Reduce,
                                 BinOp Add, BinOp Sub,
                                 BinOp Mul, BinOp Div]
             in [Builtin b [] | b <- builtinNames]

eval :: Expr -> Env -> Val
eval expr env =
  let (venv, d) = env
  in case expr of
    Lit c          -> composeN d lift $ IntVal c
    Var v          -> venv !! v
    Let p bound body -> let x = eval bound env
                        in eval body ((x:venv),d)
    Lam p body     -> LamVal env body
    App fexpr arg  -> let f = eval fexpr env
                          x = eval arg env
                      in (tabmap2 d) evalApp f x
    For body       -> let venv' = map (tabmap d lift) venv
                      in eval body (venv',d+1)
    Get e i        -> let x = eval e env
                      in tabmap (d-i-1) (diag . (tabmap 1) (promoteIdx i)) x

tabmap :: Int -> (Val -> Val) -> Val -> Val
tabmap d = let map f (TabVal m) = TabVal $ M.map f m
           in composeN d map

tabmap2 :: Int -> (Val -> Val -> Val) -> Val -> Val -> Val
tabmap2 d = composeN d map2

-- this is O(N^2) in the number of keys. Should be linear.
map2 :: (Val -> Val -> Val) -> Val -> Val -> Val
map2 f (TabVal m1) (TabVal m2) = TabVal . M.fromList $
  [ (k, f x y) | (k1, x) <- M.toList m1
               , (k2, y) <- M.toList m2
               , Just k <- [tryEq k1 k2] ]

lift :: Val -> Val
lift v = TabVal $ M.singleton Nothing v

promoteIdx :: Int -> Val -> Val
promoteIdx 0 x = x
promoteIdx n x = promoteIdx (n-1) $ tabmap (n-1) swapidxs x

swapidxs :: Val -> Val
swapidxs (TabVal m) =
  TabVal . M.map (TabVal . M.fromList) . M.fromList . group . sortOn fst $
  [(k2,(k1,v)) | (k1, (TabVal m')) <- M.toList m
               , (k2, v ) <- M.toList m']

diag :: Val -> Val
diag (TabVal m) = TabVal . M.fromList $ [(k,v) | (k1, (TabVal m')) <- M.toList m
                                               , (k2, v ) <- M.toList m'
                                               , Just k <- [tryEq k1 k2] ]

tryEq :: Eq a => Maybe a -> Maybe a -> Maybe (Maybe a)
tryEq x y = case (x, y) of
  (Just x, Just y) | x == y    -> Just $ Just x
                   | otherwise -> Nothing
  (Just x , Nothing) -> Just $ Just x
  (Nothing, Just y ) -> Just $ Just y
  (Nothing, Nothing) -> Just $ Nothing


evalApp :: Val -> Val -> Val
evalApp (LamVal (venv,ienv) body) x = eval body ((x:venv), ienv)
evalApp (Builtin name vs) x = let args = x:vs
                              in if length args < numArgs name
                                    then Builtin name args
                                    else evalBuiltin name (reverse args)

evalBuiltin :: BuiltinName -> [Val] -> Val
evalBuiltin (BinOp b) [IntVal x, IntVal y] = IntVal $ binOpFun b x y
evalBuiltin Iota [IntVal n] = TabVal $ M.fromList [(Just $ IntIdxVal i, IntVal i)
                                                  | i <- [0..(n-1)]]
evalBuiltin Reduce [f, z, TabVal m] = let f' x y = evalApp (evalApp f x) y
                                      in foldr f' z (M.elems m)

data BuiltinName = BinOp BinOpName
                 | Iota
                 | Reduce deriving (Show, Eq)

data BinOpName = Add | Mul | Sub | Div  deriving (Show, Eq)

numArgs :: BuiltinName -> Int
numArgs x = case x of
  BinOp _ -> 2
  Iota    -> 1
  Reduce  -> 3

binOpFun :: BinOpName -> Int -> Int -> Int
binOpFun Add = (+)
binOpFun Mul = (*)
binOpFun Sub = (-)

-- -- ----- printing -----

showVal :: Val -> ClosedType -> String
showVal v t = render $ text " " <> valToBox v

valToBox :: Val -> Box
valToBox v = case v of
  IntVal x -> text (show x)
  TabVal m -> vcat left [ text (showMaybeIdxVal k) <> text " | " <> valToBox v
                        | (k, v) <- M.toList m]
  LamVal _ _  -> text "<builtin>"
  Builtin _ _ -> text "<builtin>"

showMaybeIdxVal :: Maybe IdxVal -> String
showMaybeIdxVal Nothing = "*"
showMaybeIdxVal (Just x) = case x of
  IntIdxVal  x -> show x
  RealIdxVal x -> show x
  StrIdxVal  s -> s
