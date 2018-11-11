module Interpreter (evalExpr, valPatMatch, initValEnv, showVal, ValEnv,
                    Val (..), IdxVal (..)) where

import qualified Data.Map.Strict as M
import Control.Monad

import Data.Foldable
import Data.List (sortOn)
import Data.Foldable (toList)
import Text.PrettyPrint.Boxes

import Syntax
import Util
import Typer
import Record

data Val = IntVal Int
         | TabVal (M.Map IdxVal Val)
         | RecVal (Record Val)
         | LamVal Pat Env Expr
         | Builtin BuiltinName [Val]  deriving (Eq, Show)

data IdxVal = Any
            | IntIdxVal  Int
            | RealIdxVal Float
            | StrIdxVal  String
            | RecIdxVal (Record IdxVal)
                deriving (Eq, Ord)

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
eval expr env@(venv, d) =
  case expr of
    Lit c          -> composeN d lift $ IntVal c
    Var v          -> venv !! v
    Let p bound body -> let x = eval bound env
                        in eval body (valPatMatch p x ++ venv, d)
    Lam p body     -> LamVal p env body
    App fexpr arg  -> let f = eval fexpr env
                          x = eval arg env
                      in (tabmap2 d) evalApp f x
    For p body     -> let n = patSize p
                          venv' = map (tabmap d (composeN n lift)) venv
                          ans = eval body (venv',d+n)
                      in tabmap d (structureTabVal p . uncurryTabVal n) ans
    Get e ie        ->
        curryTabVal d $ diagWithIdxExpr d ie $ uncurryTabVal d $ eval e env
    RecCon r       -> RecVal $ fmap (flip eval env) r


valPatMatch :: Pat -> Val -> [Val]
valPatMatch VarPat v = [v]
valPatMatch (RecPat p) (RecVal v) = let vs = toList v
                                        ps = toList p
                                    in concat $ zipWith valPatMatch ps vs

tabVal :: [(IdxVal, Val)] -> Val
tabVal = TabVal . M.fromList

uncurryTabVal :: Int -> Val -> Val
uncurryTabVal 0 v = tabVal [(RecIdxVal emptyRecord, v)]
uncurryTabVal n (TabVal m) = tabVal [(RecIdxVal $ consRecord k ks, v')
                                       | (k, v) <- M.toList m
                                       , let TabVal m'= uncurryTabVal (n-1) v
                                       , (RecIdxVal ks, v') <- M.toList m' ]

curryTabVal :: Int -> Val -> Val
curryTabVal 0 (TabVal m) = case M.toList m of [(emptyRecord, v)] -> v
curryTabVal n (TabVal m) =
  let grouped = group [(k, (RecIdxVal r', v)) | (RecIdxVal r, v) <- M.toList m
                                              , let (k, r') = unConsRecord r]
  in tabVal [(k, curryTabVal (n-1) (tabVal v)) | (k, v) <- grouped]

structureTabVal :: IdxPat -> Val -> Val
structureTabVal p (TabVal m) =
  tabVal [(structureIdx p (fromPosRecord r), v)
             | (RecIdxVal r, v) <- M.toList m]

structureIdx :: IdxPat -> [IdxVal] -> IdxVal
structureIdx VarPat [k] = k
structureIdx (RecPat (Record r)) idxs =
  let (ks, ps) = unzip $ M.toList r
      subPatSizes = map patSize ps
      idxGroups = part subPatSizes idxs
  in RecIdxVal . Record . M.fromList $ zip ks $ zipWith structureIdx ps idxGroups

part :: [Int] -> [a] -> [[a]]
part [] [] = []
part (size:sizes) xs = let (prefix, rest) = splitAt size xs
                       in prefix : part sizes rest

diagWithIdxExpr :: Int -> IdxExpr -> Val -> Val
diagWithIdxExpr d ie (TabVal m) =
  tabVal $ [(RecIdxVal (posRecord k),v)
                           | (RecIdxVal r, (TabVal m')) <- M.toList m
                           , (k2, v ) <- M.toList m'
                           , Just k <- [matchIdxExpr (toList r) ie k2] ]

matchIdxExpr :: [IdxVal] -> IdxExpr -> IdxVal -> Maybe [IdxVal]
matchIdxExpr idxs (IdxVar v) i = do i' <- tryEq i (idxs !! v)
                                    return $ update v i' idxs
matchIdxExpr idxs (IdxRecCon vs) (RecIdxVal is) = do
  idxs' <- sequence $ zipWith (matchIdxExpr idxs) (toList vs) (toList is)
  foldM mergeIdxs (take (length idxs) (repeat Any)) idxs'

mergeIdxs :: [IdxVal] -> [IdxVal] -> Maybe [IdxVal]
mergeIdxs idxs1 idxs2 = sequence $ zipWith tryEq idxs1 idxs2

diag :: Val -> Val
diag (TabVal m) = tabVal $ [(k,v) | (k1, (TabVal m')) <- M.toList m
                                               , (k2, v ) <- M.toList m'
                                               , Just k <- [tryEq k1 k2] ]

patSize :: IdxPat -> Int
patSize VarPat = 1
patSize (RecPat r) = foldr (+) 0 $ fmap patSize r

update :: Int -> a -> [a] -> [a]
update i x xs = let (prefix, _:rest) = splitAt i xs
                in prefix ++ (x:rest)

tabmap :: Int -> (Val -> Val) -> Val -> Val
tabmap d = let map f (TabVal m) = TabVal $ M.map f m
           in composeN d map

tabmap2 :: Int -> (Val -> Val -> Val) -> Val -> Val -> Val
tabmap2 d = composeN d map2

-- this is O(N^2) in the number of keys. Should be linear.
map2 :: (Val -> Val -> Val) -> Val -> Val -> Val
map2 f (TabVal m1) (TabVal m2) = tabVal [ (k, f x y) | (k1, x) <- M.toList m1
                                                     , (k2, y) <- M.toList m2
                                                     , Just k <- [tryEq k1 k2] ]

tryEq :: IdxVal -> IdxVal -> Maybe IdxVal
tryEq x y = case (x, y) of
  (Any, Any) -> Just Any
  (Any, y) -> Just y
  (x, Any) -> Just x
  (x, y) | x == y -> Just x
         | otherwise -> Nothing

lift :: Val -> Val
lift v = tabVal [(Any, v)]

evalApp :: Val -> Val -> Val
evalApp (LamVal p (venv,ienv) body) x = eval body (valPatMatch p x ++ venv, ienv)
evalApp (Builtin name vs) x = let args = x:vs
                              in if length args < numArgs name
                                    then Builtin name args
                                    else evalBuiltin name (reverse args)

evalBuiltin :: BuiltinName -> [Val] -> Val
evalBuiltin (BinOp b) [IntVal x, IntVal y] = IntVal $ binOpFun b x y
evalBuiltin Iota [IntVal n] = tabVal [(IntIdxVal i, IntVal i)
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
  TabVal m -> vcat left [ text (show k) <> text " | " <> valToBox v
                        | (k, v) <- M.toList m]
  RecVal r -> text $ show r
  LamVal _ _ _ -> text "<lambda>"
  Builtin _ _  -> text "<builtin>"

instance Show IdxVal where
  show x = case x of
    Any -> "*"
    IntIdxVal  x -> show x
    RealIdxVal x -> show x
    StrIdxVal  s -> s
    RecIdxVal  r -> show r
