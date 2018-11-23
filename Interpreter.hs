module Interpreter (evalExpr, valPatMatch, initValEnv, ValEnv,
                    Val (..), IdxVal, unitVal, TypedVal, validTypedVal) where

import qualified Data.Map.Strict as M
import Control.Monad
import Data.Foldable
import Data.List (sortOn)
import Data.Foldable (toList)
import Test.QuickCheck
import qualified Data.Map.Strict as M


import Syntax
import Util
import Typer
import Record

data Val = Any
         | IntVal Int
         | RealVal Float
         | StrVal String
         | BoolVal  Bool
         | TabVal (M.Map IdxVal Val)
         | RecVal (Record Val)
         | LamVal Pat Env Expr
         | Builtin BuiltinName [Val]  deriving (Eq, Ord, Show)

type IdxVal = Val
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
uncurryTabVal 0 v = tabVal [(RecVal emptyRecord, v)]
uncurryTabVal n (TabVal m) = tabVal [(RecVal $ consRecord k ks, v')
                                       | (k, v) <- M.toList m
                                       , let TabVal m'= uncurryTabVal (n-1) v
                                       , (RecVal ks, v') <- M.toList m' ]

curryTabVal :: Int -> Val -> Val
curryTabVal 0 (TabVal m) = case M.toList m of [(emptyRecord, v)] -> v
curryTabVal n (TabVal m) =
  let grouped = group [(k, (RecVal r', v)) | (RecVal r, v) <- M.toList m
                                              , let (k, r') = unConsRecord r]
  in tabVal [(k, curryTabVal (n-1) (tabVal v)) | (k, v) <- grouped]

structureTabVal :: IdxPat -> Val -> Val
structureTabVal p (TabVal m) =
  tabVal [(structureIdx p (fromPosRecord r), v)
             | (RecVal r, v) <- M.toList m]

structureIdx :: IdxPat -> [IdxVal] -> IdxVal
structureIdx VarPat [k] = k
structureIdx (RecPat (Record r)) idxs =
  let (ks, ps) = unzip $ M.toList r
      subPatSizes = map patSize ps
      idxGroups = part subPatSizes idxs
  in RecVal . Record . M.fromList $ zip ks $ zipWith structureIdx ps idxGroups

part :: [Int] -> [a] -> [[a]]
part [] [] = []
part (size:sizes) xs = let (prefix, rest) = splitAt size xs
                       in prefix : part sizes rest

diagWithIdxExpr :: Int -> IdxExpr -> Val -> Val
diagWithIdxExpr d ie (TabVal m) =
  tabVal $ [(RecVal (posRecord k),v)
                           | (RecVal r, (TabVal m')) <- M.toList m
                           , (k2, v ) <- M.toList m'
                           , Just k <- [matchIdxExpr (toList r) ie k2] ]

matchIdxExpr :: [IdxVal] -> IdxExpr -> IdxVal -> Maybe [IdxVal]
matchIdxExpr idxs (IdxVar v) i = do i' <- tryEq i (idxs !! v)
                                    return $ update v i' idxs
matchIdxExpr idxs (IdxRecCon vs) (RecVal is) = do
  idxs' <- sequence $ zipWith (matchIdxExpr idxs) (toList vs) (toList is)
  foldM mergeIdxs (replicate (length idxs) Any) idxs'

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
evalBuiltin Iota [IntVal n] = tabVal [(IntVal i, IntVal i)
                                         | i <- [0..(n-1)]]
evalBuiltin Reduce [f, z, TabVal m] = let f' x y = evalApp (evalApp f x) y
                                      in foldr f' z (M.elems m)

data BuiltinName = BinOp BinOpName
                 | Iota
                 | Reduce deriving (Show, Eq, Ord)

data BinOpName = Add | Mul | Sub | Div  deriving (Show, Eq, Ord)

numArgs :: BuiltinName -> Int
numArgs x = case x of
  BinOp _ -> 2
  Iota    -> 1
  Reduce  -> 3

binOpFun :: BinOpName -> Int -> Int -> Int
binOpFun Add = (+)
binOpFun Mul = (*)
binOpFun Sub = (-)

unitVal :: Val
unitVal = RecVal emptyRecord

data TypedVal = TypedVal Type Val  deriving (Show)

instance Arbitrary TypedVal where
  arbitrary = do
    t <- arbitrary
    v <- arbitraryVal t
    return $ TypedVal t v

arbitraryVal :: Type -> Gen Val
arbitraryVal t = case t of
  BaseType b -> case b of
                  IntType  -> fmap IntVal arbitrary
                  BoolType -> fmap BoolVal arbitrary
                  RealType -> fmap RealVal arbitrary
                  StrType  -> fmap StrVal arbitrary
  TabType a b -> let rowGen = liftM2 (,) (arbitraryVal a) (arbitraryVal b)
                 in fmap (TabVal . M.fromList) (shortList 4 rowGen)
  RecType r -> fmap RecVal $ sequence (fmap arbitraryVal r)
  ArrType _ _ -> return Any
  TypeVar _ -> return Any

validTypedVal :: TypedVal -> Either String ()
validTypedVal (TypedVal t v) = validVal t v

validVal :: Type -> Val -> Either String ()
validVal t v = case (t,v) of
  (BaseType b, v') -> case (b,v') of
                        (IntType , IntVal  _) -> return ()
                        (BoolType, BoolVal _) -> return ()
                        (RealType, RealVal _) -> return ()
                        (StrType , StrVal  _) -> return ()
                        _ -> fail b v'
  (TabType a b, TabVal m) -> sequence [ validVal a k >> validVal b v
                                      | (k, v) <- M.toList m] >> return ()
  (RecType t, RecVal v) -> case zipWithRecord validVal t v of
                             Nothing -> Left $ "Records with mismatched keys"
                             Just r -> sequence r >> return ()
  (ArrType _ _ , LamVal _ _ _) -> return ()
  (ArrType _ _ , Builtin _ _ ) -> return ()
  (_, Any) -> return ()
  _ -> fail t v
  where fail t v = Left $ "Couldn't match type " ++ show t ++ " with " ++ show v
