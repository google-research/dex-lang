module Interpreter (Expr (..), ValEnv, BinOpName (..), evalClosed,
                    Val (..), eval, gettype, builtinEnv) where

import Control.Monad
import Control.Monad.Reader (ReaderT, runReaderT, local, ask)
import Control.Monad.State (StateT, evalStateT, put, get)
import qualified Data.Map.Strict as Map
import Util
import qualified Table as T

data Expr = Lit Int
          | Var Int
          | Let Expr Expr
          | Lam Expr
          | App Expr Expr
          | For Expr
          | Get Expr Int
              deriving (Show)

data Val = IntVal Depth (T.Table Int Int)
         | LamVal ValEnv IEnv Expr
         | Builtin BuiltinName [Val]

data BinOpName = Add | Mul | Sub | Div  deriving (Show, Eq)

type IEnv = (Depth, [Int])
type ValEnv = [Val]
type Depth = Int

eval :: Expr -> ValEnv -> IEnv -> Val
eval (Lit c) _   (d, _) = (composeN d lift) $ IntVal 0 (T.fromScalar c)
eval (Var v) env ienv = env !! v
eval (Let bound body) env ienv = let x = eval bound env ienv
                                 in eval body (x:env) ienv
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
    let f' x y = case evalApp (evalApp f (IntVal 0 x)) (IntVal 0 y)
                 of IntVal 0 t -> t
    in IntVal d (T.reduceD d f' z t)

binOpFun :: BinOpName -> Int -> Int -> Int
binOpFun Add = (+)
binOpFun Mul = (*)
binOpFun Sub = (-)

builtinEnv = [ Builtin Iota []
             , Builtin Reduce []
             , Builtin (BinOp Add) []
             , Builtin (BinOp Sub) []
             , Builtin (BinOp Mul) []
             , Builtin (BinOp Div) [] ]

evalClosed :: Expr -> Val
evalClosed e = eval e builtinEnv (0, [])

instance Show Val where
  show (IntVal _ t) = T.printTable t
  show (LamVal _ _ _) = "<lambda>"
  show (Builtin _ _ ) = "<builtin>"

-- -------------------- types --------------------

data Type = IntType
          | ArrType Type Type
          | TabType Type Type
          | TypeVar TypeVarName   deriving (Eq)

-- data Scheme = Scheme [TypeVarName] Type
type Scheme = Type

type ConstrainEnv = [Scheme]
type Constraint = (Type, Type)
type TypeVarName = String
type Subst = Map.Map TypeVarName Type

type ConstrainMonad a = ReaderT ConstrainEnv (StateT Int (Either String)) a
type SolverMonad a = Either String a

instance Show Type where
  show (ArrType a b) = paren a ++ "->" ++ paren b
  show (TabType a b) = paren a ++ "=>" ++ paren b
  show IntType = "Int"
  show (TypeVar v) = v

emptyConstrainEnv :: ConstrainEnv
emptyConstrainEnv = undefined

gettype :: Expr -> Either String Type
gettype expr = let f = runReaderT (constrain expr) emptyConstrainEnv
                   t = evalStateT f 0
               in case t of
                    Left e -> Left e
                    Right (t, _) -> Right t


paren :: Show a => a -> String
paren x = "(" ++ show x ++ ")"

constrain :: Expr -> ConstrainMonad (Type, [Constraint])
constrain expr = case expr of
  Lit c -> return (IntType, [])
  Var v -> do
    t <- lookupTEnv v
    return (t, [])
  Lam body -> do
    a <- fresh
    (b, c) <- local (updateTEnv a) (constrain body)
    return (a `ArrType` b, c)
  App fexpr arg -> do
    (x, c1) <- constrain arg
    (f, c2) <- constrain fexpr
    y <- fresh
    return (y, c1 ++ c2 ++ [(f, x `ArrType` y)])

lookupTEnv :: Int -> ConstrainMonad Type
lookupTEnv i = do env <- ask
                  return $ env !! i

updateTEnv :: Scheme -> ConstrainEnv -> ConstrainEnv
updateTEnv = (:)

fresh :: ConstrainMonad Type
fresh = do i <- get
           put $ i + 1
           return $ TypeVar (show i)


bind :: TypeVarName -> Type -> SolverMonad Subst
bind v t | v `occursIn` t = Left "Infinite type"
         | otherwise = Right $ Map.singleton v t

occursIn :: TypeVarName -> Type -> Bool
occursIn v t = False -- todo: fix!

unify :: Type -> Type -> SolverMonad Subst
unify t1 t2 | t1 == t2 = return idSubst
unify t (TypeVar v) = bind v t
unify (TypeVar v) t = bind v t
unify (ArrType a b) (ArrType a' b') = do
  sa  <- unify a a'
  sb <- unify (applySub sa b) (applySub sa b')
  return $ sa >>> sb

(>>>) :: Subst -> Subst -> Subst
(>>>) s1 s2 = let s1' = Map.map (applySub s2) s1
              in Map.union s1' s2

applySub :: Subst -> Type -> Type
applySub s t = case t of
  IntType     -> IntType
  ArrType a b -> applySub s a `ArrType` applySub s b
  TabType k v -> applySub s k `TabType` applySub s v
  TypeVar v   -> case Map.lookup v s of
                   Just t  -> t
                   Nothing -> TypeVar v

idSubst :: Subst
idSubst = Map.empty

solve :: Subst -> Constraint -> SolverMonad Subst
solve s (t1, t2) = do
  s' <- unify (applySub s t1) (applySub s t2)
  return $ s >>> s'

solveAll :: [Constraint] -> SolverMonad Subst
solveAll = foldM solve idSubst
