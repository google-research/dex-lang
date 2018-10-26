module Typer (Type (..), TypeErr (..), TypeEnv, initTypeEnv, typeExpr) where

import Control.Monad
import Control.Monad.Reader (ReaderT, runReaderT, local, ask)
import Control.Monad.State (StateT, evalStateT, put, get)
import qualified Data.Map.Strict as Map
import Data.List (nub)
import Syntax

data Type = IntType
          | ArrType Type Type
          | TabType Type Type
          | TypeVar TypeVarName   deriving (Eq)

data TypeErr = TypeErr String
             | UnificationError Type Type
             | InfiniteType  deriving (Show, Eq)

type Except a = Either TypeErr a
type Scheme = Type   -- data Scheme = Scheme [TypeVarName] Type
type TypeEnv = [Scheme]
type Constraint = (Type, Type)
type TypeVarName = String
type Subst = Map.Map TypeVarName Type
type ConstrainMonad a = ReaderT TypeEnv (StateT Int (Either TypeErr)) a


typeExpr :: Expr -> TypeEnv -> Except Type
typeExpr expr env = do
  (ty, constraints) <- evalStateT (runReaderT (constrain expr) env) 0
  subst <- solveAll constraints
  return $ canonicalize $ applySub subst ty

initTypeEnv :: TypeEnv
initTypeEnv = [TypeVar "BAD", TypeVar "BAD", binOpT, binOpT, binOpT, binOpT]

binOpT = IntType `ArrType` (IntType `ArrType` IntType)

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

updateTEnv :: Scheme -> TypeEnv -> TypeEnv
updateTEnv = (:)

fresh :: ConstrainMonad Type
fresh = do i <- get
           put $ i + 1
           return $ TypeVar (varName i)

varName :: Int -> String
varName n | n < 26    = [['a'..'z'] !! n]
          | otherwise = varName (mod n 26) ++ show (div n 26)

bind :: TypeVarName -> Type -> Except Subst
bind v t | v `occursIn` t = Left InfiniteType
         | otherwise = Right $ Map.singleton v t

occursIn :: TypeVarName -> Type -> Bool
occursIn v t = case t of
  IntType     -> False
  ArrType a b -> occursIn v a || occursIn v b
  TabType a b -> occursIn v a || occursIn v b
  TypeVar v'  -> v == v'


unify :: Type -> Type -> Except Subst
unify t1 t2 | t1 == t2 = return idSubst
unify t (TypeVar v) = bind v t
unify (TypeVar v) t = bind v t
unify (ArrType a b) (ArrType a' b') = do
  sa  <- unify a a'
  sb <- unify (applySub sa b) (applySub sa b')
  return $ sa >>> sb
unify t1 t2 = Left $ UnificationError t1 t2


(>>>) :: Subst -> Subst -> Subst
(>>>) s1 s2 = let s1' = Map.map (applySub s2) s1
              in Map.union s1' s2

applySub :: Subst -> Type -> Type
applySub s t = case t of
  IntType     -> IntType
  ArrType a b -> applySub s a `ArrType` applySub s b
  TabType a b -> applySub s a `TabType` applySub s b
  TypeVar v   -> case Map.lookup v s of
                   Just t  -> t
                   Nothing -> TypeVar v

allVars :: Type -> [TypeVarName]
allVars t = case t of
  IntType     -> []
  ArrType a b -> allVars a ++ allVars b
  TabType a b -> allVars a ++ allVars b
  TypeVar v   -> [v]

canonicalize :: Type -> Type
canonicalize t = let prevVars = nub $ allVars t
                     newTypeVars = map (TypeVar . varName) [0..]
                     sub = Map.fromList $ zip prevVars newTypeVars
                 in applySub sub t

idSubst :: Subst
idSubst = Map.empty

solve :: Subst -> Constraint -> Except Subst
solve s (t1, t2) = do
  s' <- unify (applySub s t1) (applySub s t2)
  return $ s >>> s'

solveAll :: [Constraint] -> Except Subst
solveAll = foldM solve idSubst

instance Show Type where
  show (ArrType a b) = "(" ++ show a ++ " -> " ++ show b ++ ")"
  show (TabType a b) = "(" ++ show a ++ "=>" ++ show b ++ ")"
  show IntType = "Int"
  show (TypeVar v) = v
