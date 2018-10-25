module Typer (TypeEnv, initTypeEnv, gettype) where

import Control.Monad
import Control.Monad.Reader (ReaderT, runReaderT, local, ask)
import Control.Monad.State (StateT, evalStateT, put, get)
import qualified Data.Map.Strict as Map
import Syntax

data Type = IntType
          | ArrType Type Type
          | TabType Type Type
          | TypeVar TypeVarName   deriving (Eq)

data TypeErr = TypeErr String
             | InfiniteType  deriving (Show)

type Except a = Either TypeErr a
type Scheme = Type   -- data Scheme = Scheme [TypeVarName] Type
type TypeEnv = [Scheme]
type Constraint = (Type, Type)
type TypeVarName = String
type Subst = Map.Map TypeVarName Type
type ConstrainMonad a = ReaderT TypeEnv (StateT Int (Either TypeErr)) a

initTypeEnv :: TypeEnv
initTypeEnv = []

gettype :: Expr -> TypeEnv -> Except Type
gettype expr env = let f = runReaderT (constrain expr) env
                       t = evalStateT f 0
                   in case t of
                       Left e       -> Left e
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

updateTEnv :: Scheme -> TypeEnv -> TypeEnv
updateTEnv = (:)

fresh :: ConstrainMonad Type
fresh = do i <- get
           put $ i + 1
           return $ TypeVar (show i)

bind :: TypeVarName -> Type -> Except Subst
bind v t | v `occursIn` t = Left InfiniteType
         | otherwise = Right $ Map.singleton v t

occursIn :: TypeVarName -> Type -> Bool
occursIn v t = False -- todo: fix!

unify :: Type -> Type -> Except Subst
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

solve :: Subst -> Constraint -> Except Subst
solve s (t1, t2) = do
  s' <- unify (applySub s t1) (applySub s t2)
  return $ s >>> s'

solveAll :: [Constraint] -> Except Subst
solveAll = foldM solve idSubst

instance Show Type where
  show (ArrType a b) = paren a ++ "->" ++ paren b
  show (TabType a b) = paren a ++ "=>" ++ paren b
  show IntType = "Int"
  show (TypeVar v) = v
