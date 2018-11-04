module Typer (Type (..), TypeErr (..), ClosedType (..), BaseType (..), TypeEnv,
              initTypeEnv, typeExpr) where


import Control.Monad
import Control.Monad.Reader (ReaderT, runReaderT, local, ask)
import Control.Monad.State (StateT, evalStateT, put, get)
import qualified Data.Map.Strict as Map
import Data.List (nub, intersperse)
import Syntax
import Record

data Type = BaseType BaseType
          | ArrType Type Type
          | TabType Type Type
          | RecType (Record Type)
          | TypeVar Int  deriving (Eq)

data BaseType = IntType | RealType | StrType deriving (Eq, Show)

data ClosedType = Forall Int Type  deriving (Eq)
data InferType = Open Type | Closed ClosedType

data TypeErr = UnificationError Type Type
             | InfiniteType  deriving (Eq)

type Except a = Either TypeErr a
type TypeEnv = [ClosedType]
type ITypeEnv = [Type]
type Env = ([InferType], ITypeEnv)
type Constraint = (Type, Type)
type Subst = Map.Map Int Type
type ConstrainMonad a = ReaderT Env (StateT Int (Either TypeErr)) a

typeExpr :: Expr -> TypeEnv -> Except ClosedType
typeExpr expr tenv = do
  let env = (map Closed tenv, [])
  (ty, constraints) <- evalStateT (runReaderT (constrain expr) env) 0
  subst <- solveAll constraints
  return $ generalize $ applySub subst ty

initTypeEnv :: TypeEnv
initTypeEnv =
  let a = TypeVar 0
      b = TypeVar 1
      int = BaseType IntType
      binOp = Forall 0 $ int --> int --> int
  in [ Forall 0 $ int --> int ==> int                        -- iota
     , Forall 2 $ (b --> b --> b) --> b --> (a ==> b) --> b  -- reduce
     , binOp, binOp, binOp, binOp]

infixr 1 -->
infixr 2 ==>
(-->) = ArrType
(==>) = TabType

constrain :: Expr -> ConstrainMonad (Type, [Constraint])
constrain expr = case expr of
  Lit c -> return (BaseType IntType, [])
  Var v -> do
    t <- lookupEnv v
    return (t, [])
  Let p bound body -> do
    (t1, c1) <- constrain bound
    (env, _) <- ask
    (t2, c2) <- local (updateEnv t1) (constrain body)
    return (t2, c1 ++ c2)
  Lam p body -> do
    a <- fresh
    (b, c) <- local (updateEnv a) (constrain body)
    return (a --> b, c)
  App fexpr arg -> do
    (x, c1) <- constrain arg
    (f, c2) <- constrain fexpr
    y <- fresh
    return (y, c1 ++ c2 ++ [(f, x --> y)])
  For body -> do
    a <- fresh
    (b, c) <- local (updateIEnv a) (constrain body)
    return (a ==> b, c)
  Get expr idx -> do
    i <- lookupIEnv idx
    (e, c) <- constrain expr
    y <- fresh
    return (y, c ++ [(e, i ==> y)])
  RecCon exprs -> do
    ts_and_cs <- sequenceRecord (mapRecord constrain exprs)
    return ( RecType              $ mapRecord fst ts_and_cs
           , concat . recordElems $ mapRecord snd ts_and_cs)

lookupEnv :: Int -> ConstrainMonad Type
lookupEnv i = do (env,_) <- ask
                 case env !! i of
                   Open t     -> return t
                   Closed t -> specialize t

lookupIEnv :: Int -> ConstrainMonad Type
lookupIEnv i = do (_,ienv) <- ask
                  return $ ienv !! i

updateEnv :: Type -> Env -> Env
updateEnv t (env, ienv) = (Open t : env, ienv)

updateIEnv :: Type -> Env -> Env
updateIEnv t (env, ienv) = (env, t:ienv)

generalize :: Type -> ClosedType
generalize t = let vs = allVars t
                   s = Map.fromList $ zip vs $ map TypeVar [0..]
               in Forall (length vs) (applySub s t)

specialize :: ClosedType -> ConstrainMonad Type
specialize (Forall n t) = do
   vs <- replicateM n fresh
   let s = Map.fromList $ zip [0..] vs
   return $ applySub s t

fresh :: ConstrainMonad Type
fresh = do i <- get
           put $ i + 1
           return $ TypeVar i

bind :: Int -> Type -> Except Subst
bind v t | v `occursIn` t = Left InfiniteType
         | otherwise = Right $ Map.singleton v t

occursIn :: Int -> Type -> Bool
occursIn v t = case t of
  BaseType _  -> False
  ArrType a b -> occursIn v a || occursIn v b
  TabType a b -> occursIn v a || occursIn v b
  TypeVar v'  -> v == v'

unify :: Type -> Type -> Except Subst
unify t1 t2 | t1 == t2 = return idSubst
unify t (TypeVar v) = bind v t
unify (TypeVar v) t = bind v t
unify (ArrType a b) (ArrType a' b') = unifyPair (a,b) (a', b')
unify (TabType a b) (TabType a' b') = unifyPair (a,b) (a', b')
unify t1 t2 = Left $ UnificationError t1 t2

unifyPair :: (Type,Type) -> (Type,Type) -> Except Subst
unifyPair (a,b) (a',b') = do
  sa  <- unify a a'
  sb <- unify (applySub sa b) (applySub sa b')
  return $ sa >>> sb

(>>>) :: Subst -> Subst -> Subst
(>>>) s1 s2 = let s1' = Map.map (applySub s2) s1
              in Map.union s1' s2

applySub :: Subst -> Type -> Type
applySub s t = case t of
  BaseType b  -> BaseType b
  ArrType a b -> applySub s a --> applySub s b
  TabType a b -> applySub s a ==> applySub s b
  RecType r   -> RecType $ mapRecord (applySub s) r
  TypeVar v   -> case Map.lookup v s of
                   Just t  -> t
                   Nothing -> TypeVar v

allVars :: Type -> [Int]
allVars t = case t of
  BaseType _  -> []
  ArrType a b -> nub $ allVars a ++ allVars b
  TabType a b -> nub $ allVars a ++ allVars b
  RecType r   -> nub . concat . recordElems . mapRecord allVars $ r
  TypeVar v   -> [v]

idSubst :: Subst
idSubst = Map.empty

solve :: Subst -> Constraint -> Except Subst
solve s (t1, t2) = do
  s' <- unify (applySub s t1) (applySub s t2)
  return $ s >>> s'

solveAll :: [Constraint] -> Except Subst
solveAll = foldM solve idSubst

instance Show ClosedType where
  show (Forall 0 t) = show t
  show (Forall n t) = let vs = concat $ intersperse " " $ map varName [0..n-1]
                      in "forall " ++ vs ++ ": " ++ show t

instance Show Type where
  show t = case t of
    ArrType a b -> "(" ++ show a ++ " -> " ++ show b ++ ")"
    TabType a b -> "(" ++ show a ++ "=>" ++ show b ++ ")"
    BaseType b  -> case b of
                     IntType -> "Int"
                     StrType -> "Str"
                     RealType -> "Real"
    RecType m   -> show m
    TypeVar v   -> varName v


instance Show TypeErr where
  show e = "Type error: " ++
    case e of
      InfiniteType     -> "infinite type"
      UnificationError t1 t2 -> "can't unify " ++ show t1
                                   ++ " with " ++ show t2

varName :: Int -> String
varName n | n < 26    = [['a'..'z'] !! n]
          | otherwise = varName (mod n 26) ++ show (div n 26)
