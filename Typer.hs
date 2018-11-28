module Typer (Type (..), TypeErr (..), ClosedType (..), BaseType (..), TypeEnv,
              typeExpr, typePatMatch, unitType) where


import Control.Monad
import Control.Monad.Identity
import Control.Monad.Reader (ReaderT, runReaderT, local, ask)
import Control.Monad.Writer (WriterT, runWriterT, tell)
import Control.Monad.State (StateT, evalState, put, get)
import Test.QuickCheck hiding ((==>))
import qualified Data.Map.Strict as Map
import Data.List (nub, intersperse)
import Data.Foldable (toList)
import Data.Traversable
import Syntax
import Record

data Type = BaseType BaseType
          | ArrType Type Type
          | TabType Type Type
          | RecType (Record Type)
          | TypeVar Int  deriving (Eq)

data BaseType = IntType | BoolType | RealType | StrType deriving (Eq)

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
type ConstrainMonad a = ReaderT Env (
                          WriterT [Constraint] (
                            StateT Int Identity)) a

typeExpr :: Expr -> TypeEnv -> Except ClosedType
typeExpr expr tenv = do
  let env = (map Closed tenv, [])
      (ty, constraints) = runConstrainMonad env (constrain expr)
  subst <- solveAll constraints
  return $ generalize $ applySub subst ty

typePatMatch :: Pat -> ClosedType -> Except [ClosedType]
typePatMatch p t = do
  let m = specialize t >>= constrainPat p
      (ts, constraints) = runConstrainMonad ([],[]) m
  subst <- solveAll constraints
  return $ map (generalize . applySub subst) ts

runConstrainMonad :: Env -> ConstrainMonad a -> (a, [Constraint])
runConstrainMonad env m = evalState (runWriterT (runReaderT m env)) 0


infixr 1 -->
infixr 2 ==>
(-->) = ArrType
(==>) = TabType

constrain :: Expr -> ConstrainMonad Type
constrain expr = case expr of
  Lit c -> return $ litType c
  Var v -> do
    t <- lookupEnv v
    return t
  Let p bound body -> do
    tBound <- constrain bound
    tVars  <- constrainPat p tBound
    t      <- local (updateEnv tVars) (constrain body)
    return t
  Lam p body -> do
    a     <- fresh
    tVars <- constrainPat p a
    b     <- local (updateEnv tVars) (constrain body)
    return (a --> b)
  App fexpr arg -> do
    x <- constrain arg
    f <- constrain fexpr
    y <- fresh
    addConstraint (f, x --> y)
    return y
  For p body -> do
    a <- fresh
    tVars <- constrainIdxPat p a
    b <- local (updateIEnv tVars) (constrain body)
    return (a ==> b)
  Get expr p -> do
    i <- constrainIdxExpr p
    e <- constrain expr
    y <- fresh
    addConstraint (e, i ==> y)
    return y
  RecCon exprs -> do
    ts <- mapM constrain exprs
    return (RecType ts)

litType :: LitVal -> Type
litType v = BaseType $ case v of
  IntLit  _ -> IntType
  RealLit _ -> RealType
  StrLit  _ -> StrType

constrainIdxExpr :: IdxExpr -> ConstrainMonad Type
constrainIdxExpr expr = case expr of
  IdxVar v -> lookupIEnv v
  IdxRecCon r -> do ts <- mapM constrainIdxExpr r
                    return (RecType ts)

constrainPat :: Pat -> Type -> ConstrainMonad [Type]
constrainPat p t = case p of
  VarPat   -> return [t]
  RecPat r -> do
    freshRecType <- mapM (\_ -> fresh) r
    addConstraint (t, RecType freshRecType)
    ts <- sequence $ zipWith constrainPat (toList r)
                                          (toList freshRecType)
    return (concat ts)

constrainIdxPat :: IdxPat -> Type -> ConstrainMonad [Type]
constrainIdxPat = constrainPat

addConstraint :: Constraint -> ConstrainMonad ()
addConstraint x = tell [x]

lookupEnv :: Int -> ConstrainMonad Type
lookupEnv i = do (env,_) <- ask
                 case env !! i of
                   Open t   -> return t
                   Closed t -> specialize t

lookupIEnv :: Int -> ConstrainMonad Type
lookupIEnv i = do (_,ienv) <- ask
                  return $ ienv !! i

updateEnv :: [Type] -> Env -> Env
updateEnv ts (env, ienv) = (map Open ts ++ env, ienv)


updateIEnv :: [Type] -> Env -> Env
updateIEnv t (env, ienv) = (env, t ++ ienv)

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
occursIn v t = v `elem` allVars t

unify :: Type -> Type -> Except Subst
unify t1 t2 | t1 == t2 = return idSubst
unify t (TypeVar v) = bind v t
unify (TypeVar v) t = bind v t
unify (ArrType a b) (ArrType a' b') = unifyPair (a,b) (a', b')
unify (TabType a b) (TabType a' b') = unifyPair (a,b) (a', b')
unify (RecType r) (RecType r') = unifyRec r r'
unify t1 t2 = Left $ UnificationError t1 t2

unifyPair :: (Type,Type) -> (Type,Type) -> Except Subst
unifyPair (a,b) (a',b') = do
  sa  <- unify a a'
  sb <- unify (applySub sa b) (applySub sa b')
  return $ sa >>> sb

unifyRec :: Record Type -> Record Type -> Except Subst
unifyRec r r' = case zipWithRecord unify r r' of
  Just s -> do subs <- sequence s
               return $ foldr (>>>) idSubst subs
  Nothing -> Left $ UnificationError (RecType r) (RecType r')


(>>>) :: Subst -> Subst -> Subst
(>>>) s1 s2 = let s1' = Map.map (applySub s2) s1
              in Map.union s1' s2

applySub :: Subst -> Type -> Type
applySub s t = case t of
  BaseType b  -> BaseType b
  ArrType a b -> applySub s a --> applySub s b
  TabType a b -> applySub s a ==> applySub s b
  RecType r   -> RecType $ fmap (applySub s) r
  TypeVar v   -> case Map.lookup v s of
                   Just t  -> t
                   Nothing -> TypeVar v

allVars :: Type -> [Int]
allVars t = case t of
  BaseType _  -> []
  ArrType a b -> nub $ allVars a ++ allVars b
  TabType a b -> nub $ allVars a ++ allVars b
  RecType r   -> nub . foldMap allVars $ r
  TypeVar v   -> [v]

idSubst :: Subst
idSubst = Map.empty

solve :: Subst -> Constraint -> Except Subst
solve s (t1, t2) = do
  s' <- unify (applySub s t1) (applySub s t2)
  return $ s >>> s'

solveAll :: [Constraint] -> Except Subst
solveAll = foldM solve idSubst

unitType :: ClosedType
unitType = Forall 0 (RecType emptyRecord)

instance Show ClosedType where
  show (Forall 0 t) = show t
  show (Forall n t) = let vs = concat $ intersperse " " $ map varName [0..n-1]
                      in "forall " ++ vs ++ ": " ++ show t

instance Show Type where
  show t = case t of
    ArrType a b -> "(" ++ show a ++ " -> " ++ show b ++ ")"
    TabType a b -> show a ++ "=>" ++ show b
    BaseType b  -> show b
    RecType m   -> printRecord show (RecordPrintSpec ", " ":" "," Nothing) m
    TypeVar v   -> varName v

instance Show BaseType where
  show b = case b of
             IntType -> "Int"
             StrType -> "Str"
             BoolType -> "Bool"
             RealType -> "Real"

instance Show TypeErr where
  show e = "Type error: " ++
    case e of
      InfiniteType     -> "infinite type"
      UnificationError t1 t2 -> "can't unify " ++ show t1
                                   ++ " with " ++ show t2

varName :: Int -> String
varName n | n < 26    = [['a'..'z'] !! n]
          | otherwise = varName (mod n 26) ++ show (div n 26)

nonNeg :: Gen Int
nonNeg = fmap unwrap arbitrary
  where unwrap (NonNegative x) = x

genLeaf :: Gen Type
genLeaf = frequency [ (4, fmap BaseType arbitrary)
                    , (1, fmap TypeVar nonNeg) ]

genSimpleType :: Int -> Gen Type
genSimpleType 0 = genLeaf
genSimpleType n = oneof [ genLeaf
                        , fmap RecType (arbitraryRecord subtree)]
  where subtree = genSimpleType (n `div` 2)

genType :: Int -> Gen Type
genType 0 = genLeaf
genType n = frequency $
  [ (3, genLeaf)
  , (3, fmap RecType (arbitraryRecord subTree))
  , (1, liftM2 ArrType subTree subTree)
  , (3, liftM2 TabType simpleSubTree subTree) ]
            where
              subTree       = genType n'
              simpleSubTree = genSimpleType n'
              n' = n `div` 2

instance Arbitrary BaseType where
  arbitrary = elements [IntType, BoolType, RealType, StrType]

instance Arbitrary Type where
  arbitrary = sized genType
