module Typer (Type (..), TypeErr (..), SigmaType (..), BaseType (..), TypeEnv,
              typeExpr, typedExpr, unitType) where

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
import Record

import Lower
import qualified Syntax as S
import Syntax (Type (..), SigmaType (..), BaseType (..), MetaVar (..), IdxType)

data TypeErr = UnificationError Type Type
             | InfiniteType  deriving (Eq)

type Except a = Either TypeErr a

type TypeEnv = [SigmaType]
type ITypeEnv = [IdxType]

type Env = (TypeEnv, ITypeEnv)
type Constraint = (Type, Type)
type Subst = Map.Map MetaVar Type
type ConstrainMonad a = ReaderT Env (
                          WriterT [Constraint] (
                            StateT Int Identity)) a

typeExpr :: Expr -> TypeEnv -> Except SigmaType
typeExpr rawExpr tenv = fmap fst (inferTypes rawExpr tenv)

typedExpr :: Expr -> TypeEnv -> Except S.Expr
typedExpr rawExpr tenv = fmap snd (inferTypes rawExpr tenv)

inferTypes :: Expr -> TypeEnv -> Except (SigmaType, S.Expr)
inferTypes rawExpr tenv = do
  let env = (tenv, [])
      ((t, expr), constraints) = runConstrainMonad env (constrain rawExpr)
  subst <- solveAll constraints
  return $ generalize (applySub subst t) (applySubExpr subst expr)

runConstrainMonad :: Env -> ConstrainMonad a -> (a, [Constraint])
runConstrainMonad env m = evalState (runWriterT (runReaderT m env)) 0

infixr 1 -->
infixr 2 ==>
(-->) = ArrType
(==>) = TabType

constrain :: Expr -> ConstrainMonad (Type, S.Expr)
constrain expr = case expr of
  Lit c -> return (litType c, S.Lit c)
  Var v -> do
    (varType, maybeTApp) <- lookupEnv v
    return (varType, maybeTApp (S.Var v))
  Let p bound body -> do
    (tBound, bound') <- constrain bound
    (tVars, p') <- constrainPat p tBound
    (t, body') <- local (updateEnv tVars) (constrain body)
    return (t, S.Let p' (S.TLam 0 bound') body')
  Lam p body -> do
    a     <- fresh
    (tVars, p') <- constrainPat p a
    (b, body') <- local (updateEnv tVars) (constrain body)
    return (a --> b, S.Lam p' body')
  App fexpr arg -> do
    (x, fexpr') <- constrain arg
    (f, arg')  <- constrain fexpr
    y <- fresh
    addConstraint (f, x --> y)
    return (y, S.App fexpr' (S.TLam 0 arg'))
  For p body -> do
    a <- fresh
    (tVars, p') <- constrainIdxPat p a
    (b, body') <- local (updateIEnv tVars) (constrain body)
    return (a ==> b, S.For p' body')
  Get expr p -> do
    i <- constrainIdxExpr p
    (e, expr') <- constrain expr
    y <- fresh
    addConstraint (e, i ==> y)
    return (y, S.Get expr' p)
  RecCon exprs -> do
    tes <- mapM constrain exprs
    return (RecType (fmap fst tes), S.RecCon (fmap snd tes))

litType :: S.LitVal -> Type
litType v = BaseType $ case v of
  S.IntLit  _ -> IntType
  S.RealLit _ -> RealType
  S.StrLit  _ -> StrType

constrainIdxExpr :: IdxExpr -> ConstrainMonad Type
constrainIdxExpr expr = case expr of
  IdxVar v -> lookupIEnv v
  IdxRecCon r -> do ts <- mapM constrainIdxExpr r
                    return (RecType ts)

constrainPat :: Pat -> Type -> ConstrainMonad ([Type], S.Pat)
constrainPat p t = case p of
  VarPat   -> return ([t], S.VarPat t)
  RecPat r -> do
    freshRecType <- mapM (\_ -> fresh) r
    addConstraint (t, RecType freshRecType)
    tes <- sequence $ zipWith constrainPat (toList r)
                                           (toList freshRecType)
    return (concat (fmap fst tes), undefined)

constrainIdxPat :: IdxPat -> Type -> ConstrainMonad ([Type], S.IdxPat)
constrainIdxPat = constrainPat

addConstraint :: Constraint -> ConstrainMonad ()
addConstraint x = tell [x]

lookupEnv :: Int -> ConstrainMonad (Type, S.Expr -> S.Expr)
lookupEnv i = do (env,_) <- ask
                 case env !! i of
                   Forall n t -> specialize n t
                   t          -> return (t, id)

lookupIEnv :: Int -> ConstrainMonad Type
lookupIEnv i = do (_,ienv) <- ask
                  return $ ienv !! i

updateEnv :: [Type] -> Env -> Env
updateEnv ts (env, ienv) = (ts ++ env, ienv)

updateIEnv :: [Type] -> Env -> Env
updateIEnv t (env, ienv) = (env, t ++ ienv)

generalize :: Type -> S.Expr -> (SigmaType, S.Expr)
generalize t e =
  let vs = nub $ metaTypeVars t ++ metaTypeVarsExpr e
      s = Map.fromList $ zip vs $ map TypeVar [0..]
      n = (length vs)
  in (Forall n (applySub s t), S.TLam n (applySubExpr s e))

specialize :: Int -> Type -> ConstrainMonad (Type, S.Expr -> S.Expr)
specialize n t = do
   vs <- replicateM n fresh
   return $ (instantiateType vs t, \e -> S.TApp e vs)

instantiateType :: [Type] -> Type -> Type
instantiateType env t = case t of
    ArrType a b   -> recur a --> recur b
    TabType a b   -> recur a ==> recur b
    RecType r     -> RecType $ fmap recur r
    TypeVar v     ->  env !! v
    t -> t
  where recur = instantiateType env

fresh :: ConstrainMonad Type
fresh = do i <- get
           put $ i + 1
           return $ MetaTypeVar (MetaVar i)

bind :: MetaVar -> Type -> Except Subst
bind v t | v `occursIn` t = Left InfiniteType
         | otherwise = Right $ Map.singleton v t

occursIn :: MetaVar -> Type -> Bool
occursIn v t = v `elem` metaTypeVars t

unify :: Type -> Type -> Except Subst
unify t1 t2 | t1 == t2 = return idSubst
unify t (MetaTypeVar v) = bind v t
unify (MetaTypeVar v) t = bind v t
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
  ArrType a b   -> applySub s a --> applySub s b
  TabType a b   -> applySub s a ==> applySub s b
  RecType r     -> RecType $ fmap (applySub s) r
  MetaTypeVar v ->  case Map.lookup v s of
                     Just t  -> t
                     Nothing -> MetaTypeVar v
  t -> t

applySubExpr :: Subst -> S.Expr -> S.Expr
applySubExpr s expr = case expr of
    S.Let p bound body -> S.Let (applySubPat p) (recur bound) (recur body)
    S.Lam p body     -> S.Lam (applySubPat p) (recur body)
    S.App fexpr arg  -> S.App (recur fexpr) (recur arg)
    S.For p body     -> S.For (applySubPat p) (recur body)
    S.Get e ie       -> S.Get (recur e) ie
    S.RecCon r       -> S.RecCon $ fmap recur r
    S.TLam n expr    -> S.TLam n (recur expr)
    S.TApp expr ts   -> S.TApp (recur expr) (map (applySub s) ts)
    expr -> expr
  where
    recur = applySubExpr s
    applySubPat p = case p of
      S.VarPat t -> S.VarPat $ applySub s t
      S.RecPat r -> S.RecPat $ fmap applySubPat r

metaTypeVars :: Type -> [MetaVar]
metaTypeVars t = case t of
  BaseType _  -> []
  ArrType a b -> nub $ metaTypeVars a ++ metaTypeVars b
  TabType a b -> nub $ metaTypeVars a ++ metaTypeVars b
  RecType r   -> nub . foldMap metaTypeVars $ r
  TypeVar _   -> []
  MetaTypeVar v   -> [v]

metaTypeVarsExpr :: S.Expr -> [MetaVar]
metaTypeVarsExpr = undefined

idSubst :: Subst
idSubst = Map.empty

solve :: Subst -> Constraint -> Except Subst
solve s (t1, t2) = do
  s' <- unify (applySub s t1) (applySub s t2)
  return $ s >>> s'

solveAll :: [Constraint] -> Except Subst
solveAll = foldM solve idSubst

unitType :: SigmaType
unitType = RecType emptyRecord

instance Show TypeErr where
  show e = "Type error: " ++
    case e of
      InfiniteType     -> "infinite type"
      UnificationError t1 t2 -> "can't unify " ++ show t1
                                   ++ " with " ++ show t2

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
