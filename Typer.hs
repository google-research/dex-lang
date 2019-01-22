module Typer (inferTypes, inferTypesCmd, inferTypesExpr) where

import Control.Monad
import Control.Monad.Identity
import Control.Monad.Reader (ReaderT, runReaderT, local, ask, asks)
import Control.Monad.Writer (WriterT, runWriterT, tell)
import Control.Monad.State (StateT, evalState, put, get)
import Test.QuickCheck hiding ((==>))
import qualified Data.Map.Strict as M
import Data.List (nub)
import Data.Foldable (toList)
import Data.Semigroup ((<>))

import Syntax
import Env
import Record

type TypingEnv = FullEnv SigmaType IdxType ()
type Constraint = (Type, Type)
type Subst = M.Map MetaVar Type
type ConstrainMonad a = ReaderT TypingEnv (
                          WriterT [Constraint] (
                            StateT Int Identity)) a

inferTypesCmd :: Command UExpr -> TypingEnv -> Command (Type, Expr)
inferTypesCmd (Command cmdName expr) ftenv = case cmdName of
    GetParse -> CmdResult (show expr)
    _ -> case inferTypes expr ftenv of
      Left e -> CmdErr e
      Right (ty, expr') -> case cmdName of
        GetType  -> CmdResult (show ty)
        GetTyped -> CmdResult (show expr')
        _ -> Command cmdName (ty, expr')
inferTypesCmd (CmdResult s) _ = CmdResult s
inferTypesCmd (CmdErr e)    _ = CmdErr e

inferTypesExpr :: UExpr -> TypingEnv -> Except (Type, (Type, Expr))
inferTypesExpr rawExpr ftenv = do
  (ty, expr) <- inferTypes rawExpr ftenv
  return (ty, (ty, expr))

inferTypes :: UExpr -> TypingEnv -> Except (Type, Expr)
inferTypes rawExpr fenv = do
  let env = setLEnv (<> builtinEnv) fenv
      ((t, expr), constraints) = runConstrainMonad env (constrain rawExpr)
  subst <- solveAll constraints
  let (t', expr') = generalize (applySub subst t) (applySubExpr subst expr)
  t'' <- getType env expr'
  assertEq t'' t' "Final types don't match: "
  return (t', expr')

runConstrainMonad :: TypingEnv -> ConstrainMonad a -> (a, [Constraint])
runConstrainMonad env m = evalState (runWriterT (runReaderT m env)) 0

assertEq :: (Show a, Eq a) => a -> a -> String -> Except ()
assertEq x y s = if x == y then return () else Left (CompilerErr msg)
  where msg = s ++ show x ++ " != " ++ show y

constrain :: UExpr -> ConstrainMonad (Type, Expr)
constrain expr = case expr of
  ULit c -> return (litType c, Lit c)
  UVar v -> do
    t <- asks $ (! v) . lEnv
    case t of
      Forall tvs t' -> do vs <- replicateM (length tvs) fresh
                          return (instantiateType vs t', TApp (Var v) vs)
      _ -> return (t, Var v)
  ULet p bound body -> do
    (tBound, bound') <- constrain bound
    (tVars, p') <- constrainPat p tBound
    (t, body') <- local (setLEnv $ addBVars tVars) (constrain body)
    return (t, Let p' bound' body')
  ULam p body -> do
    a     <- fresh
    (tVars, p') <- constrainPat p a
    (b, body') <- local (setLEnv $ addBVars tVars) (constrain body)
    return (a --> b, Lam p' body')
  UApp fexpr arg -> do
    (f, fexpr')  <- constrain fexpr
    (x, arg') <- constrain arg
    y <- fresh
    addConstraint (f, x --> y)
    return (y, App fexpr' arg')
  UFor p body -> do
    a <- fresh
    (tVars, p') <- constrainIdxPat p a
    (b, body') <- local (setIEnv $ addBVars tVars) (constrain body)
    return (a ==> b, For p' body')
  UGet expr p -> do
    i <- constrainIdxExpr p
    (e, expr') <- constrain expr
    y <- fresh
    addConstraint (e, i ==> y)
    return (y, Get expr' p)
  URecCon exprs -> do
    tes <- mapM constrain exprs
    return (RecType (fmap fst tes), RecCon (fmap snd tes))
  UAnnot expr t -> do -- this is almost certainly wrong!
    (t', e) <- constrain expr
    case t of
      Forall vs body -> do addConstraint (body, t')
                           let n = length vs
                           return (Forall (replicate n "") body, TLam n e)
      _ -> do addConstraint (t, t')
              return (t, e)

litType :: LitVal -> Type
litType v = BaseType $ case v of
  IntLit  _ -> IntType
  RealLit _ -> RealType
  StrLit  _ -> StrType

constrainIdxExpr :: IdxExpr -> ConstrainMonad Type
constrainIdxExpr expr = case expr of
  RecLeaf v -> asks $ (! v) . iEnv
  RecTree r -> do ts <- mapM constrainIdxExpr r
                  return (RecType ts)

constrainPat :: UPat -> Type -> ConstrainMonad ([Type], Pat)
constrainPat p t = case p of
  VarPat _ -> return ([t], VarPat t)
  RecPat r -> do
    freshRecType <- mapM (\_ -> fresh) r
    addConstraint (t, RecType freshRecType)
    tes <- sequence $ case zipWithRecord constrainPat r freshRecType
                        of Just r' -> r'
    return (concat (map fst (toList tes)), RecPat $ fmap snd tes)

constrainIdxPat :: UIPat -> Type -> ConstrainMonad ([Type], IPat)
constrainIdxPat = constrainPat

addConstraint :: Constraint -> ConstrainMonad ()
addConstraint x = tell [x]

generalize :: Type -> Expr -> (SigmaType, Expr)
generalize t e =
  let vs = nub $ metaTypeVars t ++ metaTypeVarsExpr e
      s = M.fromList $ zip vs $ map (TypeVar . BV) [0..]
      n = (length vs)
  in (Forall (replicate n "") (applySub s t), TLam n (applySubExpr s e))

instantiateType :: [Type] -> Type -> Type
instantiateType env t = case t of
    ArrType a b   -> recur a --> recur b
    TabType a b   -> recur a ==> recur b
    RecType r     -> RecType $ fmap recur r
    TypeVar (BV v) -> env !! v
    t -> t
  where recur = instantiateType env

fresh :: ConstrainMonad Type
fresh = do i <- get
           put $ i + 1
           return $ MetaTypeVar (MetaVar i)

skolemVar :: ConstrainMonad Type
skolemVar = do i <- get
               put $ i + 1
               return $ TypeVar (FV ("*" ++ show i))

bind :: MetaVar -> Type -> Except Subst
bind v t | v `occursIn` t = Left InfiniteTypeErr
         | otherwise = Right $ M.singleton v t

occursIn :: MetaVar -> Type -> Bool
occursIn v t = v `elem` metaTypeVars t

unify :: Type -> Type -> Except Subst
unify t1 t2 | t1 == t2 = return idSubst
unify t (MetaTypeVar v) = bind v t
unify (MetaTypeVar v) t = bind v t
unify (ArrType a b) (ArrType a' b') = unifyPair (a,b) (a', b')
unify (TabType a b) (TabType a' b') = unifyPair (a,b) (a', b')
unify (RecType r) (RecType r') = unifyRec r r'
unify t1 t2 = Left $ UnificationErr t1 t2

unifyPair :: (Type,Type) -> (Type,Type) -> Except Subst
unifyPair (a,b) (a',b') = do
  sa  <- unify a a'
  sb <- unify (applySub sa b) (applySub sa b')
  return $ sa >>> sb

unifyRec :: Record Type -> Record Type -> Except Subst
unifyRec r r' = case zipWithRecord unify r r' of
  Just s -> do subs <- sequence s
               return $ foldr (>>>) idSubst subs
  Nothing -> Left $ UnificationErr (RecType r) (RecType r')

(>>>) :: Subst -> Subst -> Subst
(>>>) s1 s2 = let s1' = M.map (applySub s2) s1
              in M.union s1' s2

applySub :: Subst -> Type -> Type
applySub s t = case t of
  ArrType a b   -> applySub s a --> applySub s b
  TabType a b   -> applySub s a ==> applySub s b
  RecType r     -> RecType $ fmap (applySub s) r
  MetaTypeVar v ->  case M.lookup v s of
                     Just t  -> t
                     Nothing -> MetaTypeVar v
  t -> t

applySubExpr :: Subst -> Expr -> Expr
applySubExpr s expr = case expr of
    Let p bound body -> Let (applySubPat p) (recur bound) (recur body)
    Lam p body     -> Lam (applySubPat p) (recur body)
    App fexpr arg  -> App (recur fexpr) (recur arg)
    For p body     -> For (applySubPat p) (recur body)
    Get e ie       -> Get (recur e) ie
    RecCon r       -> RecCon $ fmap recur r
    TLam n expr    -> TLam n (recur expr)
    TApp expr ts   -> TApp (recur expr) (map (applySub s) ts)
    expr -> expr
  where
    recur = applySubExpr s
    applySubPat p = case p of
      VarPat t -> VarPat $ applySub s t
      RecPat r -> RecPat $ fmap applySubPat r

metaTypeVars :: Type -> [MetaVar]
metaTypeVars t = case t of
  BaseType _  -> []
  ArrType a b -> nub $ metaTypeVars a ++ metaTypeVars b
  TabType a b -> nub $ metaTypeVars a ++ metaTypeVars b
  RecType r   -> nub . foldMap metaTypeVars $ r
  TypeVar _   -> []
  Forall vs t -> metaTypeVars t
  MetaTypeVar v   -> [v]

metaTypeVarsExpr :: Expr -> [MetaVar]
metaTypeVarsExpr expr = case expr of
    Let p bound body -> metaTypeVarsPat p ++ recur bound ++ recur body
    Lam p body     -> metaTypeVarsPat p ++ recur body
    App fexpr arg  -> recur fexpr ++ recur arg
    For p body     -> metaTypeVarsPat p ++ recur body
    Get e ie       -> recur e
    RecCon r       -> concat $ map recur (toList r)
    TLam n expr    -> recur expr
    TApp expr ts   -> recur expr ++ concat (map metaTypeVars ts)
    expr -> []
  where
    recur = metaTypeVarsExpr
    metaTypeVarsPat p = concat $ map metaTypeVars (patLeaves p)

idSubst :: Subst
idSubst = M.empty

solve :: Subst -> Constraint -> Except Subst
solve s (t1, t2) = do
  s' <- unify (applySub s t1) (applySub s t2)
  return $ s >>> s'

solveAll :: [Constraint] -> Except Subst
solveAll = foldM solve idSubst

getType :: TypingEnv -> Expr -> Except Type
getType env expr = case expr of
    Lit c          -> return $ litType c
    Var v          -> return $ (lEnv env) ! v
    Let p bound body -> do bt <- recur bound
                           bt' <- getPatType' p
                           assertEq' bt' bt
                           recurWithEnv p body
    Lam p body     -> do b <- recurWithEnv p body
                         a <- getPatType' p
                         return $ a --> b
    App fexpr arg  -> do (ArrType a b) <- recur fexpr
                         a' <- recur arg
                         assertEq' a a'
                         return b
    For p body     -> do b <- recurWithIEnv p body
                         a <- getPatType' p
                         return $ a ==> b
    Get e ie       -> do (TabType a b) <- recur e
                         assertEq' a (getIdxExprType ie)
                         return b
    RecCon r       -> fmap RecType $ sequence $ fmap recur r
    TLam n expr    -> do t <- recurWithTVEnv n expr
                         return $ Forall (replicate n "") t
    TApp expr ts   -> do Forall tvs t <- recur expr
                         assertEq' (length tvs) (length ts)
                         return $ instantiateType ts t
    Unpack expr    -> recurWithTVEnv 1 expr
    Pack ty expr asty -> case asty of
                           Exists "" asty' -> do
                             subty <- recur expr
                             assertEq' subty asty'
                             return asty
  where
    recur = getType env
    assertEq' x y = assertEq x y (show expr)
    recurWithEnv   p = getType $ setLEnv (addBVars (patLeaves p)) env
    recurWithIEnv  p = getType $ setIEnv (addBVars (patLeaves p)) env
    recurWithTVEnv n = getType $ setTEnv (addBVars (replicate n ())) env
    getIdxExprType ie = case ie of RecLeaf v -> iEnv env ! v
                                   RecTree r -> RecType $ fmap getIdxExprType r
    getPatType' p = do let t = getPatType p
                       assertValidType (tEnv env) t
                       return t

assertValidType :: Env TVar () -> Type -> Except ()
assertValidType env t = case t of
    BaseType _  -> return ()
    ArrType a b -> recur a >> recur b
    TabType a b -> recur a >> recur b
    RecType r   -> sequence (fmap recur r) >> return ()
    TypeVar v | v `isin` env   -> return ()
              | otherwise -> err $ "Type variable not in scope: " ++ show v
    Forall vs body        -> let newEnv = addBVars [() | _ <- vs] env
                             in assertValidType newEnv body
    MetaTypeVar _         -> err "variable not in scope"
  where err = Left . CompilerErr
        recur = assertValidType env

patLeaves :: Pat -> [Type]
patLeaves p = case p of
  VarPat t -> [t]
  RecPat r -> concat $ map patLeaves (toList r)

getPatType :: Pat -> Type
getPatType p = case p of
  VarPat t -> t
  RecPat r -> RecType $ fmap getPatType r

unitType :: SigmaType
unitType = RecType emptyRecord

builtinEnv :: Env Var SigmaType
builtinEnv = newEnv
    [ ("add", binOpType)
    , ("sub", binOpType)
    , ("mul", binOpType)
    , ("pow", binOpType)
    , ("exp", realUnOpType)
    , ("log", realUnOpType)
    , ("sqrt", realUnOpType)
    , ("sin", realUnOpType)
    , ("cos", realUnOpType)
    , ("tan", realUnOpType)
    , ("reduce", reduceType)
    , ("iota", iotaType)
    ]
  where
    binOpType = int --> int --> int
    realUnOpType = real --> real
    reduceType = Forall ["a","b"] $ (b --> b --> b) --> b --> (a ==> b) --> b
    iotaType = int --> int ==> int
    a = TypeVar (BV 0)
    b = TypeVar (BV 1)
    int = BaseType IntType
    real = BaseType RealType

instance Arbitrary BaseType where
  arbitrary = elements [IntType, BoolType, RealType, StrType]

instance Arbitrary Type where
  arbitrary = sized genType

nonNeg :: Gen Int
nonNeg = fmap unwrap arbitrary
  where unwrap (NonNegative x) = x

genLeaf :: Gen Type
genLeaf = frequency [ (4, fmap BaseType arbitrary)
                    , (1, fmap (TypeVar . BV) nonNeg) ]

genSimpleType :: Int -> Gen Type
genSimpleType 0 = genLeaf
genSimpleType n = oneof [genLeaf, fmap RecType (arbitraryRecord subtree)]
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
