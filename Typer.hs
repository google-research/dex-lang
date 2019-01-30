module Typer (translateExpr, inferTypesCmd, inferTypesExpr) where

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

type TypingEnv = FullEnv SigmaType ISet () ()
type Constraint = (Type, Type)
type Subst = (M.Map MetaVar Type, M.Map IMetaVar ISet)
type ConstrainMonad a = ReaderT TypingEnv (
                          WriterT [Constraint] (
                            StateT Int Identity)) a

inferTypesCmd :: Command UExpr -> TypingEnv -> Command TLamExpr
inferTypesCmd (Command cmdName expr) ftenv = case cmdName of
    GetParse -> CmdResult (show expr)
    _ -> case translateExpr expr env of
      Left e -> CmdErr e
      Right expr' -> case cmdName of
        GetType  -> CmdResult $ case getSigmaType env expr' of
                                  Left e -> error $ show e
                                  Right t -> show t
        GetTyped -> CmdResult $ show expr'
        _ -> Command cmdName expr'
  where env = addBuiltins ftenv

inferTypesCmd (CmdResult s) _ = CmdResult s
inferTypesCmd (CmdErr e)    _ = CmdErr e

inferTypesExpr :: UExpr -> TypingEnv -> Except (SigmaType, TLamExpr)
inferTypesExpr rawExpr fenv = do
  let env = addBuiltins fenv
  expr <- translateExpr rawExpr env
  ty <- getSigmaType env expr
  return (ty, expr)

translateExpr :: UExpr -> TypingEnv -> Except TLamExpr
translateExpr rawExpr env = do
  let (expr, constraints) = runConstrainMonad env (fresh >>= check rawExpr)
  subst <- solveAll constraints
  return $ generalize $ applySubExpr subst expr

runConstrainMonad :: TypingEnv -> ConstrainMonad a -> (a, [Constraint])
runConstrainMonad env m = evalState (runWriterT (runReaderT m env)) 0

check :: UExpr -> Type -> ConstrainMonad Expr
check expr reqTy = case expr of
  ULit c -> do addConstraint (litType c, reqTy)
               return (Lit c)
  UVar v -> do
    s@(Forall n _ t) <- asks $ (! v) . lEnv
    vs <- replicateM n fresh
    addConstraint (reqTy, instantiateSigmaType s vs)
    return $ Var v vs
  ULet p bound body -> do
    (tBound, bound') <- infer bound
    (tVars, p') <- constrainPat p tBound
    body' <- local (setLEnv $ addBVars (map asSigma tVars)) (check body reqTy)
    return $ Let p' bound' body'
  ULam p body -> do
    (a, b) <- splitFun reqTy
    (tVars, p') <- constrainPat p a
    body' <- local (setLEnv $ addBVars (map asSigma tVars)) (check body b)
    return $ Lam p' body'
  UApp fexpr arg -> do
    (f, fexpr') <- infer fexpr
    (a, b) <- splitFun f
    arg' <- check arg a
    addConstraint (b, reqTy)
    return $ App fexpr' arg'
  UFor p body -> do
    (i, v) <- splitTab reqTy
    body' <- local (setIEnv $ addBVar i) (check body v)
    return $ For (VarPat i) body'
  UGet expr idxExpr -> do
    (tabTy, expr') <- infer expr
    (i, v) <- splitTab tabTy
    constrainIdxExpr idxExpr i
    addConstraint (v, reqTy)
    return $ Get expr' idxExpr
  UUnpack _ bound body -> do
    (tBound, bound') <- infer bound
    tBound' <- unpackExists tBound
    body' <- local (setLEnv $ addBVars [asSigma tBound']) (check body reqTy)
    return $ Unpack tBound' bound' body'
  where
    infer :: UExpr -> ConstrainMonad (Type, Expr)
    infer expr = do ty <- fresh
                    expr' <- check expr ty
                    return (ty, expr')
    constrainIdxExpr :: IdxExpr -> ISet -> ConstrainMonad ()
    constrainIdxExpr expr reqISet = case expr of
      RecLeaf v -> do actualISet <- asks $ (! v) . iEnv
                      addConstraint (reqISet ==> unitTy, actualISet ==> unitTy)
      -- RecTree r -> do ts <- mapM constrainIdxExpr r
      --                 return (RecType ts)

litType :: LitVal -> Type
litType v = BaseType $ case v of
  IntLit  _ -> IntType
  RealLit _ -> RealType
  StrLit  _ -> StrType


constrainPat :: UPat -> Type -> ConstrainMonad ([Type], Pat)
constrainPat p t = case p of
  VarPat _ -> return ([t], VarPat t)
  -- RecPat r -> do
  --   freshRecType <- mapM (\_ -> fresh) r
  --   addConstraint (t, RecType freshRecType)
  --   tes <- sequence $ case zipWithRecord constrainPat r freshRecType
  --                       of Just r' -> r'
  --   return (concat (map fst (toList tes)), RecPat $ fmap snd tes)

-- constrainIdxPat :: UIPat -> Type -> ConstrainMonad ([Type], IPat)
-- constrainIdxPat = constrainPat

addConstraint :: Constraint -> ConstrainMonad ()
addConstraint x = tell [x]

skolemVar :: ConstrainMonad (VarName, Type)
skolemVar = do i <- get
               put $ i + 1
               let name = "*" ++ show i
               return (name, TypeVar (FV name))

splitFun :: Type -> ConstrainMonad (Type, Type)
splitFun f = case f of
  ArrType a b -> return (a, b)
  _ -> do a <- fresh
          b <- fresh
          addConstraint (f, a --> b)
          return (a, b)

splitTab :: Type -> ConstrainMonad (ISet, Type)
splitTab t = case t of
  TabType i v -> return (i, v)
  _ -> do i <- freshI
          v <- fresh
          addConstraint (t, i ==> v)
          return (i, v)

unpackExists :: Type -> ConstrainMonad Type
unpackExists t = case t of
  Exists body -> return body
  _ -> do body <- fresh
          addConstraint (Exists body, t)
          return body

generalize :: Expr -> TLamExpr
generalize e =
  let (vs, vsI) = metaTypeVarsExpr e
      s1 = M.fromList $ zip (nub vs)  $ map (TypeVar . BV) [0..]
      s2 = M.fromList $ zip (nub vsI) $ map (ISet . BV) [0..]
  in TLam (length (nub vs)) (length (nub vsI)) (applySubExpr (s1, s2) e)

instantiateSigmaType :: SigmaType -> [Type] -> Type
instantiateSigmaType (Forall _ _ t) env = recur t
  where recur t = case t of
                    ArrType a b -> recur a --> recur b
                    TypeVar (BV v) | v < length env -> env !! v
                    t -> t
                    -- TabType a b   -> recur a ==> recur b
                    -- RecType r     -> RecType $ fmap recur r

inc :: ConstrainMonad Int
inc = do i <- get
         put $ i + 1
         return i

fresh :: ConstrainMonad Type
fresh = liftM (MetaTypeVar . MetaVar) inc

freshI :: ConstrainMonad ISet
freshI = liftM (IMetaTypeVar . IMetaVar) inc

bind :: MetaVar -> Type -> Except Subst
bind v t | v `occursIn` t = Left InfiniteTypeErr
         | otherwise = Right $ (M.singleton v t, M.empty)

occursIn :: MetaVar -> Type -> Bool
occursIn v t = v `elem` fst (metaTypeVars t)

unify :: Type -> Type -> Except Subst
unify t1 (TypeVar v) = Left $ UnificationErr t1 (TypeVar v)
unify (TypeVar v) t2 = Left $ UnificationErr t2 (TypeVar v)
unify t1 t2 | t1 == t2 = return idSubst
unify t (MetaTypeVar v) = bind v t
unify (MetaTypeVar v) t = bind v t
unify (ArrType a b) (ArrType a' b') = unifyPair (a,b) (a', b')
unify (TabType a b) (TabType a' b') = unifyTab (a,b) (a', b')
unify (Exists t) (Exists t') = unify t t'
unify t1 t2 = Left $ UnificationErr t1 t2

unifyPair :: (Type,Type) -> (Type,Type) -> Except Subst
unifyPair (a,b) (a',b') = do
  sa  <- unify a a'
  sb <- unify (applySub sa b) (applySub sa b')
  return $ sa >>> sb

unifyTab :: (ISet,Type) -> (ISet,Type) -> Except Subst
unifyTab (a,b) (a',b') = do
  sa <- unifyISet a a'
  sb <- unify (applySub sa b) (applySub sa b')
  return $ sa >>> sb

unifyISet :: ISet -> ISet -> Except Subst
unifyISet s1 s2 | s1 == s2 = return idSubst
unifyISet s (IMetaTypeVar v) = ibind v s
unifyISet (IMetaTypeVar v) s = ibind v s
unifyISet s1 s2 = Left $ UnificationErr (s1 ==> unitTy) (s2 ==> unitTy)

-- need an occurs check here
ibind :: IMetaVar -> ISet -> Except Subst
ibind v s = Right $ (M.empty, M.singleton v s)

(>>>) :: Subst -> Subst -> Subst
(>>>) s1@(tySub1, setSub1) s2@(tySub2, setSub2) =
  let tySub1' = M.map (applySub s2) tySub1
      setSub1' = M.map (applySetSub setSub2) setSub1
  in (M.union tySub1' tySub2, M.union setSub1' setSub2)

applySetSub :: M.Map IMetaVar ISet -> ISet -> ISet
applySetSub sub set = case set of
  ISet _ -> set
  IMetaTypeVar v -> case M.lookup v sub of
                     Just set' -> set'
                     Nothing   -> set

applySub :: Subst -> Type -> Type
applySub s@(tySub, setSub) t = case t of
  BaseType _    -> t
  TypeVar _     -> t
  ArrType a b   -> recur a --> recur b
  TabType a b   -> applySetSub setSub a ==> recur b
  MetaTypeVar v ->  case M.lookup v tySub of
                     Just t' -> t'
                     Nothing -> t
  Exists body -> Exists $ recur body
  where recur = applySub s


applySubExpr :: Subst -> Expr -> Expr
applySubExpr s expr = case expr of
    Lit _ -> expr
    Var v ts -> Var v $ map (applySub s) ts
    Let p bound body -> Let (applySubPat p) (recur bound) (recur body)
    Lam p body     -> Lam (applySubPat p) (recur body)
    App fexpr arg  -> App (recur fexpr) (recur arg)
    For p body     -> For (applyISubPat p) (recur body)
    Get e ie       -> Get (recur e) ie
    Unpack t bound body -> Unpack (applySub s t) (recur bound) (recur body)

  where
    recur = applySubExpr s
    applySubPat = fmap (applySub s)
    applyISubPat = fmap (applySetSub (snd s))

metaTypeVars :: Type -> ([MetaVar], [IMetaVar])
metaTypeVars t = case t of
  ArrType a b -> catPair (metaTypeVars a) (metaTypeVars b)
  TabType a b -> catPair (iMetaTypeVars a) (metaTypeVars b)
  MetaTypeVar v   -> ([v], [])
  _ -> ([], [])

metaTypeVarsExpr :: Expr -> ([MetaVar], [IMetaVar])
metaTypeVarsExpr expr = case expr of
    Var v ts         -> pairConcat (map metaTypeVars ts)
    Let p bound body -> metaTypeVarsPat p `catPair` recur bound `catPair` recur body
    Lam p body       -> metaTypeVarsPat p  `catPair` recur body
    App fexpr arg    -> recur fexpr `catPair` recur arg
    For p body       -> metaITypeVarsPat p `catPair` recur body
    Get e ie         -> recur e
    _ -> ([], [])
  where
    recur = metaTypeVarsExpr
    metaTypeVarsPat  p = pairConcat $ map metaTypeVars (toList p)
    metaITypeVarsPat p = pairConcat $ map iMetaTypeVars (toList p)

iMetaTypeVars :: ISet -> ([MetaVar], [IMetaVar])
iMetaTypeVars s = ([], case s of ISet _ -> []
                                 IMetaTypeVar v -> [v])

catPair :: ([a], [b]) -> ([a], [b]) -> ([a], [b])
catPair (xs, ys) (xs', ys') = (xs ++ xs', ys ++ ys')

pairConcat :: [([a], [b])] -> ([a], [b])
pairConcat xs = (concat (map fst xs), concat (map snd xs))


idSubst :: Subst
idSubst = (M.empty, M.empty)

solve :: Subst -> Constraint -> Except Subst
solve s (t1, t2) = do
  s' <- unify (applySub s t1) (applySub s t2)
  return $ s >>> s'

solveAll :: [Constraint] -> Except Subst
solveAll = foldM solve idSubst

asSigma :: Type -> SigmaType
asSigma = Forall 0 0

getSigmaType :: TypingEnv -> TLamExpr -> Except SigmaType
getSigmaType env (TLam n i expr) = liftM (Forall n i) (getType env' expr)
  where env' = setTEnv (addBVars (replicate n ())) env

getType :: TypingEnv -> Expr -> Except Type
getType env expr = case expr of
    Lit c          -> return $ litType c
    Var v ts       -> return $ instantiateSigmaType ((lEnv env) ! v) ts
    Let p bound body -> do bt <- recur bound
                           bt' <- getPatType' p
                           assertEq bt' bt "Type mismatch in 'let'"
                           recurWithEnv p body
    Lam p body     -> do b <- recurWithEnv p body
                         a <- getPatType' p
                         return $ a --> b
    App fexpr arg  -> do (ArrType a b) <- recur fexpr
                         a' <- recur arg
                         assertEq a a' "Type mismatch in 'app'"
                         return b
    For p body     -> do b <- recurWithIEnv p body
                         a <- getIPatType p
                         return $ a ==> b
    Get e ie       -> do (TabType a b) <- recur e
                         assertEq a (getIdxExprType ie) "Type mismatch in 'get'"
                         return b
    Unpack t bound body -> do (Exists bt) <- recur bound
                              assertValidType (tEnv env) t
                              assertEq t bt "Type mismatch in 'unpack'"
                              recurWithEnv (VarPat t) body
  where
    recur = getType env
    recurWithEnv   p = getType $ setLEnv (addBVars (map asSigma $ toList p)) env
    recurWithIEnv  p = getType $ setIEnv (addBVars (toList p)) env
    getIdxExprType ie = case ie of RecLeaf v -> iEnv env ! v
                                   -- RecTree r -> RecType $ fmap getIdxExprType r
    getPatType' p = do let t = getPatType p
                       assertValidType (tEnv env) t
                       return t
    getIPatType p = return $ case p of (VarPat i) -> i

assertValidType :: Env TVar () -> Type -> Except ()
assertValidType env t = case t of
    BaseType _  -> return ()
    ArrType a b -> recur a >> recur b
    TabType a b -> assertValidISet a >> recur b
    TypeVar v | v `isin` env   -> return ()
              | otherwise -> err $ "Type variable not in scope: " ++ show (t, v)
    MetaTypeVar _         -> err "variable not in scope"
  where err = Left . CompilerErr
        recur = assertValidType env
        assertValidISet s = case s of ISet v -> Right ()
                                      IMetaTypeVar _ -> err "Meta set variable"

getPatType :: Pat -> Type
getPatType p = case p of
  VarPat t -> t
  -- RecPat r -> RecType $ fmap getPatType r

addBuiltins :: TypingEnv -> TypingEnv
addBuiltins = setLEnv (<> builtinEnv)

builtinEnv :: Env Var SigmaType
builtinEnv = newEnv $
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
    , ("sum", sumType)
    ]
  where
    binOpType    = asSigma $ int --> int --> int
    realUnOpType = asSigma $ real --> real
    reduceType = Forall 1 1 $ (a --> a --> a) --> a --> (i ==> a) --> a
    iotaType = asSigma $ int --> Exists (i ==> int)
    sumType = Forall 0 1 $ (i ==> int) --> int
    a = TypeVar (BV 0)
    b = TypeVar (BV 1)
    i = ISet (BV 0)
    int = BaseType IntType
    real = BaseType RealType

instance Arbitrary BaseType where
  arbitrary = elements [IntType, BoolType, RealType, StrType]

instance Arbitrary Type where
  arbitrary = sized genType

assertEq :: (Show a, Eq a) => a -> a -> String -> Except ()
assertEq x y s = if x == y then return () else Left (CompilerErr msg)
  where msg = s ++ ": " ++ show x ++ " != " ++ show y

nonNeg :: Gen Int
nonNeg = fmap unwrap arbitrary
  where unwrap (NonNegative x) = x

genLeaf :: Gen Type
genLeaf = frequency [ (4, fmap BaseType arbitrary)
                    , (1, fmap (TypeVar . BV) nonNeg) ]

genSimpleType :: Int -> Gen Type
genSimpleType 0 = genLeaf
-- genSimpleType n = oneof [genLeaf, fmap RecType (arbitraryRecord subtree)]
--   where subtree = genSimpleType (n `div` 2)

genType :: Int -> Gen Type
genType 0 = genLeaf
genType n = frequency $
  [ (3, genLeaf)
  , (1, liftM2 ArrType subTree subTree)
  -- , (3, fmap RecType (arbitraryRecord subTree))
  -- , (3, liftM2 TabType simpleSubTree subTree)
  ]
            where
              subTree       = genType n'
              simpleSubTree = genSimpleType n'
              n' = n `div` 2
