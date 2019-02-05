module Typer (translateExpr, inferTypesCmd, inferTypesExpr) where

import Control.Monad
import Control.Monad.Identity
import Control.Monad.Reader (ReaderT, runReaderT, local, ask, asks)
import Control.Monad.Writer hiding ((<>))
import Control.Monad.State (StateT, evalState, put, get)
import Test.QuickCheck hiding ((==>))
import qualified Data.Map.Strict as M
import Data.List (nub, elemIndex)
import Data.Foldable (toList)
import Data.Semigroup
import qualified Data.Set as Set
import Control.Lens.Fold (toListOf)
import Control.Lens.Setter (over)

import Syntax
import Env
import Record

type TypingEnv = FullEnv SigmaType ISet () ()
type Subst = (M.Map MetaVar Type, M.Map IMetaVar ISet)
type ConstrainMonad a = ReaderT TypingEnv (
                          WriterT Constraints (
                            StateT Int Identity)) a
type Constraint = (Type, Type)
data Constraints = Constraints [Constraint] [MetaVar] [IMetaVar]

inferTypesCmd :: Command UExpr -> TypingEnv -> Command Expr
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

inferTypesExpr :: UExpr -> TypingEnv -> Except (SigmaType, Expr)
inferTypesExpr rawExpr fenv = do
  let env = addBuiltins fenv
  expr <- translateExpr rawExpr env
  ty <- getSigmaType env expr
  return (ty, expr)

translateExpr :: UExpr -> TypingEnv -> Except Expr
translateExpr rawExpr env = do
  let (expr, cs) = runConstrainMonad env (fresh >>= check rawExpr)
  (subst, Constraints [] [] [], flexVars) <- solvePartial cs
  return $ generalize flexVars $ applySubExpr subst expr

runConstrainMonad :: TypingEnv -> ConstrainMonad a -> (a, Constraints)
runConstrainMonad env m = evalState (runWriterT (runReaderT m env)) 0

capture :: MonadWriter w m => m a -> m (a, w)
capture m = censor (const mempty) (listen m)

check :: UExpr -> Type -> ConstrainMonad Expr
check expr reqTy = case expr of
  ULit c -> do addConstraint (litType c, reqTy)
               return (Lit c)
  UVar v -> do
    s <- asks $ (! v) . lEnv
    case s of
      Forall n _ t -> do
        vs <- replicateM n fresh
        addConstraint (reqTy, instantiateSigmaType s vs)
        return $ TApp (Var v) vs
      _ -> do
        addConstraint (reqTy, s)
        return $ Var v
  ULet (VarPat _) bound body -> do
    ((boundTy, bound'), constraints) <- capture (infer bound)
    let (Right (sub, newConstraints, flexVars)) = solvePartial constraints
    tell newConstraints
    let boundTyGen = generalizeTy flexVars (applySubTy sub boundTy)
        boundGen   = generalize   flexVars (applySubExpr sub bound')
    body' <- local (setLEnv $ addBVar boundTyGen) (check body reqTy)
    return $ Let (VarPat boundTyGen) boundGen body'
  ULam p body -> do
    (a, b) <- splitFun reqTy
    (tVars, p') <- constrainPat p a
    body' <- local (setLEnv $ addBVars tVars) (check body b)
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
    -- this should create a free index set variable, occuring in tBound'
    -- should also return the name of this variable
    let updateL = setLEnv $ addBVars [tBound']
        updateS = setSEnv $ addBVars [()]
    body' <- local (updateL . updateS) (check body reqTy)
    -- debruijnify body with the index set variable name
    --   does this require having solved the constraints?
    --     yes, at least the constraints in the body

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


-- partially solves enought to discover unconstrained variables
solvePartial :: Constraints -> Except (Subst, Constraints, ([MetaVar], [IMetaVar]))
solvePartial (Constraints constraints vs ivs) = do
  (sub, isub) <- foldM solve idSubst constraints
  let (freshSub , remSub ) = splitMap  vs sub
      (freshISub, remISub) = splitMap ivs isub
      leakedVars = rhsVars remSub
      leakedIVars = nub $ rhsIVars remISub ++ rhsIVarsTy remSub
      newConstraints =     map asConstraint  (M.toList remSub)
                       ++  map asIConstraint (M.toList remISub)
      flexVars  = ( vs `listDiff` leakedVars ) `listDiff` M.keys freshSub
      flexIVars = (ivs `listDiff` leakedIVars) `listDiff` M.keys freshISub
  return ((freshSub, freshISub),
          Constraints newConstraints leakedVars leakedIVars,
          (flexVars, flexIVars))

  where
    splitMap :: Ord k => [k] -> M.Map k v -> (M.Map k v, M.Map k v)
    splitMap ks m = let ks' = Set.fromList ks
                        pos = M.filterWithKey (\k _ -> k `Set.member` ks') m
                    in (pos, m M.\\ pos)

    rhsVars :: M.Map MetaVar Type -> [MetaVar]
    rhsVars s = nub $ concat $ map (toListOf tyMetaVars) (M.elems s)

    rhsIVars :: M.Map IMetaVar ISet -> [IMetaVar]
    rhsIVars s = nub $ concat $ map (toListOf iSetMetaVars) (M.elems s)

    rhsIVarsTy :: M.Map MetaVar Type -> [IMetaVar]
    rhsIVarsTy s = nub $ concat $ map (toListOf (tyISets . iSetMetaVars)) (M.elems s)

    listDiff :: Ord a => [a] -> [a] -> [a]
    listDiff xs ys = Set.toList $ Set.difference (Set.fromList xs) (Set.fromList ys)

    asConstraint (mv, t) = (MetaTypeVar mv, t)
    asIConstraint (mv, t) = (IMetaTypeVar mv ==> int, t ==> int)
    int = BaseType IntType

generalize :: ([MetaVar], [IMetaVar]) -> Expr -> Expr
generalize (vs, ivs) expr = TLam (length vs) (length ivs) body
  where body = subExprDepth 0 0 sub isub expr
        sub t s v = case elemIndex v vs of
                      Just i  -> Just $ TypeVar (BV (t + i))
                      Nothing -> Nothing
        isub t s v = case elemIndex v ivs of
                      Just i  -> Just $ ISet (BV (t + i))
                      Nothing -> Nothing

generalizeTy :: ([MetaVar], [IMetaVar]) -> Type -> Type
generalizeTy (vs, ivs) expr = Forall (length vs) (length ivs) body
  where body = subTyDepth 0 0 sub isub expr
        sub t s v = case elemIndex v vs of
                      Just i  -> Just $ TypeVar (BV (t + i))
                      Nothing -> Nothing
        isub t s v = case elemIndex v ivs of
                      Just i  -> Just $ ISet (BV (t + i))
                      Nothing -> Nothing

litType :: LitVal -> Type
litType v = BaseType $ case v of
  IntLit  _ -> IntType
  RealLit _ -> RealType
  StrLit  _ -> StrType

constrainPat :: UPat -> Type -> ConstrainMonad ([Type], Pat)
constrainPat p t = case p of
  VarPat _ -> return ([t], VarPat t)

addConstraint :: Constraint -> ConstrainMonad ()
addConstraint x = tell (Constraints [x] [] [])

skolemVar :: ConstrainMonad (VarName, Type)
skolemVar = do i <- get
               put $ i + 1
               let name = "*" ++ show i
               return (name, TypeVar (FV name))

splitFun :: Type -> ConstrainMonad Constraint
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
fresh = do i <- inc
           let v = MetaVar i
           tell $ Constraints [] [v] []
           return $ MetaTypeVar v

freshI :: ConstrainMonad ISet
freshI = do i <- inc
            let v = IMetaVar i
            tell $ Constraints [] [] [v]
            return $ IMetaTypeVar v

bind :: MetaVar -> Type -> Except Subst
bind v t | v `occursIn` t = Left InfiniteTypeErr
         | otherwise = Right $ (M.singleton v t, M.empty)

occursIn :: MetaVar -> Type -> Bool
occursIn v t = v `elem` toListOf tyMetaVars t

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
  sb <- unify (applySubTy sa b) (applySubTy sa b')
  return $ sa >>> sb

unifyTab :: (ISet,Type) -> (ISet,Type) -> Except Subst
unifyTab (a,b) (a',b') = do
  sa <- unifyISet a a'
  sb <- unify (applySubTy sa b) (applySubTy sa b')
  return $ sa >>> sb

unifyISet :: ISet -> ISet -> Except Subst
unifyISet s1 s2 | s1 == s2 = return idSubst
unifyISet s (IMetaTypeVar v) = ibind v s
unifyISet (IMetaTypeVar v) s = ibind v s
unifyISet s1 s2 = Left $ UnificationErr (s1 ==> unitTy) (s2 ==> unitTy)

-- need an occurs check here
ibind :: IMetaVar -> ISet -> Except Subst
ibind v s = Right $ (M.empty, M.singleton v s)

-- invariant: lhs and rhs metavars of substitutions are distinct
(>>>) :: Subst -> Subst -> Subst
(>>>) s1@(tySub1, setSub1) s2@(tySub2, setSub2) =
  let tySub1' = M.map (applySubTy s2) tySub1
      setSub1' = M.map (applySetSub setSub2) setSub1
  in (M.union tySub1' tySub2, M.union setSub1' setSub2)

applySetSub :: M.Map IMetaVar ISet -> ISet -> ISet
applySetSub sub = subISet (subAsFun sub)

applySubTy :: Subst -> Type -> Type
applySubTy (tySub, setSub) = applyISetSub . applyTySub
  where applyTySub   = subTy (subAsFun tySub)
        applyISetSub = over tyISets (subISet (subAsFun setSub))

applySubExpr :: Subst -> Expr -> Expr
applySubExpr (tySub, setSub) = applyISetSub . applyTySub
  where applyTySub   = over exprTypes (subTy   (subAsFun tySub))
        applyISetSub = over exprISets (subISet (subAsFun setSub))

subAsFun :: Ord k => M.Map k v -> k -> Maybe v
subAsFun = flip M.lookup

idSubst :: Subst
idSubst = (M.empty, M.empty)

solve :: Subst -> Constraint -> Except Subst
solve s (t1, t2) = do
  s' <- unify (applySubTy s t1) (applySubTy s t2)
  return $ s >>> s'

getSigmaType :: TypingEnv -> Expr -> Except SigmaType
getSigmaType env (TLam n i expr) = liftM (Forall n i) (getType env' expr)
  where env' = setTEnv (addBVars (replicate n ())) env

getType :: TypingEnv -> Expr -> Except Type
getType env expr = case expr of
    Lit c          -> return $ litType c
    Var v          -> return $ (lEnv env) ! v
    Let p bound body -> do bt <- recur bound
                           bt' <- getPatType' p
                           assertEq bt' bt "Type mismatch in 'let'"
                           recurWithEnv p body
    Lam p body     -> do b <- recurWithEnv p body
                         a <- getPatType' p
                         return $ a --> b
    App fexpr arg  -> do t <- recur fexpr
                         a' <- recur arg
                         case t of ArrType a b -> do
                                     assertEq a a' "Type mismatch in 'app'"
                                     return b
                                   _ -> error $ show t ++ " is not an arrow type."
    For p body     -> do b <- recurWithIEnv p body
                         a <- getIPatType p
                         return $ a ==> b
    Get e ie       -> do (TabType a b) <- recur e
                         assertEq a (getIdxExprType ie) "Type mismatch in 'get'"
                         return b
    TLam nt ns expr -> do ty' <- recurWithtEnv nt expr
                          return $ Forall nt ns ty'
    TApp expr ts   -> do ty' <- recur expr
                         return $ instantiateSigmaType ty' ts
    Unpack t bound body -> do (Exists bt) <- recur bound
                              assertValidType (tEnv env) t
                              assertEq t bt "Type mismatch in 'unpack'"
                              recurWithEnv (VarPat t) body

  where
    recur = getType env
    recurWithEnv   p = getType $ setLEnv (addBVars (toList p)) env
    recurWithtEnv  n = getType $ setTEnv (addBVars (replicate n ())) env
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
    Forall t s body -> assertValidType (addBVars (replicate t ()) env) body
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
    binOpType    = int --> int --> int
    realUnOpType = real --> real
    reduceType = Forall 1 1 $ (a --> a --> a) --> a --> (i ==> a) --> a
    iotaType = int --> Exists (i ==> int)
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

instance Semigroup Constraints where
  (Constraints c1 v1 s1) <> (Constraints c2 v2 s2) =
    Constraints (c1 ++ c2) (v1 ++ v2) (s1 ++ s2)

instance Monoid Constraints where
  mempty = Constraints [] [] []
  mappend = (<>)
