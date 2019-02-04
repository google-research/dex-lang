module Typer (translateExpr, inferTypesCmd, inferTypesExpr) where

import Control.Monad
import Control.Monad.Identity
import Control.Monad.Reader (ReaderT, runReaderT, local, ask, asks)
import Control.Monad.Writer hiding ((<>))
import Control.Monad.State (StateT, evalState, put, get)
import Test.QuickCheck hiding ((==>))
import qualified Data.Map.Strict as M
import Data.List (nub)
import Data.Foldable (toList)
import Data.Semigroup
import qualified Data.Set as Set

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
  let (expr, (Constraints cs _ _)) = runConstrainMonad env (fresh >>= check rawExpr)
  subst <- solveAll cs
  return $ generalize $ applySubExpr subst expr

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
    ((tBound, bound'), Constraints cs tVars _) <- capture (infer bound)
    let (Right sub) = solveAll cs
        (freshSub, oldSub) = splitSub tVars sub
        leakedVars = rhsVars oldSub
        newConstraints = subAsConstraints oldSub
        tBound'' = applySub freshSub tBound
        bound'' = applySubExpr freshSub bound'
        flexVars = listDiff (listDiff tVars leakedVars)
                            (M.keys (fst freshSub))
        s = (M.fromList $ zip flexVars $ map (TypeVar . BV) [0..], M.empty)
        tBoundGen = Forall (length flexVars) 0 $ applySub s tBound''
        boundGen  = TLam   (length flexVars) 0 $ applySubExpr s bound''

    tell $ Constraints newConstraints leakedVars []
    body' <- local (setLEnv $ addBVar tBoundGen) (check body reqTy)
    return $ Let (VarPat tBoundGen) boundGen body'

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

splitSub :: [MetaVar] -> Subst -> (Subst, Subst)
splitSub ks (s, _) =
  let posSubst = M.fromList $ [(k, v) | k <- ks, (Just v) <- [M.lookup k s]]
      negSubst = s M.\\ M.fromList (zip ks (repeat ()))
  in ((posSubst, M.empty), (negSubst, M.empty))

rhsVars :: Subst -> [MetaVar]
rhsVars (s, _) = nub $ concat $ map (fst . metaTypeVars) (M.elems s)

subAsConstraints :: Subst -> [Constraint]
subAsConstraints (m, _) = map asConstraint (M.toList m)
  where asConstraint (mv, t) = (MetaTypeVar mv, t)

listDiff :: Ord a => [a] -> [a] -> [a]
listDiff xs ys = Set.toList $ Set.difference (Set.fromList xs) (Set.fromList ys)

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

generalize :: Expr -> Expr
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

-- invariant: lhs and rhs metavars of substitutions are distinct
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
  Forall t s body -> Forall t s $ recur body
  where recur = applySub s


applySubExpr :: Subst -> Expr -> Expr
applySubExpr s expr = case expr of
    Lit _ -> expr
    Var _ -> expr
    Let p bound body -> Let (applySubPat p) (recur bound) (recur body)
    Lam p body     -> Lam (applySubPat p) (recur body)
    App fexpr arg  -> App (recur fexpr) (recur arg)
    For p body     -> For (applyISubPat p) (recur body)
    Get e ie       -> Get (recur e) ie
    Unpack t bound body -> Unpack (applySub s t) (recur bound) (recur body)
    TLam nt ns expr -> TLam nt ns (recur expr)
    TApp expr ts -> TApp (recur expr) (map (applySub s) ts)

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
    Let p bound body -> metaTypeVarsPat p `catPair` recur bound `catPair` recur body
    Lam p body       -> metaTypeVarsPat p  `catPair` recur body
    App fexpr arg    -> recur fexpr `catPair` recur arg
    For p body       -> metaITypeVarsPat p `catPair` recur body
    Get e ie         -> recur e
    TLam _ _ expr    -> recur expr
    TApp expr ts     -> recur expr `catPair` pairConcat (map metaTypeVars ts)
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
