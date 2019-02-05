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
import Util

type TypingEnv = FullEnv SigmaType Kind
type Subst = M.Map MetaVar Type
type ConstrainMonad a = ReaderT TypingEnv (
                          WriterT Constraints (
                            StateT Int Identity)) a
type Constraint = (Type, Type)
data Constraints = Constraints [Constraint] [MetaVar]

inferTypesCmd :: Command UExpr -> TypingEnv -> Command Expr
inferTypesCmd (Command cmdName expr) ftenv = case cmdName of
    GetParse -> CmdResult (show expr)
    _ -> case translateExpr expr env of
      Left e -> CmdErr e
      Right expr' -> case cmdName of
        GetType  -> CmdResult $ case getType env expr' of
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
  ty <- getType env expr
  return (ty, expr)

translateExpr :: UExpr -> TypingEnv -> Except Expr
translateExpr rawExpr env = do
  let (expr, cs) = runConstrainMonad env (fresh >>= check rawExpr)
  (subst, Constraints [] [], flexVars) <- solvePartial cs
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
      Forall kinds t -> do
        vs <- mapM (const fresh) kinds
        addConstraint (reqTy, instantiateType vs s)
        return $ TApp (Var v) vs
      _ -> do
        addConstraint (reqTy, s)
        return $ Var v
  ULet _ bound body -> do
    (boundTy, bound', flexVars) <- inferPartial bound
    let boundTyGen = generalizeTy flexVars boundTy
        boundGen   = generalize   flexVars bound'
    body' <- local (setLEnv $ addBVar boundTyGen) (check body reqTy)
    return $ Let boundTyGen boundGen body'
  ULam _ body -> do
    (a, b) <- splitFun reqTy
    body' <- local (setLEnv $ addBVar a) (check body b)
    return $ Lam a body'
  UApp fexpr arg -> do
    (f, fexpr') <- infer fexpr
    (a, b) <- splitFun f
    arg' <- check arg a
    addConstraint (b, reqTy)
    return $ App fexpr' arg'
  UFor p body -> do
    (i, v) <- splitTab reqTy
    body' <- local (setLEnv $ addBVar i) (check body v)
    return $ For i body'
  UGet expr idxExpr -> do
    (tabTy, expr') <- infer expr
    (i, v) <- splitTab tabTy
    actualISet <- asks $ (! idxExpr) . lEnv
    addConstraint (i, actualISet)
    addConstraint (v, reqTy)
    return $ Get expr' idxExpr
  UUnpack _ bound body -> undefined --do
    -- (boundTy, bound', _) <- inferPartial bound
    -- let updateL = setLEnv $ addBVar (instantiateType [i] boundTy)
    --     updateS = setSEnv $ addBVar IdxSetKind
    -- (bodyTy, body', flexVars) <- local (updateL . updateS) (inferPartial body)
    -- i <- freshIdx
    -- -- debruijnify body with the index set variable name
    -- --   does this require having solved the constraints?
    -- --     yes, at least the constraints in the body
    -- return $ Unpack tBound' bound' body'

infer :: UExpr -> ConstrainMonad (Type, Expr)
infer expr = do ty <- fresh
                expr' <- check expr ty
                return (ty, expr')

inferPartial :: UExpr -> ConstrainMonad (Type, Expr, [MetaVar])
inferPartial expr = do
  ((ty, expr'), constraints) <- capture (infer expr)
  let (Right (sub, newConstraints, flexVars)) = solvePartial constraints
  tell newConstraints
  return (applySubTy sub ty, applySubExpr sub expr', flexVars)

-- partially solves enought to discover unconstrained variables
solvePartial :: Constraints -> Except (Subst, Constraints, [MetaVar])
solvePartial (Constraints constraints vs) = do
  sub <- foldM solve idSubst constraints
  let (freshSub, remSub) = splitMap  vs sub
      leakedVars = rhsVars remSub
      newConstraints = map asConstraint  (M.toList remSub)
      flexVars  = (vs `listDiff` leakedVars) `listDiff` M.keys freshSub
  return (freshSub, Constraints newConstraints leakedVars, flexVars)
  where
    rhsVars s = nub $ concat $ map (toListOf tyMetaVars) (M.elems s)
    asConstraint (mv, t) = (MetaTypeVar mv, t)

generalize :: [MetaVar] -> Expr -> Expr
generalize vs expr = TLam kinds body
  where kinds = [k | MetaVar k _ <- vs]
        body = subExprDepth 0 sub expr
        sub d v = case elemIndex v vs of
                    Just i  -> Just $ TypeVar (BV (d + i))
                    Nothing -> Nothing

generalizeTy :: [MetaVar] -> Type -> Type
generalizeTy vs expr = Forall kinds body
  where kinds = [k | MetaVar k _ <- vs]
        body = subTyDepth 0 sub expr
        sub d v = case elemIndex v vs of
                    Just i  -> Just $ TypeVar (BV (d + i))
                    Nothing -> Nothing

litType :: LitVal -> Type
litType v = BaseType $ case v of
  IntLit  _ -> IntType
  RealLit _ -> RealType
  StrLit  _ -> StrType

addConstraint :: Constraint -> ConstrainMonad ()
addConstraint x = tell (Constraints [x] [])

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

splitTab :: Type -> ConstrainMonad (IdxSet, Type)
splitTab t = case t of
  TabType i v -> return (i, v)
  _ -> do i <- freshIdx
          v <- fresh
          addConstraint (t, i ==> v)
          return (i, v)

instantiateType :: [Type] -> Type -> Type
instantiateType ts t = case t of
  Forall kinds body | nt == length kinds -> instantiateBody ts body
  Exists body       | nt == 1            -> instantiateBody ts body
  where nt = length ts

instantiateBody :: [Type] -> Type -> Type
instantiateBody env t = case t of
  BaseType _  -> t
  TypeVar (BV v) | v < n -> env !! v
                 | otherwise -> TypeVar (BV (v - n))
  ArrType a b -> ArrType (recur a) (recur b)
  TabType a b -> TabType (recur a) (recur b)
  MetaTypeVar _ -> t
  _ -> error $ "Can't instantiate " ++ show t
  where recur = instantiateBody env
        n = length env

inc :: ConstrainMonad Int
inc = do i <- get
         put $ i + 1
         return i

freshMeta :: Kind -> ConstrainMonad Type
freshMeta kind = do i <- inc
                    let v = MetaVar kind i
                    tell $ Constraints [] [v]
                    return $ MetaTypeVar v

fresh = freshMeta TyKind
freshIdx = freshMeta IdxSetKind

bind :: MetaVar -> Type -> Except Subst
bind v t | v `occursIn` t = Left InfiniteTypeErr
         | otherwise = Right $ M.singleton v t

occursIn :: MetaVar -> Type -> Bool
occursIn v t = v `elem` toListOf tyMetaVars t

unify :: Type -> Type -> Except Subst
unify t1 (TypeVar v) = Left $ UnificationErr t1 (TypeVar v)
unify (TypeVar v) t2 = Left $ UnificationErr t2 (TypeVar v)
unify t1 t2 | t1 == t2 = return idSubst
unify t (MetaTypeVar v) = bind v t
unify (MetaTypeVar v) t = bind v t
unify (ArrType a b) (ArrType a' b') = unifyPair (a,b) (a', b')
unify (TabType a b) (TabType a' b') = unifyPair (a,b) (a', b')
unify (Exists t) (Exists t') = unify t t'
unify t1 t2 = Left $ UnificationErr t1 t2

unifyPair :: (Type,Type) -> (Type,Type) -> Except Subst
unifyPair (a,b) (a',b') = do
  sa  <- unify a a'
  sb <- unify (applySubTy sa b) (applySubTy sa b')
  return $ sa >>> sb

-- invariant: lhs and rhs metavars of substitutions are distinct
(>>>) :: Subst -> Subst -> Subst
(>>>) s1 s2 = let s1' = M.map (applySubTy s2) s1
              in M.union s1' s2

solve :: Subst -> Constraint -> Except Subst
solve s (t1, t2) = do
  s' <- unify (applySubTy s t1) (applySubTy s t2)
  return $ s >>> s'

applySubTy :: Subst -> Type -> Type
applySubTy = subTy . subAsFun

applySubExpr :: Subst -> Expr -> Expr
applySubExpr = over exprTypes . applySubTy

subAsFun :: Ord k => M.Map k v -> k -> Maybe v
subAsFun = flip M.lookup

idSubst :: Subst
idSubst = M.empty

type CheckingEnv = FullEnv (SigmaType, Int) Kind

getType :: TypingEnv -> Expr -> Except Type
getType (FullEnv lEnv tEnv) = getType' $ FullEnv (addDepth lEnv) tEnv
  where addDepth = fmap $ \t -> (t, numBound tEnv)

getType' :: CheckingEnv -> Expr -> Except Type
getType' env expr = case expr of
    Lit c          -> return $ litType c
    Var v          -> return $ lookupLVar v
    Let t bound body -> do assertValid t
                           t' <- recur bound
                           assertEq t' t "Type mismatch in 'let'"
                           recurWith t body
    Lam a body     -> do assertValid a
                         b <- recurWith a body
                         return $ ArrType a b
    App fexpr arg  -> do ArrType a b <- recur fexpr
                         a' <- recur arg
                         assertEq a a' "Type mismatch in 'app'"
                         return b
    For a body     -> do assertValidIdxSet a
                         b <- recurWith a body
                         return $ TabType a b
    Get e ie       -> do TabType a b <- recur e
                         assertEq a (lookupLVar ie) "Type mismatch in 'get'"
                         return b
    TLam kinds expr -> do t <- recurWithT kinds expr
                          return $ Forall kinds t
    TApp expr ts   -> do t <- recur expr
                         return $ instantiateType ts t
    Unpack t bound body -> do
        Exists t' <- recur bound
        assertValid t
        assertEq t t' "Type mismatch in 'unpack'"
        let update = setLEnv (addBVar (t, depth)) . setTEnv (addBVar IdxSetKind)
        bodyTy <- getType' (update env) body
        let resultTy = instantiateType [dummyTy] (Exists bodyTy)
        assertValid resultTy
        return resultTy
  where
    recur = getType' env
    recurWith  t     = getType' $ setLEnv (addBVar (t, depth)) env
    recurWithT kinds = getType' $ setTEnv (addBVars kinds) env
    dummyTy = MetaTypeVar $ MetaVar IdxSetKind (-1)
    assertValid = checkKind (tEnv env) TyKind
    assertValidIdxSet = checkKind (tEnv env) IdxSetKind
    depth = numBound (tEnv env)
    lookupLVar v = let (t, d) = (lEnv env) ! v
                   in promoteBVs (depth - d) 0 t

getKind :: Env TVar Kind -> Type -> Except Kind
getKind env t = case t of
  BaseType _  -> return TyKind
  TypeVar v   -> return $ env ! v
  ArrType a b -> check TyKind     a >> check TyKind b >> return TyKind
  TabType a b -> check IdxSetKind a >> check TyKind b >> return TyKind
  MetaTypeVar _ -> Left $ CompilerErr "MetaVar in type"
  Forall kinds body -> getKind (addBVars kinds env) body
  where recur = getKind env
        check k = checkKind env k

promoteBVs :: Int -> Int -> Type -> Type
promoteBVs 0     depth t = t -- optimization
promoteBVs delta depth t = case t of
  BaseType _  -> t
  TypeVar (BV i) -> let i' = if i < depth then i
                                          else i + delta
                    in TypeVar (BV i')
  ArrType a b -> ArrType (recur a) (recur b)
  TabType a b -> TabType (recur a) (recur b)
  MetaTypeVar _ -> error "Can't have metavar"
  Forall kinds body  -> Forall kinds $ recurWith (length kinds) body
  Exists body        -> Exists       $ recurWith 1 body
  where recur = promoteBVs delta depth
        recurWith n = promoteBVs delta (depth + n)

checkKind :: Env TVar Kind -> Kind -> Type -> Except ()
checkKind env k t = do k' <- getKind env t
                       if k == k' then return ()
                                  else Left $ CompilerErr "Wrong kind"


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
    reduceType = Forall [TyKind, IdxSetKind] $ (a --> a --> a) --> a --> (j ==> a) --> a
    iotaType = int --> Exists (i ==> int)
    sumType = Forall [IdxSetKind] $ (i ==> int) --> int
    a = TypeVar (BV 0)
    b = TypeVar (BV 1)
    i = TypeVar (BV 0)
    j = TypeVar (BV 1)
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

genType :: Int -> Gen Type
genType 0 = genLeaf
genType n = frequency $
  [ (3, genLeaf)
  , (1, liftM2 ArrType subTree subTree)
  ]
            where
              subTree       = genType n'
              simpleSubTree = genSimpleType n'
              n' = n `div` 2

instance Semigroup Constraints where
  (Constraints c1 v1) <> (Constraints c2 v2) =
    Constraints (c1 ++ c2) (v1 ++ v2)

instance Monoid Constraints where
  mempty = Constraints [] []
  mappend = (<>)
