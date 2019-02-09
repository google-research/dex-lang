module Typer (translateExpr, inferTypesCmd, inferTypesExpr,
              litType, MetaVar, MType, MExpr) where

import Control.Monad
import Control.Monad.Identity
import Control.Monad.Reader (ReaderT, runReaderT, local, ask, asks)
import Control.Monad.Writer hiding ((<>))
import Control.Monad.State (StateT, evalStateT, put, get)
import Control.Monad.Except (throwError)
import Test.QuickCheck hiding ((==>))
import qualified Data.Map.Strict as M
import Data.List (nub, elemIndex, (\\))
import Data.Foldable (toList)
import Data.Semigroup
import qualified Data.Set as Set

import Syntax
import Env
import Record
import Util

type TypingEnv = FullEnv MType MetaVar
type Subst = M.Map MetaVar MType
type SupplyT = StateT Int
type ConstrainMonad a = ReaderT TypingEnv (
                          WriterT Constraints (
                            SupplyT (Either Err))) a

type Constraint = (MType, MType)
data Constraints = Constraints [Constraint] [MetaVar]  deriving (Show)
data MetaVar = MetaVar Kind Int  deriving (Eq, Show, Ord)

type MType   = GenType   MetaVar
type MExpr   = GenExpr   MetaVar
type MIdxSet = GenIdxSet MetaVar

inferTypesCmd :: Command UExpr -> TypingEnv -> Command Expr
inferTypesCmd (Command cmdName expr) ftenv = case cmdName of
    GetParse -> CmdResult (show expr)
    _ -> case translateExpr expr env of
      Left e -> CmdErr e
      Right expr' -> case cmdName of
        GetType -> case getAndCheckType' env expr' of
                     Left e -> CmdErr e
                     Right t ->  CmdResult $ show t
        GetTyped -> CmdResult $ show expr'
        _ -> Command cmdName expr'
  where env = addBuiltins ftenv

inferTypesCmd (CmdResult s) _ = CmdResult s
inferTypesCmd (CmdErr e)    _ = CmdErr e

inferTypesExpr :: UExpr -> TypingEnv -> Except (MType, Expr)
inferTypesExpr rawExpr fenv = do
  let env = addBuiltins fenv
  expr <- translateExpr rawExpr env
  ty <- getAndCheckType' env expr
  return (noLeaves ty, expr)

translateExpr :: UExpr -> TypingEnv -> Except Expr
translateExpr rawExpr env = do
  (expr, cs) <- runConstrainMonad env (fresh >>= check rawExpr)
  (subst, Constraints [] [], flexVars) <- solvePartial cs
  checkNoLeaves $ generalize flexVars $ applySubExpr subst expr

runConstrainMonad :: TypingEnv -> ConstrainMonad a -> Except (a, Constraints)
runConstrainMonad env m = evalStateT (runWriterT (runReaderT m env)) 0

capture :: MonadWriter w m => m a -> m (a, w)
capture m = censor (const mempty) (listen m)

check :: UExpr -> MType -> ConstrainMonad MExpr
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
  UUnpack _ bound body -> do
    (boundTy, bound', _) <- inferPartial bound
    Meta i <- freshIdx -- skolem var here would give better error messages
    let updateEnv = setLEnv $ addBVar (instantiateType [Meta i] boundTy)
    (body', Constraints cs vs) <- capture $ local updateEnv (check body reqTy)
    (sub, newConstraints, flexVars) <- liftExcept $ solvePartial $
                                         Constraints cs (i:vs)
    i' <- case M.lookup i sub of
             Nothing -> return i
             Just (Meta v) -> return v
             t -> throwError $ CompilerErr
                    ("Index variable unified with " ++ show t)
    if i' `elem` flexVars
      then return ()
      else throwError $ TypeErr "existential variable leaked scope"
    tell newConstraints
    tell $ Constraints [] (flexVars \\ [i'])
    let body'' = bindMetaExpr [i'] (applySubExpr sub body')
    return $ Unpack bound' body''

infer :: UExpr -> ConstrainMonad (MType, MExpr)
infer expr = do ty <- fresh
                expr' <- check expr ty
                return (ty, expr')

inferPartial :: UExpr -> ConstrainMonad (MType, MExpr, [MetaVar])
inferPartial expr = do
  ((ty, expr'), constraints) <- capture (infer expr)
  (sub, newConstraints, flexVars) <- liftExcept $ solvePartial constraints
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
    rhsVars s = nub $ concat $ map toList (M.elems s)
    asConstraint (mv, t) = (Meta mv, t)

generalize :: [MetaVar] -> MExpr -> MExpr
generalize vs expr = TLam (map mvKind vs) (bindMetaExpr vs expr)

generalizeTy :: [MetaVar] -> MType -> MType
generalizeTy vs ty = Forall (map mvKind vs) (bindMetaTy vs ty)

mvKind :: MetaVar -> Kind
mvKind (MetaVar k _) = k

litType :: LitVal -> MType
litType v = BaseType $ case v of
  IntLit  _ -> IntType
  RealLit _ -> RealType
  StrLit  _ -> StrType

addConstraint :: Constraint -> ConstrainMonad ()
addConstraint x = tell (Constraints [x] [])

splitFun :: MType -> ConstrainMonad Constraint
splitFun f = case f of
  ArrType a b -> return (a, b)
  _ -> do a <- fresh
          b <- fresh
          addConstraint (f, a --> b)
          return (a, b)

splitTab :: MType -> ConstrainMonad (MIdxSet, MType)
splitTab t = case t of
  TabType i v -> return (i, v)
  _ -> do i <- freshIdx
          v <- fresh
          addConstraint (t, i ==> v)
          return (i, v)

instantiateType :: [MType] -> MType -> MType
instantiateType ts t = case t of
  Forall kinds body | nt == length kinds -> instantiateBody ts' body
  Exists       body | nt == 1            -> instantiateBody ts' body
  where nt = length ts
        ts' = map Just ts

instantiateBody :: [Maybe MType] -> MType -> MType
instantiateBody env t = case t of
  BaseType _  -> t
  TypeVar (BV v) -> case env !! v of
                      Just t' -> t'
                      Nothing -> TypeVar (BV v)
  ArrType a b -> ArrType (recur a) (recur b)
  TabType a b -> TabType (recur a) (recur b)
  Forall kinds body -> let env' = map (const Nothing) kinds ++ env
                       in Forall kinds $ instantiateBody env' body
  Meta _ -> t
  where recur = instantiateBody env

inc :: ConstrainMonad Int
inc = do i <- get
         put $ i + 1
         return i

freshMeta :: Kind -> ConstrainMonad MType
freshMeta kind = do i <- inc
                    let v = MetaVar kind i
                    tell $ Constraints [] [v]
                    return $ Meta v

fresh = freshMeta TyKind
freshIdx = freshMeta IdxSetKind

bind :: MetaVar -> MType -> Except Subst
bind v t | v `occursIn` t = Left InfiniteTypeErr
         | otherwise = Right $ M.singleton v t

occursIn :: MetaVar -> MType -> Bool
occursIn v t = v `elem` toList t

unify :: MType -> MType -> Except Subst
unify t1 (TypeVar v) = unifyErr t1 (TypeVar v)
unify (TypeVar v) t2 = unifyErr t2 (TypeVar v)
unify t1 t2 | t1 == t2 = return idSubst
unify t (Meta v) = bind v t
unify (Meta v) t = bind v t
unify (ArrType a b) (ArrType a' b') = unifyPair (a,b) (a', b')
unify (TabType a b) (TabType a' b') = unifyPair (a,b) (a', b')
unify (Exists t) (Exists t') = unify t t'
unify t1 t2 = unifyErr t1 t2

unifyErr :: MType -> MType -> Except a
unifyErr t1 t2 = Left $ UnificationErr (show t1) (show t2)

unifyPair :: (MType,MType) -> (MType,MType) -> Except Subst
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

applySubTy :: Subst -> MType -> MType
applySubTy = subTy . subAsFun

applySubExpr :: Subst -> MExpr -> MExpr
applySubExpr = subExpr . subAsFun

subAsFun :: Subst -> MetaVar -> MType
subAsFun m v = case M.lookup v m of Just t -> t
                                    Nothing -> Meta v

idSubst :: Subst
idSubst = M.empty

type CheckM a = ReaderT TypingEnv (StateT Int (Either Err)) a

getAndCheckType' :: TypingEnv -> Expr -> Except Type
getAndCheckType' env expr =
  evalStateT (runReaderT (getAndCheckType expr) env) 0 >>= checkNoLeaves

getAndCheckType ::  Expr -> CheckM MType
getAndCheckType expr = case expr of
    Lit c          -> return $ litType c
    Var v          -> lookupLVar v
    Let t bound body -> do t' <- checkTy TyKind t
                           t'' <- recur bound
                           assertEq' t'' t' "Type mismatch in 'let'"
                           recurWith t' body
    Lam a body     -> do a' <- checkTy TyKind a
                         b <- recurWith a' body
                         return $ ArrType a' b
    App fexpr arg  -> do ArrType a b <- recur fexpr
                         a' <- recur arg
                         assertEq' a a' "Type mismatch in 'app'"
                         return b
    For a body     -> do a' <- checkTy IdxSetKind a
                         b <- recurWith a' body -- TODO check and convert a
                         return $ TabType a' b
    Get e ie       -> do TabType a b <- recur e
                         ieTy <- lookupLVar ie
                         assertEq' a ieTy "Type mismatch in 'get'"
                         return b
    TLam kinds body -> do mvs <- mapM freshMeta kinds
                          t <- recurWithT mvs body
                          return $ Forall kinds $ bindMetaTy mvs t
    TApp fexpr ts   -> do Forall kinds body <- recur fexpr
                          ts' <- zipWithM checkTy kinds ts
                          return $ instantiateBody (map Just ts') body
    Unpack bound body -> do
        Exists t' <- recur bound
        mv <- freshMeta IdxSetKind
        let t'' = instantiateBody [Just (Meta mv)] t'
        let update = setLEnv (addBVar t'') . setTEnv (addBVar mv)
        local update (recur body)

  where
    recur = getAndCheckType
    recurWith  t   = local (setLEnv (addBVar  t  )) . recur
    recurWithT mvs = local (setTEnv (addBVars mvs)) . recur

    freshMeta :: Kind -> CheckM MetaVar
    freshMeta kind = do i <- get
                        put $ i + 1
                        return $ MetaVar kind i
    fresh    = freshMeta TyKind
    freshIdx = freshMeta IdxSetKind

    lookupLVar :: Var -> CheckM MType
    lookupLVar v = asks ((! v) . lEnv)

    assertEq' :: MType -> MType -> String -> CheckM ()
    assertEq' t1 t2 s = liftExcept $ assertEq t1 t2 s

checkTy :: Kind -> Type -> CheckM MType
checkTy kind t = do
  mvs <- asks (bVars . tEnv)
  mt <- liftExcept $ checkNoLeaves t
  let t' = instantiateBody (map (Just . Meta) mvs) (noLeaves t)
  liftExcept $ checkKind mempty kind t'
  return t'

getKind :: Env TVar Kind -> MType -> Except Kind
getKind env t = case t of
  Meta (MetaVar k _) -> Right k
  BaseType _  -> return TyKind
  TypeVar v   -> return $ env ! v
  ArrType a b -> check TyKind     a >> check TyKind b >> return TyKind
  TabType a b -> check IdxSetKind a >> check TyKind b >> return TyKind
  Forall kinds body -> getKind (addBVars kinds        env) body
  Exists       body -> getKind (addBVars [IdxSetKind] env) body
  where recur = getKind env
        check k = checkKind env k

checkKind :: Env TVar Kind -> Kind -> MType -> Except ()
checkKind env k t = do
  k' <- getKind env t
  if k == k' then return ()
             else Left $ CompilerErr $ "Wrong kind. Expected "
                                        ++ show k ++ " got " ++ show k'
addBuiltins :: TypingEnv -> TypingEnv
addBuiltins = setLEnv (<> fmap noLeaves builtinEnv)

builtinEnv :: Env Var Type
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
    reduceType = Forall [TyKind, IdxSetKind] $
                   (a --> a --> a) --> a --> (j ==> a) --> a
    iotaType = int --> Exists (i ==> int)
    sumType = Forall [IdxSetKind] $ (i ==> int) --> int
    a = TypeVar (BV 0)
    b = TypeVar (BV 1)
    i = TypeVar (BV 0)
    j = TypeVar (BV 1)
    int = BaseType IntType
    real = BaseType RealType

instance Semigroup Constraints where
  (Constraints c1 v1) <> (Constraints c2 v2) =
    Constraints (c1 ++ c2) (v1 ++ v2)

instance Monoid Constraints where
  mempty = Constraints [] []
  mappend = (<>)
