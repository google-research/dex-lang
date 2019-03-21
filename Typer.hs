module Typer (typePass, translateExpr, inferTypesCmd, inferTypesExpr,
              litType, MetaVar, MType, MExpr, getType, builtinType,
              checkSysF) where

import Control.Monad
import Control.Monad.Identity
import Control.Monad.Reader (ReaderT, runReaderT,
                             local, ask, asks)
import Control.Monad.Writer hiding ((<>))
import Control.Monad.State (StateT, evalStateT, execStateT, put, get, modify)
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

type GenEnv a = FullEnv (GenType a) a
type TypingEnv = FullEnv MType ()
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



typePass :: Pass UExpr Expr Type ()
typePass = Pass
  { lowerExpr   = \expr env   -> liftErrIO $ inferTypesExpr expr env
  , lowerUnpack = \v expr env -> liftErrIO $ inferTypesUnpack v expr env
  , lowerCmd    = \cmd  env   -> return $ inferTypesCmd cmd env }

checkSysF :: FullEnv Type () -> Expr -> Except Type
checkSysF env expr = getAndCheckType (asTypingEnv env) expr

inferTypesCmd :: Command UExpr -> FullEnv Type () -> Command Expr
inferTypesCmd (Command cmdName expr) ftenv = case cmdName of
    GetParse -> CmdResult $ TextOut (show expr)
    _ -> case translateExpr expr env of
      Left e -> CmdErr e
      Right expr' -> case cmdName of
        GetType -> case getAndCheckType env expr' of
                     Left e -> CmdErr e
                     Right t -> CmdResult $ TextOut  $ show t
        GetTyped -> CmdResult $ TextOut  $ show expr'
        Plot -> case getType ftenv expr' of
                  TabType _ (BaseType IntType) -> Command Plot expr'
                  ty -> CmdErr $ TypeErr $
                      "Plot data must have form i=>Int. Got: " ++ show ty
        PlotMat ->
          case getType ftenv expr' of
                 TabType _ (TabType _ (BaseType IntType)) -> Command PlotMat expr'
                 ty -> CmdErr $ TypeErr $
                        "Plotmat data must have form i=>j=>Int. Got: " ++ show ty
        _ -> Command cmdName expr'
  where env = asTypingEnv ftenv

inferTypesCmd (CmdResult s) _ = CmdResult s
inferTypesCmd (CmdErr e)    _ = CmdErr e

inferTypesExpr :: UExpr -> FullEnv Type () -> Except (Type, Expr)
inferTypesExpr rawExpr fenv = do
  let env = asTypingEnv fenv
  expr <- translateExpr rawExpr env
  ty <- getAndCheckType env expr
  return (noLeaves ty, expr)

inferTypesUnpack :: VarName -> UExpr -> FullEnv Type () -> Except (Type, (), Expr)
inferTypesUnpack v expr env = do
  (ty, expr') <- inferTypesExpr expr env
  ty' <- case ty of
    Exists body -> return $ instantiateBody [Just (TypeVar (FV v))] body
    _ -> throwError $ TypeErr $ "Can't unpack type: " ++ show ty
  return (ty', (), expr')

asTypingEnv :: FullEnv Type () -> TypingEnv
asTypingEnv env = FullEnv (fmap noLeaves $ lEnv env) (tEnv env)

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
  UVar v -> do ty <- asks $ (! v) . lEnv
               instantiate ty reqTy (Var v)
  UBuiltin b -> instantiate (builtinType b) reqTy (Builtin b)
  ULet (RecLeaf _) bound body -> do
    (boundTy, bound', flexVars) <- inferPartial bound
    let boundTyGen = generalizeTy flexVars boundTy
        boundGen   = generalize   flexVars bound'
    body' <- local (setLEnv $ addBVar boundTyGen) (check body reqTy)
    return $ Let (RecLeaf boundTyGen) boundGen body'
  ULet p bound body -> do
    (a, bound') <- infer bound
    a' <- recTy p a
    body' <- local (setLEnv $ addBVars (toList a')) (check body reqTy)
    return $ Let a'  bound' body'
  ULam p body -> do
    (a, b) <- splitFun reqTy
    a' <- recTy p a
    body' <- local (setLEnv $ addBVars (toList a')) (check body b)
    return $ Lam a' body'
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
  URecCon r -> do tyExpr <- traverse infer r
                  addConstraint (reqTy, RecType (fmap fst tyExpr))
                  return $ RecCon (fmap snd tyExpr)
  UGet expr idxExpr -> do
    (tabTy, expr') <- infer expr
    (i, v) <- splitTab tabTy
    actualISet <- asks $ (! idxExpr) . lEnv
    addConstraint (i, actualISet)
    addConstraint (v, reqTy)
    return $ Get expr' idxExpr
  UUnpack _ bound body -> do
    (Exists boundTy, bound', _) <- inferPartial bound
    Meta i <- hiddenFreshIdx -- skolem var here would give better error messages
    let updateEnv = setLEnv $ addBVar (instantiateType [Meta i] (Exists boundTy))
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
        boundTy' = applySubTy sub boundTy
    return $ Unpack boundTy' bound' body''

recTy :: UPat -> MType -> ConstrainMonad (RecTree MType)
recTy pat ty = do tree <- traverse (const fresh) pat
                  addConstraint (recTreeAsType tree, ty)
                  return tree

recTreeAsType :: RecTree (GenType a) -> GenType a
recTreeAsType (RecTree r) = RecType (fmap recTreeAsType r)
recTreeAsType (RecLeaf t) = t


instantiate :: MType -> MType -> MExpr -> ConstrainMonad MExpr
instantiate ty reqTy expr =
  case ty of
    Forall kinds t -> do
      vs <- mapM freshMeta kinds
      addConstraint (reqTy, instantiateType vs ty)
      return $ TApp expr vs
    _ -> do
      addConstraint (reqTy, ty)
      return $ expr

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
  sub <- solve constraints
  let (freshSub, remSub) = splitMap  vs sub
      leakedVars = rhsVars remSub
      newConstraints = map asConstraint  (M.toList remSub)
      flexVars  = (vs `listDiff` leakedVars) `listDiff` M.keys freshSub
  return (freshSub, Constraints newConstraints leakedVars, flexVars)
  where
    rhsVars s = nub $ concat $ map toList (M.elems s)
    asConstraint (mv, t) = (Meta mv, t)

generalize :: [MetaVar] -> MExpr -> MExpr
generalize [] expr = expr
generalize vs expr = TLam (map mvKind vs) (bindMetaExpr vs expr)

generalizeTy :: [MetaVar] -> MType -> MType
generalizeTy [] ty = ty
generalizeTy vs ty = Forall (map mvKind vs) (bindMetaTy vs ty)

mvKind :: MetaVar -> Kind
mvKind (MetaVar k _) = k

litType :: LitVal -> GenType a
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

hiddenFreshIdx :: ConstrainMonad MType
hiddenFreshIdx = do i <- inc
                    let v = MetaVar IdxSetKind i
                    return $ Meta v

-- TODO: unification scheme is at least quadratic. Replace with some 'zonking'

-- invariant: lhs and rhs metavars of substitution is distinct
bind :: MetaVar -> MType -> UnifyM ()
bind v t | v `occursIn` t = throwError InfiniteTypeErr
         | otherwise = modify $ M.insert v t . M.map (subTy update)
  where update v' = if v == v' then t else Meta v'

occursIn :: MetaVar -> MType -> Bool
occursIn v t = v `elem` toList t

type UnifyM a = StateT Subst (Either Err) a

-- TODO: check kinds
unify :: MType -> MType -> UnifyM ()
unify t1 t2 = do sub <- get
                 unify' (applySubTy sub t1) (applySubTy sub t2)

unify' :: MType -> MType -> UnifyM ()
unify' t1 t2@(TypeVar (BV v)) = unifyErr t1 t2
unify' t1@(TypeVar (BV v)) t2 = unifyErr t2 t1
unify' t1 t2 | t1 == t2 = return ()
unify' t (Meta v) = bind v t
unify' (Meta v) t = bind v t
unify' (ArrType a b) (ArrType a' b') = unify a a' >> unify b b'
unify' (TabType a b) (TabType a' b') = unify a a' >> unify b b'
unify' (Exists t) (Exists t') = unify t t'
unify' (RecType r) (RecType r') = unifyRec r r'
unify' t1 t2 = unifyErr t1 t2

unifyRec :: Record MType -> Record MType -> UnifyM ()
unifyRec r r' = case zipWithRecord unify r r' of
                  Nothing -> unifyErr (RecType r) (RecType r')
                  Just unifiers -> sequence unifiers >> return ()

unifyErr :: MType -> MType -> UnifyM a
unifyErr t1 t2 = throwError $ UnificationErr (show t1) (show t2)

solve :: [Constraint] -> Except Subst
solve constraints = execStateT (mapM (uncurry unify) constraints) M.empty

applySubTy :: Subst -> MType -> MType
applySubTy = subTy . subAsFun

applySubExpr :: Subst -> MExpr -> MExpr
applySubExpr = subExpr . subAsFun

subAsFun :: Subst -> MetaVar -> MType
subAsFun m v = case M.lookup v m of Just t -> t
                                    Nothing -> Meta v

type CheckM a = ReaderT (FullEnv MType MetaVar) (StateT Int (Either Err)) a

getAndCheckType :: TypingEnv -> Expr -> Except Type
getAndCheckType env expr = do
  ty <- evalStateT (runReaderT (getAndCheckType' expr) env') 0 >>= checkNoLeaves
  ty' <- return (getType env' expr) >>= checkNoLeaves
  assertEq ty ty' "non-checking type getter failed"
  return ty
  where env' = FullEnv (lEnv env) mempty

getAndCheckType' ::  Expr -> CheckM MType
getAndCheckType' expr = case expr of
    Lit c          -> return $ litType c
    Var v          -> lookupLVar v
    Builtin b      -> return (builtinType b)
    Let t bound body -> do t' <- traverse (checkTy TyKind) t
                           t'' <- recur bound
                           assertEq' t'' (recTreeAsType t') "Type mismatch in 'let'"
                           recurWithMany (toList t') body
    Lam a body     -> do a' <- traverse (checkTy TyKind) a
                         b <- recurWithMany (toList a') body
                         return $ ArrType (recTreeAsType a') b
    App fexpr arg  -> do ArrType a b <- recur fexpr
                         a' <- recur arg
                         assertEq' a a' "Type mismatch in 'app'"
                         return b
    For a body     -> do a' <- checkTy IdxSetKind a
                         b <- recurWith a' body -- TODO check and convert a
                         return $ TabType a' b
    RecCon r       -> liftM RecType (traverse recur r)
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
    Unpack tyReq bound body -> do
        Exists t' <- recur bound
        tyReq' <- checkTy TyKind (Exists tyReq)
        assertEq' (Exists t') tyReq' "Type mismatch in 'unpack'"
        mv <- freshMeta IdxSetKind
        let t'' = instantiateBody [Just (Meta mv)] t'
        let update = setLEnv (addBVar t'') . setTEnv (addBVar mv)
        local update (recur body)

  where
    recur = getAndCheckType'
    recurWith  t     = local (setLEnv (addBVar  t  )) . recur
    recurWithMany ts = local (setLEnv (addBVars ts )) . recur
    recurWithT mvs   = local (setTEnv (addBVars mvs)) . recur

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
  liftExcept $ checkKind mempty kind t'  -- TODO: add 'IdxSetKind' for freevars
  return t'

getKind :: Env TVar Kind -> MType -> Except Kind
getKind env t = case t of
  Meta (MetaVar k _) -> Right k
  BaseType _  -> return TyKind
  TypeVar v -> return $ case v of BV _ -> env ! v
                                  FV _ -> IdxSetKind
  ArrType a b -> check TyKind     a >> check TyKind b >> return TyKind
  TabType a b -> check IdxSetKind a >> check TyKind b >> return TyKind
  RecType r   -> return TyKind -- TODO actually check this
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
data MetaOrUniq a = MetaV a | UniqV Int
type GetTypeM a b = ReaderT (GenEnv a) (SupplyT Identity) b

instance Eq (MetaOrUniq a) where
  (==) (UniqV x) (UniqV y) | y == x = True
  (==) _ _ = False

mapGenEnv :: (a -> b) -> GenEnv a -> GenEnv b
mapGenEnv f (FullEnv lenv tenv) = FullEnv (fmap (fmap f) lenv) (fmap f tenv)

getType :: GenEnv a -> Expr -> GenType a
getType env expr = fmap noUniq $
  runIdentity $ evalStateT (runReaderT (getType' expr) (mapGenEnv MetaV env)) 0
  where noUniq :: MetaOrUniq a -> a
        noUniq x = case x of MetaV v -> v

getType' :: Expr -> GetTypeM (MetaOrUniq a) (GenType (MetaOrUniq a))
getType' expr = case expr of
    Lit c        -> return $ litType c
    Var v        -> lookupLVar v
    Builtin b    -> return $ builtinType b
    Let p _ body -> do p' <- traverse asMeta p
                       recurWithMany (toList p') body
    Lam p body -> do p' <- traverse asMeta p
                     let a' = recTreeAsType p'
                     liftM (ArrType a') (recurWithMany (toList p') body)
    For a body -> do { a' <- asMeta a; liftM (TabType a') (recurWith a' body) }
    App e arg  -> do { ArrType a b <- recur e; return b }
    Get e ie   -> do { TabType a b <- recur e; return b }
    RecCon r   -> liftM RecType $ traverse recur r
    TLam kinds body -> do uniqVars <- mapM (const fresh) kinds
                          t <- recurWithT uniqVars body
                          return $ Forall kinds $ bindMetaTy uniqVars t
    TApp fexpr ts   -> do Forall _ body <- recur fexpr
                          ts' <- mapM asMeta ts
                          return $ instantiateBody (map Just ts') body
    Unpack t bound body -> do
        uniq <- fresh
        let updateT = setTEnv (addBVar uniq)
        t' <- local updateT (asMeta t)
        let updateL = setLEnv (addBVar t')
        local (updateL . updateT) (recur body)

  where
    recur = getType'
    recurWith     t  = local (setLEnv (addBVar  t  )) . recur
    recurWithMany ts = local (setLEnv (addBVars ts )) . recur
    recurWithT   mvs = local (setTEnv (addBVars mvs)) . recur

    lookupLVar :: Var -> GetTypeM a (GenType a)
    lookupLVar v = asks ((! v) . lEnv)

    fresh :: GetTypeM (MetaOrUniq a) (MetaOrUniq a)
    fresh = do { i <- get; put (i + 1); return (UniqV i) }

    asMeta :: Type -> GetTypeM a (GenType a)
    asMeta t = do
      mvs <- asks $ fmap (Just . Meta) . tEnv
      return $ instantiateBodyFVs mvs (noLeaves t)

builtinType :: Builtin -> GenType a
builtinType builtin = case builtin of
  Add      -> binOpType
  Sub      -> binOpType
  Mul      -> binOpType
  Pow      -> binOpType
  Exp      -> realUnOpType
  Log      -> realUnOpType
  Sqrt     -> realUnOpType
  Sin      -> realUnOpType
  Cos      -> realUnOpType
  Tan      -> realUnOpType
  Fold     -> foldType
  Iota     -> iotaType
  Doubleit -> int --> int
  Hash     -> int --> int --> int
  Rand     -> int --> real
  Randint  -> int --> int --> int
  where
    binOpType    = int --> int --> int
    realUnOpType = real --> real
    foldType = Forall [TyKind, TyKind, IdxSetKind] $
                   (a --> a --> b) --> b --> (k ==> a) --> b
    iotaType = int --> Exists (i ==> int)
    a = TypeVar (BV 0)
    b = TypeVar (BV 1)
    i = TypeVar (BV 0)
    j = TypeVar (BV 1)
    k = TypeVar (BV 2)
    int = BaseType IntType
    real = BaseType RealType

instance Semigroup Constraints where
  (Constraints c1 v1) <> (Constraints c2 v2) =
    Constraints (c1 ++ c2) (v1 ++ v2)

instance Monoid Constraints where
  mempty = Constraints [] []
  mappend = (<>)
