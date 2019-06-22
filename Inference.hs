module Inference (typePass, inferKinds) where

import Control.Monad
import Control.Monad.Reader
import Control.Monad.Except (liftEither)
import Control.Monad.Writer
import Control.Monad.State
import Data.List (nub, (\\))
import Data.Foldable (toList)
import Data.Maybe (fromJust)
import qualified Data.Map.Strict as M

import Syntax hiding (Subst)
import Env
import Record
import Type
import PPrint
import Fresh
import Pass
import Util (onSnd)
import Cat

type Subst   = Env Type
type TempEnv = Env Kind
data InferState = InferState { tempEnv :: TempEnv
                             , subst :: Subst }

type InferM a = Pass TypeEnv InferState a
type UAnnot = Maybe Type

typePass :: TopDeclP UAnnot -> TopPass TypeEnv TopDecl
typePass tdecl = case tdecl of
  TopDecl (Let b expr) -> do
    (b', expr') <- liftTop $ inferLetBinding b expr
    putEnv $ lbind b'
    return $ TopDecl (Let b' expr')
  TopDecl (Unpack b tv expr) -> do
    (ty, expr') <- liftTop (infer expr)
    ty' <- liftEither $ unpackExists ty tv
    let b' = fmap (const ty') b -- TODO: actually check the annotated type
    putEnv $ lbind b' <> tv @> T idxSetKind
    return $ TopDecl (Unpack b' tv expr')
  EvalCmd NoOp -> return (EvalCmd NoOp)
  EvalCmd (Command cmd expr) -> do
    (ty, expr') <- liftTop $ infer expr >>= uncurry generalize
    case cmd of
      GetType -> do writeOut (pprint ty)
                    return $ EvalCmd NoOp
      Passes  -> do writeOut ("\nSystem F\n" ++ pprint expr')
                    return $ EvalCmd (Command cmd expr')
      _ -> return $ EvalCmd (Command cmd expr')

liftTop :: HasTypeVars a => InferM a -> TopPass TypeEnv a
liftTop m  = liftTopPass (InferState mempty mempty) mempty (m >>= zonk)

infer :: ExprP UAnnot -> InferM (Type, Expr)
infer expr = do ty <- freshVar TyKind
                expr' <- check expr ty
                return (ty, expr')

check :: ExprP UAnnot -> Type -> InferM Expr
check expr reqTy = case expr of
  Lit c -> do
    unify (BaseType (litType c)) reqTy
    return (Lit c)
  Var v -> do
    maybeTy <- asks $ (flip envLookup v)
    ty <- case maybeTy of Nothing -> throw UnboundVarErr (pprint v)
                          Just (L ty) -> return ty
    instantiate ty reqTy (Var v)
  PrimOp b [] args -> do
    let BuiltinType kinds argTys ansTy = builtinType b
    vs <- mapM freshVar kinds
    unify reqTy (instantiateTVs vs ansTy)
    let argTys' = map (instantiateTVs vs) argTys
    args' <- zipWithM check args argTys'
    return $ PrimOp b vs args'
  Decls decls body -> foldr checkDecl (check body reqTy) decls
  Lam b body -> do
    (a, bTy) <- splitFun reqTy
    b' <- checkBinder b a
    body' <- recurWith b' body bTy
    return $ Lam b' body'
  App fexpr arg -> do
    (f, fexpr') <- infer fexpr
    (a, b) <- splitFun f
    arg' <- check arg a
    unify b reqTy
    return $ App fexpr' arg'
  For b body -> do
    (i, elemTy) <- splitTab reqTy
    b' <- inferBinder b
    unify (binderAnn b') i
    body' <- recurWith b' body elemTy
    return $ For b' body'
  Get tabExpr idxExpr -> do
    (tabTy, expr') <- infer tabExpr
    (i, v) <- splitTab tabTy
    actualISet <- asks $ fromL . (!idxExpr)
    unify i actualISet
    unify v reqTy
    return $ Get expr' idxExpr
  RecCon r -> do
    tyExpr <- traverse infer r
    unify reqTy (RecType (fmap fst tyExpr))
    return $ RecCon (fmap snd tyExpr)
  RecGet e field -> do
    (ty, e') <- infer e
    r <- splitRec (otherFields field) ty
    unify reqTy (recGet r field) -- TODO: throw graceful error on bad field
    return $ RecGet e' field
  TabCon _ _ xs -> do
    (n, elemTy) <- splitTab reqTy
    xs' <- mapM (flip check elemTy) xs
    let n' = length xs
    unify n (IdxSetLit n')
    return $ TabCon n' elemTy xs'
  Annot e annTy -> do
    -- TODO: check that the annotation is a monotype
    unify annTy reqTy
    check e reqTy
  where
    checkDecl :: DeclP UAnnot -> InferM Expr -> InferM Expr
    checkDecl decl cont = case decl of
      Let b bound -> do
        (b', bound') <- inferLetBinding b bound
        extendR (lbind b') $ do
          body' <- cont
          return $ wrapDecls [Let b' bound'] body'
      Unpack b tv bound -> do
        (maybeEx, bound') <- infer bound >>= zonk
        boundTy <- case maybeEx of Exists t -> return $ instantiateTVs [TypeVar tv] t
                                   _ -> throw TypeErr (pprint maybeEx)
        let b' = replaceAnnot b boundTy
        body' <- extendR (lbind b' <> tv @> T idxSetKind) cont
        tvsEnv <- tempVarsEnv
        tvsReqTy <- tempVars reqTy
        if (tv `elem` tvsEnv) || (tv `elem` tvsReqTy)  then leakErr else return ()
        return $ wrapDecls [Unpack b' tv bound'] body'

    leakErr = throw TypeErr "existential variable leaked"
    recurWith b expr ty = extendR (lbind b) (check expr ty)

checkBinder :: BinderP UAnnot -> Type -> InferM Binder
checkBinder b ty = do
  b' <- inferBinder b
  unify ty (binderAnn b')
  return b'

inferBinder :: BinderP UAnnot -> InferM Binder
inferBinder b = liftM (replaceAnnot b) $ case binderAnn b of
                                           Nothing -> freshTy
                                           Just ty -> return ty

inferLetBinding :: BinderP UAnnot -> ExprP UAnnot -> InferM (Binder, Expr)
inferLetBinding b expr = case binderAnn b of
  Nothing -> do
    (ty', expr') <- infer expr
    (forallTy, tLam) <- generalize ty' expr'
    return (replaceAnnot b forallTy, tLam)
  Just sigmaTy@(Forall kinds tyBody) -> do
    skolVars <- mapM (fresh . pprint) kinds
    let skolBinders = zipWith (:>) skolVars kinds
    let exprTy = instantiateTVs (map TypeVar skolVars) tyBody
    expr' <- extendR (foldMap tbind skolBinders) (check expr exprTy)
    return (replaceAnnot b sigmaTy, TLam skolBinders expr')
  Just ty -> do
    expr' <- check expr ty
    return (fmap fromJust b, expr')

splitFun :: Type -> InferM (Type, Type)
splitFun f = case f of
  ArrType a b -> return (a, b)
  _ -> do a <- freshTy
          b <- freshTy
          unify f (a --> b)
          return (a, b)

splitTab :: Type -> InferM (IdxSet, Type)
splitTab t = case t of
  TabType i v -> return (i, v)
  _ -> do i <- freshIdx
          v <- freshTy
          unify t (i ==> v)
          return (i, v)

splitRec :: Record () -> Type -> InferM (Record Type)
splitRec r ty = case ty of
  RecType r' -> return r'  -- TODO: check it matches r
  _ -> do r' <- traverse (const freshTy) r
          unify ty (RecType r')
          return r'

freshVar :: Kind -> InferM Type
freshVar kind = do v <- fresh $ pprint kind
                   modify $ setTempEnv (<> v @> kind)
                   return (TypeVar v)

freshTy  = freshVar TyKind
freshIdx = freshVar idxSetKind

generalize :: Type -> Expr -> InferM (Type, Expr)
generalize ty expr = do
  ty'   <- zonk ty
  expr' <- zonk expr
  flexVars <- getFlexVars ty' expr'
  case flexVars of
    [] -> return (ty', expr')
    _  -> do kinds <- mapM getKind flexVars
             return (Forall kinds $ abstractTVs flexVars ty',
                     TLam (zipWith (:>) flexVars kinds) expr')
  where
    getKind :: Var -> InferM Kind
    getKind v = gets $ (! v) . tempEnv

getFlexVars :: Type -> Expr -> InferM [Var]
getFlexVars ty expr = do
  tyVars   <- tempVars ty
  exprVars <- tempVars expr
  envVars  <- tempVarsEnv
  return $ nub (tyVars ++ exprVars) \\ envVars

tempVarsEnv :: InferM [Var]
tempVarsEnv = do env <- ask
                 vs <- mapM tempVars [ty | L ty <- toList env]
                 let vs' = [v | (v, T _) <- envPairs env]
                 return $ vs' ++ (concat vs)

tempVars :: HasTypeVars a => a -> InferM [Var]
tempVars x = liftM freeTyVars (zonk x)

instantiate :: Type -> Type -> Expr -> InferM Expr
instantiate ty reqTy expr = do
  ty'    <- zonk ty
  case ty' of
    Forall kinds body -> do
      vs <- mapM freshVar kinds
      unify reqTy (instantiateTVs vs body)
      return $ TApp expr vs
    _ -> do
      unify reqTy ty'
      return expr

bindMVar:: Var -> Type -> InferM ()
bindMVar v t | v `occursIn` t = throw TypeErr (pprint (v, t))
             | otherwise = do modify $ setSubst $ (<> v @> t)
                              modify $ setTempEnv $ envDelete v

-- TODO: check kinds
unify :: Type -> Type -> InferM ()
unify t1 t2 = do
  t1' <- zonk t1
  t2' <- zonk t2
  env <- ask
  let unifyErr = throw TypeErr $
                   "can't unify " ++ pprint t1' ++ " and " ++ pprint t2'
  case (t1', t2') of
    _ | t1' == t2'               -> return ()
    (t, TypeVar v) | not (v `isin` env) -> bindMVar v t
    (TypeVar v, t) | not (v `isin` env) -> bindMVar v t
    (ArrType a b, ArrType a' b') -> unify a a' >> unify b b'
    (TabType a b, TabType a' b') -> unify a a' >> unify b b'
    (Exists t, Exists t')        -> unify t t'
    (RecType r, RecType r')      ->
      case zipWithRecord unify r r' of
             Nothing -> unifyErr
             Just unifiers -> void $ sequence unifiers
    _ -> unifyErr


occursIn :: Var -> Type -> Bool
occursIn v t = v `elem` freeTyVars t

zonk :: HasTypeVars a => a -> InferM a
zonk x = subFreeTVs lookupVar x

lookupVar :: Var -> InferM Type
lookupVar v = do
  mty <- gets $ flip envLookup v . subst
  case mty of Nothing -> return $ TypeVar v
              Just ty -> do ty' <- zonk ty
                            modify $ setSubst (<> v @> ty')
                            return ty'

setSubst :: (Subst -> Subst) -> InferState -> InferState
setSubst update state = state { subst = update (subst state) }

setTempEnv :: (TempEnv -> TempEnv) -> InferState -> InferState
setTempEnv update state = state { tempEnv = update (tempEnv state) }

inferKinds :: [Var] -> Type -> Except [Kind]
inferKinds vs ty = do
  let kinds = execWriter (collectKinds TyKind ty)
  m <- case fromUnambiguousList kinds of
    Nothing -> throw TypeErr $ "Conflicting kinds for " ++ pprint vs
    Just m -> return m
  let lookupKind v = case M.lookup v m of
        Nothing   -> Left $ Err TypeErr $ "Ambiguous kind for " ++ pprint v
        Just kind -> Right kind
  mapM lookupKind vs

fromUnambiguousList :: (Ord k, Eq a) => [(k, a)] -> Maybe (M.Map k a)
fromUnambiguousList xs = sequence $ M.fromListWith checkEq (map (onSnd Just) xs)
  where checkEq (Just v) (Just v') | v == v' = Just v
                                   | otherwise = Nothing

collectKinds :: Kind -> Type -> Writer [(Var, Kind)] ()
collectKinds kind ty = case ty of
  BaseType _    -> return ()
  TypeVar v     -> tell [(v, kind)]
  ArrType a b   -> recur kind       a >> recur kind b
  TabType a b   -> recur idxSetKind a >> recur kind b
  RecType r     -> mapM_ (recur kind) r
  Forall _ body -> recur kind body
  Exists body   -> recur kind body
  IdxSetLit _   -> return ()
  BoundTVar _   -> return ()
  where recur = collectKinds
