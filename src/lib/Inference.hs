module Inference (typePass, inferKinds) where

import Control.Monad
import Control.Monad.Reader
import Control.Monad.Except (liftEither)
import Control.Monad.Writer
import Control.Monad.State
import Data.Foldable (toList)
import Data.List (nub, (\\))
import qualified Data.Map.Strict as M

import Syntax
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

typePass :: UTopDecl -> TopPass TypeEnv TopDecl
typePass tdecl = case tdecl of
  TopDecl decl -> case decl of
    LetMono p bound -> do
      (p', bound') <- liftTop $ do
        (patTy, p') <- inferPat p
        bound' <- check bound patTy
        return (p', bound')
      putEnv (foldMap asEnv p')
      return $ TopDecl $ LetMono p' bound'
    LetPoly b@(_:> Forall _ tyBody) (TLam tbs tlamBody) -> do
      tlamBody' <- liftTop $ do
        let tyBody' = instantiateTVs [TypeVar v | (v:>_) <- tbs] tyBody
        extendR (foldMap tbind tbs) (check tlamBody tyBody')
      putEnv (lbind b)
      return $ TopDecl $ LetPoly b (TLam tbs tlamBody')
    Unpack b tv expr -> do
      (ty, expr') <- liftTop (infer expr)
      ty' <- liftEither $ unpackExists ty tv
      let b' = fmap (const ty') b -- TODO: actually check the annotated type
      putEnv $ asEnv b' <> tv @> T idxSetKind
      return $ TopDecl (Unpack b' tv expr')
    TAlias _ _ -> error "Shouldn't have TAlias left"
  EvalCmd NoOp -> return (EvalCmd NoOp)
  EvalCmd (Command cmd expr) -> do
    case cmd of
      GetType -> do
        (ty, _) <- liftTop $ infer expr >>= uncurry generalize
        writeOutText (pprint ty)
        return $ EvalCmd NoOp
      Passes  -> do
        (_, expr') <- liftTop $ infer expr
        writeOutText ("\nSystem F\n" ++ pprint expr')
        return $ EvalCmd (Command cmd expr')
      _ -> do
        (_, expr') <- liftTop $ infer expr
        return $ EvalCmd (Command cmd expr')

liftTop :: HasTypeVars a => InferM a -> TopPass TypeEnv a
liftTop m = do
  source <- getSource
  addErrSource source $ liftTopPass (InferState mempty mempty) mempty (m >>= zonk)

infer :: UExpr -> InferM (Type, Expr)
infer expr = do ty <- freshVar TyKind
                expr' <- check expr ty
                return (ty, expr')

check :: UExpr -> Type -> InferM Expr
check expr reqTy = case expr of
  Lit c -> do
    unifyReq (BaseType (litType c))
    return (Lit c)
  Var v ts -> do
    maybeTy <- asks $ (flip envLookup v)
    Forall kinds body <- case maybeTy of
      Nothing -> throw UnboundVarErr (pprint v)
      Just (L ty) -> return ty
      Just (T _ ) -> error "Expected let-bound var"
    vs <- mapM freshVar (drop (length ts) kinds)
    let ts' = ts ++ vs
    unifyCtx expr reqTy (instantiateTVs ts' body)
    return $ Var v ts'
  PrimOp b [] args -> do
    let BuiltinType kinds argTys ansTy = builtinType b
    vs <- mapM freshVar kinds
    unifyReq (instantiateTVs vs ansTy)
    let argTys' = map (instantiateTVs vs) argTys
    args' <- zipWithM check args argTys'
    return $ PrimOp b vs args'
  Decl decl body -> checkDecl decl (check body reqTy)
  Lam p body -> do
    (a, b) <- splitFun expr reqTy
    p' <- checkPat p a
    body' <- recurWithP p' body b
    return $ Lam p' body'
  App fexpr arg -> do
    (f, fexpr') <- infer fexpr
    (a, b) <- splitFun expr f
    arg' <- check arg a
    unifyReq b
    return $ App fexpr' arg'
  For p body -> do
    (i, elemTy) <- splitTab expr reqTy
    p' <- checkPat p i
    body' <- recurWithP p' body elemTy
    return $ For p' body'
  Get tabExpr idxExpr -> do
    (tabTy, expr') <- infer tabExpr
    (i, v) <- splitTab expr tabTy
    idxExpr' <- check idxExpr i
    unifyReq v
    return $ Get expr' idxExpr'
  RecCon r -> do
    tyExpr <- traverse infer r
    unifyReq (RecType (fmap fst tyExpr))
    return $ RecCon (fmap snd tyExpr)
  TabCon _ xs -> do
    (n, elemTy) <- splitTab expr reqTy
    xs' <- mapM (flip check elemTy) xs
    let n' = length xs
    -- `==> elemTy` for better messages
    unifyCtx expr (n ==> elemTy) (IdxSetLit n' ==> elemTy)
    return $ TabCon reqTy xs'
  Pack e ty exTy -> do
    let (Exists exBody) = exTy
    unifyReq exTy
    let t = instantiateTVs [ty] exBody
    e' <- check e t
    return $ Pack e' ty exTy
  DerivAnnot e ann -> do
    e' <- check e reqTy
    ann' <- check ann (tangentBunType reqTy) -- TODO: handle type vars and meta vars)
    return $ DerivAnnot e' ann'
  Annot e annTy -> do
    -- TODO: check that the annotation is a monotype
    unifyReq annTy
    check e reqTy
  SrcAnnot e pos -> addErrSourcePos pos (check e reqTy)
  _ -> error $ "Unexpected expression: " ++ show expr
  where
    unifyReq ty = unifyCtx expr reqTy ty

    -- TODO: return env rather than do things cps-like
    checkDecl :: UDecl -> InferM Expr -> InferM Expr
    checkDecl decl cont = case decl of
      -- TODO: check there are no ambiguous tvars to prevent upstream inference
      LetMono p bound -> do
        (patTy, p') <- inferPat p
        bound' <- check bound patTy
        extendR (foldMap asEnv p') $ do
          body' <- cont
          return $ Decl (LetMono p' bound') body'
      LetPoly b@(_:> Forall _ tyBody) (TLam tbs tlamBody) -> do
        let tyBody' = instantiateTVs [TypeVar v | (v:>_) <- tbs] tyBody
        tlamBody' <- extendR (foldMap tbind tbs) (check tlamBody tyBody')
        -- TODO: check if bound vars leaked?
        extendR (lbind b) $ do
          body' <- cont
          return $ Decl (LetPoly b (TLam tbs tlamBody')) body'
      Unpack b tv bound -> do
        (maybeEx, bound') <- infer bound >>= zonk
        boundTy <- case maybeEx of Exists t -> return $ instantiateTVs [TypeVar tv] t
                                   _ -> throw TypeErr (pprint maybeEx)
        let b' = replaceAnnot b boundTy
        body' <- extendR (asEnv b' <> tv @> T idxSetKind) cont
        tvsEnv <- tempVarsEnv
        tvsReqTy <- tempVars reqTy
        if (tv `elem` tvsEnv) || (tv `elem` tvsReqTy)  then leakErr else return ()
        return $ Decl (Unpack b' tv bound') body'
      TAlias _ _ -> error "Shouldn't have TAlias left"

    leakErr = throw TypeErr "existential variable leaked"
    recurWithP p e ty = extendR (foldMap asEnv p) (check e ty)

inferBinder :: UBinder -> InferM Binder
inferBinder b = liftM (replaceAnnot b) $ case binderAnn b of
                                           NoAnn -> freshTy
                                           Ann ty -> return ty

checkPat :: UPat -> Type -> InferM Pat
checkPat p ty = do (ty', p') <- inferPat p
                   unifyCtx unitCon ty ty'
                   return p'

inferPat :: UPat -> InferM (Type, Pat)
inferPat pat = do tree <- traverse inferBinder pat
                  return (patType tree, tree)

asEnv :: Binder -> TypeEnv
asEnv (v:>ty) = v @> L (asSigma ty)

-- TODO: consider expected/actual distinction. App/Lam use it in opposite senses
splitFun :: UExpr -> Type -> InferM (Type, Type)
splitFun e f = case f of
  ArrType a b -> return (a, b)
  _ -> do a <- freshTy
          b <- freshTy
          unifyCtx e f (a --> b)
          return (a, b)

splitTab :: UExpr -> Type -> InferM (IdxSet, Type)
splitTab e t = case t of
  TabType i v -> return (i, v)
  _ -> do i <- freshIdx
          v <- freshTy
          unifyCtx e t (i ==> v)
          return (i, v)

freshVar :: Kind -> InferM Type
freshVar kind = do v <- fresh $ pprint kind
                   modify $ setTempEnv (<> v @> kind)
                   return (TypeVar v)

freshTy :: InferM Type
freshTy  = freshVar TyKind

freshIdx :: InferM Type
freshIdx = freshVar idxSetKind

generalize :: Type -> Expr -> InferM (SigmaType, TLam)
generalize ty expr = do
  ty'   <- zonk ty
  expr' <- zonk expr
  flexVars <- getFlexVars ty' expr'
  kinds <- mapM getKind flexVars
  return (Forall kinds $ abstractTVs flexVars ty',
          TLam (zipWith (:>) flexVars kinds) expr')
  where
    getKind :: Name -> InferM Kind
    getKind v = gets $ (! v) . tempEnv

getFlexVars :: Type -> Expr -> InferM [Name]
getFlexVars ty expr = do
  tyVars   <- tempVars ty
  exprVars <- tempVars expr
  envVars  <- tempVarsEnv
  return $ nub (tyVars ++ exprVars) \\ envVars

tempVarsEnv :: InferM [Name]
tempVarsEnv = do
  env <- ask
  vs <- mapM tempVars [ty | L ty <- toList env]
  let vs' = [v | (v, T _) <- envPairs env]
  return $ vs' ++ (concat vs)

tempVars :: HasTypeVars a => a -> InferM [Name]
tempVars x = liftM freeTyVars (zonk x)

bindMVar :: Name -> Type -> InferM ()
bindMVar v t | v `occursIn` t = throw TypeErr (pprint (v, t))
             | otherwise = do modify $ setSubst $ (<> v @> t)
                              modify $ setTempEnv $ envDelete v

unifyCtx :: UExpr -> Type -> Type -> InferM ()
unifyCtx expr tyReq tyActual = do
  -- TODO: avoid the double zonking
  tyReq'    <- zonk tyReq
  tyActual' <- zonk tyActual
  let s = "\nExpected: " ++ pprint tyReq'
       ++ "\n  Actual: " ++ pprint tyActual'
       ++ "\nIn: "       ++ pprint expr
  unify s tyReq' tyActual'

-- TODO: check kinds
unify :: String -> Type -> Type -> InferM ()
unify s t1 t2 = do
  t1' <- zonk t1
  t2' <- zonk t2
  env <- ask
  case (t1', t2') of
    _ | t1' == t2'               -> return ()
    (t, TypeVar v) | not (v `isin` env) -> bindMVar v t
    (TypeVar v, t) | not (v `isin` env) -> bindMVar v t
    (ArrType a b, ArrType a' b') -> unify s a a' >> unify s b b'
    (TabType a b, TabType a' b') -> unify s a a' >> unify s b b'
    (Exists t, Exists t')        -> unify s t t'
    (RecType r, RecType r')      ->
      case zipWithRecord (unify s) r r' of
             Nothing -> throw TypeErr s
             Just unifiers -> void $ sequence unifiers
    _ -> throw TypeErr s


occursIn :: Name -> Type -> Bool
occursIn v t = v `elem` freeTyVars t

zonk :: HasTypeVars a => a -> InferM a
zonk x = subFreeTVs lookupVar x

lookupVar :: Name -> InferM Type
lookupVar v = do
  mty <- gets $ flip envLookup v . subst
  case mty of Nothing -> return $ TypeVar v
              Just ty -> do ty' <- zonk ty
                            modify $ setSubst (<> v @> ty')
                            return ty'

setSubst :: (Subst -> Subst) -> InferState -> InferState
setSubst update s = s { subst = update (subst s) }

setTempEnv :: (TempEnv -> TempEnv) -> InferState -> InferState
setTempEnv update s = s { tempEnv = update (tempEnv s) }

inferKinds :: [Name] -> Type -> Except [Kind]
inferKinds vs _ = return $ replicate (length vs) TyKind  -- TODO: other kinds
-- inferKinds vs ty = do
  -- let kinds = execWriter (collectKinds TyKind ty)
  -- m <- case fromUnambiguousList kinds of
  --   Nothing -> throw TypeErr $ "Conflicting kinds for " ++ pprint vs
  --   Just m -> return m
  -- let lookupKind v = case M.lookup v m of
  --       Nothing   -> Left $ Err TypeErr Nothing $ "Ambiguous kind for " ++ pprint v
  --       Just kind -> Right kind
  -- mapM lookupKind vs

fromUnambiguousList :: (Ord k, Eq a) => [(k, a)] -> Maybe (M.Map k a)
fromUnambiguousList xs = sequence $ M.fromListWith checkEq (map (onSnd Just) xs)
  where checkEq (Just v) (Just v') | v == v' = Just v
                                   | otherwise = Nothing
        checkEq _ _ = error "Shouldn't happen"

collectKinds :: Kind -> Type -> Writer [(Name, Kind)] ()
collectKinds kind ty = case ty of
  BaseType _    -> return ()
  TypeVar v     -> tell [(v, kind)]
  ArrType a b   -> recur kind       a >> recur kind b
  TabType a b   -> recur idxSetKind a >> recur kind b
  RecType r     -> mapM_ (recur kind) r
  -- Forall _ body -> recur kind body
  Exists body   -> recur kind body
  IdxSetLit _   -> return ()
  BoundTVar _   -> return ()
  where recur = collectKinds
