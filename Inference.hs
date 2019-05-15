module Inference (typePass, inferKinds) where

import Control.Monad
import Control.Monad.Reader
import Control.Monad.Except (liftEither)
import Control.Monad.Writer
import Control.Monad.State
import Data.List (nub, (\\))
import Data.Foldable (toList)
import qualified Data.Map.Strict as M

import Syntax
import Env
import Record
import Type
import PPrint
import Fresh
import Pass
import Util (onSnd)

type Subst   = Env Type
type TempEnv = Env Kind
data InferState = InferState { tempEnv :: TempEnv
                             , subst :: Subst }

type InferM a = Pass TypeEnv InferState a
type Constraint = (Type, Type)

typePass :: UDecl -> TopPass TypeEnv Decl
typePass decl = case decl of
  UTopLet (v,_) expr -> do
    (ty, expr') <- translate expr
    putEnv $ newFullEnv [(v,ty)] []
    return $ TopLet (v,ty) expr'
  UTopUnpack (v,_) expr -> do
    (ty, expr') <- translate expr
    let iv = rawName "idx" -- TODO: sort out variables properly
    ty' <- liftEither $ unpackExists ty iv
    putEnv $ newFullEnv [(v,ty')] [(iv, IdxSetKind)]
    return $ TopUnpack (v,ty') iv expr'
  UEvalCmd NoOp -> return (EvalCmd NoOp)
  UEvalCmd (Command cmd expr) -> do
    (ty, expr') <- translate expr
    case cmd of
      GetType -> do writeOut (pprint ty)
                    return $ EvalCmd NoOp
      Passes  -> do writeOut ("\nSystem F\n" ++ pprint expr')
                    return $ EvalCmd (Command cmd expr')
      _ -> return $ EvalCmd (Command cmd expr')

  where translate expr = liftTopPass (InferState mempty mempty) mempty (inferTop expr)

inferTop :: UExpr -> InferM (Type, Expr)
inferTop expr = do infer expr >>= uncurry generalize

infer :: UExpr -> InferM (Type, Expr)
infer expr = do ty <- freshVar TyKind
                expr' <- check expr ty
                return (ty, expr')

check :: UExpr -> Type -> InferM Expr
check expr reqTy = case expr of
  ULit c -> do unify (BaseType (litType c)) reqTy
               return (Lit c)
  UVar v -> do
    maybeTy <- asks $ (flip envLookup v) . lEnv
    ty <- case maybeTy of Nothing -> throw UnboundVarErr (pprint v)
                          Just ty -> return ty
    instantiate ty reqTy (Var v)
  UBuiltin b -> instantiate (builtinType b) reqTy (Builtin b)
  ULet (RecLeaf (v, Nothing)) bound body -> do
    (ty', bound') <- infer bound
    (forallTy, tLam) <- generalize ty' bound'
    let p = RecLeaf (v, forallTy)
    body' <- recurWith p body reqTy
    return $ Let p tLam body'
  ULet p bound body -> do
    (patTy, p') <- inferPat p
    bound' <- check bound patTy
    body' <- recurWith p' body reqTy
    return $ Let p'  bound' body'
  ULam p body -> do
    (a, b) <- splitFun reqTy
    p' <- checkPat p a
    body' <- recurWith p' body b
    return $ Lam p' body'
  UApp fexpr arg -> do
    (f, fexpr') <- infer fexpr
    (a, b) <- splitFun f
    arg' <- check arg a
    unify b reqTy
    return $ App fexpr' arg'
  UFor (v, Nothing) body -> do
    (i, elemTy) <- splitTab reqTy
    body' <- recurWith [(v, i)] body elemTy
    return $ For (v, i) body'
  UGet tabExpr idxExpr -> do
    (tabTy, expr') <- infer tabExpr
    (i, v) <- splitTab tabTy
    actualISet <- asks $ (! idxExpr) . lEnv
    unify i actualISet
    unify v reqTy
    return $ Get expr' idxExpr
  UUnpack v bound body -> do
    (maybeEx, bound') <- infer bound >>= zonk
    tv <- fresh $ "r"
    boundTy <- case maybeEx of Exists t -> return $ instantiateTVs [TypeVar tv] t
                               _ -> throw TypeErr (pprint maybeEx)
    body' <- local (  setLEnv (addV (v, boundTy))
                    . setTEnv (addV (tv, IdxSetKind))) (check body reqTy)
    tvsEnv <- tempVarsEnv
    tvsReqTy <- tempVars reqTy
    if (tv `elem` tvsEnv) || (tv `elem` tvsReqTy)  then leakErr else return ()
    return $ Unpack (v, boundTy) tv bound' body'
  URecCon r -> do tyExpr <- traverse infer r
                  unify reqTy (RecType (fmap fst tyExpr))
                  return $ RecCon (fmap snd tyExpr)
  -- This won't work for quantified annotations, because unifying such
  -- types is difficult, and Hindley-Milner assumes that quantifiers
  -- are only introduced at let binders.  Ergo, it may be necessary to
  -- treat quantified annotations specially (when there are parsing
  -- rules for them and so on).
  UAnnot e annTy -> do unify annTy reqTy
                       check e reqTy

  where
    leakErr = throw TypeErr "existential variable leaked"
    recurWith p expr ty = local (setLEnv $ addVs p) (check expr ty)

checkPat :: UPat -> Type -> InferM Pat
checkPat p ty = do (ty', p') <- inferPat p
                   unify ty ty'
                   return p'

inferPat :: UPat -> InferM (Type, Pat)
inferPat pat = do tree <- traverse addFresh pat
                  return (patType tree, tree)
  where addFresh (v, Nothing) = do { ty <- freshTy; return (v, ty) }
        addFresh (v, Just ty) = return (v, ty)

splitFun :: Type -> InferM Constraint
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

freshVar :: Kind -> InferM Type
freshVar kind = do v <- fresh $ pprint kind
                   modify $ setTempEnv $ addV (v, kind)
                   return (TypeVar v)

freshTy  = freshVar TyKind
freshIdx = freshVar IdxSetKind

generalize :: Type -> Expr -> InferM (Type, Expr)
generalize ty expr = do
  ty'   <- zonk ty
  expr' <- zonk expr
  flexVars <- getFlexVars ty' expr'
  case flexVars of
    [] -> return (ty', expr')
    _  -> do kinds <- mapM getKind flexVars
             return (Forall kinds $ abstractTVs flexVars ty',
                     TLam (zip flexVars kinds) expr')
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
tempVarsEnv = do envTypes <- asks $ toList . lEnv
                 vs <- mapM tempVars envTypes
                 return (concat vs)

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

bind :: Var -> Type -> InferM ()
bind v t | v `occursIn` t = throw TypeErr (pprint (v, t))
         | otherwise = do modify $ setSubst $ addV (v, t)
                          modify $ setTempEnv $ envDelete v

-- TODO: check kinds
unify :: Type -> Type -> InferM ()
unify t1 t2 = do
  t1' <- zonk t1
  t2' <- zonk t2
  tenv <- asks tEnv
  let unifyErr = throw TypeErr $
                   "can't unify " ++ pprint t1' ++ " and " ++ pprint t2'
  case (t1', t2') of
    _ | t1' == t2'               -> return ()
    (t, TypeVar v) | not (v `isin` tenv) -> bind v t
    (TypeVar v, t) | not (v `isin` tenv) -> bind v t
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
                            modify $ setSubst (updateV (v, ty'))
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
  TabType a b   -> recur IdxSetKind a >> recur kind b
  Forall _ body -> recur kind body
  Exists body   -> recur kind body
  IdxSetLit _   -> return ()
  BoundTVar _   -> return ()
  where recur = collectKinds
