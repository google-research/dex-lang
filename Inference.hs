module Inference (typePass) where

import Control.Monad
import Control.Monad.Reader (ReaderT, runReaderT, local, asks)
import Control.Monad.Writer (tell)
import Control.Monad.State (StateT, evalStateT, gets, put, modify)
import Control.Monad.Except (throwError)
import Data.List (nub, (\\))
import Data.Foldable (toList)

import Syntax
import Env
import Record
import Util
import Type
import PPrint
import Fresh
import Pass

type Subst   = Env Type
type TempEnv = Env Kind
data InferState = InferState { tempEnv :: TempEnv
                             , subst :: Subst }

type InferM a = MonadPass TypeEnv InferState a
type Constraint = (Type, Type)

typePass :: UDecl -> TopMonadPass TypeEnv Decl
typePass decl = case decl of
  UTopLet v expr -> do
    (ty, expr') <- translate expr
    put $ newFullEnv [(v,ty)] []
    return $ TopLet (v,ty) expr'
  UTopUnpack v expr -> do
    (ty, expr') <- translate expr
    ty' <- liftExcept $ unpackExists ty v
    let iv = Qual v "idx" 0 -- TODO: sort out variables properly
    put $ newFullEnv [(v,ty')] [(iv, IdxSetKind)]
    return $ TopUnpack (v,ty') iv expr'
  UEvalCmd NoOp -> put mempty >> return (EvalCmd NoOp)
  UEvalCmd (Command cmd expr) -> do
    (ty, expr') <- translate expr
    put mempty
    case cmd of
      GetType -> do tell [pprint ty]
                    return $ EvalCmd NoOp
      Passes  -> do tell ["\nSystem F\n" ++ pprint expr']
                    return $ EvalCmd (Command cmd expr')
      _ -> return $ EvalCmd (Command cmd expr')

  where translate expr = liftTopPass (InferState mempty mempty) (inferTop expr)

inferTop :: UExpr -> InferM (Type, Expr)
inferTop rawExpr = infer rawExpr >>= uncurry generalize

infer :: UExpr -> InferM (Type, Expr)
infer expr = do ty <- freshVar TyKind
                expr' <- check expr ty
                return (ty, expr')

check :: UExpr -> Type -> InferM Expr
check expr reqTy = case expr of
  ULit c -> do unify (BaseType (litType c)) reqTy
               return (Lit c)
  UVar v -> do ty <- asks $ (! v) . lEnv
               instantiate ty reqTy (Var v)
  UBuiltin b -> instantiate (builtinType b) reqTy (Builtin b)
  ULet (RecLeaf v) bound body -> do
    (ty', bound') <- infer bound
    (forallTy, tLam) <- generalize ty' bound'
    let p = RecLeaf (v, forallTy)
    body' <- recurWith p body reqTy
    return $ Let p tLam body'
  ULet p bound body -> do
    (a, bound') <- infer bound
    p' <- checkPat p a
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
  UFor v body -> do
    (i, elemTy) <- splitTab reqTy
    body' <- recurWith [(v, i)] body elemTy
    return $ For (v, i) body'
  URecCon r -> do tyExpr <- traverse infer r
                  unify reqTy (RecType (fmap fst tyExpr))
                  return $ RecCon (fmap snd tyExpr)
  UGet tabExpr idxExpr -> do
    (tabTy, expr') <- infer tabExpr
    (i, v) <- splitTab tabTy
    actualISet <- asks $ (! idxExpr) . lEnv
    unify i actualISet
    unify v reqTy
    return $ Get expr' idxExpr
  UUnpack v bound body -> do
    (maybeEx, bound') <- infer bound >>= zonk
    idxTy <- freshIdx
    boundTy <- case maybeEx of Exists t -> return $ instantiateTVs [idxTy] t
                               _ -> throwError $ TypeErr $ pprint maybeEx
    body' <- recurWith [(v, boundTy)] body reqTy
    idxTy' <- zonk idxTy
    tv <- case idxTy' of TypeVar tv -> return tv
                         _ -> leakErr
    tvsEnv <- tempVarsEnv
    tvsReqTy <- tempVars reqTy
    if (tv `elem` tvsEnv) || (tv `elem` tvsReqTy)  then leakErr else return ()
    return $ Unpack (v, boundTy) tv bound' body'


  where
    leakErr = throwError $ TypeErr "existential variable leaked"
    recurWith p expr ty = local (setLEnv $ addVs p) (check expr ty)

checkPat :: UPat -> Type -> InferM Pat
checkPat pat ty = do tree <- traverse addFresh pat
                     unify (patType tree) ty
                     return tree
  where addFresh v = do { t <- freshTy; return (v,t) }

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
  return $ nub $ (tyVars ++ exprVars) \\ envVars

tempVarsEnv :: InferM [Var]
tempVarsEnv = do envTypes <- asks $ toList . lEnv
                 vs <- mapM tempVars envTypes
                 vs' <- asks $ envVars . tEnv
                 return (concat vs ++ vs')

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
bind v t | v `occursIn` t = error $ pprint (v, t)  -- throwError InfiniteTypeErr
         | otherwise = do modify $ setSubst $ addV (v, t)
                          modify $ setTempEnv $ envDelete v

-- TODO: check kinds
unify :: Type -> Type -> InferM ()
unify t1 t2 = do
  t1' <- zonk t1
  t2' <- zonk t2
  let unifyErr = throwError $ UnificationErr t1' t2'
  case (t1', t2') of
    _ | t1' == t2'               -> return ()
    (t, TypeVar v)               -> bind v t
    (TypeVar v, t)               -> bind v t
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
                            modify $ setSubst (addV (v, ty'))
                            return ty'

setSubst :: (Subst -> Subst) -> InferState -> InferState
setSubst update state = state { subst = update (subst state) }

setTempEnv :: (TempEnv -> TempEnv) -> InferState -> InferState
setTempEnv update state = state { tempEnv = update (tempEnv state) }
