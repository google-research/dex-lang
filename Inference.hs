module Inference (typePass, translateExpr) where

import Control.Monad
import Control.Monad.Reader (ReaderT, runReaderT, local, asks)
import Control.Monad.State (StateT, evalStateT, gets, modify)
import Control.Monad.Except (throwError)
import qualified Data.Map.Strict as M
import Data.List (nub, (\\))
import Data.Foldable (toList)

import Syntax
import Env
import Record
import Util
import Type

type TypingEnv = FullEnv Type Kind
type TempVar = Int
type TempEnv = M.Map TempVar Kind
type Subst = M.Map TempVar Type
data InferState = InferState { freshCounter :: Int
                             , subst :: Subst
                             , tempEnv :: TempEnv}

type InferM a = ReaderT TypingEnv (
                          StateT InferState (
                            Either Err)) a

type Constraint = (Type, Type)

typePass :: Pass UExpr Expr Type ()
typePass = Pass
  { lowerExpr   = \expr env   -> liftErrIO $ translateExpr expr env
  , lowerUnpack = \v expr env -> liftErrIO $ inferTypesUnpack v expr env
  , lowerCmd    = \cmd  env   -> return $ inferTypesCmd cmd env }

inferTypesCmd :: Command UExpr -> FullEnv Type () -> Command Expr
inferTypesCmd (Command cmdName expr) env = case cmdName of
    GetParse -> CmdResult $ TextOut (show expr)
    _ -> case translateExpr expr env of
      Left e -> CmdErr e
      Right (ty, expr') -> case cmdName of
        GetType ->  CmdResult $ TextOut  $ show ty
        GetTyped -> CmdResult $ TextOut  $ show expr'
        -- Plot -> case getType (lEnv ftenv) expr' of
        --           TabType _ (BaseType IntType) -> Command Plot expr'
        --           ty -> CmdErr $ TypeErr $
        --               "Plot data must have form i=>Int. Got: " ++ show ty
        -- PlotMat ->
        --   case getType (lEnv ftenv) expr' of
        --          TabType _ (TabType _ (BaseType IntType)) -> Command PlotMat expr'
        --          ty -> CmdErr $ TypeErr $
        --                 "Plotmat data must have form i=>j=>Int. Got: " ++ show ty
        _ -> Command cmdName expr'
inferTypesCmd (CmdResult s) _ = CmdResult s
inferTypesCmd (CmdErr e)    _ = CmdErr e

-- TODO: check integrity as well
translateExpr :: UExpr -> FullEnv Type () -> Except (Type, Expr)
translateExpr rawExpr (FullEnv lenv tenv) = evalInferM env (inferTop rawExpr)
  where env = FullEnv lenv $ fmap (const IdxSetKind) tenv

inferTypesUnpack :: VarName -> UExpr -> FullEnv Type () -> Except (Type, (), Expr)
inferTypesUnpack v expr env = do
  (ty, expr') <- translateExpr expr env
  ty' <- case ty of
    Exists body -> return $ instantiateTypeV [v] body
    _ -> throwError $ TypeErr $ "Can't unpack type: " ++ show ty
  return (ty', (), expr')


evalInferM :: TypingEnv -> InferM a -> Except a
evalInferM env m = evalStateT (runReaderT m env) initState
  where initState = InferState 0 M.empty mempty

inferTop :: UExpr -> InferM (Type, Expr)
inferTop rawExpr = infer rawExpr >>= uncurry generalize

infer :: UExpr -> InferM (Type, Expr)
infer expr = do v <- freshVar TyKind
                let ty = TypeVar (FV v)
                expr' <- check expr ty
                return (ty, expr')

check :: UExpr -> Type -> InferM Expr
check expr reqTy = case expr of
  ULit c -> do unify (litType c) reqTy
               return (Lit c)
  UVar v -> do ty <- asks $ (! v) . lEnv
               instantiate  ty reqTy (Var v)
  UBuiltin b -> instantiate (builtinType b) reqTy (Builtin b)
  ULet (RecLeaf _) bound body -> do
    (ty', bound') <- infer bound
    (forallTy, tLam) <- generalize ty' bound'
    body' <- local (setLEnv $ addBVar forallTy) (check body reqTy)
    return $ Let (RecLeaf forallTy) tLam body'
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
    unify b reqTy
    return $ App fexpr' arg'
  UFor _ body -> do
    (i, v) <- splitTab reqTy
    body' <- local (setLEnv $ addBVar i) (check body v)
    return $ For i body'
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
  UUnpack _ bound body -> do
    (maybeEx, bound') <- infer bound >>= zonk
    boundTy <- case maybeEx of
                 Exists t -> return t
                 _ -> throwError $ TypeErr $ "Expected existential, got: " ++ show maybeEx
    idxTy@(TypeVar (FV v)) <- freshIdx
    let updateEnv = setLEnv $ addBVar (instantiateTypeV [v] boundTy)
    body' <- local updateEnv (check body reqTy)
    idxTy' <- zonk idxTy
    v' <- case idxTy' of
            TypeVar (FV (TempVar tv)) -> return tv
            _ -> throwError $ TypeErr "existential variable leaked scope"
    vs <- tempVarsEnv
    if v' `elem` vs then throwError $ TypeErr "existential variable leaked scope"
                    else return ()
    boundTy' <- zonk boundTy
    body'' <- zonk body'
    return $ Unpack (abstractTVs [TempVar v'] boundTy') bound'
                    (abstractTVs [TempVar v'] body'')

recTy :: UPat -> Type -> InferM (RecTree Type)
recTy pat ty = do tree <- traverse (const (freshVar TyKind)) pat
                  let tree' = fmap (TypeVar . FV) tree
                  unify (recTreeAsType tree') ty
                  return tree'

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

inc :: InferM Int
inc = do i <- gets freshCounter
         modify $ \s -> s { freshCounter = i + 1 }
         return i

freshVar :: Kind -> InferM VarName
freshVar kind = do i <- inc
                   env <- gets tempEnv
                   modify $ \s -> s {tempEnv = M.insert i kind env}
                   return (TempVar i)

freshTy :: InferM Type
freshTy = freshVar TyKind >>= return . TypeVar . FV

freshIdx :: InferM Type
freshIdx = freshVar IdxSetKind >>= return . TypeVar . FV

generalize :: Type -> Expr -> InferM (Type, Expr)
generalize ty expr = do
  ty'   <- zonk ty
  expr' <- zonk expr
  flexVars <- getFlexVars ty' expr'
  case flexVars of
    [] -> return (ty', expr')
    _  -> do kinds <- mapM getKind flexVars
             let flexVars' = map TempVar flexVars
             return (Forall kinds $ abstractTVs flexVars' ty',
                     TLam   kinds $ abstractTVs flexVars' expr')
  where
    getKind :: TempVar -> InferM Kind
    getKind v = gets $ unJust . M.lookup v . tempEnv

getFlexVars :: Type -> Expr -> InferM [TempVar]
getFlexVars ty expr = do
  tyVars   <- tempVars ty
  exprVars <- tempVars expr
  envVars  <- tempVarsEnv
  return $ nub $ (tyVars ++ exprVars) \\ envVars

tempVarsEnv :: InferM [TempVar]
tempVarsEnv = do envTypes <- asks $ bVars . lEnv
                 vs <- mapM tempVars envTypes
                 return (concat vs)

tempVars :: HasTypeVars a => a -> InferM [TempVar]
tempVars x = liftM (filterTVs . freeTyVars) (zonk x)
  where filterTVs vs = [v | TempVar v <- vs]

instantiate :: Type -> Type -> Expr -> InferM Expr
instantiate ty reqTy expr = do
  ty'    <- zonk ty
  reqTy' <- zonk reqTy
  case ty' of
    Forall kinds body -> do
      vs <- mapM freshVar kinds
      unify reqTy' (instantiateTypeV vs body)
      return $ TApp expr $ map (TypeVar . FV) vs
    _ -> do
      unify reqTy' ty'
      return expr

bind :: TempVar -> Type -> InferM ()
bind v t | v `occursIn` t = error $ show (v, t)  -- throwError InfiniteTypeErr
         | otherwise = do modify $ setSubst $ M.insert v t
                          modify $ setTempEnv $ M.delete v

-- TODO: check kinds
unify :: Type -> Type -> InferM ()
unify t1 t2 = do
  t1' <- zonk t1
  t2' <- zonk t2
  let unifyErr = throwError $ UnificationErr (show t1') (show t2')
  case (t1', t2') of
    _ | t1' == t2'                -> return ()
    (t, TypeVar (FV (TempVar v))) -> bind v t
    (TypeVar (FV (TempVar v)), t) -> bind v t
    (ArrType a b, ArrType a' b')  -> unify a a' >> unify b b'
    (TabType a b, TabType a' b')  -> unify a a' >> unify b b'
    (Exists t, Exists t')         -> unify t t'
    (RecType r, RecType r')       ->
      case zipWithRecord unify r r' of
             Nothing -> unifyErr
             Just unifiers -> sequence unifiers >> return ()
    _ -> unifyErr

occursIn :: TempVar -> Type -> Bool
occursIn v t = TempVar v `elem` freeTyVars t

zonk :: HasTypeVars a => a -> InferM a
zonk x = subFreeTVs lookupVar x

lookupVar :: VarName -> InferM Type
lookupVar (TempVar v) = do
  mty <- gets $ M.lookup v . subst
  case mty of Nothing -> return $ TypeVar (FV (TempVar v))
              Just ty -> do ty' <- zonk ty
                            modify $ setSubst (M.insert v ty')
                            return ty'
lookupVar v = return (TypeVar (FV v))

setSubst :: (Subst -> Subst) -> InferState -> InferState
setSubst update state = state { subst = update (subst state) }

setTempEnv :: (TempEnv -> TempEnv) -> InferState -> InferState
setTempEnv update state = state { tempEnv = update (tempEnv state) }

instantiateTypeV :: [VarName] -> Type -> Type
instantiateTypeV vs t = instantiateTVs (map (TypeVar . FV) vs) t
