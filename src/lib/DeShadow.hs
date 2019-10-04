{-# LANGUAGE FlexibleContexts #-}

module DeShadow (sourcePass, deShadowPass) where

import Control.Monad.Reader
import Control.Monad.Except hiding (Except)

import Env
import Syntax
import Pass
import Fresh
import PPrint
import Cat

type DeShadowM a = ReaderT DeShadowEnv (FreshRT (Either Err)) a
type DeShadowCat a = (CatT (DeShadowEnv, FreshScope) (Either Err)) a
type DeShadowEnv = (Env Name, Env Type)

sourcePass :: TopPass SourceBlock UTopDecl
sourcePass = TopPass sourcePass'

sourcePass' :: SourceBlock -> TopPassM () UTopDecl
sourcePass' block = case sbContents block of
  UTopDecl (EvalCmd (Command Parse expr)) -> emitOutput $ TextOut $ pprint expr
  UTopDecl decl -> return decl
  UnParseable s -> throwTopErr $ Err ParseErr Nothing s
  ProseBlock _ -> emitOutput NoOutput
  CommentLine  -> emitOutput NoOutput
  EmptyLines   -> emitOutput NoOutput

deShadowPass :: TopPass UTopDecl UTopDecl
deShadowPass = TopPass $ \topDecl ->  case topDecl of
  TopDecl decl -> do decl' <- catToTop $ deShadowDecl decl
                     case decl' of
                       Just decl'' -> return $ TopDecl decl''
                       Nothing -> emitOutput NoOutput
  EvalCmd (Command cmd expr) -> do
    expr' <- deShadowTop expr
    case cmd of
      Passes -> emitOutput $ TextOut $ "\n\nDeshadowed\n" ++ show expr'
      _ -> return $ EvalCmd (Command cmd expr')

deShadowTop :: UExpr -> TopPassM (DeShadowEnv, FreshScope) UExpr
deShadowTop expr = do
  (env, scope) <- look
  liftExceptTop $ runFreshRT (runReaderT (deShadowExpr expr) env) scope

deShadowExpr :: UExpr -> DeShadowM UExpr
deShadowExpr expr = case expr of
  Lit x -> return (Lit x)
  Var v tys -> liftM2 Var (asks $ lookupSubst v . fst) (mapM deShadowType tys)
  PrimOp b [] args -> liftM (PrimOp b []) (traverse recur args)
  PrimOp _ ts _ -> error $ "Unexpected type args to primop " ++ pprint ts
  Decl decl body ->
    withCat (deShadowDecl decl) $ \decl' -> do
      body' <- recur body
      return $ case decl' of Nothing -> body'
                             Just decl'' -> Decl decl'' body'
  Lam p body ->
    withCat (deShadowPat p) $ \p' ->
      liftM (Lam p') (recur body)
  App fexpr arg -> liftM2 App (recur fexpr) (recur arg)
  For p body ->
    withCat (deShadowPat p) $ \p' ->
      liftM (For p') (recur body)
  Get e v -> liftM2 Get (recur e) (recur v)
  RecCon r -> liftM RecCon $ traverse recur r
  TabCon NoAnn xs -> liftM (TabCon NoAnn) (mapM recur xs)
  Annot body ty -> liftM2 Annot (recur body) (deShadowType ty)
  DerivAnnot e ann -> liftM2 DerivAnnot (recur e) (recur ann)
  SrcAnnot e pos -> liftM (flip SrcAnnot pos) (recur e)
  Pack e ty exTy -> liftM3 Pack (recur e) (deShadowType ty) (deShadowType exTy)
  IdxLit _ _ -> error "Not implemented"
  TabCon (Ann _) _ -> error "No annotated tabcon in source language"
  where recur = deShadowExpr

deShadowDecl :: UDecl -> DeShadowCat (Maybe UDecl)
deShadowDecl (LetMono p bound) = do
  bound' <- toCat $ deShadowExpr bound
  p' <- deShadowPat p
  return $ Just $ LetMono p' bound'
deShadowDecl (LetPoly (v:>ty) tlam) = do
  tlam' <- toCat $ deShadowTLam tlam
  ty' <- toCat $ deShadowSigmaType ty
  b' <- freshBinderP (v:>ty')
  return $ Just $ LetPoly b' tlam'
deShadowDecl (Unpack b tv bound) = do
  bound' <- toCat $ deShadowExpr bound
  tv' <- looks $ rename tv . snd
  extend (asSnd (tv @> TypeVar tv'), tv'@>())
  b' <- freshBinder b
  return $ Just $ Unpack b' tv' bound'
deShadowDecl (TAlias v ty) = do  -- TODO: deal with capture
  ty' <- toCat $ deShadowType ty
  extend (asSnd (v @> ty'), v@>())
  return Nothing

deShadowTLam :: UTLam -> DeShadowM UTLam
deShadowTLam (TLam tbs body) = do
  withCat (traverse freshTBinder tbs) $ \tbs' ->
    liftM (TLam tbs') (deShadowExpr body)

deShadowPat :: UPat -> DeShadowCat UPat
deShadowPat pat = traverse freshBinder pat

freshBinder :: UBinder -> DeShadowCat UBinder
freshBinder (v:>ann) = do
  ann' <- case ann of
            Ann ty -> liftM Ann $ toCat $ deShadowType ty
            NoAnn -> return NoAnn
  freshBinderP (v:>ann')

freshBinderP :: BinderP a -> DeShadowCat (BinderP a)
freshBinderP (v:>ann) = do
  shadowed <- looks $ (v `isin`) . fst . fst
  if shadowed && v /= Name "_" 0
    then throw RepeatedVarErr (" " ++ pprint v)
    else return ()
  v' <- looks $ rename v . snd
  extend (asFst (v@>v'), v'@>())
  return (v':>ann)

freshTBinder :: TBinder -> DeShadowCat TBinder
freshTBinder (v:>k) = do
  shadowed <- looks $ (v `isin`) . snd . fst
  if shadowed && v /= Name "_" 0
    then throw RepeatedVarErr (" " ++ pprint v)
    else return ()
  v' <- looks $ rename v . snd
  extend (asSnd (v@>TypeVar v'), v'@>())
  return (v':>k)

deShadowType :: Type -> DeShadowM Type
deShadowType ty = do
  subst <- asks $ snd
  return $ subType subst ty

deShadowSigmaType :: SigmaType -> DeShadowM SigmaType
deShadowSigmaType (Forall kinds body) = liftM (Forall kinds) (deShadowType body)

subType :: Env Type -> Type -> Type
subType sub ty = case ty of
  BaseType _ -> ty
  TypeVar v  -> case envLookup sub v of Nothing  -> ty
                                        Just ty' -> ty'
  ArrType a b -> ArrType (recur a) (recur b)
  TabType a b -> TabType (recur a) (recur b)
  RecType r   -> RecType $ fmap recur r
  Exists body -> Exists $ recur body
  IdxSetLit _ -> ty
  BoundTVar _ -> ty
  where recur = subType sub

toCat :: DeShadowM a -> DeShadowCat a
toCat m = do
  (env, scope) <- look
  liftEither $ flip runFreshRT scope $ flip runReaderT env $ m

withCat :: DeShadowCat a -> (a -> DeShadowM b) -> DeShadowM b
withCat m cont = do
  env <- ask
  scope <- askFresh
  (ans, (env', scope')) <- liftEither $ flip runCatT (env, scope) m
  extendR env' $ localFresh (<> scope') $ cont ans

catToTop :: DeShadowCat a -> TopPassM (DeShadowEnv, FreshScope) a
catToTop m = do
  env <- look
  (ans, env') <- liftExceptTop $ flip runCatT env m
  extend env'
  return ans
