-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

module DeShadow (sourcePass, deShadowPass) where

import Control.Monad.Reader
import Control.Monad.Except hiding (Except)

import Env
import Syntax
import Pass
import Fresh
import PPrint
import Cat
import Parser
import Serialize

type DeShadowM a = ReaderT DeShadowEnv (FreshRT (Either Err)) a
type DeShadowCat a = (CatT (DeShadowEnv, FreshScope) (Either Err)) a
type DeShadowEnv = (Env Name, Env Type)

sourcePass :: TopPass SourceBlock UTopDecl
sourcePass = TopPass sourcePass'

sourcePass' :: SourceBlock -> TopPassM () [UTopDecl]
sourcePass' block = case sbContents block of
  UTopDecl (EvalCmd (Command ShowParse expr)) -> emitOutput $ TextOut $ pprint expr
  UTopDecl decl -> return [decl]
  IncludeSourceFile fname -> do
    source <- liftIO $ readFile fname
    liftM concat $ mapM sourcePass' $ parseProg source
  LoadData p fmt fname -> do
    (FlatVal ty refs) <- liftIO (loadDataFile fname fmt)
    let expr = PrimOp (MemRef refs) [ty] []
    return [TopDecl PlainDecl $ LetMono p expr]
  UnParseable _ s -> throwTopErr $ Err ParseErr Nothing s
  _ -> return []

deShadowPass :: TopPass UTopDecl UTopDecl
deShadowPass = TopPass $ \topDecl ->  case topDecl of
  TopDecl ann decl -> do
    decl' <- catToTop $ deShadowDecl decl
    case decl' of
      Just decl'' -> return [TopDecl ann decl'']
      Nothing -> emitOutput NoOutput
  RuleDef ann ty tlam -> liftTop $ do
    ann'  <- deShadowRuleAnn ann
    ty'   <- deShadowSigmaType ty
    tlam' <- deShadowTLam tlam
    return [RuleDef ann' ty' tlam']
  EvalCmd (Command cmd expr) -> do
    expr' <- liftTop $ deShadowExpr expr
    case cmd of
      ShowDeshadowed -> emitOutput $ TextOut $ show expr'
      _ -> return [EvalCmd (Command cmd expr')]

liftTop :: DeShadowM a -> TopPassM (DeShadowEnv, FreshScope) a
liftTop m = do
  (env, scope) <- look
  liftExceptTop $ runFreshRT (runReaderT m env) scope

deShadowExpr :: UExpr -> DeShadowM UExpr
deShadowExpr expr = case expr of
  Lit x -> return (Lit x)
  Var v ann tyArgs -> do
    v' <- lookupLVar v
    ann' <- deShadowAnn ann
    tyArgs' <- mapM deShadowType tyArgs
    return $ Var v' ann' tyArgs'
  PrimOp b ts args -> liftM2 (PrimOp b) (mapM deShadowType ts) (traverse recur args)
  Decl decl body ->
    withCat (deShadowDecl decl) $ \decl' -> do
      body' <- recur body
      return $ case decl' of Nothing -> body'
                             Just decl'' -> Decl decl'' body'
  Lam l p body ->
    withCat (deShadowPat p) $ \p' ->
      liftM (Lam l p') (recur body)
  App fexpr arg -> liftM2 App (recur fexpr) (recur arg)
  For p body ->
    withCat (deShadowPat p) $ \p' ->
      liftM (For p') (recur body)
  Get e v -> liftM2 Get (recur e) (recur v)
  RecCon k r -> liftM (RecCon k) $ traverse recur r
  TabCon NoAnn xs -> liftM (TabCon NoAnn) (mapM recur xs)
  Annot body ty -> liftM2 Annot (recur body) (deShadowType ty)
  SrcAnnot e pos -> liftM (flip SrcAnnot pos) (recur e)
  Pack e ty exTy -> liftM3 Pack (recur e) (deShadowType ty) (deShadowType exTy)
  IdxLit n i     -> return $ IdxLit n i
  TabCon (Ann _) _ -> error "No annotated tabcon in source language"
  where recur = deShadowExpr

deShadowRuleAnn :: RuleAnn -> DeShadowM RuleAnn
deShadowRuleAnn (LinearizationDef v) = liftM LinearizationDef (lookupLVar v)

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
deShadowDecl (TyDef TyAlias v ty) = do  -- TODO: deal with capture
  ty' <- toCat $ deShadowType ty
  extend (asSnd (v @> ty'), v@>())
  return Nothing
deShadowDecl (TyDef NewType v ty) = do
  ty' <- toCat $ deShadowType ty
  extend (asSnd (v @> TypeVar v), mempty)
  return (Just $ TyDef NewType v ty')  -- assumes top-level only

deShadowTLam :: UTLam -> DeShadowM UTLam
deShadowTLam (TLam tbs body) = do
  withCat (traverse freshTBinder tbs) $ \tbs' ->
    liftM (TLam tbs') (deShadowExpr body)

deShadowPat :: UPat -> DeShadowCat UPat
deShadowPat pat = traverse freshBinder pat

lookupLVar :: Name -> DeShadowM Name
lookupLVar v = do
  v' <- asks $ flip envLookup v . fst
  case v' of
    Nothing  -> throw UnboundVarErr $ pprint v
    Just v'' -> return v''

freshBinder :: UBinder -> DeShadowCat UBinder
freshBinder (v:>ann) = do
  ann' <- toCat $ deShadowAnn ann
  freshBinderP (v:>ann')

freshBinderP :: BinderP a -> DeShadowCat (BinderP a)
freshBinderP (v:>ann) = do
  shadowed <- looks $ (v `isin`) . fst . fst
  if shadowed && v /= "_"
    then throw RepeatedVarErr (pprint v)
    else return ()
  v' <- looks $ rename v . snd
  extend (asFst (v@>v'), v'@>())
  return (v':>ann)

freshTBinder :: TBinder -> DeShadowCat TBinder
freshTBinder (v:>k) = do
  shadowed <- looks $ (v `isin`) . snd . fst
  if shadowed && v /= "_"
    then throw RepeatedVarErr (pprint v)
    else return ()
  v' <- looks $ rename v . snd
  extend (asSnd (v@>TypeVar v'), v'@>())
  return (v':>k)

deShadowAnn :: Ann -> DeShadowM Ann
deShadowAnn NoAnn = return NoAnn
deShadowAnn (Ann ty) = liftM Ann (deShadowType ty)

deShadowType :: Type -> DeShadowM Type
deShadowType ty = case ty of
  BaseType _ -> return ty
  TypeVar v  -> do
    (vsub, tsub) <- ask
    case envLookup tsub v of
      Just ty' -> return ty'
      Nothing -> throw UnboundVarErr $ "type variable \"" ++ pprint v ++ "\"" ++
                   (if v `isin` vsub
                       then " (a term variable of the same name is in scope)"
                       else "")
  ArrType l a b -> liftM2 (ArrType l) (recur a) (recur b)
  TabType a b -> liftM2 TabType (recur a) (recur b)
  RecType k r   -> liftM (RecType k) $ traverse recur r
  Exists body -> liftM Exists $ recur body
  IdxSetLit _ -> return ty
  BoundTVar _ -> return ty
  Mult      _ -> return ty
  where recur = deShadowType

deShadowSigmaType :: SigmaType -> DeShadowM SigmaType
deShadowSigmaType (Forall kinds body) = liftM (Forall kinds) (deShadowType body)

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
