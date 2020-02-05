-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

module DeShadow (deShadowModule) where

import Control.Monad.Reader
import Control.Monad.Except hiding (Except)

import Env
import Syntax
import Fresh
import PPrint
import Cat
import Type

type DeShadowM a = ReaderT DeShadowEnv (FreshRT (Either Err)) a
type DeShadowCat a = (CatT (DeShadowEnv, FreshScope) (Either Err)) a
type DeShadowEnv = (Env Name, Env Type)

-- TODO: check top-level binders are all unique wrt imports and each other
-- TODO: work through type aliases from incoming top env
deShadowModule :: TopEnv -> FModule -> Except FModule
deShadowModule env (FModule imports decls exports) = do
  decls' <- runFreshRT (runReaderT (deShadowTopDecls decls) env') scope
  return $ FModule imports decls' exports
  where env' = topEnvToDeshadowEnv env
        scope = fmap (const ()) env

topEnvToDeshadowEnv :: TopEnv -> DeShadowEnv
topEnvToDeshadowEnv env = (termEnv, tyEnv)
  where
    env' = fmapNames (,) env
    termEnv = flip envMapMaybe env' $ \x -> case x of
                (v, L _) -> Just v
                _        -> Nothing
    tyEnv = flip envMapMaybe env $ \x -> case x of
                L _  -> Nothing
                T ty -> Just ty

deShadowTopDecls :: [FDecl] -> DeShadowM [FDecl]
deShadowTopDecls [] = return []
deShadowTopDecls (decl : decls) = do
  withCat (deShadowDecl decl) $ \decl' ->
    liftM (decl':) (deShadowTopDecls decls)

deShadowExpr :: FExpr -> DeShadowM FExpr
deShadowExpr expr = case expr of
  FDecl decl body ->
    withCat (deShadowDecl decl) $ \decl' ->
      liftM (FDecl decl') $ recur body
  FVar (v:>ty) tyArgs -> do
    v' <- lookupLVar v
    ty' <- deShadowType ty
    tyArgs' <- mapM deShadowType tyArgs
    return $ FVar (v':>ty') tyArgs'
  FPrimExpr e ->
    liftM FPrimExpr $ traverseExpr e deShadowType deShadowExpr deShadowLam
  Annot body ty  -> liftM2 Annot (recur body) (deShadowType ty)
  SrcAnnot e pos -> liftM (flip SrcAnnot pos) (recur e)
  where recur = deShadowExpr

deShadowRuleAnn :: RuleAnn -> DeShadowM RuleAnn
deShadowRuleAnn (LinearizationDef v) = liftM LinearizationDef (lookupLVar v)

deShadowLam :: FLamExpr -> DeShadowM FLamExpr
deShadowLam (FLamExpr p body) =
  withCat (deShadowPat p) $ \p' ->
    liftM (FLamExpr p') (deShadowExpr body)

deShadowDecl :: FDecl -> DeShadowCat FDecl
deShadowDecl (LetMono p bound) = do
  bound' <- toCat $ deShadowExpr bound
  p' <- deShadowPat p
  return $ LetMono p' bound'
deShadowDecl (LetPoly (v:>ty) tlam) = do
  tlam' <- toCat $ deShadowTLam tlam
  ty' <- toCat $ deShadowType ty
  b' <- freshBinderP (v:>ty')
  return $ LetPoly b' tlam'
deShadowDecl (FRuleDef ann ty tlam) = toCat $
  liftM3 FRuleDef (deShadowRuleAnn ann) (deShadowType ty) (deShadowTLam tlam)
deShadowDecl (TyDef v ty) = do
  -- TODO: handle shadowing from binders
  ty' <- toCat $ deShadowType ty
  extend (asSnd (v @> ty'), v@>())
  return $ TyDef v ty'

deShadowTLam :: FTLam -> DeShadowM FTLam
deShadowTLam (FTLam tbs body) = do
  withCat (traverse freshTBinder tbs) $ \tbs' ->
    liftM (FTLam tbs') (deShadowExpr body)

deShadowPat :: Pat -> DeShadowCat Pat
deShadowPat pat = traverse freshBinder pat

lookupLVar :: Name -> DeShadowM Name
lookupLVar v = do
  v' <- asks $ flip envLookup (v:>()) . fst
  case v' of
    Nothing  -> throw UnboundVarErr $ pprint v
    Just v'' -> return v''

freshBinder :: Var -> DeShadowCat Var
freshBinder (v:>ty) = do
  ann' <- toCat $ deShadowType ty
  freshBinderP (v:>ann')

freshBinderP :: VarP a -> DeShadowCat (VarP a)
freshBinderP v = do
  shadowed <- looks $ (v `isin`) . fst . fst
  if shadowed && varName v /= "_"
    then throw RepeatedVarErr (pprint (varName v))
    else return ()
  v' <- looks $ rename v . snd
  extend (asFst (v@> varName v'), v'@>())
  return v'

freshTBinder :: TVar -> DeShadowCat TVar
freshTBinder v = do
  shadowed <- looks $ (v `isin`) . snd . fst
  if shadowed && varName v /= "_"
    then throw RepeatedVarErr (pprint v)
    else return ()
  v' <- looks $ rename v . snd
  extend (asSnd (v@> TypeVar v'), v'@>())
  return v'

deShadowType :: Type -> DeShadowM Type
deShadowType ty = case ty of
  BaseType _ -> return ty
  TypeVar v -> do
    (vsub, tsub) <- ask
    case envLookup tsub v of
      Just (TypeAlias ks _ ) ->
          throw TypeErr $ pprint v ++ " must be applied to " ++
                          show (length ks) ++ " type variables"
      Just ty' -> return ty'
      Nothing -> throw UnboundVarErr $ "type variable \"" ++ pprint v ++ "\"" ++
                   (if v `isin` vsub
                       then " (a term variable of the same name is in scope)"
                       else "")
  TypeApp f args -> do
    args' <- mapM deShadowType args
    case f of
      TypeVar tv -> do
        sub <- asks snd
        case envLookup sub tv of
          Just (TypeAlias ks ty') -> do
            unless (length ks == length args') $ throw TypeErr $
                "Expected " ++ show (length ks) ++ " type args in " ++ pprint ty
            return $ instantiateTVs args' ty'
          Just ty' -> return ty'
          Nothing -> throw UnboundVarErr $ "type variable \"" ++ pprint tv ++ "\""
      _ -> throw TypeErr $ "Unexpected type application: " ++ pprint ty
  ArrType l a b -> liftM2 (ArrType l) (recur a) (recur b)
  TabType a b -> liftM2 TabType (recur a) (recur b)
  RecType r   -> liftM RecType $ traverse recur r
  Monad eff a -> liftM2 Monad (traverse recur eff) (recur a)
  Lens a b    -> liftM2 Lens (recur a) (recur b)
  Forall    kinds body -> liftM (Forall    kinds) (deShadowType body)
  TypeAlias kinds body -> liftM (TypeAlias kinds) (deShadowType body)
  IdxSetLit _ -> return ty
  BoundTVar _ -> return ty
  Mult _      -> return ty
  NoAnn       -> return ty
  where recur = deShadowType

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
