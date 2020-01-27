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
import Data.Foldable

import Env
import Syntax
import Pass
import Fresh
import PPrint
import Cat
import Parser
import Serialize
import Subst

type DeShadowM a = ReaderT DeShadowEnv (FreshRT (Either Err)) a
type DeShadowCat a = (CatT (DeShadowEnv, FreshScope) (Either Err)) a
type DeShadowEnv = (Env Name, Env ([TVar], Type))

sourcePass :: TopPass SourceBlock TopDecl
sourcePass = TopPass sourcePass'

sourcePass' :: SourceBlock -> TopPassM () [TopDecl]
sourcePass' block = case sbContents block of
  UTopDecl (EvalCmd (Command ShowParse expr)) -> emitOutput $ TextOut $ pprint expr
  UTopDecl decl -> return [decl]
  IncludeSourceFile fname -> do
    source <- liftIOTop $ readFile fname
    liftM concat $ mapM sourcePass' $ parseProg source
  LoadData p fmt fname -> do
    (FlatVal ty refs) <- liftIOTop $ loadDataFile fname fmt
    let expr = FPrimExpr $ PrimConExpr (MemRef ty refs)
    return [TopDecl PlainDecl $ LetMono p expr]
  UnParseable _ s -> throwTopErr $ Err ParseErr Nothing s
  _ -> return []

deShadowPass :: TopPass TopDecl TopDecl
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

deShadowExpr :: FExpr -> DeShadowM FExpr
deShadowExpr expr = case expr of
  FDecl decl body ->
    withCat (deShadowDecl decl) $ \decl' -> do
      body' <- recur body
      return $ case decl' of Nothing -> body'
                             Just decl'' -> FDecl decl'' body'
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

deShadowDecl :: FDecl -> DeShadowCat (Maybe FDecl)
deShadowDecl (LetMono p bound) = do
  bound' <- toCat $ deShadowExpr bound
  p' <- deShadowPat p
  return $ Just $ LetMono p' bound'
deShadowDecl (LetPoly (v:>ty) tlam) = do
  tlam' <- toCat $ deShadowTLam tlam
  ty' <- toCat $ deShadowSigmaType ty
  b' <- freshBinderP (v:>ty')
  return $ Just $ LetPoly b' tlam'
deShadowDecl (FUnpack b tv bound) = do
  bound' <- toCat $ deShadowExpr bound
  tv' <- looks $ rename tv . snd
  extend (asSnd (tv @> ([], TypeVar tv')), tv'@>())
  b' <- freshBinder b
  return $ Just $ FUnpack b' tv' bound'
deShadowDecl (TyDef TyAlias v bs ty) = do  -- TODO: deal with capture
  -- TODO: handle shadowing from binders
  let env = fold [tv@>([], TypeVar tv) | tv <- bs]
  ty' <- toCat $ extendR (asSnd env) $ deShadowType ty
  extend (asSnd (v @> (bs, ty')), v@>())
  return Nothing
deShadowDecl (TyDef NewType v [] ty) = do
  ty' <- toCat $ deShadowType ty
  extend (asSnd (v @> ([], TypeVar v)), mempty)
  return (Just $ TyDef NewType v [] ty')  -- assumes top-level only
deShadowDecl (TyDef NewType _ _ _) = error "Parametric newtype not implemented"

deShadowTLam :: TLam -> DeShadowM TLam
deShadowTLam (TLam tbs body) = do
  withCat (traverse freshTBinder tbs) $ \tbs' ->
    liftM (TLam tbs') (deShadowExpr body)

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
  extend (asSnd (v@>([], TypeVar v')), v'@>())
  return v'

deShadowType :: Type -> DeShadowM Type
deShadowType ty = case ty of
  BaseType _ -> return ty
  TypeVar v -> do
    (vsub, tsub) <- ask
    case envLookup tsub v of
      Just ([], ty') -> return ty'
      Just (bs, _  ) -> throw TypeErr $ pprint v ++ " must be applied to " ++
                          show (length bs) ++ " type variables"
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
          Just (bs, ty') -> do
            unless (length bs == length args') $ throw TypeErr $
              "Expected " ++ show (length bs) ++ " type args in " ++ pprint ty
            let env = fold [v@>T arg | (v, arg) <- zip bs args']
            return $ subst (env, mempty) ty'
          Nothing -> throw UnboundVarErr $ "type variable \"" ++ pprint tv ++ "\""
      _ -> throw TypeErr $ "Unexpected type application: " ++ pprint ty
  ArrType l a b -> liftM2 (ArrType l) (recur a) (recur b)
  TabType a b -> liftM2 TabType (recur a) (recur b)
  RecType k r -> liftM (RecType k) $ traverse recur r
  Monad eff a -> liftM2 Monad (traverse recur eff) (recur a)
  Lens a b    -> liftM2 Lens (recur a) (recur b)
  Exists body -> liftM Exists $ recur body
  IdxSetLit _ -> return ty
  BoundTVar _ -> return ty
  Mult _      -> return ty
  NoAnn       -> return ty
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
