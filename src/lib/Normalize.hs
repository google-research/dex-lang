-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

module Normalize (normalizeModule) where

import Control.Monad
import Control.Monad.Reader
import Data.Foldable
import Data.Bifunctor

import Env
import Syntax
import Cat
import PPrint
import Type
import Embed
import Subst
import Record

type NormM a = ReaderT SubstEnv Embed a

normalizeModule :: FModule -> Module
normalizeModule (Module bid (imports, exports) decls) =
  Module bid (desugarSig imports, desugarSig exports) $ wrapDecls decls' ans
  where
    desugarSig = fmap (fmap $ bimap desugarType id)
    outFVars = [FVar (v:>ty) | (v:>L ty) <- exports]
    outTuple = FPrimExpr $ ConExpr $ RecCon $ Tup outFVars
    (ans, decls') = runNormM $ normalize $ wrapFDecls decls outTuple

runNormM :: NormM a -> (a, [Decl])
runNormM m = (ans, decls)
  where (ans, (_, decls)) = runEmbed (runReaderT m mempty) mempty

normalize :: FExpr -> NormM Atom
normalize expr = case expr of
  FDecl decl body -> do
    env <- normalizeDecl decl
    extendR env $ normalize body
  FVar v -> lookupVar v
  FPrimExpr (OpExpr (SumCase sumVal lBody rBody)) -> do
    ~(Tup [side, lInput, rInput]) <- unpackRec =<< normalize sumVal
    lOutput <- app lBody lInput
    rOutput <- app rBody rInput
    emit $ Select (getType lOutput) side lOutput rOutput
    where
      app body arg =
        let lam = FPrimExpr $ ConExpr $ Lam NonLin noEffect body in
        normalize $ FPrimExpr $ OpExpr $ App NonLin lam $ toAtomicFExpr arg
  FPrimExpr (OpExpr op) ->
    traverseExpr op substType normalize normalizeLam >>= emit
  FPrimExpr (ConExpr (SumCon ty' e' side)) -> do
    other <- arbitraryValue <$> substType ty'
    value <- normalize e'
    return $ Con $ RecCon $ Tup $ case side of
      Left  _ -> [Con $ Lit $ BoolLit True, value, other]
      Right _ -> [Con $ Lit $ BoolLit False, other, value]
  FPrimExpr (ConExpr con) ->
    liftM Con $ traverseExpr con substType normalize normalizeLam
  Annot    e _ -> normalize e
  SrcAnnot e _ -> normalize e

arbitraryValue :: Type -> Atom
arbitraryValue (TabTy a b)                = Con $ AFor a $ arbitraryValue b
arbitraryValue (TC (BaseType RealType))   = Con $ Lit $ RealLit 1.0
arbitraryValue (TC (BaseType IntType))    = Con $ Lit $ IntLit 1
arbitraryValue (TC (BaseType BoolType))   = Con $ Lit $ BoolLit False
arbitraryValue (TC (BaseType StrType))    = Con $ Lit $ StrLit ""
arbitraryValue (TC (RecType r))           = Con $ RecCon $ fmap arbitraryValue r
-- XXX: This might not be strictly legal, because those types might have no inhabitants!
arbitraryValue t@(TC (IndexRange _ _ _))  = Con $ AsIdx t $ Con $ Lit $ IntLit 0
arbitraryValue t@(TC (IntRange _ _))      = Con $ AsIdx t $ Con $ Lit $ IntLit 0
arbitraryValue t                          = Con $ AsIdx t $ Con $ Lit $ IntLit 0
-- TODO: If if conforms to IdxSet then we can just return AsIdx
--arbitraryValue t = error $ "arbitraryValue only supports types that conform to Data, but got: " ++ pprint t

lookupVar :: Var -> NormM Atom
lookupVar v = do
  env <- ask
  case envLookup env v of
     Nothing    -> Var <$> traverse substType v
     Just (L x) -> return x
     Just (T _) -> error $ "Lookup failed: " ++ pprint v

normalizeLam :: FLamExpr -> NormM LamExpr
normalizeLam (FLamExpr p body) = do
  b <- normalizePat p
  buildLamExpr b $ \x -> do
    env <- bindPat p x
    extendR env $ normalize body

normalizePat :: Pat -> NormM Var
normalizePat p = do
  ty <- getType <$> traverse (traverse substType) p
  let v' = case toList p of (v:>_):_ -> v
                            []       -> NoName
  return $ v':>ty

bindPat :: Pat -> Atom -> NormM SubstEnv
bindPat (RecLeaf v) x = return $ v @> L x
bindPat (RecTree r) xs =
  liftM fold $ flip traverse (recNameVals r) $ \(i, p) -> do
    x <- nRecGet xs i
    bindPat p x

normalizeDecl :: FDecl -> NormM SubstEnv
normalizeDecl decl = case decl of
  LetMono p bound -> do
    xs <- normalize bound  -- TODO: preserve names
    bindPat p xs
  LetPoly v tlam -> do
    x <- normalizeTLam tlam
    return $ v @> L x
  _ -> error $ "Shouldn't this left: " ++ pprint decl

normalizeTLam ::FTLam -> NormM Atom
normalizeTLam (FTLam tvs qs body) =
  buildTLam tvs $ \tys -> do
    qs' <- mapM substNorm qs
    let env = fold [tv @> T ty | (tv, ty) <- zip tvs tys]
    body' <- extendR env $ normalize body
    return (qs', body')

desugarType :: Type -> Type
desugarType (SumTy l r) = RecTy $ Tup $ [TC $ BaseType BoolType, l, r]
desugarType tv@(TypeVar _) = tv
desugarType (ArrowType l (Pi a (eff, b))) = ArrowType l $ Pi (desugarType a) (eff, desugarType b)
desugarType (TabType (Pi a b)) = TabType $ Pi (desugarType a) (desugarType b)
desugarType (Forall vs qs t)   = Forall vs qs $ desugarType t
desugarType (TypeAlias vs t)   = TypeAlias vs $ desugarType t
desugarType (TC con)           = TC $ fmapTyCon con desugarType id
desugarType eff@(Effect _ _)   = eff
desugarType NoAnn = NoAnn

substType :: Type -> NormM Type
substType t = desugarType <$> substNorm t

substNorm :: Subst a => a -> NormM a
substNorm x = do
  env <- ask
  scope <- embedScope
  return $ subst (env, scope) x
