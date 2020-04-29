-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

module Simplify (simplifyModule) where

import Control.Monad
import Control.Monad.Reader

import Autodiff
import Env
import Syntax
import Cat
import Embed
import Record
import Subst
import Type

type SimpEnv = SubstEnv
data SimpOpts = SimpOpts { preserveDerivRules :: Bool }
type SimplifyM a = ReaderT SimpEnv (ReaderT (TopEnv, SimpOpts) Embed) a

simplifyModule :: TopEnv -> Module -> Module
simplifyModule env m = simplifyModuleOpts (SimpOpts False) env $
                       simplifyModuleOpts (SimpOpts True ) env $ m

simplifyModuleOpts :: SimpOpts -> TopEnv -> Module -> Module
simplifyModuleOpts opts env (Module bid (_, exports) m) =
  Module bid (imports, exports) modBody
  where
    (ans', (_, decls)) = flip runEmbed mempty $ flip runReaderT (env, opts) $
                         flip runReaderT mempty $ simplifyModBody m
    modBody = ModBody decls ans'
    imports = freeVars modBody

simplifyModBody :: ModBody -> SimplifyM TopEnv
simplifyModBody (ModBody decls result) = do
  env <- catFold simplifyDecl decls
  extendR env $ substEmbed result

simplify :: Expr -> SimplifyM Atom
simplify expr = case expr of
  Decl decl body -> do
    env <- simplifyDecl decl
    extendR env $ simplify body
  CExpr e -> simplifyCExpr e
  Atom x -> simplifyAtom x

simplifyAtom :: Atom -> SimplifyM Atom
simplifyAtom atom = case atom of
  Var v -> do
    -- TODO: simplify this by requiring different namespaces for top/local vars
    (topEnv, opts) <- lift ask
    localEnv <- ask
    case envLookup localEnv v of
      Just ~(L x) -> deShadow x
      Nothing -> case envLookup (topSubstEnv topEnv) v of
        Just ~(L x)
          | preserveDerivRules opts && v `isin` linRules topEnv -> substEmbed atom
          | otherwise -> dropSub $ simplifyAtom x
        _             -> substEmbed atom
  -- We don't simplify bodies of lam/tlam because we'll beta-reduce them soon.
  TLam _ _ _      -> substEmbed atom
  Con (Lam _ _ _) -> substEmbed atom
  Con con -> liftM Con $ traverseExpr con substEmbed simplifyAtom
                       $ error "Shouldn't have lambda left"

-- Unlike `substEmbed`, this simplifies under the binder too.
simplifyLam :: LamExpr -> SimplifyM (LamExpr, Maybe (Atom -> SimplifyM Atom))
simplifyLam (LamExpr b body) = do
  b' <- substEmbed b
  if isData (getType body)
    then do
      lam <- buildLamExpr b' $ \x -> extendR (b @> L x) $ simplify body
      return (lam, Nothing)
    else do
      (lam, recon) <- buildLamExprAux b' $ \x -> extendR (b @> L x) $ do
        (body', (scope, decls)) <- scoped $ simplify body
        extend (mempty, decls)
        return $ separateDataComponent scope body'
      return $ (lam, Just recon)

separateDataComponent :: (MonadCat EmbedEnv m)
                      => Scope -> Atom -> (Atom, Atom -> m Atom)
separateDataComponent localVars atom = (TupVal $ map Var vs, recon)
  where
    vs = [v:>ty | (v, L ty) <- envPairs $ localVars `envIntersect` freeVars atom]
    recon :: MonadCat EmbedEnv m => Atom -> m Atom
    recon xs = do
      ~(Tup xs') <- unpackRec xs
      scope <- looks fst
      return $ subst (newLEnv vs xs', scope) atom

reconstructAtom :: MonadCat EmbedEnv m
                => Maybe (Atom -> m Atom) -> Atom -> m Atom
reconstructAtom recon x = case recon of
  Nothing -> return x
  Just f  -> f x

-- TODO: come up with a coherent strategy for ordering these various reductions
simplifyCExpr :: CExpr -> SimplifyM Atom
simplifyCExpr expr = do
  expr' <- traverseExpr expr substEmbed simplifyAtom simplifyLam
  case expr' of
    Linearize (lam, _) -> do
      (topEnv, _) <- lift ask
      scope <- looks fst
      -- TODO: simplify the result to remove functions introduced by linearization
      return $ linearize topEnv scope lam
    Transpose (lam, _) -> do
      scope <- looks fst
      return $ transposeMap scope lam
    RunReader r (lam, recon) -> do
      ans <- emit $ RunReader r lam
      reconstructAtom recon ans
    RunWriter (lam, recon) -> do
      (ans, w) <- fromPair =<< emit (RunWriter lam)
      ans' <- reconstructAtom recon ans
      return $ PairVal ans' w
    RunState s (lam, recon) -> do
      (ans, s') <- fromPair =<< emit (RunState s lam)
      ans' <- reconstructAtom recon ans
      return $ PairVal ans' s'
    App _ (Con (Lam _ _ (LamExpr b body))) x -> do
      dropSub $ extendR (b @> L x) $ simplify body
    TApp (TLam tbs _ body) ts -> do
      dropSub $ extendR (newTEnv tbs ts) $ simplify body
    RecGet (RecVal r) i -> return $ recGet r i
    Select ty p x y -> selectAt ty p x y
    _ -> emit $ fmapExpr expr' id id fst

simplifyDecl :: Decl -> SimplifyM SimpEnv
simplifyDecl decl = case decl of
  Let b bound -> do
    x <- simplifyCExpr bound
    return $ b @> L x

dropSub :: SimplifyM a -> SimplifyM a
dropSub m = local mempty m
