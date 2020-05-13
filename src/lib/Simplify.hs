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
type SimplifyM a = ReaderT SimpEnv (ReaderT ((SubstEnv, RuleEnv), SimpOpts) Embed) a

simplifyModule :: SubstEnv -> RuleEnv -> Module -> (Module, SubstEnv)
simplifyModule substEnv rulesEnv m = (mOut', subst (envOut', mempty) envOut)
  where (mOut , envOut ) = simplifyModuleOpts (SimpOpts True ) (substEnv, rulesEnv) m
        (mOut', envOut') = simplifyModuleOpts (SimpOpts False) (substEnv, rulesEnv) mOut

simplifyModuleOpts :: SimpOpts -> (SubstEnv, RuleEnv)
                   -> Module -> (Module, SubstEnv)
simplifyModuleOpts opts env (Module bid (_, exports) expr) =
  (Module bid (imports', (fmap (fmap L) exports')) expr', outEnv)
  where
    (exports', expr', results) = runSimplifyM opts env $ simplifyTop expr
    imports' = map (uncurry (:>)) $ envPairs $ freeVars expr'
    outEnv = newLEnv exports results

runSimplifyM :: SimpOpts -> (SubstEnv, RuleEnv) -> SimplifyM a -> a
runSimplifyM opts env m =
  fst $ flip runEmbed mempty $ flip runReaderT (env, opts) $
    flip runReaderT mempty m

simplifyTop :: Expr -> SimplifyM ([Var], Expr, [Atom])
simplifyTop expr = do
  ~(ans@(TupVal results), (scope, decls)) <- scoped $ simplify expr
  let vs = [v:>ty | (v, L ty) <- envPairs $ scope `envIntersect` freeVars ans]
  let expr' = wrapDecls decls $ TupVal $ map Var vs
  return (vs, expr', results)  -- no need to choose fresh names

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
    ((topEnv, rulesEnv), opts) <- lift ask
    localEnv <- ask
    case envLookup localEnv v of
      Just ~(L x) -> deShadow x <$> embedScope
      Nothing -> case envLookup topEnv v of
        Just ~(L x)
          | preserveDerivRules opts && v `isin` rulesEnv -> substEmbed atom
          | otherwise -> dropSub $ simplifyAtom x
        _             -> substEmbed atom
  -- We don't simplify bodies of lam/tlam because we'll beta-reduce them soon.
  TLam _ _ _      -> substEmbed atom
  Con (Lam _ _ _) -> substEmbed atom
  Con (AnyValue (TabTy a b)) -> Con . AFor a <$> mkAny b
  Con (AnyValue (RecTy r))   -> RecVal <$> mapM mkAny r
  Con (AnyValue (SumTy l r)) -> do
    Con <$> (SumCon <$> mkAny (TC $ BaseType BoolType) <*> mkAny l <*> mkAny r)
  Con con -> liftM Con $ traverseExpr con substEmbed simplifyAtom
                       $ error "Shouldn't have lambda left"
  where mkAny t = Con . AnyValue <$> substEmbed t >>= simplifyAtom

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
      rulesEnv <- lift $ asks (snd . fst)
      scope <- looks fst
      -- TODO: simplify the result to remove functions introduced by linearization
      return $ linearize rulesEnv scope lam
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
    SumCase c (lBody, _) (rBody, _) -> do
      l <- projApp lBody True
      r <- projApp rBody False
      isLeft <- simplRec $ SumTag c
      emit $ Select (getType l) isLeft l r
      where
        simplRec = dropSub . simplifyCExpr
        projApp body isLeft = do
          cComp <- simplRec $ SumGet c isLeft
          simplRec $ App NonLin (Con $ Lam NonLin noEffect body) cComp
    App _ (Con (Lam _ _ (LamExpr b body))) x -> do
      dropSub $ extendR (b @> L x) $ simplify body
    TApp (TLam tbs _ body) ts -> do
      dropSub $ extendR (newTEnv tbs ts) $ simplify body
    RecGet (RecVal r) i -> return $ recGet r i
    SumGet (SumVal _ l r) getLeft -> return $ if getLeft then l else r
    SumTag (SumVal s _ _) -> return $ s
    Select ty p x y -> selectAt ty p x y
    _ -> emit $ fmapExpr expr' id id fst

simplifyDecl :: Decl -> SimplifyM SimpEnv
simplifyDecl decl = case decl of
  Let b bound -> do
    x <- simplifyCExpr bound
    return $ b @> L x

dropSub :: SimplifyM a -> SimplifyM a
dropSub m = local mempty m
