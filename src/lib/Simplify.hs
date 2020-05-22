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
import PPrint
import Util (uncurry3)

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
  (Module bid (imports', exports') expr', outEnv)
  where
    (exports', expr', results) = runSimplifyM opts env $ simplifyTop expr
    imports' = map (uncurry (:>)) $ envPairs $ freeVars expr'
    outEnv = newEnv exports results

runSimplifyM :: SimpOpts -> (SubstEnv, RuleEnv) -> SimplifyM a -> a
runSimplifyM opts env m =
  fst $ flip runEmbed mempty $ flip runReaderT (env, opts) $
    flip runReaderT mempty m

simplifyTop :: Expr -> SimplifyM ([Var], Expr, [Atom])
simplifyTop expr = do
  ~(ans@(TupVal results), (scope, decls)) <- scoped $ simplify expr
  let vs = map (uncurry (:>)) $ envPairs $ scope `envIntersect` freeVars ans
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
      Just x -> deShadow x <$> embedScope
      Nothing -> case envLookup topEnv v of
        Just x
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
  _ -> error "Not implemented"
  where mkAny t = Con . AnyValue <$> substEmbed t >>= simplifyAtom

-- Unlike `substEmbed`, this simplifies under the binder too.
simplifyLam :: LamExpr -> SimplifyM (LamExpr, Maybe (Atom -> SimplifyM Atom))
simplifyLam (LamExpr b body) = do
  b' <- substEmbed b
  if isData (getType body)
    then do
      lam <- buildLamExpr b' $ \x -> extendR (b@>x) $ simplify body
      return (lam, Nothing)
    else do
      (lam, recon) <- buildLamExprAux b' $ \x -> extendR (b@>x) $ do
        (body', (scope, decls)) <- scoped $ simplify body
        extend (mempty, decls)
        return $ separateDataComponent scope body'
      return $ (lam, Just recon)

separateDataComponent :: (MonadCat EmbedEnv m)
                      => Scope -> Atom -> (Atom, Atom -> m Atom)
separateDataComponent localVars atom = (TupVal $ map Var vs, recon)
  where
    vs = map (uncurry (:>)) $ envPairs $ localVars `envIntersect` freeVars atom
    recon :: MonadCat EmbedEnv m => Atom -> m Atom
    recon xs = do
      ~(Tup xs') <- unpackRec xs
      scope <- looks fst
      return $ subst (newEnv vs xs', scope) atom

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
    Cmp Equal t a b  -> resolveEq     t a b
    Cmp op    t  a b -> resolveOrd op t a b
    App _ (Con (Lam _ _ (LamExpr b body))) x -> do
      dropSub $ extendR (b@>x) $ simplify body
    TApp (TLam tbs _ body) ts -> do
      dropSub $ extendR (newEnv tbs ts) $ simplify body
    RecGet (RecVal r) i -> return $ recGet r i
    SumGet (SumVal _ l r) getLeft -> return $ if getLeft then l else r
    SumTag (SumVal s _ _) -> return $ s
    Select ty p x y -> selectAt ty p x y
    _ -> emit $ fmapExpr expr' id id fst

resolveEq :: Type -> Atom -> Atom -> SimplifyM Atom
resolveEq t x y = case t of
  IntTy     -> emit $ ScalarBinOp (ICmp Equal) x y
  RealTy    -> emit $ ScalarBinOp (FCmp Equal) x y
  RecTy ts  -> do
    xs <- unpackRec x
    ys <- unpackRec y
    equals <- mapM (uncurry3 resolveEq) $ recZipWith3 (,,) ts xs ys
    foldM andE (BoolVal True) equals
  -- instance Eq a => Eq n=>a
  TabTy ixty elty -> do
    writerLam <- buildLamExpr ("ref":> RefTy RealTy) $ \ref -> do
      forLam <- buildLamExpr ("i":>ixty) $ \i -> do
        (x', y') <- (,) <$> nTabGet x i <*> nTabGet y i
        eqReal <- boolToReal =<< resolveEq elty x' y'
        emit $ PrimEffect ref $ MTell eqReal
      emit $ For Fwd forLam
    idxSetSize <- intToReal =<< emit (IdxSetSize ixty)
    total <- snd <$> (fromPair =<< emit (RunWriter writerLam))
    emit $ Cmp Equal RealTy total idxSetSize
  -- instance (Eq a, Eq b) => Eq (Either a b)
  SumTy lty rty -> do
    xt <- emit $ SumTag x
    yt <- emit $ SumTag y
    tagsEq <- resolveEq BoolTy xt yt
    lEq <- compareSide True
    rEq <- compareSide False
    sideEq <- select BoolTy xt lEq rEq
    andE tagsEq sideEq
    where
      compareSide isLeft = do
        xe <- emit $ SumGet x isLeft
        ye <- emit $ SumGet y isLeft
        resolveEq (if isLeft then lty else rty) xe ye
  -- instance Idx a => Eq a
  BoolTy                -> idxEq
  TC (IntRange _ _)     -> idxEq
  TC (IndexRange _ _ _) -> idxEq
  _ -> error $ pprint t ++ " doesn't implement Eq"
  where
    idxEq = do
      xi <- emit $ IndexAsInt x
      yi <- emit $ IndexAsInt y
      emit $ ScalarBinOp (ICmp Equal) xi yi

resolveOrd :: CmpOp -> Type -> Atom -> Atom -> SimplifyM Atom
resolveOrd op t x y = case t of
  IntTy  -> emit $ ScalarBinOp (ICmp op) x y
  RealTy -> emit $ ScalarBinOp (FCmp op) x y
  TC con -> case con of
    IntRange _ _     -> idxOrd
    IndexRange _ _ _ -> idxOrd
    _ -> error $ pprint t ++ " doesn't implement Ord"
  _ -> error $ pprint t ++ " doesn't implement Ord"
  where
    idxOrd = do
      xi <- emit $ IndexAsInt x
      yi <- emit $ IndexAsInt y
      emit $ ScalarBinOp (ICmp op) xi yi

simplifyDecl :: Decl -> SimplifyM SimpEnv
simplifyDecl decl = case decl of
  Let b bound -> do
    x <- simplifyCExpr bound
    return $ b @> x

dropSub :: SimplifyM a -> SimplifyM a
dropSub m = local mempty m
