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
import Type
import PPrint

type SimpEnv = SubstEnv
data SimpOpts = SimpOpts { preserveDerivRules :: Bool }
-- The outer SimpEnv is for local variables, while the nested (SubstEnv, RuleEnv) is for globals.
-- Note that you _have to_ apply the local substitution everywhere, because the binders for those
-- variables have been eliminated. In principle the substitution with global env is optional, but
-- in practice it also has to happen sooner or later, because the Imp pass assumes that only array
-- variables are imported.
type SimplifyM a = ReaderT SimpEnv (ReaderT (SubstEnv, SimpOpts) Embed) a

simplifyModule :: SubstEnv -> Module -> (Module, SubstEnv)
simplifyModule substEnv m = simplifyModuleOpts (SimpOpts False) substEnv m

simplifyModuleOpts :: SimpOpts -> SubstEnv -> Module -> (Module, SubstEnv)
simplifyModuleOpts opts env (Module bid _ exports expr) =
  (Module bid imports' exports' expr', outEnv)
  where
    (exports', expr', results) = runSimplifyM opts env $ simplifyTop expr
    imports' = map (uncurry (:>)) $ envPairs $ freeVars expr'
    outEnv = newEnv exports results

runSimplifyM :: SimpOpts -> SubstEnv -> SimplifyM a -> a
runSimplifyM opts env m =
  fst $ flip runEmbed mempty $ flip runReaderT (env, opts) $
    flip runReaderT mempty m

simplifyTop :: Block -> SimplifyM ([Var], Block, [Atom])
simplifyTop block = do
  (ans, (scope, decls)) <- embedScoped $ simplifyBlock block
  let results = ignoreExcept $ fromConsList ans
  let vs = map (uncurry (:>)) $ envPairs $ scope `envIntersect` freeVars ans
  let expr' = wrapDecls decls $ mkConsList $ map Var vs
  return (vs, expr', results)  -- no need to choose fresh names

simplifyBlock :: Block -> SimplifyM Atom
simplifyBlock (Block (decl:decls) result) = do
   env <- simplifyDecl decl
   extendR env $ simplifyBlock body
   where body = Block decls result
simplifyBlock (Block [] result) = simplifyExpr result

simplifyAtom :: Atom -> SimplifyM Atom
simplifyAtom atom = case atom of
  Var v -> do
    -- TODO: simplify this by requiring different namespaces for top/local vars
    (topEnv, opts) <- lift ask
    localEnv <- ask
    case envLookup localEnv v of
      Just x -> deShadow x <$> getScope
      Nothing -> case envLookup topEnv v of
        Just x -> dropSub $ simplifyAtom x
        _      -> substEmbed atom
  -- We don't simplify body of lam because we'll beta-reduce it soon.
  Lam _ -> substEmbed atom
  Pi  _ -> substEmbed atom
  Con (AnyValue (TabTy v b)) -> TabValA v <$> mkAny b
  Con (AnyValue (PairTy a b))-> PairVal <$> mkAny a <*> mkAny b
  Con (AnyValue (SumTy l r)) -> do
    Con <$> (SumCon <$> mkAny (TC $ BaseType BoolType) <*> mkAny l <*> mkAny r)
  Con con -> Con <$> mapM simplifyAtom con
  TC tc -> TC <$> mapM substEmbed tc
  Eff eff -> Eff <$> substEmbed eff
  where mkAny t = Con . AnyValue <$> substEmbed t >>= simplifyAtom

-- Unlike `substEmbed`, this simplifies under the binder too.
simplifyLam :: Atom -> SimplifyM (Atom, Maybe (Atom -> SimplifyM Atom))
simplifyLam atom = substEmbed atom >>= (dropSub . simplifyLam')

simplifyLam' :: Atom -> SimplifyM (Atom, Maybe (Atom -> SimplifyM Atom))
simplifyLam' (Lam (Abs b (arr, body))) = do
  b' <- mapM substEmbed b
  if isData (getType body)
    then liftM (,Nothing) $ do
      buildDepEffLam b' (\x -> extendR (b@>x) $ substEmbed arr)
                        (\x -> extendR (b@>x) $ simplifyBlock body)
    else do
      (lam, recon) <- buildLamAux b'
        ( \x -> extendR (b@>x) $ substEmbed arr)
        $ \x -> extendR (b@>x) $ do
          (body', (scope, decls)) <- embedScoped $ simplifyBlock body
          mapM_ emitDecl decls
          return $ separateDataComponent scope body'
      return $ (lam, Just recon)
simplifyLam' atom = error $ "Not a lambda: " ++ pprint atom

simplifyBinaryLam :: Atom -> SimplifyM Atom
simplifyBinaryLam atom = substEmbed atom >>= (dropSub . simplifyBinaryLam')

simplifyBinaryLam' :: Atom -> SimplifyM Atom
simplifyBinaryLam' (BinaryFunVal b1 b2 eff body) = do
  b1' <- mapM substEmbed b1
  buildLam b1' PureArrow $ \x1 ->
    extendR (b1'@>x1) $ do
      b2' <- mapM substEmbed b2
      buildDepEffLam b2'
        (\x2 -> extendR (b2'@>x2) $ substEmbed (PlainArrow eff))
        (\x2 -> extendR (b2'@>x2) $ simplifyBlock body)
simplifyBinaryLam' atom = error $ "Not a binary lambda: " ++ pprint atom

separateDataComponent :: MonadEmbed m => Scope -> Atom -> (Atom, Atom -> m Atom)
separateDataComponent localVars atom = (mkConsList $ map Var vs, recon)
  where
    vs = map (uncurry (:>)) $ envPairs $ localVars `envIntersect` freeVars atom
    recon :: MonadEmbed m => Atom -> m Atom
    recon xs = do
      xs' <- unpackConsList xs
      scope <- getScope
      return $ subst (newEnv vs xs', scope) atom

simplifyExpr :: Expr -> SimplifyM Atom
simplifyExpr expr = case expr of
  App f x -> do
    x' <- simplifyAtom x
    f' <- simplifyAtom f
    case f' of
      Lam (Abs b (_, body)) ->
        dropSub $ extendR (b@>x') $ simplifyBlock body
      _ -> emit $ App f' x'
  Op  op  -> mapM simplifyAtom op >>= simplifyOp
  Hof hof -> simplifyHof hof
  Atom x  -> simplifyAtom x

-- TODO: come up with a coherent strategy for ordering these various reductions
simplifyOp :: Op -> SimplifyM Atom
simplifyOp op = case op of
  Cmp Equal a b -> resolveEq (getType a) a b
  Cmp cmpOp a b -> resolveOrd cmpOp (getType a) a b
  Fst (PairVal x _) -> return x
  Snd (PairVal _ y) -> return y
  SumGet (SumVal _ l r) left -> return $ if left then l else r
  SumTag (SumVal s _ _) -> return $ s
  Select p x y -> selectAt (getType x) p x y
  _ -> emitOp op

simplifyHof :: Hof -> SimplifyM Atom
simplifyHof hof = case hof of
  For d lam -> do
    ~(lam', Nothing) <- simplifyLam lam
    emit $ Hof $ For d lam'
  Linearize lam -> do
    ~(lam', Nothing) <- simplifyLam lam
    scope <- getScope
    -- TODO: simplify the result to remove functions introduced by linearization
    return $ linearize scope lam'
  Transpose lam -> do
    ~(lam', Nothing) <- simplifyLam lam
    scope <- getScope
    return $ transposeMap scope lam'
  RunReader r lam -> do
    r' <- simplifyAtom r
    lam' <- simplifyBinaryLam lam
    emit $ Hof $ RunReader r' lam'
  RunWriter lam -> do
    lam' <- simplifyBinaryLam lam
    emit $ Hof $ RunWriter lam'
  RunState s lam -> do
    s' <- simplifyAtom s
    lam' <- simplifyBinaryLam lam
    emit $ Hof $ RunState s' lam'
  SumCase c lBody rBody -> do
    ~(lBody', Nothing) <- simplifyLam lBody
    ~(rBody', Nothing) <- simplifyLam rBody
    l <- projApp lBody' True
    r <- projApp rBody' False
    isLeft <- simplRec $ Op $ SumTag c
    emitOp $ Select isLeft l r
    where
      simplRec :: Expr -> SimplifyM Atom
      simplRec = dropSub . simplifyExpr
      projApp f isLeft = do
        cComp <- simplRec $ Op $ SumGet c isLeft
        simplRec $ App f cComp

resolveEq :: Type -> Atom -> Atom -> SimplifyM Atom
resolveEq t x y = case t of
  IntTy     -> emitOp $ ScalarBinOp (ICmp Equal) x y
  RealTy    -> emitOp $ ScalarBinOp (FCmp Equal) x y
  PairTy t1 t2 -> do
    (x1, x2) <- fromPair x
    (y1, y2) <- fromPair y
    p1 <- resolveEq t1 x1 y1
    p2 <- resolveEq t2 x2 y2
    andE p1 p2
  -- instance Eq a => Eq n=>a
  -- TODO: writer with other monoids to avoid this
  TabTy v elty -> do
    writerAns <- emitRunWriter "ref" RealTy $ \ref -> do
      buildFor Fwd ("i":>varType v) $ \i -> do
        (x', y') <- (,) <$> app x i <*> app y i
        eqReal <- boolToReal =<< resolveEq elty x' y'
        emitOp $ PrimEffect ref $ MTell eqReal
    total <- getSnd writerAns
    idxSetSize <- intToReal =<< (emitOp $ IdxSetSize $ varType v)
    emitOp $ ScalarBinOp (FCmp Equal) total idxSetSize
  -- instance (Eq a, Eq b) => Eq (Either a b)
  SumTy lty rty -> do
    xt <- emitOp $ SumTag x
    yt <- emitOp $ SumTag y
    tagsEq <- resolveEq BoolTy xt yt
    lEq <- compareSide True
    rEq <- compareSide False
    sideEq <- select xt lEq rEq
    andE tagsEq sideEq
    where
      compareSide isLeft = do
        xe <- emitOp $ SumGet x isLeft
        ye <- emitOp $ SumGet y isLeft
        resolveEq (if isLeft then lty else rty) xe ye
  -- instance Idx a => Eq a
  BoolTy                -> idxEq
  TC (IntRange _ _)     -> idxEq
  TC (IndexRange _ _ _) -> idxEq
  _ -> error $ pprint t ++ " doesn't implement Eq"
  where
    idxEq = do
      xi <- emitOp $ IndexAsInt x
      yi <- emitOp $ IndexAsInt y
      emitOp $ ScalarBinOp (ICmp Equal) xi yi

resolveOrd :: CmpOp -> Type -> Atom -> Atom -> SimplifyM Atom
resolveOrd op t x y = case t of
  IntTy  -> emitOp $ ScalarBinOp (ICmp op) x y
  RealTy -> emitOp $ ScalarBinOp (FCmp op) x y
  TC con -> case con of
    IntRange _ _     -> idxOrd
    IndexRange _ _ _ -> idxOrd
    _ -> error $ pprint t ++ " doesn't implement Ord"
  _ -> error $ pprint t ++ " doesn't implement Ord"
  where
    idxOrd = do
      xi <- emitOp $ IndexAsInt x
      yi <- emitOp $ IndexAsInt y
      emitOp $ ScalarBinOp (ICmp op) xi yi

simplifyDecl :: Decl -> SimplifyM SimpEnv
simplifyDecl decl = case decl of
  Let b bound -> do
    x <- withNameHint (varName b) $ simplifyExpr bound
    return $ b @> x

dropSub :: SimplifyM a -> SimplifyM a
dropSub m = local mempty m
