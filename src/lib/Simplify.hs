-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleContexts #-}

module Simplify (simplifyModule, evalSimplified) where

import Control.Monad
import Control.Monad.Identity
import Control.Monad.Reader
import Data.Functor
import Data.List (partition)

import Autodiff
import Env
import Syntax
import Cat
import Embed
import Type
import PPrint

type SimplifyM = SubstEmbedT Identity

simplifyModule :: TopEnv -> Module -> Module
simplifyModule scope (Module Core decls _) = do
  let simpDecls = snd $ snd $ runSubstEmbed (simplifyDecls decls) scope
  let isAtomDecl decl = case decl of Let _ _ (Atom _) -> True; _ -> False
  let (declsDone, declsNotDone) = partition isAtomDecl simpDecls
  let bindings = foldMap declAsScope declsDone
  Module Simp declsNotDone bindings
simplifyModule _ (Module ir _ _) = error $ "Expected Core, got: " ++ show ir

evalSimplified :: Monad m => Module -> (Block -> m Atom) -> m Module
evalSimplified (Module Simp [] bindings) _ =
  return $ Module Evaluated [] bindings
evalSimplified (Module Simp decls bindings) evalBlock = do
  let localVars = filter (not . isGlobal) $ envAsVars $ freeVars bindings
  let block = Block decls $ Atom $ mkConsList $ map Var localVars
  vals <- (ignoreExcept . fromConsList) <$> evalBlock block
  return $ Module Evaluated [] $ scopelessSubst (zipEnv localVars vals) bindings
evalSimplified (Module _ _ _) _ =
  error "Not a simplified module"

simplifyDecls :: [Decl] -> SimplifyM SubstEnv
simplifyDecls [] = return mempty
simplifyDecls (decl:rest) = do
  substEnv <- simplifyDecl decl
  substEnv' <- extendR substEnv $ simplifyDecls rest
  return (substEnv <> substEnv')

simplifyDecl :: Decl -> SimplifyM SubstEnv
simplifyDecl (Let ann b expr) = do
  x <- simplifyExpr expr
  if isGlobal b
    then emitTo (varName b) ann (Atom x) $> mempty
    else return $ b @> x

simplifyBlock :: Block -> SimplifyM Atom
simplifyBlock (Block decls result) = do
  substEnv <- simplifyDecls decls
  extendR substEnv $ simplifyExpr result

simplifyAtom :: Atom -> SimplifyM Atom
simplifyAtom atom = case atom of
  Var v -> do
    substEnv <- ask
    scope <- getScope
    case envLookup substEnv v of
      Just x -> return $ deShadow x scope
      Nothing -> case envLookup scope v of
        -- TODO: check scope?
        Just (LetBound _ (Atom x)) -> dropSub $ simplifyAtom x
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
  Fst (PairVal x _) -> return x
  Snd (PairVal _ y) -> return y
  SumGet (SumVal _ l r) left -> return $ if left then l else r
  SumTag (SumVal s _ _) -> return $ s
  Select p x y -> selectAt (getType x) p x y
  FromNewtypeCon _ (Con (NewtypeCon _ x)) -> return x
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

dropSub :: SimplifyM a -> SimplifyM a
dropSub m = local mempty m
