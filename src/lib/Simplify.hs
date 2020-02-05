-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

module Simplify (simplifyPass) where

import Control.Monad
import Control.Monad.Reader
import Control.Monad.Writer
import Data.Foldable
import qualified Data.Map.Strict as M

import Type
import Env
import Syntax
import Cat
import PPrint
import Subst
import Embed
import Record

type SimpSubEnv = FullEnv Atom Type
type DerivRuleEnv = Env Atom
data SimpEnv = SimpEnv { subEnv   :: SimpSubEnv
                       , derivEnv :: DerivRuleEnv }

type SimplifyM a = ReaderT SimpEnv Embed a

simplifyPass :: TopEnv -> Module -> Module
simplifyPass env m = Module mempty decls ans
  where
    env' = SimpEnv env mempty
    (ans, (_, decls)) = runEmbed (runReaderT (simplifyModule m) env') mempty

simplifyModule :: Module -> SimplifyM TopEnv
simplifyModule (Module _ decls result) = case decls of
  [] -> substSimp result
  (d:ds) -> do
    env <- simplifyDecl d
    extendR env $ simplifyModule $ Module mempty ds result

simplify :: Expr -> SimplifyM Atom
simplify expr = case expr of
  Decl decl body -> do
    env <- simplifyDecl decl
    extendR env $ simplify body
  CExpr e -> simplifyCExpr e
  Atom x -> substSimp x

-- Simplifies bodies of first-order functions only.
-- Unlike `substSimp`, this simplifies under the binder too.
simplifyLam :: LamExpr -> SimplifyM LamExpr
simplifyLam (LamExpr b body) = do
  b' <- substSimp b
  buildLam b' $ \x -> extendSub (b @> L x) $ simplify body

simplifyCExpr :: CExpr -> SimplifyM Atom
simplifyCExpr expr = do
  expr' <- traverseExpr expr substSimp substSimp simplifyLam
  case expr' of
    App (PrimCon (Lam _ (LamExpr b body))) x ->
      dropSub $ extendSub (b @> L x) $ simplify body
    TApp (TLam tbs body) ts -> do
      let env = fold [tv @> T t' | (tv, t') <- zip tbs ts]
      dropSub $ extendSub env $ simplify body
    -- TODO: remove this once we have monadic traversal instead of scan
    For (LamExpr b body) ->
      buildFor b $ \x -> extendSub (b @> L x) (simplify body)
    Select ty p x y -> selectAt ty p x y
    _ -> emit expr'

simplifyDecl :: Decl -> SimplifyM SimpEnv
simplifyDecl decl = case decl of
  Let b bound -> do
    x <- simplifyCExpr bound
    return $ mempty {subEnv = b @> L x}

extendSub :: SimpSubEnv -> SimplifyM a -> SimplifyM a
extendSub env m = local (\r -> r { subEnv = subEnv r <> env }) m

dropSub :: SimplifyM a -> SimplifyM a
dropSub m = local (\r -> r {subEnv = mempty}) m

substSimp :: (MonadCat EmbedEnv m, MonadReader SimpEnv m, Subst a) => a -> m a
substSimp x = do
  env <- asks subEnv
  scope <- looks fst  -- do we have to reach into the embedding monad this way?
  return $ subst (env, scope) x

-- -- === linearization ===

type TangentM a = ReaderT (Env Atom) Embed a

runLinearization :: Atom -> LamExpr -> SimplifyM Expr
runLinearization x (LamExpr b expr) = do
  (ans, f) <- extendSub (b @> L x) $ linearize expr
  f' <- runTangent b f
  -- TODO: check type here, especially linearity
  return $ Atom $ PrimCon $ RecCon (Tup [ans, f'])

runTangent :: Var -> TangentM Atom -> SimplifyM Atom
runTangent b m = liftM (PrimCon . Lam (Mult Lin)) $ buildLam b $ \t ->
                    withReaderT (const $ b@>t) m

linearize :: Expr -> SimplifyM (Atom, TangentM Atom)
linearize expr = case expr of
  Decl decl body -> do
    (env, makeTangentEnv) <- linearizeDecl decl
    (ans, fLin) <- extendSub env (linearize body)
    return (ans, do tEnv <- makeTangentEnv
                    extendR tEnv fLin)
  Atom x -> linearizeAtom x

linearizeDecl :: Decl -> SimplifyM (SimpSubEnv, TangentM (Env Atom))
linearizeDecl decl = case decl of
  Let b bound -> do
    b' <- substSimp b
    (x, fLin) <- linearizeCExpr bound
    return (b' @> L x, do { t <- fLin; return (b'@>t) })
  _ -> error "Not implemented"

linearizeCExpr :: CExpr -> SimplifyM (Atom, TangentM Atom)
linearizeCExpr expr = case expr of
  App (Var v) x -> do
    linRule <- do
      maybeRule <- asks $ flip envLookup v . derivEnv
      case maybeRule of
        Nothing -> error $ "Linearization not implemented: " ++ pprint v
        Just rule -> deShadow rule
    (x', xTangents) <- linearizeAtom x
    (y, f) <- liftM fromPair $ emit (App linRule x')
    return (y, do {ts <- xTangents; emit $ App f ts})
  App _ _      -> error $ "Shouldn't have NApp left: " ++ pprint expr

mapLinearize :: (a -> SimplifyM (a, TangentM a))
             -> [a] -> SimplifyM ([a], TangentM [a])
mapLinearize f xs = do
  (xs', tangents) <- liftM unzip $ mapM f xs
  return (xs', sequence tangents)

linearizeAtom :: Atom -> SimplifyM (Atom, TangentM Atom)
linearizeAtom atom = case atom of
  Var v -> do
    maybeVal <- asks $ flip envLookup v . subEnv
    case maybeVal of
      Just (L x) -> return (x, lookupTangent v)
      Nothing -> return $ zeroDeriv atom
      _ -> error "unexpected lookup"
  PrimCon con -> case con of
    Lit _ -> return $ zeroDeriv atom
    TabGet x i -> do
      (x', xt) <- linearizeAtom x
      (i', _) <- linearizeAtom i
      return (PrimCon (TabGet x' i'), liftM (PrimCon . flip TabGet i') xt)
    _ -> error $ "not implemented: " ++ pprint atom
  _ -> error $ "not implemented: " ++ pprint atom

zeroDeriv :: Atom -> (Atom, TangentM Atom)
zeroDeriv x = (x, zeroAt (getType x))

linearizedDiv :: MonadCat EmbedEnv m
              => Atom -> Atom -> Atom -> Atom -> m Atom
linearizedDiv x y tx ty = do
  tx'  <- div' tx y
  ty'  <- mul ty x
  ySq  <- mul y y
  ty'' <- div' ty' ySq >>= neg
  add tx' ty''

lookupTangent :: Var -> TangentM Atom
lookupTangent v = asks (!v)

getContinuousVars :: Expr -> SimplifyM [Var]
getContinuousVars expr = do
  let bs = [v:>ty | (v, L ty) <- envPairs $ freeVars expr]
  return $ filter (isContinuous . varAnn) bs

isContinuous :: Type -> Bool
isContinuous ty = case ty of
  BaseType RealType -> True
  TabType _ a       -> isContinuous a
  _                  -> False

-- -- === transposition ===

type LinVars = Env Type
type CotangentVals = MonMap Name [Atom]  -- TODO: consider folding as we go
type TransposeM a = WriterT CotangentVals (ReaderT (LinVars, SimpSubEnv) Embed) a

runTransposition :: Atom -> LamExpr -> SimplifyM Expr
runTransposition ct (LamExpr b expr) = do
  (((), ct'), _) <- lift $ flip runReaderT (asFst (b@>varAnn b)) $ runWriterT $
                        extractCT b $ transpose expr ct
  return $ Atom ct'

transpose :: Expr -> Atom -> TransposeM ()
transpose expr ct = case expr of
  Decl (Let b bound) body -> do
    maybeExpr <- substNonLin bound
    case maybeExpr of
      Nothing -> do
        let env = asFst (b@>varAnn b)
        (_, ct') <- extractCT b $ extendR env $ transpose body ct
        transposeCExpr bound ct'
      Just bound' -> do
        x <- emitTo b bound'
        extendR (asSnd (b @> L x)) $ transpose body ct
  CExpr e -> transposeCExpr e ct
  Atom x  -> transposeAtom x ct
  _ -> error $ "Transpose not implemented for " ++ pprint expr

transposeCExpr :: CExpr -> Atom -> TransposeM ()
transposeCExpr = undefined

isLin :: HasVars a => a -> TransposeM Bool
isLin x = do linVs <- asks fst
             return $ not $ null $ toList $ envIntersect (freeVars x) linVs

emitCT :: Name -> Atom -> TransposeM ()
emitCT v ct = tell $ MonMap $ M.singleton v [ct]

substNonLin ::  (HasVars a, Subst a) => a -> TransposeM (Maybe a)
substNonLin x = do
  x' <- substTranspose x
  lin <- isLin x'
  if lin then return Nothing
         else return (Just x')

substTranspose :: Subst a => a -> TransposeM a
substTranspose x = do
  env <- asks snd
  scope <- looks fst
  return $ subst (env, scope) x

transposeAtom :: Atom -> Atom -> TransposeM ()
transposeAtom atom ct = case atom of
  Var (v:>_) -> emitCT v ct
  _ -> error $ "Can't transpose: " ++ pprint atom

extractCT :: Var -> TransposeM a -> TransposeM (a, Atom)
extractCT b m = do
  (ans, ctEnv) <- captureW m
  (ct, ctEnv') <- sepCotangent b ctEnv
  tell ctEnv'
  return (ans, ct)

sepCotangent :: MonadCat EmbedEnv m =>
                  Var -> CotangentVals -> m (Atom, CotangentVals)
sepCotangent (v:>ty) (MonMap m) = do
  ans <- sumAt ty $ M.findWithDefault [] v m
  return (ans, MonMap (M.delete v m))

-- === misc ===

instance Semigroup SimpEnv where
  SimpEnv x1 x2 <> SimpEnv y1 y2  = SimpEnv (x1 <> y1) (x2 <> y2)

instance Monoid SimpEnv where
  mempty = SimpEnv mempty mempty
  mappend = (<>)
