-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

module Simplify (derivPass, simpPass) where

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
import Pass
import Subst
import Embed
import Record

type SimpSubEnv = FullEnv Atom Type
type DerivRuleEnv = Env Atom

data SimpEnv = SimpEnv { subEnv   :: SimpSubEnv
                       , derivEnv :: DerivRuleEnv }

type SimpTopEnv = (SimpEnv, Scope)
type SimplifyM a = ReaderT SimpEnv (EmbedT (Either Err)) a

derivPass :: TopPass NTopDecl NTopDecl
derivPass = TopPass $ \topDecl -> case topDecl of
  NTopDecl PlainDecl decl -> simplifyDeclTop decl
  NTopDecl ADPrimitive decl -> do
    let Let v _ = decl
    decl' <- liftTopNoDecl $ substSimp decl
    extend $ asSnd $ v@>()
    return [NTopDecl PlainDecl decl']
  NRuleDef (LinearizationDef v) _ ~(Atom f) -> do
    f' <- liftTopNoDecl $ substSimp f
    extend $ asFst $ mempty {derivEnv = (v:>()) @> f' }
    emitOutput $ NoOutput
  NEvalCmd (Command cmd (ty, expr)) -> do
    expr' <- liftTopNoDecl $ buildScoped $ simplifyMat expr
    case cmd of
      ShowDeriv -> emitOutput $ TextOut $ pprint expr'
      _ -> return [NEvalCmd (Command cmd (ty, expr'))]

simpPass :: TopPass NTopDecl NTopDecl
simpPass = TopPass $ \topDecl -> case topDecl of
  NTopDecl _ decl -> simplifyDeclTop decl
  NRuleDef _ _ _ -> error "Shouldn't have derivative rules left"
  NEvalCmd (Command cmd (ty, expr)) -> do
    expr' <- liftTopNoDecl $ buildScoped $ simplifyMat expr
    case cmd of
      ShowSimp -> emitOutput $ TextOut $ pprint expr'
      _ -> return [NEvalCmd (Command cmd (ty, expr'))]

liftTopNoDecl :: SimplifyM a -> TopPassM SimpTopEnv a
liftTopNoDecl m = do
  (ans, decls) <- liftTop m
  unless (null decls) $ throwTopErr $ Err CompilerErr Nothing "Shouldn't have emitted decls"
  return ans

liftTop :: SimplifyM a -> TopPassM SimpTopEnv (a, [Decl])
liftTop m = do
  (env, scope) <- look
  (ans, (scope', decls)) <- liftExceptTop $ runEmbedT (runReaderT m env) scope
  extend $ asSnd scope'
  return (ans, decls)

simplifyDeclTop :: Decl -> TopPassM SimpTopEnv [NTopDecl]
simplifyDeclTop decl = do
  (env, decls) <- liftTop $ simplifyDecl decl
  extend (asFst env)
  return $ map (NTopDecl PlainDecl) decls

-- Simplification gives us a ([Decl], Atom) pair. The decls are fully
-- simplified: no `NLam`, `AtomicFor` or differentiation operations. The atom
-- isn't: e.g. a lambda that can't be beta-reduced yet.
simplify :: Expr -> SimplifyM Atom
simplify expr = case expr of
  Decl decl body -> do
    env <- simplifyDecl decl
    extendR env $ simplify body
  CExpr e -> simplifyCExpr e
  Atom x -> simplifyAtom x

-- Simplifies bodies of first-order functions only.
-- Unlike `SimplifyAtom`, the simplifies under the binder too.
simplifyLam :: LamExpr -> SimplifyM LamExpr
simplifyLam (LamExpr b body) = do
  b' <- substSimp b
  buildLam b' $ \x ->
    extendSub (b @> L x) $
      simplify body >>= materializeAtom

simplifyAtom :: Atom -> SimplifyM Atom
simplifyAtom atom = substSimp atom

simplifyCExpr :: CExpr -> SimplifyM Atom
simplifyCExpr (Scan x (LamExpr b body)) = do
  x' <- simplifyAtom x >>= materializeAtom
  ~b'@(_:>RecType _ (Tup [n, _]))  <- substSimp b
  ((cOut, yOut), b'', (scope, decls)) <-
     withBinder b' $ \ic -> do
        extendSub (b @> L ic) $ do
           (cOut, yOut) <- liftM fromPair $ simplify body
           cOut' <- materializeAtom cOut
           return (cOut', yOut)
  let (yClosure, reconstruct) = splitAtom scope yOut
  (cOut', yClosure') <- liftM fromPair $ emit $ Scan x' $ LamExpr b'' $
                          wrapDecls decls (makePair cOut yClosure)
  yOutLam <- buildLam ("i":>n) $ \i -> do
               scope <- looks fst
               return $ reconstruct scope (nTabGet yClosure' i)
  return $ makePair cOut' (PrimCon $ AtomicFor yOutLam)
simplifyCExpr expr = do
  expr' <- traverseExpr expr substSimp (simplifyAtom >=> materializeAtom) simplifyLam
  case expr' of
    App (PrimCon (Lam _ (LamExpr b body))) x ->
      dropSub $ extendSub (b @> L x) $ simplify body
    _ -> emit expr'

simplifyDecl :: Decl -> SimplifyM SimpEnv
simplifyDecl decl = case decl of
  Let b bound -> do
    x <- simplifyCExpr bound
    return $ mempty {subEnv = b @> L x}
  Unpack b tv bound -> do
    bound' <- simplifyAtom bound
    ~(TypeVar tv', emitUnpackRest) <- emitUnpack tv bound'
    let tEnv = tv @> T (TypeVar tv')
    b' <- extendSub tEnv $ substSimp b
    x <- emitUnpackRest b'
    return $ mempty {subEnv = tEnv <> b' @> L x}

-- As we prepare to leave a scope (say that of `Scan`) we save the variables
-- we'll no longer have access to once we've left, along with a function that
-- can reconstruct the atom (e.g. lambdas) on the other side.
splitAtom :: Scope -> Atom -> (Atom, Scope -> Atom -> Atom)
splitAtom scope atom = (xsSaved, reconstruct)
  where
    isVar x = case x of Var _-> True; _ -> False
    vsTys = envPairs $ envIntersect scope (freeVars atom)
    xsSaved = makeTup [Var (v:>ty) | (v, L ty) <- vsTys]
    reconstruct scope x = subst (env, scope) atom
      where env = fold [(v:>())@>L x' | ((v,_),x') <- zip vsTys $ fromTup x]

simplifyMat :: Expr -> SimplifyM Atom
simplifyMat expr = simplify expr >>= materializeAtom

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

type TangentM a = ReaderT (Env Atom) (EmbedT (Either Err)) a

runLinearization :: Atom -> LamExpr -> SimplifyM Expr
runLinearization x (LamExpr b expr) = do
  (ans, f) <- extendSub (b @> L x) $ linearize expr
  f' <- runTangent b f
  -- TODO: check type here, especially linearity
  return $ Atom $ PrimCon $ RecCon Cart (Tup [ans, f'])

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
        Nothing -> throw NotImplementedErr $ " linearization for " ++ pprint v
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
  Exists _          -> error "Not implemented"
  _                  -> False

splitLast :: [a] -> ([a], a)
splitLast xs = case reverse xs of x:xs' -> (reverse xs', x)
                                  _ -> error "list must be nonempty"

-- -- === transposition ===

type LinVars = Env Type
type CotangentVals = MonMap Name [Atom]  -- TODO: consider folding as we go
type TransposeM a = WriterT CotangentVals
                      (ReaderT (LinVars, SimpSubEnv) (EmbedT (Either Err))) a

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
