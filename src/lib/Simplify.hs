-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

module Simplify (simpPass) where

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
import Util

type NScope = FullEnv NType ()
type SimpSubEnv = FullEnv NAtom Name
type SimpEnv = (SimpSubEnv, NScope)
type SimplifyM a = ReaderT SimpSubEnv (NEmbedT (Either Err)) a

-- TODO: consider maintaining free variables explicitly
-- ions are atoms with a few bits missing
data Ions = Ions NExpr [NBinder] [NAtom] | Unchanged

simpPass :: TopPass NTopDecl NTopDecl
simpPass = TopPass $ \topDecl -> case topDecl of
  NTopDecl decl -> do
    (env, decls) <- simpAsTopPassM $ simplifyDecl True decl
    extend (asFst env)
    decl' <- case decls of
      [] -> return $ dummyDecl
      [decl'] -> return decl'
      _ -> error "Multiple decls not implemented"
    return $ NTopDecl decl'
    where dummyDecl = NLet [] (NAtoms [])
  NEvalCmd (Command cmd (ty, ntys, expr)) -> do
    -- TODO: handle type vars
    (expr', decls) <- simpAsTopPassM $ simplify True expr
    let expr'' = wrapNDecls decls expr'
    case cmd of
      ShowSimp -> emitOutput $ TextOut $ pprint expr''
      _ -> return $ NEvalCmd (Command cmd (ty, ntys, expr''))

simpAsTopPassM :: SimplifyM a -> TopPassM SimpEnv (a, [NDecl])
simpAsTopPassM m = do
  (env, scope) <- look
  (ans, (scope', decls)) <- liftExceptTop $ runEmbedT (runReaderT m env) scope
  extend (asSnd (scope'))
  return (ans, decls)

-- Simplification gives us a ([NDecl], NExpr) pair. The decls are fully
-- simplified: no `NLam`, `NAtomicFor` or differentiation operations. The
-- expression itself will be in a state of partial simplification. e.g a lambda
-- that can't be beta-reduced until it meets its argument.
simplify :: Bool -> NExpr -> SimplifyM NExpr
simplify mat expr = case expr of
  NDecl decl body -> do
    env <- simplifyDecl False decl
    extendR env $ simplify mat body
  NScan ib bs xs e -> do
    xs' <- mapM (simplifyAtom >=> materializeAtom) xs
    ib' <- nSubstSimp ib
    bs' <- mapM nSubstSimp bs
    buildNScan ib' bs' xs' $ \i carry -> do
      let env = bindEnv [ib'] [i] <> bindEnv bs' carry
      extendR env $ simplify mat e
  NApp f xs -> do
    xs' <- mapM simplifyAtom xs
    f' <- simplifyAtom f
    case f' of
      NLam _ bs body -> local (const env) (simplify mat body)
        where env = bindEnv bs xs'
      _ -> error $ "Should only have lambda here. Got: " ++ pprint expr
  NPrimOp Linearize _ ~(f:xs) -> do
    xs' <- mapM simplifyAtom xs
    (bs, body) <- simplifyLam f
    local mempty $ runLinearization bs xs' body >>= simplify mat
  NPrimOp Transpose [_, bTy] ~[f] -> do
    (bs, body) <- simplifyLam f
    bTy' <- mapM nSubstSimp bTy
    transposed <- buildNLam Lin ["ct":>ty | ty <- bTy'] $ \cts ->
                    local mempty $ runTransposition bs cts body
    return $ NAtoms [transposed]
  NPrimOp b ts xs -> liftM2 (NPrimOp b) (mapM (mapM nSubstSimp) ts)
                                        (mapM simplifyAtom xs)
  NAtoms xs -> do
    xs' <- mapM simplifyAtom xs
    if mat
      then liftM NAtoms $ mapM materializeAtom xs'
      else return $ NAtoms xs'
  NTabCon n ts rows -> liftM3 NTabCon (nSubstSimp n) (mapM nSubstSimp ts)
                                      (mapM (simplify mat) rows)

-- simplifies bodies of first-order functions only
simplifyLam :: NAtom -> SimplifyM ([NBinder], NExpr)
simplifyLam f = do
  ~(NLam l bs body) <- simplifyAtom f
  bs' <- mapM nSubstSimp bs
  ~(NLam _ bs'' body') <- buildNLam l bs' $ \vs -> extendR (bindEnv bs' vs)
                                                     (simplify False body)
  return (bs'', body')

simplifyAtom :: NAtom -> SimplifyM NAtom
simplifyAtom atom = case atom of
  NLit x -> return $ NLit x
  NVar v -> do
    x <- asks $ flip envLookup v
    case x of
      Nothing -> return $ NVar v
      -- is this freshening necessary here?
      Just (L x') -> local mempty (simplifyAtom x')
      Just (T _ ) -> error "Expected let-bound var"
  NGet e i -> do
    e' <- simplifyAtom e
    i' <- simplifyAtom i
    return $ nGet e' i'
  NAtomicFor ib body -> do
    ib' <- nSubstSimp ib
    buildNAtomicFor ib' $ \i ->
      extendR (bindEnv [ib'] [i]) (simplifyAtom body)
  NLam _ _ _ -> nSubstSimp atom

materializeAtom :: NAtom -> SimplifyM NAtom
materializeAtom atom = do
  expr <- atomToNExpr atom
  ~[atom'] <- emit expr
  return atom'

atomToNExpr :: NAtom -> SimplifyM NExpr
atomToNExpr atom = case atom of
  NAtomicFor ib body -> do
    ib' <- nSubstSimp ib
    buildNScan ib' [] [] $ \i _ ->
      extendR (bindEnv [ib'] [i]) (atomToNExpr body)
  _ -> return (NAtoms [atom])

-- TODO: make sure we don't lose the names at the top level
emitDecomposedTo :: [NBinder] -> NExpr -> SimplifyM [NAtom]
emitDecomposedTo bs expr = do
  case decompose mempty expr of
    Unchanged -> emitTo bs expr
    Ions expr' bs' atoms -> do
      xs <- emitTo (renameBinders (getNameHint bs) bs') expr'
      scope <- looks fst  -- do we have to reach into the embedding monad this way?
      let env = (bindEnv bs' xs, fmap (const ()) scope)
      return $ map (nSubst env) atoms

renameBinders :: Name -> [NBinder] -> [NBinder]
renameBinders v bs = [v:>ty | _:>ty <- bs]

getNameHint :: [NBinder] -> Name
getNameHint bs = case bs of [] -> "tmp"
                            (v:>_):_ -> v

simplifyDecl :: Bool -> NDecl -> SimplifyM SimpSubEnv
simplifyDecl scopedRhs decl = case decl of
  NLet bs bound -> do
    -- As pointed out in the 'ghc inliner' paper, this can lead to exponential
    -- blowup in compile times. The solution will be to defer some
    -- simplification, pairing the expression with the env, to be forced later.
    bound' <- maybeScoped $ simplify False bound
    bs' <- mapM nSubstSimp bs
    xs <- emitDecomposedTo bs' bound'
    return (bindEnv bs' xs)
  NUnpack bs tv bound -> do
    bound' <- maybeScoped $ simplify True bound
    ~(NTypeVar tv', emitUnpackRest) <- emitUnpack tv bound'
    let tEnv = tv @> T tv'
    bs' <- extendR tEnv $ mapM nSubstSimp bs
    xs <- emitUnpackRest bs'
    return $ tEnv <> bindEnv bs' xs
  where
    maybeScoped = if scopedRhs then buildScoped else id

-- `decompose` splits an expression into two parts: a simple expression, (no
-- lambda etc.) and a list of atoms with holes in them. Once these 'ions' are
-- filled with values corresponding to the results of the simple expression,
-- they become equivalent to the original expression. For example, an expression
-- that constructs a pair of functions becomes an expression that constructs a
-- pair of closures, paired with ions that can reconstruct the functions given
-- values for the closures:
--    f = (y = x + x
--         (lam z. z + y, lam w. w - y) )
-- becomes `x + x` and the ions:
--   Ions (hole::Real) [lam z. z + hole, lam w. w - hole]

decompose :: Env NType -> NExpr -> Ions
decompose scope expr = case expr of
  NDecl decl body -> case body' of
    Ions e bs atoms -> Ions (NDecl decl e) bs atoms
    Unchanged -> Unchanged
    where
      body' = decompose (scope <> scope') body
      scope' = case decl of
        NLet bs _ -> bindFold bs
        _ -> error "Not implemented"
  NScan b@(_:>n) [] [] body -> case decompose mempty body of
    Unchanged -> Unchanged
    Ions body' bs atoms -> Ions (NScan b [] [] body') bs' atoms'
      where bs' = map (fmap (NTabType n)) bs
            atoms' = map (wrapAtomicFor b bs) atoms
  NScan _ _ _ _ -> Unchanged
  NPrimOp _ _ _ -> Unchanged
  NApp _ _      -> Unchanged
  NAtoms xs -> Ions expr' bs xs  -- TODO: special treatment of unchanged case
    where
      vs = foldMap freeVars xs
      bs = map (uncurry (:>)) $ envPairs $ envIntersect vs scope
      expr' = NAtoms $ fmap (NVar . binderVar) bs
  NTabCon _ _ _ -> Unchanged

bindEnv :: [BinderP c] -> [a] -> FullEnv a b
bindEnv bs xs = fold $ zipWith f bs xs
  where f (v:>_) x = v @> L x

nSubstSimp :: (MonadCat NEmbedEnv m, MonadReader SimpSubEnv m)
                 => NSubst a => a -> m a
nSubstSimp x = do
  env <- ask
  scope <- looks fst  -- do we have to reach into the embedding monad this way?
  return $ nSubst (env, fmap (const ()) scope) x

-- === linearization ===

type TangentM a = ReaderT (Env NAtom) (NEmbedT (Either Err)) a

runLinearization :: [NBinder] -> [NAtom] -> NExpr -> SimplifyM NExpr
runLinearization bs xs expr = do
  (ans, f) <- extendR (bindEnv bs xs) $ linearize expr
  ans' <- emit ans
  f' <- buildNLam Lin bs $ \ts -> withReaderT (const $ bindEnvTangent bs ts) f
  return $ NAtoms $ ans' ++ [f']

bindEnvTangent :: [NBinder] -> [NAtom] -> Env NAtom
bindEnvTangent bs xs = fold $ zipWith f bs xs
  where f (v:>_) x = v @> x

linearize :: NExpr -> SimplifyM (NExpr, TangentM NExpr)
linearize expr = case expr of
  NDecl decl body -> do
    (env, makeTangentEnv) <- linearizeDecl decl
    (ans, fLin) <- extendR env (linearize body)
    return (ans, do tEnv <- makeTangentEnv
                    extendR tEnv fLin)
  NScan _ _ _ _ -> error "not implemented"
  NApp _ _      -> error "Shouldn't have NApp left"
  NPrimOp b tys xs -> do
    (xs', xsTangents) <- linearizeAtoms xs
    let (ans, f) = linearizeBuiltin b tys xs'
    return (ans, xsTangents >>= f)
  NAtoms xs -> do
    (xs', tangents) <- linearizeAtoms xs
    return (NAtoms xs', liftM NAtoms tangents)
  NTabCon _ _ _ -> error "not implemented"

linearizeDecl :: NDecl -> SimplifyM (SimpSubEnv, TangentM (Env NAtom))
linearizeDecl decl = case decl of
  NLet bs bound -> do
    bs' <- mapM nSubstSimp bs
    (xs, fLin) <- linearize bound
    xs' <- emitTo bs' xs
    return (bindEnv bs' xs', do ts <- fLin
                                ts' <- emitTo bs' ts
                                return (bindEnvTangent bs' ts'))
  _ -> error "Not implemented"

linearizeAtoms :: [NAtom] -> SimplifyM ([NAtom], TangentM [NAtom])
linearizeAtoms xs = do
  (xs', tangents) <- liftM unzip $ mapM linearizeAtom xs
  return (xs', sequence tangents)

linearizeAtom :: NAtom -> SimplifyM (NAtom, TangentM NAtom)
linearizeAtom atom = case atom of
  NLit _ -> zeroDeriv atom
  NVar v -> do
    maybeVal <- asks $ flip envLookup v
    case maybeVal of
      Just (L x) -> return (x, asks (! v))
      Nothing -> zeroDeriv atom
      _ -> error "unexpected lookup"
  NGet _ _       -> error "not implemented"
  NAtomicFor _ _ -> error "not implemented"
  NLam _ _ _     -> error "not implemented"

zeroDeriv :: NAtom -> SimplifyM (NAtom, TangentM NAtom)
zeroDeriv x = do
  ~[xTy] <- askType (NAtoms [x])
  return (x, zeroAt xTy)

linearizeBuiltin :: MonadCat NEmbedEnv m =>
    Builtin -> [[NType]] -> [NAtom] -> (NExpr, [NAtom] -> m NExpr)
linearizeBuiltin op tys xs | nLin == nArgs = (NPrimOp op tys xs, f)
  where
    BuiltinType _ (nLin, prodKind) xTys outTy = builtinType op
    outsTy = typeToNTypes outTy
    nArgs = length xTys
    f ts = case prodKind of
             Cart -> return $ NPrimOp op tys ts
             Tens -> sumsAt outsTy [NPrimOp op tys (swapAt i t xs)
                                   | (i, t) <- zip [0..] ts]
linearizeBuiltin op _ _ = error $ "Not implemented: linearization for: " ++ pprint op

-- === transposition ===

type LinVars = Env NType
type CotangentVals = MonMap Name [NAtom]  -- TODO: consider folding as we go
type TransposeM a = WriterT CotangentVals
                      (ReaderT (LinVars, SimpSubEnv) (NEmbedT (Either Err))) a

runTransposition :: [NBinder] -> [NAtom] -> NExpr -> SimplifyM NExpr
runTransposition bs cts expr = do
  (((), cts'), _) <- lift $ flip runReaderT (asFst (bindFold bs)) $ runWriterT $
                        extractCTs bs $ transpose expr cts
  return $ NAtoms cts'

transpose :: NExpr -> [NAtom] -> TransposeM ()
transpose expr cts = case expr of
  NPrimOp b tys xs -> do
    -- TODO: subst types
    xs' <- mapM substNonLin xs
    cts' <- transposeBuiltin b tys xs' cts
    sequence_ [transposeAtom x ct | (x, Just ct) <- zip xs cts']
  NDecl (NLet bs bound) body -> do
    lin <- isLin bound
    if lin
      then do
        (_, cts') <- extractCTs bs $ extendR (asFst (bindFold bs)) $ transpose body cts
        transpose bound cts'
      else do
        error "Not implemented: nonlinear parts"
  NAtoms xs -> zipWithM_ transposeAtom xs cts
  _ -> error $ "Transpose not implemented for " ++ pprint expr

isLin :: HasVars a => a -> TransposeM Bool
isLin x = do linVs <- asks fst
             return $ not $ null $ toList $ envIntersect (freeVars x) linVs

substNonLin :: NAtom -> TransposeM (Maybe NAtom)
substNonLin x = do
  x' <- do env <- asks snd
           return $ nSubst (env, mempty) x
  lin <- isLin x'
  if lin then return Nothing
         else return (Just x')

transposeAtom :: NAtom -> NAtom -> TransposeM ()
transposeAtom atom ct = case atom of
  NLit _ -> return ()
  NVar v -> tell $ MonMap $ M.singleton v [ct]
  _ -> error $ "Can't transpose: " ++ pprint atom

transposeBuiltin :: MonadCat NEmbedEnv m =>
    Builtin -> [[NType]] -> [Maybe NAtom] -> [NAtom] -> m [Maybe NAtom]
transposeBuiltin op _ xs cts = case op of
  FAdd -> return [Just ct, Just ct]
            where [ct] = cts
  FMul -> case xs of
            [Just x, Nothing] -> do ~[ans] <- emit $ NPrimOp FMul [] [x, ct]
                                    return [Nothing, Just ans]
            [Nothing, Just y] -> do ~[ans] <- emit $ NPrimOp FMul [] [ct, y]
                                    return [Just ans, Nothing]
            _ -> error $ "Can't transpose: " ++ pprint (op, xs)
            where [ct] = cts
  _ -> error $ "Not implemented: transposition for: " ++ pprint op

extractCTs :: [NBinder] -> TransposeM a -> TransposeM (a, [NAtom])
extractCTs bs m = do
  (ans, ctEnv) <- captureW m
  (cts, ctEnv') <- sepCotangents bs ctEnv
  tell ctEnv'
  return (ans, cts)

sepCotangent :: MonadCat NEmbedEnv m =>
                  NBinder -> CotangentVals -> m (NAtom, CotangentVals)
sepCotangent (v:>ty) (MonMap m) = do
  ans <- sumAt ty $ M.findWithDefault [] v m
  return (ans, MonMap (M.delete v m))

sepCotangents :: MonadCat NEmbedEnv m =>
                   [NBinder] -> CotangentVals -> m ([NAtom], CotangentVals)
sepCotangents [] cts = return ([], cts)
sepCotangents (b:bs) cts = do
  (x , cts' ) <- sepCotangent  b  cts
  (xs, cts'') <- sepCotangents bs cts'
  return (x:xs, cts'')
