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
import Data.Foldable

import Env
import Syntax
import Cat
import PPrint
import Pass
import Subst
import Embed

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
    (env, decls) <- simpAsTopPassM $ simplifyDecl decl
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
-- expression itself will be in a partial state of simplification. e.g a lambda
-- can't be beta-reduced until it meets its argument.
simplify :: Bool -> NExpr -> SimplifyM NExpr
simplify mat expr = case expr of
  NDecl decl body -> do
    env <- simplifyDecl decl
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
      _ -> return $ NApp f' xs'
  NPrimOp b ts xs -> liftM2 (NPrimOp b) (mapM nSubstSimp ts) (mapM simplifyAtom xs)
  NAtoms xs -> do
    xs' <- mapM simplifyAtom xs
    if mat
      then liftM NAtoms $ mapM materializeAtom xs'
      else return $ NAtoms xs'
  NTabCon n ts rows -> liftM3 NTabCon (nSubstSimp n) (mapM nSubstSimp ts)
                                      (mapM (simplify mat) rows)

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
  NLam l bs body -> do
    bs' <- mapM nSubstSimp bs
    buildNLam l bs' $ \xs ->
      extendR (bindEnv bs' xs) (simplify False body)

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

simplifyDecl :: NDecl -> SimplifyM SimpSubEnv
simplifyDecl decl = case decl of
  NLet bs bound -> do
    -- As pointed out in the 'ghc inliner' paper, this can lead to exponential
    -- blowup in compile times. The solution will be to defer some
    -- simplification, pairing the expression with the env, to be forced later.
    bound' <- buildScoped $ simplify False bound
    bs' <- mapM nSubstSimp bs
    xs <- emitDecomposedTo bs' bound'
    return (bindEnv bs' xs)
  NUnpack bs tv bound -> do
    bound' <- simplify True bound
    ~(NTypeVar tv', emitUnpackRest) <- emitUnpack tv bound'
    let tEnv = tv @> T tv'
    bs' <- extendR tEnv $ mapM nSubstSimp bs
    xs <- emitUnpackRest bs'
    return $ tEnv <> bindEnv bs' xs

-- `decompose` splits an expression into two parts: a simple expression, (no
-- lambda etc.) and a list of atoms with holes in them. Once these 'ions' are
-- filled with values corresponding to the results of the simple expression,
-- they become equivalent to the original expression. For example an expression
-- that constructs a pair of functions becomes an expression that constructrs a
-- pair of closures, paired with ions that can reconstruct the functions given
-- values for the closures. For example, this expression
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

nSubstSimp :: NSubst a => a -> SimplifyM a
nSubstSimp x = do
  env <- ask
  scope <- looks fst  -- do we have to reach into the embedding monad this way?
  return $ nSubst (env, fmap (const ()) scope) x
