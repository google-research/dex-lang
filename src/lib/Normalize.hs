-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleContexts #-}

module Normalize (normalizePass, simpPass) where

import Control.Monad
import Control.Monad.Reader
import Data.Foldable

import Env
import Syntax
import Cat
import PPrint
import Fresh
import Type
import Pass
import Subst
import Embed

data TLamEnv = TLamContents NormEnv [TBinder] Expr
type NormSubEnv = FullEnv (Either [NAtom] TLamEnv) [NType]
type NormEnv = (TypeEnv, NormSubEnv)
type NormM a = ReaderT NormEnv (NEmbedT (Either Err)) a

-- TODO: add top-level freshness scope to top-level env
normalizePass :: TopPass TopDecl NTopDecl
normalizePass = TopPass $ \topDecl -> case topDecl of
  TopDecl decl -> do
    (env, decls) <- asTopPassM (normalizeDecl decl)
    extend (asFst env)
    case decls of
      [] -> emitOutput $ NoOutput
      [decl'] -> return $ NTopDecl decl'
      _ -> error "Multiple decls not implemented"
  EvalCmd (Command cmd expr) -> do
    tyEnv <- looks (fst . fst)
    let ty = getType tyEnv expr
    ((ntys, expr'), _) <- asTopPassM $ do
       expr' <- buildScoped $ normalize expr
       ntys <- askType expr'
       return (ntys, expr')
    case cmd of
      ShowNormalized -> emitOutput $ TextOut $ pprint expr'
      _ -> return $ NEvalCmd (Command cmd (ty, ntys, expr'))

asTopPassM :: NormM a -> TopPassM (NormEnv, NEmbedScope) (a, [NDecl])
asTopPassM m = do
  (env, scope) <- look
  (ans, (scope', decls)) <- liftExceptTop $ runEmbedT (runReaderT m env) scope
  extend (asSnd (scope'))
  return (ans, decls)

normalize :: Expr -> NormM NExpr
normalize expr = case expr of
  Lit x -> return $ NAtoms [NLit x]
  Var v ts -> do
    x <- asks $ fromL . (! v) . snd
    case x of
      Left xs -> case ts of
        [] -> return $ NAtoms xs
        _ -> error "Unexpected type application"
      Right (TLamContents env tbs body) -> do
        ts' <- mapM normalizeTy ts
        let env' = (foldMap tbind tbs,
                    foldMap tbind $ zipWith replaceAnnot tbs ts')
        local (const (env <> env')) $ normalize body
  PrimOp Scan _ [x, For ip (Lam _ p body)] -> do
    xs <- atomize x
    (ibs, iToEnv) <- normalizePat ip
    (bs , toEnv ) <- normalizePat p
    buildNestedNScans ibs bs xs $ \idxs carry ->
      extendR (iToEnv idxs <> toEnv carry) (normalize body)
  PrimOp b ts xs -> do
    ts' <- liftM concat $ mapM normalizeTy ts  -- TODO: don't concat
    xs' <- liftM concat $ mapM atomize xs
    return $ NPrimOp b ts' xs'
  Decl decl body -> do
    env <- normalizeDecl decl
    extendR env $ normalize body
  Lam l p body -> do
    (bs, toEnv) <- normalizePat p
    f <- buildNLam l bs $ \xs -> extendR (toEnv xs) (normalize body)
    return $ NAtoms [f]
  App f x -> do
    ~[f'] <- atomize f
    x'    <- atomize x
    return $ NApp f' x'
  For p body -> do
    (bs, toEnv) <- normalizePat p
    buildNestedNScans bs [] [] $ \idxs _ ->
      extendR (toEnv idxs) (normalize body)
  Get e i -> do
    e' <- atomize e
    i' <- atomize i
    return $ NAtoms $ map (\x -> foldl NGet x i') e'
  RecCon _ r -> do
    r' <- traverse atomize r
    return $ NAtoms $ concat r'
  TabCon (TabType (IdxSetLit n) ty) rows -> do
    ts' <- normalizeTy ty
    rows' <- mapM normalize rows
    return $ NTabCon (NIdxSetLit n) ts' rows'
  _ -> error $ "Can't yet normalize: " ++ pprint expr

atomize :: Expr -> NormM [NAtom]
atomize expr = normalize expr >>= emit

normalizePat :: Traversable f => f Binder -> NormM ([NBinder], [NAtom] -> NormEnv)
normalizePat p = do
  p' <- traverse (traverse normalizeTy) p
  let bs = fold (fmap flattenBinder p')
  let tyEnv = foldMap (\(v:>ty) -> v @> L (asSigma ty)) p
  return (bs, \xs -> (tyEnv, bindPat p' xs))
  where
    flattenBinder :: BinderP [NType] -> [NBinder]
    flattenBinder (v:>ts) = map (v:>) ts

bindPat :: Traversable f => f (BinderP [a]) -> [NAtom] -> NormSubEnv
bindPat p xs = fst $ foldl addBinder (mempty, xs) p
  where
    addBinder :: (NormSubEnv, [NAtom]) -> BinderP [a] -> (NormSubEnv, [NAtom])
    addBinder (env, xs') (v:>ts) = (env <> (v @> L (Left cur)), rest)
      where (cur, rest) = splitAt (length ts) xs'

normalizeDecl :: Decl -> NormM NormEnv
normalizeDecl decl = case decl of
  LetMono p bound -> do
    (bs, toEnv) <- normalizePat p
    bound' <- buildScoped $ normalize bound
    xs <- emitTo bs bound'
    return $ toEnv xs
  LetPoly (v:>ty) (TLam tbs body) -> do
    env <- ask
    return (v@>L ty, v@>L (Right (TLamContents env tbs body)))
  Unpack b tv bound -> do
    bound' <- buildScoped $ normalize bound
    (ty, emitUnpackRest) <- emitUnpack tv bound'
    let tenv = (tv @> T (Kind [IdxSet]), tv @> T [ty])
    (bs, toEnv) <- extendR tenv $ normalizePat [b]
    xs <- emitUnpackRest bs
    return (tenv <> toEnv xs)
  TAlias _ _ -> error "Shouldn't have TAlias left"

normalizeTy :: Type -> NormM [NType]
normalizeTy ty = case ty of
  BaseType b -> return [NBaseType b]
  TypeVar v -> asks $ fromT . (!v) . snd
  ArrType l a b -> do
    a' <- normalizeTy a
    b' <- normalizeTy b
    return [NArrType l (toList a') (toList b')]
  TabType a b -> do
    a' <- normalizeTy a
    b' <- normalizeTy b
    return $ fmap (\x -> foldr NTabType x a') b'
  RecType _ r -> liftM fold $ traverse normalizeTy r
  Exists body -> do
    body' <- normalizeTy body
    return [NExists (toList body')]
  IdxSetLit x -> return [NIdxSetLit x]
  BoundTVar n -> return [NBoundTVar n]

-- === simplification pass ===

type NScope = FullEnv NType ()
type SimpEnv = (FullEnv NAtom Name, NScope)
type SimplifyM a = ReaderT SimpEnv (Either Err) a

-- TODO: consider maintaining free variables explicitly
-- ions are atoms with a few bits missing
data Ions = Ions NExpr [NBinder] [NAtom] | Unchanged

simpPass :: TopPass NTopDecl NTopDecl
simpPass = TopPass $ \topDecl -> case topDecl of
  NTopDecl decl -> do
    (decls, env) <- simpAsTopPassM $ simplifyDecl decl
    decl' <- case decls of

      [] -> return $ dummyDecl
      [decl'] -> return decl'
      _ -> error "Multiple decls not implemented"
    extend env
    return $ NTopDecl decl'
    where dummyDecl = NLet [] (NAtoms [])
  NEvalCmd (Command cmd (ty, ntys, expr)) -> do
    -- TODO: handle type vars
    expr' <- simpAsTopPassM $ simplify True expr
    case cmd of
      ShowSimp -> emitOutput $ TextOut $ pprint expr'
      _ -> return $ NEvalCmd (Command cmd (ty, ntys, expr'))

simpAsTopPassM :: SimplifyM a -> TopPassM SimpEnv a
simpAsTopPassM m = do
  env <- look
  liftExceptTop $ runReaderT m env

simplify :: Bool -> NExpr -> SimplifyM NExpr
simplify mat expr = case expr of
  NDecl decl body -> do
    (decls, env) <- simplifyDecl decl
    body' <- extendR env $ simplify mat body
    return $ wrapNDecls decls body'
  NScan b bs xs e -> do
    xs' <- mapM simplifyAtom xs
    (xs'', decls, env) <- materializeAtoms xs'
    extendR env $
      refreshBindersRSimp (b:bs) $ \(b':bs') -> do
        e' <- simplify mat e
        return $ wrapNDecls decls (NScan b' bs' xs'' e')
  NApp f xs -> do
    xs' <- mapM simplifyAtom xs
    f' <- simplifyAtom f
    case f' of
      NLam _ bs body -> local (\(_, scope) -> (env, scope)) (simplify mat body)
        where env = bindEnv bs xs'
      _ -> return $ NApp f' xs'
  NPrimOp b ts xs -> liftM2 (NPrimOp b) (mapM nSubstSimp ts) (mapM simplifyAtom xs)
  NAtoms xs -> do
    xs' <- mapM simplifyAtom xs
    if mat
      then do
        (xs'', decls, _) <- materializeAtoms xs'
        return $ wrapNDecls decls (NAtoms xs'')
      else return $ NAtoms xs'
  NTabCon n ts rows ->
    liftM3 NTabCon (nSubstSimp n) (mapM nSubstSimp ts) (mapM (simplify mat) rows)

simplifyAtom :: NAtom -> SimplifyM NAtom
simplifyAtom atom = case atom of
  NLit x -> return $ NLit x
  NVar v -> do
    x <- asks $ flip envLookup v . fst
    case x of
      Nothing -> return $ NVar v
      Just (L x') -> local (\(_, scope) -> (mempty, scope)) (simplifyAtom x')
      Just (T _) -> error "Expected let-bound var"
  NGet e i -> do
    e' <- simplifyAtom e
    i' <- simplifyAtom i
    return $ nGet e' i'
  NAtomicFor b body ->
    refreshBindersRSimp [b] $ \[b'@(i':>_)] -> do
      body' <- simplifyAtom body
      return $ case body' of
        NGet e (NVar i) | i == i' && not (isin i (freeVars e)) -> e
        _ -> NAtomicFor b' body'
  NLam l bs body ->
    refreshBindersRSimp bs $ \bs' -> do
      body' <- simplify False body
      return $ NLam l bs' body'

materializeAtoms :: [NAtom] -> SimplifyM ([NAtom], [NDecl], SimpEnv)
materializeAtoms xs = do
  (xsDecls, env) <- catTraverse materializeAtom xs
  let (xs', declss) = unzip xsDecls
  return (xs', concat declss, env)

materializeAtom :: NAtom -> SimplifyM ((NAtom, [NDecl]), SimpEnv)
materializeAtom atom = case atom of
  NAtomicFor _ _ -> do
    scope <- asks snd
    let ty = getAtomType scope atom
    atomExpr <- atomToNExpr atom
    let v = rename (rawName "tab") scope
    let env' = (mempty, v @> L ty)
    let decl = NLet [v:>ty] atomExpr
    return ((NVar v, [decl]), env')
  _ -> return ((atom, []), mempty)

atomToNExpr :: NAtom -> SimplifyM NExpr
atomToNExpr atom = case atom of
  NAtomicFor b body ->
    refreshBindersRSimp [b] $ \[b'] -> do
      bodyExpr <- atomToNExpr body
      return (NScan b' [] [] bodyExpr)
  _ -> return (NAtoms [atom])

simplifyDecl :: NDecl -> SimplifyM ([NDecl], SimpEnv)
simplifyDecl decl = case decl of
  NLet bs bound -> do
    -- As pointed out in the 'ghc inliner' paper, this can lead to exponential
    -- blowup in compile times. The solution will be to defer some
    -- simplification, pairing the expression with the env, to be forced later.
    bound' <- simplify False bound
    let v = case bs of [] -> error "no binders"
                       (v':>_):_ -> v'
    ions <- renameIons v $ decompose mempty bound'
    case ions of
      Unchanged -> do
        (bs', env) <- refreshBindersSimp bs
        return ([NLet bs' bound'], env)
      Ions bound'' bs' atoms ->
        return $ case bs' of [] -> ([]     , env)
                             _  -> ([decl'], env)
        where env = (bindEnv bs atoms, newScope bs')
              decl' = NLet bs' bound''
  NUnpack bs tv bound -> do
    bound' <- simplify True bound
    tv' <- asks $ rename tv . snd
    let tEnv = (tv @> T tv', tv' @> T ())
    (bs', lEnv) <- extendR tEnv $ refreshBindersSimp bs
    return ([NUnpack bs' tv' bound'], tEnv <> lEnv)

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
            atoms' = map (wrapAtomFor b bs) atoms
  NScan _ _ _ _ -> Unchanged
  NPrimOp _ _ _ -> Unchanged
  NApp _ _      -> Unchanged
  NAtoms xs -> Ions expr' bs xs  -- TODO: special treatment of unchanged case
    where
      vs = foldMap freeVars xs
      bs = map (uncurry (:>)) $ envPairs $ envIntersect vs scope
      expr' = NAtoms $ fmap (NVar . binderVar) bs
  NTabCon _ _ _ -> Unchanged

wrapAtomFor :: NBinder -> [NBinder] -> NAtom -> NAtom
wrapAtomFor b@(i:>_) bs atom = NAtomicFor b atom'
  where atom' = nSubst (env, mempty) atom
        env = foldMap (\(v:>_) -> v @> L (NGet (NVar v) (NVar i))) bs

bindEnv :: [BinderP c] -> [a] -> FullEnv a b
bindEnv bs xs = fold $ zipWith f bs xs
  where f (v:>_) x = v @> L x

newScope :: [NBinder] -> NScope
newScope bs = foldMap (\(v:>ty) -> v@>L ty) bs

-- TODO: de-dup with version in subst
refreshBindersSimp :: [NBinder] -> SimplifyM ([NBinder], SimpEnv)
refreshBindersSimp bs = catTraverse refreshBinderSimp bs

refreshBinderSimp :: NBinder -> SimplifyM (NBinder, SimpEnv)
refreshBinderSimp (v:>ty) = do
  scope <- asks snd
  ty' <- nSubstSimp ty
  let v' = rename v scope
  return (v':>ty', (v @> L (NVar v'), v' @> L ty'))

renameIons :: Name -> Ions -> SimplifyM Ions
renameIons _ Unchanged = return Unchanged
renameIons v (Ions expr bs atoms) = do
  (bs', (env, scope)) <- catTraverse (renameBinder v) bs
  let atoms' = map (nSubst (env, fmap (const ()) scope)) atoms
  return $ Ions expr bs' atoms'

renameBinder :: Name -> NBinder -> SimplifyM (NBinder, SimpEnv)
renameBinder proposal (v:>ty) = do
  scope <- asks snd
  let v' = rename proposal scope
  return (v':>ty, (v @> L (NVar v'), v' @> L ty))

nSubstSimp :: NSubst a => a -> SimplifyM a
nSubstSimp x = do
  (env, scope) <- ask
  return $ nSubst (env, fmap (const ()) scope) x

refreshBindersRSimp :: [NBinder] -> ([NBinder] -> SimplifyM a) -> SimplifyM a
refreshBindersRSimp bs cont = do (bs', env) <- refreshBindersSimp bs
                                 extendR env $ cont bs'

nGet :: NAtom -> NAtom -> NAtom
nGet (NAtomicFor (v:>_) body) i = nSubst (v@>L i, scope) body
  where scope = fmap (const ()) (freeVars i)
nGet e i = NGet e i
