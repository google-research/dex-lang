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
import Record
import Cat
import PPrint
import Fresh
import Type
import Pass
import Subst

data TLamEnv = TLamContents NormEnv [TBinder] Expr
type NormEnv = FullEnv (SigmaType, Either (RecTree Name) TLamEnv) (RecTree NType)
type NormM a = ReaderT NormEnv (CatT ([NDecl], Scope) (Either Err)) a

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
    (ty   , _) <- asTopPassM $ exprType expr -- TODO: subst type vars
    (expr', _) <- asTopPassM $ normalizeScoped expr
    (ntys , _) <- asTopPassM $ normalizeTy ty
    case cmd of
      ShowNormalized -> emitOutput $ TextOut $ pprint expr'
      _ -> return $ NEvalCmd (Command cmd (ty, toList ntys, expr'))

asTopPassM :: NormM a -> TopPassM (NormEnv, Scope) (a, [NDecl])
asTopPassM m = do
  (env, scope) <- look
  (ans, (decls, scope')) <- liftExceptTop $ runCatT (runReaderT m env) ([], scope)
  extend (asSnd scope')
  return (ans, decls)

normalize :: Expr -> NormM NExpr
normalize expr = case expr of
  Lit x -> return $ NAtoms [NLit x]
  Var v ts -> do
    x <- asks $ snd . fromL . (! v)
    case x of
      Left vs -> case ts of
        [] -> return $ NAtoms (map NVar (toList vs))
        _ -> error "Unexpected type application"
      Right (TLamContents env bs body) -> do
        ts' <- mapM normalizeTy ts
        let env' = bindFold $ zipWith replaceAnnot bs (map T ts')
        local (const (env <> env')) $ normalize body
  PrimOp Scan _ [x, For ip (Lam _ p body)] -> do
    xs <- atomize x
    normalizeBindersR ip $ \ibs ->
      normalizeBindersR p $ \bs -> do
        body' <- normalizeScoped body
        scope <- looks snd
        return $ nestedScan scope ibs bs xs body'
  PrimOp b ts xs -> do
    xs' <- mapM atomize xs
    ts' <- liftM (concat . map toList) $ mapM normalizeTy ts
    return $ NPrimOp b ts' (fmap fromOne xs') -- TODO: subst types
  Decl decl body -> do
    env <- normalizeDecl decl
    extendR env $ normalize body
  Lam l p body -> do
    normalizeBindersR p $ \bs -> do
      body' <- normalizeScoped body
      return $ NAtoms [NLam l bs body']
  App f x -> do
    ~[f'] <- atomize f
    x' <- atomize x
    return $ NApp f' x'
  For p body -> do
    normalizeBindersR p $ \bs -> do
      body' <- normalizeScoped body
      scope <- looks snd
      return $ nestedScan scope bs [] [] body'
  Get e i -> do
    e' <- atomize e
    i' <- atomize i
    return $ NAtoms $ map (\x -> foldl NGet x i') e'
  RecCon _ r -> do
    r' <- traverse atomize r
    return $ NAtoms $ concat $ toList r'
  TabCon (TabType (IdxSetLit n) ty) rows -> do
    ts' <- liftM toList $ normalizeTy ty
    rows' <- mapM normalize rows
    return $ NTabCon (NIdxSetLit n) ts' rows'
  _ -> error $ "Can't yet normalize: " ++ pprint expr

-- Only produces atoms without binders (i.e. no NLam/NAtomicFor)
atomize :: Expr -> NormM [NAtom]
atomize expr = do
  ty <- exprType expr
  expr' <- normalize expr
  case expr' of
    NAtoms atoms | all noBinders atoms -> return atoms
    _ -> do tys <- liftM toList $ normalizeTy ty
            writeVars tys expr'
  where
    noBinders :: NAtom -> Bool
    noBinders (NLam _ _ _) = False
    noBinders (NAtomicFor _ _) = False
    noBinders _ = True

-- TODO: de-shadowing might be over-zealous here
-- TODO: ought to freshen the index binders too
nestedScan :: Scope -> [NBinder] -> [NBinder] -> [NAtom] -> NExpr -> NExpr
nestedScan scope [] bs xs body = nSubst (bindEnv bs xs, scope) body
nestedScan scope (ib:ibs) bs xs body = NScan ib bs' xs body'
  where
    vs = map binderVar bs
    (vs', scope') = renames vs scope
    bs' = [v:>ty | (_:>ty, v) <- zip bs vs']
    xs' = map (NVar . binderVar) bs'
    body' = nestedScan (scope <> scope') ibs bs xs' body  -- TODO: freshen ibs

normalizeDecl :: Decl -> NormM NormEnv
normalizeDecl decl = case decl of
  LetMono p bound -> do
    bound' <- normalizeScoped bound
    (bs, env) <- normalizeBinders p
    extend $ asFst [NLet bs bound']
    return env
  LetPoly (v:>ty) (TLam tbs body) -> do
    env <- ask
    return $ v@>L (ty, Right (TLamContents env tbs body))
  Unpack b tv bound -> do
    bound' <- normalizeScoped bound
    tv' <- looks $ rename tv . snd
    let tenv = tv @> T (RecLeaf (NTypeVar tv'))
    extendR tenv $ do
      (bs, lenv) <- normalizeBinders [b]
      extend $ ([NUnpack bs tv' bound'], tv' @> ())
      return $ tenv <> lenv
  TAlias _ _ -> error "Shouldn't have TAlias left"

normalizeTy :: Type -> NormM (RecTree NType)
normalizeTy ty = case ty of
  BaseType b -> return $ RecLeaf (NBaseType b)
  TypeVar v -> asks $ fromT . (!v)
  ArrType l a b -> do
    a' <- normalizeTy a
    b' <- normalizeTy b
    return $ RecLeaf $ NArrType l (toList a') (toList b')
  TabType a b -> do
    a' <- normalizeTy a
    b' <- normalizeTy b
    return $ fmap (\x -> foldr NTabType x (toList a')) b'
  RecType _ r -> liftM RecTree $ traverse normalizeTy r
  Exists body -> do
    body' <- normalizeTy body
    return $ RecLeaf $ NExists (toList body')
  IdxSetLit x -> return $ RecLeaf $ NIdxSetLit x
  BoundTVar n -> return $ RecLeaf $ NBoundTVar n

normalizeBinder :: Binder -> NormM ([NBinder], NormEnv)
normalizeBinder (v:>ty) = do
  tys <- normalizeTy ty
  bs <- flip traverse tys $ \t -> do
          v' <- looks $ rename v . snd
          extend $ asSnd (v' @> ())
          return $ v':>t
  let env' = (v @> L (asSigma ty, Left (fmap binderVar bs)))
  return (toList bs, env')

normalizeBinders :: Traversable f =>
                      f Binder -> NormM ([NBinder], NormEnv)
normalizeBinders bs = liftM fold $ traverse normalizeBinder bs

normalizeBindersR :: Traversable f =>
                       f Binder -> ([NBinder] -> NormM a) -> NormM a
normalizeBindersR bs cont = do
  ((bs', env), catEnv) <- scoped $ normalizeBinders bs
  extendLocal catEnv $ extendR env $ cont bs'

normalizeScoped :: Expr -> NormM NExpr
normalizeScoped expr = do
  (body, (decls, _)) <- scoped $ normalize expr
  return $ wrapNDecls decls body

exprType :: Expr -> NormM Type
exprType expr = do
  env <- ask
  let env' = flip fmap env $ \x -> case x of L (ty,_) -> L ty
                                             T _      -> T ()
  return $ getType env' expr

writeVars :: Traversable f => f NType -> NExpr -> NormM (f NAtom)
writeVars tys expr = do
  scope <- looks snd
  let (bs, scope') = flip runCat scope $
                       flip traverse tys $ \t -> do
                         v <- freshCat (rawName "tmp")
                         return $ v:>t
  extend  ([NLet (toList bs) expr], scope')
  return $ fmap (NVar . binderVar) bs

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

wrapNDecls :: [NDecl] -> NExpr -> NExpr
wrapNDecls [] expr = expr
wrapNDecls (decl:decls) expr = NDecl decl (wrapNDecls decls expr)

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

fromOne :: [x] -> x
fromOne [x] = x
fromOne _ = error "Expected singleton list"

nGet :: NAtom -> NAtom -> NAtom
nGet (NAtomicFor (v:>_) body) i = nSubst (v@>L i, scope) body
  where scope = fmap (const ()) (freeVars i)
nGet e i = NGet e i
