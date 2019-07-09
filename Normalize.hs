{-# LANGUAGE FlexibleContexts #-}

module Normalize (normalizePass, simpPass) where

import Control.Monad
import Control.Monad.Reader
import Control.Monad.Except hiding (Except)
import Data.Foldable
import Data.Either

import Env
import Syntax  hiding (wrapDecls)
import Record
import Cat
import PPrint
import Fresh
import Type
import Pass

type Scope = Env ()
type TLam = ([TBinder], Expr)
type NormEnv = FullEnv (Type, Either (RecTree NAtom) TLam) (RecTree NType)
type NormM a = ReaderT NormEnv (CatT ([NDecl], Scope) (Either Err)) a

normalizePass :: TopDecl -> TopPass NormEnv NTopDecl
normalizePass topDecl = case topDecl of
  TopDecl decl -> do
    (env, decls) <- asTopPass (normalizeDecl decl)
    decl' <- case decls of
      [] -> return $ dummyDecl
      [decl'] -> return decl'
    putEnv env
    return $ NTopDecl decl'
    where dummyDecl = NLet [] (NAtoms [])
  EvalCmd NoOp -> return (NEvalCmd NoOp)
  EvalCmd (Command cmd expr) -> do
    (ty   , []) <- asTopPass $ exprType expr -- TODO: subst type vars
    (expr', []) <- asTopPass $ normalizeScoped expr
    (ntys , []) <- asTopPass $ normalizeTy ty
    case cmd of Passes -> writeOutText $ "\n\nNormalized\n" ++ pprint expr'
                _ -> return ()
    return $ NEvalCmd (Command cmd (ty, toList ntys, expr'))

asTopPass :: NormM a -> TopPass NormEnv (a, [NDecl])
asTopPass m = do
  env <- getEnv
  (ans, (decls, _)) <- liftEither $ runCatT (runReaderT m env) mempty
  return (ans, decls)

-- TODO: rewrite as normalize :: Expr -> NormM NExpr
-- to avoid unnecessary let bindings
normalize :: Expr -> NormM (RecTree NAtom)
normalize expr = case expr of
  Lit x -> return $ RecLeaf $ NLit x
  Var v -> asks $ fromLeft (error msg) . snd. fromL . (! v )
             -- TODO: use this error pattern for env loookups too
             where msg = "Type lambda should be immediately applied"
  PrimOp b [] xs -> do
    xs' <- mapM normalize xs
    writeExpr $ NPrimOp b [] (fmap fromLeaf xs') -- TODO: subst types
  Decls [] body -> normalize body
  Decls (decl:decls) final -> do
    env <- normalizeDecl decl
    extendR env $ normalize (Decls decls final)
  Lam b body -> do
    normalizeBinderR b $ \bs -> do
      body' <- normalizeScoped body
      return $ RecLeaf $ NLam bs body'
  App f x -> do
    f' <- normalize f
    x' <- normalize x
    writeExpr $ NApp (fromLeaf f') (toList x')
  For b body -> do
    normalizeBinderR b $ \[b'] -> do
      body' <- normalizeScoped body
      writeExpr $ NFor b' body'
  Get e i -> do
    e' <- normalize e
    i' <- normalize i
    return $ fmap (flip NGet (fromLeaf i')) e'
  -- TODO: consider finding these application sites in a bottom-up pass and
  -- making a single monorphic version for each distinct type found,
  -- rather than inlining
  TApp (Var v) ts -> do -- Assumes HM-style type lambdas only
    (bs, body) <- asks $ fromRight (error "Expected t-lambda") . snd . fromL . (! v)
    ts' <- mapM normalizeTy ts
    extendR (bindFold $ zipWith replaceAnnot bs (map T ts')) $ do
      normalize body
  RecCon r -> liftM RecTree $ traverse normalize r
  RecGet e field -> do
    (RecTree r) <- normalize e
    return $ recGet r field
  _ -> error $ "Can't yet normalize: " ++ pprint expr
  where
     -- TODO: accept name hint
     writeExpr :: NExpr -> NormM (RecTree NAtom)
     writeExpr nexpr = do
       ty <- exprType expr
       writeVars ty nexpr

normalizeDecl :: Decl -> NormM NormEnv
normalizeDecl decl = case decl of
  Let (v:>ty) (TLam tbs body) -> return $ v@>L (ty, Right (tbs, body))
  Let b bound -> do
    bound' <- normalizeScoped bound
    (bs, env) <- normalizeBinder b
    extend $ asFst [NLet bs bound']
    return env
  Unpack b tv bound -> do
    bound' <- normalizeScoped bound
    tv' <- freshVar tv
    let tenv = tv @> T (RecLeaf (NTypeVar tv'))
    extendR tenv $ do
      (bs, lenv) <- normalizeBinder b
      extend $ asFst [NUnpack bs tv' bound']
      return $ tenv <> lenv

freshVar :: Name -> NormM Name
freshVar v = do
  v' <- looks $ rename v . snd
  extend $ asSnd $ v'@> ()
  return v'

normalizeTy :: Type -> NormM (RecTree NType)
normalizeTy ty = case ty of
  BaseType b -> return $ RecLeaf (NBaseType b)
  TypeVar v -> asks $ fromT . (!v)
  ArrType a b -> do
    a' <- normalizeTy a
    b' <- normalizeTy b
    return $ RecLeaf $ NArrType (toList a') (toList b')
  TabType n ty -> do
    ty' <- normalizeTy ty
    n'  <- normalizeTy n
    return $ fmap (NTabType (fromLeaf n')) ty'
  RecType r -> liftM RecTree $ traverse normalizeTy r
  Exists ty -> do
    ty' <- normalizeTy ty
    return $ RecLeaf $ NExists (toList ty')
  IdxSetLit x -> return $ RecLeaf $ NIdxSetLit x
  BoundTVar n -> return $ RecLeaf $ NBoundTVar n
  Forall _ _ -> error "Shouldn't have forall types left"

normalizeBinder :: Binder -> NormM ([NBinder], NormEnv)
normalizeBinder (v:>ty) = do
  tys <- normalizeTy ty
  bs <- flip traverse tys $ \t -> do
          v' <- freshVar v -- TODO: incorporate field names
          return $ v':>t
  let env' = (v @> L (ty, Left (fmap (NVar . binderVar) bs)))
  return (toList bs, env')

normalizeBinderR :: Binder -> ([NBinder] -> NormM a) -> NormM a
normalizeBinderR b cont = do
  (bs, env) <- normalizeBinder b
  extendR env (cont bs)

normalizeScoped :: Expr -> NormM NExpr
normalizeScoped expr = do
  (body, (decls, _)) <- scoped $ normalize expr
  -- TODO: reduce clutter in the case where these atoms are all
  -- vars bound at last expression
  return $ ndecls decls $ NAtoms (toList body)

ndecls :: [NDecl] -> NExpr -> NExpr
ndecls [] e = e
ndecls decls e = NDecls decls e

exprType :: Expr -> NormM Type
exprType expr = do
  env <- ask
  let env' = flip fmap env $ \x -> case x of L (ty,_) -> L ty
                                             T _      -> T ()
  return $ getType env' expr

writeVars :: Type -> NExpr -> NormM (RecTree NAtom)
writeVars ty expr = do
  tys <- normalizeTy ty
  bs <- flip traverse tys $ \t -> do
          v' <- freshVar (rawName "tmp")
          return $ v':>t
  extend $ asFst [NLet (toList bs) expr]
  return $ fmap (NVar . binderVar) bs

-- === simplification pass ===

type SubstEnv = (FullEnv NAtom Var, Scope)
type SimplifyM a = ReaderT SubstEnv (Either Err) a

-- TODO: consider maintaining free variables explicitly
data Ions = Ions NExpr [NBinder] [NAtom] | Unchanged

simpPass :: NTopDecl -> TopPass SubstEnv NTopDecl
simpPass topDecl = case topDecl of
  NTopDecl decl -> do
    (decls, env) <- simpAsTopPass $ simplifyDecl decl
    decl' <- case decls of
      [] -> return $ dummyDecl
      [decl'] -> return decl'
    putEnv env
    return $ NTopDecl decl'
    where dummyDecl = NLet [] (NAtoms [])
  NEvalCmd NoOp -> return (NEvalCmd NoOp)
  NEvalCmd (Command cmd (ty, ntys, expr)) -> do
    -- TODO: handle type vars
    expr' <- simpAsTopPass $ simplify expr
    case cmd of Passes -> writeOutText $ "\n\nSimp\n" ++ pprint expr'
                _ -> return ()
    return $ NEvalCmd (Command cmd (ty, ntys, expr'))

simpAsTopPass :: SimplifyM a -> TopPass SubstEnv a
simpAsTopPass m = do
  env <- getEnv
  liftEither $ runReaderT m env

simplify :: NExpr -> SimplifyM NExpr
simplify expr = case expr of
  NDecls [] body -> simplify body
  NDecls (decl:rest) final -> do
    (decls, env) <- simplifyDecl decl
    body' <- extendR env $ simplify body
    return $ wrapDecls decls body'
    where body = NDecls rest final
  NFor b e -> do
    refreshBindersR [b] $ \[b'] -> do
      e' <- simplify e
      return $ NFor b' e'
  NApp f xs -> do
    xs' <- mapM nSubst xs
    f <- nSubst f
    case f of
      NLam bs body -> extendR env (simplify body)
        where env = asFst $ bindEnv bs xs'
      _ -> error "Expected lambda"
  NPrimOp _ _ _ -> nSubst expr
  NAtoms _ -> nSubst expr

simplifyDecl :: NDecl -> SimplifyM ([NDecl], SubstEnv)
simplifyDecl decl = case decl of
  NLet bs bound -> do
    bound' <- simplify bound
    case decompose mempty bound' of
      Unchanged -> do
        (bs', env) <- refreshBinders bs
        return ([NLet bs' bound'], env)
      Ions bound'' bs' ions ->
        return ([NLet bs' bound''], env)
        where env = (bindEnv bs ions, newScope bs')
  NUnpack bs tv bound -> do
    bound' <- simplify bound
    tv' <- asks $ rename tv . snd
    let tEnv = (tv @> T tv', tv' @> ())
    (bs', lEnv) <- extendR tEnv $ refreshBinders bs
    return ([NUnpack bs' tv' bound'], tEnv <> lEnv)

decompose :: Env NType -> NExpr -> Ions
decompose scope expr = case expr of
  NDecls decls body -> case body' of
    Ions expr bs atoms-> Ions (wrapDecls decls expr) bs atoms
    Unchanged -> Unchanged
    where
      body' = decompose (scope <> scope') body
      scope' = foldMap declsScope decls
      declsScope decl = case decl of
        NLet bs _ -> bindFold bs
  NFor _ _ -> undefined
  NPrimOp _ _ _ -> Unchanged
  NApp _ _ -> error $ "Shouldn't have app left: " ++ pprint expr
  NAtoms xs -> Ions expr' bs xs  -- TODO: special treatment of unchanged case
    where
      vs = foldMap freeVars xs
      bs = map (uncurry (:>)) $ envPairs $ envIntersect vs scope
      expr' = NAtoms $ fmap (NVar . binderVar) bs

bindEnv :: [BinderP c] -> [a] -> FullEnv a b
bindEnv bs xs = fold $ zipWith f bs xs
  where f (v:>_) x = v @> L x

newScope :: [BinderP a] -> Scope
newScope bs = foldMap (\(v:>_) -> v@>()) bs

refreshBinders :: MonadReader SubstEnv m => [NBinder] -> m ([NBinder], SubstEnv)
refreshBinders bs = do
  scope <- asks snd
  ts' <- mapM nSubst ts
  let vs' = renames vs scope
      env' = fold $ zipWith (\v v' -> v @> L (NVar v')) vs vs'
      scope' = foldMap (\v -> v @> ()) vs'
      bs' = zipWith (:>) vs' ts'
  return (bs', (env', scope'))
  where (vs, ts) = unzip [(v,t) | v:>t <- bs]

refreshBindersR :: MonadReader SubstEnv m =>
                     [NBinder] -> ([NBinder] -> m a) -> m a
refreshBindersR bs cont = do (bs', env) <- refreshBinders bs
                             extendR env $ cont bs'

wrapDecls :: [NDecl] -> NExpr -> NExpr
wrapDecls decls (NDecls decls' body) = NDecls (decls ++ decls') body
wrapDecls decls body = NDecls decls body

-- === capture-avoiding substitutions on NExpr and friends ===

class NSubst a where
  nSubst :: MonadReader (FullEnv NAtom Var, Scope) m => a -> m a

instance NSubst NExpr where
  nSubst expr = case expr of
    NDecls [] body -> nSubst body
    NDecls (decl:rest) final -> case decl of
      NLet bs bound -> do
        bound' <- nSubst bound
        refreshBindersR bs $ \bs' -> do
           body' <- nSubst body
           return $ wrapDecls [NLet bs' bound'] body'
       where body = NDecls rest final
    NFor b e -> refreshBindersR [b] $ \[b'] -> liftM (NFor b') (nSubst e)
    NPrimOp b ts xs -> liftM2 (NPrimOp b) (mapM nSubst ts) (mapM nSubst xs)
    NApp f xs -> liftM2 NApp (nSubst f) (mapM nSubst xs)
    NAtoms xs -> liftM NAtoms $ mapM nSubst xs

instance NSubst NAtom where
  nSubst atom = case atom of
    NLit x -> return $ NLit x
    NVar v -> do
      x <- asks $ flip envLookup v . fst
      return $ case x of
        Nothing -> NVar v
        Just (L x') -> x'
    NGet e i -> do
      e' <- nSubst e
      i' <- nSubst i
      return $ NGet e' i'  -- TODO atomic 'for' beta reduction
    -- AFor b body -> undefined -- TODO subst (refreshing binder) and possibly eta convert
    NLam bs body ->
      refreshBindersR bs $ \bs' -> do
        body' <- nSubst body
        return $ NLam bs' body'

instance NSubst NType where
  nSubst ty = case ty of
    NBaseType _ -> return ty
    NTypeVar v -> do
      x <- asks $ flip envLookup v . fst
      return $ case x of Nothing -> ty
                         Just (T x') -> NTypeVar x'
    NArrType as bs -> liftM2 NArrType (mapM nSubst as) (mapM nSubst bs)
    NTabType a b -> liftM2 NTabType (nSubst a) (nSubst b)
    NExists ts -> liftM NExists (mapM nSubst ts)
    NIdxSetLit _ -> return ty
    NBoundTVar _ -> return ty
