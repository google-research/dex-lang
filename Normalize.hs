module Normalize (normalizePass) where

import Control.Monad
import Control.Monad.Reader
import Control.Monad.Except hiding (Except)
import Data.Foldable
import Data.Either

import Env
import Syntax
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

normalizePass :: TopDecl -> TopPass NormEnv TopDecl
normalizePass decl = do normalizePass' decl
                        return decl

normalizePass' :: TopDecl -> TopPass NormEnv NTopDecl
normalizePass' topDecl = case topDecl of
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
    (ty   , []) <- asTopPass $ exprType expr
    (expr', []) <- asTopPass $ normalizeScoped expr
    case cmd of Passes -> writeOutText $ "\n\nNormalized\n" ++ pprint expr'
                _ -> return ()
    return $ NEvalCmd (Command cmd (ty, expr'))

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

type SimplifyEnv = (FullEnv NAtom Var, Scope)
type SimplifyM a = ReaderT SimplifyEnv (Either Err) a

-- TODO: consider maintaining free variables explicitly
data Ions = Ions NExpr [NBinder] [NAtom] | Unchanged

simplify :: NExpr -> SimplifyM NExpr
simplify expr = case expr of
  NDecls [] body -> simplify body
  NDecls (decl:rest) final -> case decl of
    NLet bs bound -> do
      bound' <- simplify bound
      case decompose mempty bound' of
        Unchanged ->
          refreshBinders bs $ \bs' -> do
            body' <- simplify body
            return $ wrapDecl (NLet bs' bound') body'
        Ions bound'' bs' ions ->
          extendR (bindEnv bs ions, newScope bs') $ do
            body' <- simplify body
            return $ wrapDecl (NLet bs' bound'') body'
    where body = NDecls rest final
  NFor b e ->
    refreshBinders [b] $ \[b'] -> do
      e' <- simplify e
      return $ NFor b' e'
  NPrimOp b ts xs -> liftM2 (NPrimOp b) (mapM substType ts) (mapM substAtom xs)
  NApp f xs -> do
    xs' <- mapM substAtom xs
    f <- substAtom f
    case f of
      NLam bs body -> extendR env (simplify body)
        where env = asFst $ bindEnv bs xs'
      _ -> error "Expected lambda"
  NAtoms xs -> liftM NAtoms $ mapM substAtom xs

decompose :: Env NType -> NExpr -> Ions
decompose scope expr = case expr of
  NDecls decls body -> decompose (scope <> scope') body
    where
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

refreshBinders :: [NBinder] -> ([NBinder] -> SimplifyM NExpr) -> SimplifyM NExpr
refreshBinders bs cont = undefined

substAtom :: NAtom -> SimplifyM NAtom
substAtom atom = case atom of
  NLit x -> return $ NLit x
  NVar v -> do
    x <- asks $ flip envLookup v . fst
    return $ case x of
      Nothing -> NVar v
      Just (L x') -> x'
  NGet e i -> do
    e' <- substAtom e
    i' <- substAtom i
    return $ NGet e' i'  -- TODO atomic 'for' beta reduction
  -- AFor b body -> undefined -- TODO subst (refreshing binder) and possibly eta convert
  NLam bs body -> undefined -- TODO just subst (refreshing binder)

substType :: NType -> SimplifyM NType
substType ty = undefined

wrapDecl :: NDecl -> NExpr -> NExpr
wrapDecl decl (NDecls decls body) = NDecls (decl:decls) body
wrapDecl decl body = NDecls [decl] body
