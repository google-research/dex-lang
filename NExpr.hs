module NExpr where

import Control.Monad
import Control.Monad.Reader
import Data.Foldable
import Data.Either

import Env
import Syntax
import Record
import Cat
import PPrint
import Fresh
import Type

data NExpr = NDecls [NDecl] NExpr
           | NFor NBinder NExpr
           | NPrimOp Builtin [NType] [Atom]
           | NApp Atom [Atom]
           | NAtom [Atom]

data NDecl = NLet [NBinder] NExpr
           | NUnpack [NBinder] Var NExpr

data Atom = ALit LitVal
          | AVar Var
          | AGet Atom Atom
          | NLam [NBinder] NExpr

data NType = NBaseType BaseType
           | NTypeVar Var
           | NArrType [NType] [NType]
           | NTabType NType NType
           | NExists [NType]
           | NIdxSetLit IdxSetVal
           | NBoundTVar Int

type NBinder = BinderP NType
type Scope = Env ()
type TLam = ([TBinder], Expr)
type NormEnv = FullEnv (Type, Either (RecTree Atom) TLam) (RecTree NType)
type NormM a = ReaderT NormEnv (CatT ([NDecl], Scope) (Either Err)) a

normalize :: Expr -> NormM (RecTree Atom)
normalize expr = case expr of
  Lit x -> return $ RecLeaf $ ALit x
  Var v -> asks $ fromLeft (error msg) . snd. fromL . (! v )
             -- TODO: use this error pattern for env loookups too
             where msg = "Type lambda should be immediately applied"
  PrimOp b [] xs -> do
    xs' <- mapM normalize xs
    writeExpr $ NPrimOp b [] (fmap fromLeaf xs') -- TODO: subst types
  Decls [] body -> normalize body
  Decls (decl:decls) final -> do
    case decl of
      Let (v:>ty) (TLam tbs body) ->
        extendR (v@>L (ty, Right (tbs, body))) $ normalize rest
      Let b bound -> do
        bound' <- normalizeScoped bound
        normalizeBinder b $ \bs -> do
          extend $ asFst [NLet bs bound']
          normalize rest
      Unpack b tv bound -> do
        bound' <- normalizeScoped bound
        tv' <- freshVar tv
        extendR (tv @> T (RecLeaf (NTypeVar tv'))) $
          normalizeBinder b $ \bs -> do
            extend $ asFst [NUnpack bs tv' bound']
            normalize rest
    where rest = Decls decls final
  Lam b body -> do
    normalizeBinder b $ \bs -> do
      body' <- normalizeScoped body
      return $ RecLeaf $ NLam bs body'
  App f x -> do
    f' <- normalize f
    x' <- normalize x
    writeExpr $ NApp (fromLeaf f') (toList x')
  For b body -> do
    normalizeBinder b $ \[b'] -> do
      body' <- normalizeScoped body
      writeExpr $ NFor b' body'
  Get e i -> do
    e' <- normalize e
    i' <- normalize i
    return $ fmap (flip AGet (fromLeaf i')) e'
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
     writeExpr :: NExpr -> NormM (RecTree Atom)
     writeExpr nexpr = do
       ty <- exprType expr
       writeVars ty nexpr

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

normalizeBinder :: Binder -> ([NBinder] -> NormM a) -> NormM a
normalizeBinder (v:>ty) cont = do
  tys <- normalizeTy ty
  bs <- flip traverse tys $ \t -> do
          v' <- freshVar v -- TODO: incorporate field names
          return $ v':>t
  extendR (v @> L (ty, Left (fmap (AVar . binderVar) bs))) $
    cont (toList bs)

normalizeScoped :: Expr -> NormM NExpr
normalizeScoped expr = do
  (body, (decls, _)) <- scoped $ normalize expr
  -- TODO: reduce clutter in the case where these atoms are all
  -- vars bound at last expression
  return $ NDecls decls $ NAtom (toList body)

exprType :: Expr -> NormM Type
exprType expr = do
  env <- ask
  let env' = flip fmap env $ \x -> case x of L (ty,_) -> L ty
                                             T _      -> T ()
  return $ getType env' expr

writeVars :: Type -> NExpr -> NormM (RecTree Atom)
writeVars ty expr = do
  tys <- normalizeTy ty
  bs <- flip traverse tys $ \t -> do
          v' <- freshVar (rawName "tmp")
          return $ v':>t
  extend $ asFst [NLet (toList bs) expr]
  return $ fmap (AVar . binderVar) bs
