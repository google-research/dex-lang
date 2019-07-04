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

data NExpr = NDecls [NDecl] NExpr
           | NFor Binder NExpr
           | NPrimOp Builtin [NType] [Atom]
           | NApp Atom [Atom]
           | NAtom [Atom]

data NDecl = NLet [Binder] NExpr
           | NUnpack [Binder] Var NExpr

data Atom = ALit LitVal
          | AVar Var
          | AGet Atom Atom
          | NLam Binder NExpr

data NType = NBaseType BaseType
           | NTypeVar Var
           | NArrType [NType] [NType]
           | NTabType IdxSet NType
           | NExists [NType]
           | NIdxSetLit IdxSetVal
           | NBoundTVar Int

type Scope = FullEnv NType ()
type OutDecls = ([NDecl], Scope)
type TLam = ([TBinder], Expr)
type NormEnv = FullEnv ((Either (RecTree Atom) TLam)) (RecTree NType)
type NormM a = ReaderT NormEnv (CatT OutDecls (Either Err)) a

-- ** TODO: maintain binder freshness throughout **
normalize :: Expr -> NormM (RecTree Atom)
normalize expr = case expr of
  Lit x -> return $ RecLeaf $ ALit x
  Var v -> asks $ fromLeft (error msg) . fromL . (! v )
             -- TODO: use this error pattern for env loookups too
             where msg = "Type lambda should be immediately applied"
  PrimOp b [] xs -> do
    xs' <- mapM normalize xs
    writeExpr $ NPrimOp b [] (fmap fromLeaf xs') -- TODO: subst types
  Decls [] body -> normalize body
  Decls (decl:decls) final -> do
    case decl of
      Let (v:>_) (TLam tbs body) ->
        extendR (v@>L (Right (tbs, body))) $ normalize rest
      Let (v:>ty) bound -> do
        bound' <- normalizeScoped bound
        atoms <- writeVars ty bound'
        extendR (v@>L (Left atoms)) $ normalize rest
      -- Unpack b tv bound -> do
      --   bound' <- normalizeScoped bound
    where rest = Decls decls final
  Lam b body -> do
    body' <- normalizeScoped body
    return $ RecLeaf $ NLam b body'
  App f x -> do
    f' <- normalize f
    x' <- normalize x
    ty <- exprType expr
    writeExpr $ NApp (fromLeaf f') (toList x')
  For b body -> do  -- TODO: freshen binder
    body' <- normalizeScoped body
    writeExpr $ NFor b body'
  Get e i -> do
    e' <- normalize e
    i' <- normalize i
    return $ fmap (flip AGet (fromLeaf i')) e'
  -- TODO: consider finding these application sites in a bottom-up pass and
  -- making a single monorphic version for each distinct type found,
  -- rather than inlining
  TApp (Var v) ts -> do -- Assumes HM-style type lambdas only
    (bs, body) <- asks $ fromRight (error "Expected t-lambda") . fromL . (! v)
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

normalizeTy :: Type -> NormM (RecTree NType)
normalizeTy ty = undefined

normalizeScoped :: Expr -> NormM NExpr
normalizeScoped = undefined

exprType :: Expr -> NormM Type
exprType = undefined

fromLeaf :: RecTree a -> a
fromLeaf (RecLeaf x) = x

writeVars :: Type -> NExpr -> NormM (RecTree Atom)
writeVars = undefined
