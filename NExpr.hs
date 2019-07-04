module NExpr where

import Control.Monad
import Control.Monad.Reader
import Data.Foldable

import Env
import Syntax
import Record
import Cat

data NExpr = NDecls [NDecl] NExpr
           | NFor Binder NExpr
           | NPrimOp Builtin [Type] [Atom]
           | NApp Atom [Atom]
           | NAtom [Atom]

data NDecl = NLet [Binder] NExpr
           | NUnpack [Binder] Var NExpr

data Atom = ALit LitVal
          | AVar Var
          | AGet Atom Atom
          | NLam Binder NExpr

type Scope = FullEnv Type ()
type OutDecls = ([NDecl], Scope)
type NormM a = ReaderT (Env (RecTree Atom))
                 (CatT OutDecls (Either Err)) a

normalize :: Expr -> NormM (RecTree Atom)
normalize expr = case expr of
  Lit x -> return $ RecLeaf $ ALit x
  Var v -> asks (! v )
  -- PrimOp b ts xs -> do
  --   xs' <- mapM normalize xs
  --   writeVar undefined $ NPrimOp b ts (fmap fromLeaf xs') -- TODO: subst types
  -- Decls [DeclP b] (ExprP b)
  -- Lam b body -> do
  --   body' <- normalize body
  --   return $ NAtom [NLam b body']  -- TODO: handle binder
  App f x -> do
    f' <- normalize f
    x' <- normalize x
    ty <- exprType expr
    writeExpr $ NApp (fromLeaf f') (toList x')
  For b body -> do  -- TODO: handle binder
    body' <- normalize body  -- TODO!! scoped
    writeExpr $ NFor b (NAtom $ toList body')
  Get e i -> do
    e' <- normalize e
    i' <- normalize i
    return $ fmap (flip AGet (fromLeaf i')) e'
  -- TLam [TBinder] (ExprP b)
  -- TApp (ExprP b) [Type]
  -- RecCon (Record (ExprP b))
  -- RecGet (ExprP b) RecField
  -- TabCon IdxSetVal Type [ExprP b]
  where
     writeExpr :: NExpr -> NormM (RecTree Atom)
     writeExpr nexpr = do
       ty <- exprType expr
       writeVars ty nexpr


exprType :: Expr -> NormM Type
exprType = undefined

fromLeaf :: RecTree a -> a
fromLeaf (RecLeaf x) = x

writeVars :: Type -> NExpr -> NormM (RecTree Atom)
writeVars = undefined
