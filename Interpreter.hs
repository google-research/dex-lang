{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}

module Interpreter (interpPass) where

import Control.Monad.Reader

import Syntax
import Env
import Pass
import PPrint

type Val = Expr -- irreducible expressions only
type Scope = Env ()
type SubstEnv = (FullEnv Val Type, Scope)
type ReduceM a = Reader SubstEnv a

interpPass :: TopDecl -> TopPass SubstEnv TopDecl
interpPass topDecl = topDecl <$ case topDecl of
  TopDecl decl -> do
    env <- getEnv
    putEnv $ runReader (reduceDecl decl) env
  EvalCmd (Command Interpret expr) -> do
    env <- getEnv
    writeOutText $ pprint $ runReader (reduce expr) env
  _ -> return ()

reduce :: Expr -> ReduceM Val
reduce expr = case expr of
  Lit _ -> subst expr
  Var _ -> subst expr
  PrimOp op ts xs -> do
    ts' <- mapM subst ts
    xs' <- mapM reduce xs
    return $ evalOp op ts' xs'
  Decls [] body -> reduce body
  Decls (decl:rest) body -> case decl of
    Let p e -> do
      e' <- reduce e
      bindPat p e' $ reduce body
  Lam _ _ -> subst expr
  App e1 e2 -> do
    Lam p body <- reduce e1
    x <- reduce e2
    bindPat p x $ reduce body

reduceDecl :: Decl -> ReduceM SubstEnv
reduceDecl = undefined

bindPat :: Pat -> Val -> ReduceM a -> ReduceM a
bindPat p val = undefined

evalOp :: Builtin -> [Type] -> [Val] -> Val
evalOp op ts xs = case op of
  IAdd -> intBinOp (+) xs
  ISub -> intBinOp (-) xs
  IMul -> intBinOp (*) xs
  FAdd -> realBinOp (+) xs
  FSub -> realBinOp (-) xs
  FMul -> realBinOp (*) xs

intBinOp :: (Int -> Int -> Int) -> [Val] -> Val
intBinOp op [Lit (IntLit x), Lit (IntLit y)] = Lit $ IntLit $ op x y

realBinOp :: (Double -> Double -> Double) -> [Val] -> Val
realBinOp op [Lit (RealLit x), Lit (RealLit y)] = Lit $ RealLit $ op x y

class Subst a where
  subst :: MonadReader SubstEnv m => a -> m a

instance Subst Expr where
  subst expr = case expr of
    Lit _ -> return expr

instance Subst Type where
  subst = undefined
