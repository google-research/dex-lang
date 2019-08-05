{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}

module Interpreter (interpPass) where

import Control.Monad.Reader
import Data.Foldable (fold)

import Syntax
import Env
import Pass
import PPrint
import Cat
import Record

-- TODO: can we make this as dynamic as the compiled version?
foreign import ccall "sqrt" c_sqrt :: Double -> Double
foreign import ccall "sin"  c_sin  :: Double -> Double
foreign import ccall "cos"  c_cos  :: Double -> Double
foreign import ccall "tan"  c_tan  :: Double -> Double
foreign import ccall "exp"  c_exp  :: Double -> Double
foreign import ccall "log"  c_log  :: Double -> Double

type Val = Expr -- irreducible expressions only
type Scope = Env ()
type SubstEnv = (FullEnv Val Type, Scope)
type ReduceM a = Reader SubstEnv a

interpPass :: TopDecl -> TopPass SubstEnv ()
interpPass topDecl = () <$ case topDecl of
  TopDecl decl -> do
    env <- getEnv
    putEnv $ runReader (reduceDecl decl) env
  EvalCmd (Command (EvalExpr Printed) expr) -> do
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
  Decls (decl:rest) body -> do
    env' <- reduceDecl decl
    extendR env' $ reduce (Decls rest body)
  Lam _ _ -> subst expr
  App e1 e2 -> do
    Lam p body <- reduce e1
    x <- reduce e2
    extendR (bindPat p x) (reduce body)
  RecCon r -> liftM RecCon (traverse reduce r)

reduceDecl :: Decl -> ReduceM SubstEnv
reduceDecl (Let p expr) = do val <- reduce expr
                             return $ bindPat p val

bindPat :: Pat -> Val -> SubstEnv
bindPat (RecLeaf (v:>_)) val = asFst $ v @> L val
bindPat (RecTree r) (RecCon r') = fold $ recZipWith bindPat r r'

evalOp :: Builtin -> [Type] -> [Val] -> Val
evalOp op ts xs = case op of
  IAdd -> intBinOp (+) xs
  ISub -> intBinOp (-) xs
  IMul -> intBinOp (*) xs
  FAdd -> realBinOp (+) xs
  FSub -> realBinOp (-) xs
  FMul -> realBinOp (*) xs
  FFICall 1 "sqrt" -> realUnOp c_sqrt xs
  FFICall 1 "sin"  -> realUnOp c_sin  xs
  FFICall 1 "cos"  -> realUnOp c_cos  xs
  FFICall 1 "tan"  -> realUnOp c_tan  xs
  FFICall 1 "exp"  -> realUnOp c_exp  xs
  FFICall 1 "log"  -> realUnOp c_log  xs


intBinOp :: (Int -> Int -> Int) -> [Val] -> Val
intBinOp op [Lit (IntLit x), Lit (IntLit y)] = Lit $ IntLit $ op x y

realBinOp :: (Double -> Double -> Double) -> [Val] -> Val
realBinOp op [Lit (RealLit x), Lit (RealLit y)] = Lit $ RealLit $ op x y

realUnOp :: (Double -> Double) -> [Val] -> Val
realUnOp op [Lit (RealLit x)] = Lit $ RealLit $ op x

class Subst a where
  subst :: MonadReader SubstEnv m => a -> m a

instance Subst Expr where
  subst expr = case expr of
    Lit _ -> return expr
    Var v -> do
      x <- asks $ flip envLookup v . fst
      case x of
        Nothing -> return expr
        Just (L x') -> local dropSubst (subst x')
          where dropSubst (_, scope) = (mempty, scope)
    PrimOp op ts xs -> liftM2 (PrimOp op) (mapM subst ts) (mapM subst xs)
    Decls [] body -> subst body
    Decls (decl:rest) final -> case decl of
      Let p bound -> do
        bound' <- subst bound
        refreshPat p $ \p' -> do
           body' <- subst body
           return $ wrapDecls [Let p' bound'] body'
      where body = Decls rest final
    Lam p body -> do
      refreshPat p $ \p' -> do
        body' <- subst body
        return $ Lam p' body'
    App e1 e2 -> liftM2 App (subst e1) (subst e2)
    For p body -> do
      refreshPat p $ \p' -> do
        body' <- subst body
        return $ For p' body'
    Get e1 e2 -> liftM2 Get (subst e1) (subst e2)
    TLam bs body -> liftM (TLam bs) (subst body) -- TODO: freshen binders
    TApp e ts -> liftM2 TApp (subst e) (mapM subst ts)
    RecCon r -> liftM RecCon (traverse subst r)
    TabCon n ty xs -> liftM2 (TabCon n) (subst ty) (mapM subst xs)
    Annot e t -> liftM2 Annot (subst e) (subst t)
    DerivAnnot e1 e2 -> liftM2 DerivAnnot (subst e1) (subst e2)
    SrcAnnot e pos -> liftM (flip SrcAnnot pos) (subst e)
    where
      refreshPat :: MonadReader SubstEnv m => Pat -> (Pat -> m a) -> m a
      refreshPat p m = m p -- TODO: actually freshen!

instance Subst Type where
  subst ty = case ty of
    BaseType _ -> return ty
    TypeVar v -> do
      x <- asks $ flip envLookup v . fst
      return $ case x of Nothing -> ty
                         Just (T ty') -> ty'
    ArrType a b -> liftM2 ArrType (subst a) (subst b)
    TabType a b -> liftM2 TabType (subst a) (subst b)
    RecType r -> liftM RecType $ traverse subst r
    Forall ks body -> liftM (Forall ks) (subst body)
    Exists body -> liftM Exists (subst body)
    IdxSetLit _ -> return ty
    BoundTVar _ -> return ty
