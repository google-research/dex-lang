-- Copyright 2019 Google LLC
--
-- Licensed under the Apache License, Version 2.0 (the "License");
-- you may not use this file except in compliance with the License.
-- You may obtain a copy of the License at
--
--     https://www.apache.org/licenses/LICENSE-2.0
--
-- Unless required by applicable law or agreed to in writing, software
-- distributed under the License is distributed on an "AS IS" BASIS,
-- WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
-- See the License for the specific language governing permissions and
-- limitations under the License.

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}

module Interpreter (interpPass, Subst, subst) where

import Control.Monad.Reader
import Data.Foldable (fold, toList)
import Data.List (mapAccumL)
import Data.Void

import Syntax
import Env
import Pass
import PPrint
import Cat
import Record
import Type
import Fresh

-- TODO: can we make this as dynamic as the compiled version?
foreign import ccall "sqrt" c_sqrt :: Double -> Double
foreign import ccall "sin"  c_sin  :: Double -> Double
foreign import ccall "cos"  c_cos  :: Double -> Double
foreign import ccall "tan"  c_tan  :: Double -> Double
foreign import ccall "exp"  c_exp  :: Double -> Double
foreign import ccall "log"  c_log  :: Double -> Double
foreign import ccall "randunif"      c_unif     :: Int -> Double
foreign import ccall "threefry2x32"  c_threefry :: Int -> Int -> Int

type Val = Expr -- irreducible expressions only
type Scope = Env ()
type SubstEnv = (FullEnv (Either Name TLam) Type, Scope)
type ReduceM a = Reader SubstEnv a

interpPass :: TopPass TopDecl Void
interpPass = TopPass interpPass'

interpPass' :: TopDecl -> TopPassM SubstEnv Void
interpPass' topDecl = case topDecl of
  TopDecl decl -> do
    env <- look
    extend $ runReader (reduceDecl decl) env
    emitOutput NoOutput
  EvalCmd (Command (EvalExpr Printed) expr) -> do
    env <- look
    emitOutput $ TextOut $ pprint $ runReader (reduce expr) env
  _ -> emitOutput NoOutput

reduce :: Expr -> ReduceM Val
reduce expr = case expr of
  Lit _ -> subst expr
  Var _ _ -> do
    expr' <- subst expr
    dropSubst $ reduce expr'
  PrimOp Scan _ [x, fs] -> do
    x' <- reduce x
    ~(RecType (Tup [_, ty@(TabType n _)])) <- exprType expr
    fs' <- subst fs
    scope <- asks snd
    let (carry, ys) = mapAccumL (evalScanBody scope fs') x' (enumerateIdxs n)
    return $ RecCon $ Tup [carry, TabCon ty ys]
  PrimOp op ts xs -> do
    ts' <- mapM subst ts
    xs' <- mapM reduce xs
    return $ evalOp op ts' xs'
  Decl decl body -> do
    env' <- reduceDecl decl
    extendR env' $ reduce body
  Lam _ _ -> subst expr
  App e1 e2 -> do
    ~(Lam p body) <- reduce e1
    x <- reduce e2
    dropSubst $ extendR (bindPat p x) (reduce body)
  For p body -> do
    ~(ty@(TabType n _)) <- exprType expr
    xs <- flip traverse (enumerateIdxs n) $ \i ->
            extendR (bindPat p i) (reduce body)
    return $ TabCon ty xs
  Get e i -> liftM2 idxTabCon (reduce e) (reduce i)
  RecCon r -> liftM RecCon (traverse reduce r)
  TabCon ty xs -> liftM2 TabCon (subst ty) (mapM reduce xs)
  Pack e ty exTy -> liftM3 Pack (reduce e) (subst ty) (subst exTy)
  IdxLit _ _ -> subst expr
  _ -> error $ "Can't evaluate in interpreter: " ++ pprint expr

exprType :: Expr -> ReduceM Type
exprType expr = do expr' <- subst expr
                   return $ getType mempty expr'

evalScanBody :: Scope -> Expr -> Val -> Val -> (Val, Val)
evalScanBody scope (For ip (Lam p body)) accum i =
  case runReader (reduce body) env of
    RecCon (Tup [accum', ys]) -> (accum', ys)
    val -> error $ "unexpected scan result: " ++ pprint val
  where env =  bindPat ip i <> bindPat p accum <> asSnd scope
evalScanBody _ e _ _ = error $ "Bad scan argument: " ++ pprint e

enumerateIdxs :: Type -> [Val]
enumerateIdxs (IdxSetLit n) = map (IdxLit n) [0..n-1]
enumerateIdxs (RecType r) = map RecCon $ traverse enumerateIdxs r  -- list monad
enumerateIdxs ty = error $ "Not an index type: " ++ pprint ty

idxTabCon :: Val -> Val -> Val
idxTabCon (TabCon _ xs) i = xs !! idxToInt i
idxTabCon v _ = error $ "Not a table: " ++ pprint v

idxToInt :: Val -> Int
idxToInt i = snd (flattenIdx i)

intToIdx :: Type -> Int -> Val
intToIdx ty i = idxs !! (i `mod` length idxs)
  where idxs = enumerateIdxs ty

flattenIdx :: Val -> (Int, Int)
flattenIdx (IdxLit n i) = (n, i)
flattenIdx (RecCon r) = foldr f (1,0) $ map flattenIdx (toList r)
  where f (size, idx) (cumSize, cumIdx) = (cumSize * size, cumIdx + idx * cumSize)
flattenIdx v = error $ "Not a valid index: " ++ pprint v

reduceDecl :: Decl -> ReduceM SubstEnv
reduceDecl (LetMono p expr) = do
  val <- reduce expr
  return $ bindPat p val
reduceDecl (LetPoly (v:>_) tlam) = do
  tlam' <- subst tlam
  return $ asFst $ v @> L (Right tlam')
reduceDecl (Unpack (v:>_) tv expr) = do
  ~(Pack val ty _) <- reduce expr
  return $ asFst $ v @> L (Right (TLam [] val)) <> tv @> T ty
reduceDecl (TAlias _ _ ) = error "Shouldn't have TAlias left"

bindPat :: Pat -> Val -> SubstEnv
bindPat (RecLeaf (v:>_)) val = asFst $ v @> L (Right (TLam [] val))
bindPat (RecTree r) (RecCon r') = fold $ recZipWith bindPat r r'
bindPat _ _ = error "Bad pattern"

evalOp :: Builtin -> [Type] -> [Val] -> Val
evalOp IAdd _ xs = intBinOp (+) xs
evalOp ISub _ xs = intBinOp (-) xs
evalOp IMul _ xs = intBinOp (*) xs
evalOp Mod  _ xs = intBinOp mod xs
evalOp FAdd _ xs = realBinOp (+) xs
evalOp FSub _ xs = realBinOp (-) xs
evalOp FMul _ xs = realBinOp (*) xs
evalOp FDiv _ xs = realBinOp (/) xs
evalOp BoolToInt _ ~[Lit (BoolLit x)] = Lit $ IntLit (if x then 1 else 0)
evalOp FLT _ ~[x, y] = Lit $ BoolLit $ fromRealLit x < fromRealLit y
evalOp FGT _ ~[x, y] = Lit $ BoolLit $ fromRealLit x > fromRealLit y
evalOp ILT _ ~[x, y] = Lit $ BoolLit $ fromIntLit  x < fromIntLit  y
evalOp IGT _ ~[x, y] = Lit $ BoolLit $ fromIntLit  x > fromIntLit  y
evalOp Range _ ~[x] = Pack unitCon (IdxSetLit (fromIntLit x)) (Exists unitTy)
evalOp IndexAsInt _ ~[x] = Lit (IntLit (idxToInt x))
evalOp IntAsIndex ~[ty] ~[Lit (IntLit x)] = intToIdx ty x
evalOp IntToReal _ ~[Lit (IntLit x)] = Lit (RealLit (fromIntegral x))
evalOp Filter _  ~[f, TabCon (TabType _ ty) xs] =
  exTable ty $ filter (fromBoolLit . asFun f) xs
evalOp (FFICall _ name) _ xs = case name of
  "sqrt" -> realUnOp c_sqrt xs
  "sin"  -> realUnOp c_sin  xs
  "cos"  -> realUnOp c_cos  xs
  "tan"  -> realUnOp c_tan  xs
  "exp"  -> realUnOp c_exp  xs
  "log"  -> realUnOp c_log  xs
  "randunif"  -> case xs of [Lit (IntLit x)] -> Lit $ RealLit $ c_unif x
                            _ -> error "bad arg"
  "threefry2x32" -> intBinOp c_threefry xs
  _ -> error $ "FFI function not recognized: " ++ name
evalOp op _ _ = error $ "Primop not implemented: " ++ pprint op

asFun :: Val -> Val -> Val
asFun f x = runReader (reduce (App f x)) mempty

exTable :: Type -> [Expr] -> Expr
exTable ty xs = Pack (TabCon ty xs) (IdxSetLit (length xs)) exTy
  where exTy = Exists $ TabType (BoundTVar 0) ty

intBinOp :: (Int -> Int -> Int) -> [Val] -> Val
intBinOp op [Lit (IntLit x), Lit (IntLit y)] = Lit $ IntLit $ op x y
intBinOp _ xs = error $ "Bad args: " ++ pprint xs

realBinOp :: (Double -> Double -> Double) -> [Val] -> Val
realBinOp op [Lit (RealLit x), Lit (RealLit y)] = Lit $ RealLit $ op x y
realBinOp _ xs = error $ "Bad args: " ++ pprint xs

realUnOp :: (Double -> Double) -> [Val] -> Val
realUnOp op [Lit (RealLit x)] = Lit $ RealLit $ op x
realUnOp _ xs = error $ "Bad args: " ++ pprint xs

fromIntLit :: Val -> Int
fromIntLit (Lit (IntLit x)) = x
fromIntLit x = error $ "Not an int lit: " ++ pprint x

fromRealLit :: Val -> Double
fromRealLit (Lit (RealLit x)) = x
fromRealLit x = error $ "Not a real lit: " ++ pprint x

fromBoolLit :: Val -> Bool
fromBoolLit (Lit (BoolLit x)) = x
fromBoolLit x = error $ "Not a bool lit: " ++ pprint x

dropSubst :: MonadReader SubstEnv m => m a -> m a
dropSubst m = do local (\(_, scope) -> (mempty, scope)) m

class Subst a where
  subst :: MonadReader SubstEnv m => a -> m a

instance Subst Expr where
  subst expr = case expr of
    Lit _ -> return expr
    Var v tys -> do
      tys' <- mapM subst tys
      x <- asks $ flip envLookup v . fst
      case x of
        Nothing -> return $ Var v tys'
        Just (L (Left v')) -> return $ Var v' tys'
        Just (L (Right (TLam tbs body))) -> dropSubst $ extendR env (subst body)
          where env = asFst $ fold [tv @> T t | (tv:>_, t) <- zip tbs tys']
        Just (T _ ) -> error "Expected let-bound var"
    PrimOp op ts xs -> liftM2 (PrimOp op) (mapM subst ts) (mapM subst xs)
    Decl decl body -> case decl of
      LetMono p bound -> do
        bound' <- subst bound
        refreshPat p $ \p' -> do
          body' <- subst body
          return $ Decl (LetMono p' bound') body'
      LetPoly (v:>ty) tlam -> do
        tlam' <- subst tlam
        ty' <- subst ty
        v' <- asks $ rename v . snd
        body' <- extendR ((v @> L (Left v'), v' @> ())) (subst body)
        return $ Decl (LetPoly (v':>ty') tlam') body'
      Unpack b tv bound -> do
        bound' <- subst bound
        refreshTBinders [tv:>idxSetKind] $ \[tv':>_] ->
          refreshPat [b] $ \[b'] -> do
            body' <- subst body
            return $ Decl (Unpack b' tv' bound') body'
      TAlias _ _ -> error "Shouldn't have TAlias left"
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
    RecCon r -> liftM RecCon (traverse subst r)
    IdxLit _ _ -> return expr
    TabCon ty xs -> liftM2 TabCon (subst ty) (mapM subst xs)
    Pack e ty exTy -> liftM3 Pack (subst e) (subst ty) (subst exTy)
    Annot e t -> liftM2 Annot (subst e) (subst t)
    DerivAnnot e1 e2 -> liftM2 DerivAnnot (subst e1) (subst e2)
    SrcAnnot e pos -> liftM (flip SrcAnnot pos) (subst e)

instance Subst TLam where
  subst (TLam tbs body) = refreshTBinders tbs $ \tbs' ->
                            liftM (TLam tbs') (subst body)

-- Might be able to de-dup these with explicit traversals, lens-style
refreshPat :: (Traversable t, MonadReader SubstEnv m) =>
                t Binder -> (t Binder -> m a) -> m a
refreshPat p m = do
  p' <- traverse (traverse subst) p
  scope <- asks snd
  let (p'', (env', scope')) =
        flip runCat (mempty, scope) $ flip traverse p' $ \(v:>ty) -> do
          v' <- freshCatSubst v
          return (v':>ty)
  extendR (fmap (L . Left) env', scope') $ m p''

refreshTBinders :: MonadReader SubstEnv m => [TBinder] -> ([TBinder] -> m a) -> m a
refreshTBinders bs m = do
  scope <- asks snd
  let (bs', (env', scope')) =
        flip runCat (mempty, scope) $ flip traverse bs $ \(v:>k) -> do
          v' <- freshCatSubst v
          return (v':>k)
  extendR (fmap (T . TypeVar) env', scope') $ m bs'

instance Subst Type where
  subst ty = case ty of
    BaseType _ -> return ty
    TypeVar v -> do
      x <- asks $ flip envLookup v . fst
      return $ case x of Nothing -> ty
                         Just (T ty') -> ty'
                         Just (L _) -> error "Expected type var"
    ArrType a b -> liftM2 ArrType (subst a) (subst b)
    TabType a b -> liftM2 TabType (subst a) (subst b)
    RecType r -> liftM RecType $ traverse subst r
    Exists body -> liftM Exists (subst body)
    IdxSetLit _ -> return ty
    BoundTVar _ -> return ty

instance Subst SigmaType where
  subst (Forall ks body) = liftM (Forall ks) (subst body)

instance Subst Binder where
  -- TODO: this only substitutes the type!
  subst (v:>ty) = liftM (v:>) (subst ty)

instance Subst Pat where
  subst p = traverse subst p

instance (Subst a, Subst b) => Subst (a, b) where
  subst (x, y) = liftM2 (,) (subst x) (subst y)
