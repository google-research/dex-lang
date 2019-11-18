-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

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

type ClosedExpr = Expr -- no free variables
type Val        = Expr -- irreducible expressions only
type Scope = Env ()
type SubstEnv = (FullEnv (Either Name TLam) Type, Scope)

interpPass :: TopPass TopDecl Void
interpPass = TopPass interpPass'

interpPass' :: TopDecl -> TopPassM SubstEnv Void
interpPass' topDecl = case topDecl of
  TopDecl decl -> do
    env <- look
    extend $ reduceDecl $ applySub env decl
    emitOutput NoOutput
  EvalCmd (Command (EvalExpr Printed) expr) -> do
    env <- look
    emitOutput $ TextOut $ pprint $ reduce $ applySub env expr
  _ -> emitOutput NoOutput

reduce :: ClosedExpr -> Val
reduce expr = case expr of
  Lit _ -> expr
  Var _ _ -> error $ "Can only reduce closed expression. Got: " ++ pprint expr
  PrimOp Scan _ [x, fs] -> RecCon Cart $ Tup [carry, TabCon ty ys]
    where
      x'  = reduce x
      (RecType _ (Tup [_, ty@(TabType n _)])) = getType mempty expr
      (carry, ys) = mapAccumL (evalScanBody fs) x' (enumerateIdxs n)
  PrimOp op ts xs -> evalOp op ts (map reduce xs)
  Decl decl body  -> subReduce (reduceDecl decl) body
  Lam _ _ _ -> expr
  App e1 e2 -> subReduce (bindPat p (reduce e2)) body
    where (Lam _ p body) = reduce e1
  For p body -> TabCon ty xs
    where
      (ty@(TabType n _)) = getType mempty expr
      xs = map (\i -> subReduce (bindPat p i) body) (enumerateIdxs n)
  Get e i        -> idxTabCon (reduce e) (reduce i)
  RecCon k r     -> RecCon k (fmap reduce r)
  TabCon ty xs   -> TabCon ty (map reduce xs)
  Pack e ty exTy -> Pack (reduce e) ty exTy
  IdxLit _ _ -> expr
  _ -> error $ "Can't evaluate in interpreter: " ++ pprint expr

subReduce :: SubstEnv -> Expr -> Val
subReduce env expr = reduce (applySub env expr)

evalScanBody :: Expr -> Val -> Val -> (Val, Val)
evalScanBody (For ip (Lam _ p body)) accum i =
  case subReduce env body of
    RecCon _ (Tup [accum', ys]) -> (accum', ys)
    val -> error $ "unexpected scan result: " ++ pprint val
  where env =  bindPat ip i <> bindPat p accum
evalScanBody e _ _ = error $ "Bad scan argument: " ++ pprint e

enumerateIdxs :: Type -> [Val]
enumerateIdxs (IdxSetLit n) = map (IdxLit n) [0..n-1]
enumerateIdxs (RecType k r) = map (RecCon k) $ traverse enumerateIdxs r  -- list monad
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
flattenIdx (RecCon _ r) = foldr f (1,0) $ map flattenIdx (toList r)
  where f (size, idx) (cumSize, cumIdx) = (cumSize * size, cumIdx + idx * cumSize)
flattenIdx v = error $ "Not a valid index: " ++ pprint v

reduceDecl :: Decl -> SubstEnv
reduceDecl (LetMono p expr) = bindPat p (reduce expr)
reduceDecl (LetPoly (v:>_) tlam) = asFst $ v @> L (Right tlam)
reduceDecl (Unpack (v:>_) tv expr) =
  asFst $ v @> L (Right (TLam [] val)) <> tv @> T ty
  where (Pack val ty _) = reduce expr
reduceDecl (TAlias _ _ ) = error "Shouldn't have TAlias left"

bindPat :: Pat -> Val -> SubstEnv
bindPat (RecLeaf (v:>_)) val = asFst $ v @> L (Right (TLam [] val))
bindPat (RecTree r) (RecCon _ r') = fold $ recZipWith bindPat r r'
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
asFun f x = reduce (App f x)

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

applySub :: Subst a => SubstEnv -> a -> a
applySub sub x = runReader (subst x) sub

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
    Decl decl body -> do
      (decl', env) <- substDeclEnv decl
      body' <- extendR env (subst body)
      return $ Decl decl' body'
    Lam l p body -> do
      p' <- traverse subst p
      (p'', env) <- renamePat p'
      body' <- extendR env (subst body)
      return $ Lam l p'' body'
    App e1 e2 -> liftM2 App (subst e1) (subst e2)
    For p body -> do
      p' <- traverse subst p
      (p'', env) <- renamePat p'
      body' <- extendR env (subst body)
      return $ For p'' body'
    Get e1 e2 -> liftM2 Get (subst e1) (subst e2)
    RecCon k r -> liftM (RecCon k) (traverse subst r)
    IdxLit _ _ -> return expr
    TabCon ty xs -> liftM2 TabCon (subst ty) (mapM subst xs)
    Pack e ty exTy -> liftM3 Pack (subst e) (subst ty) (subst exTy)
    Annot e t -> liftM2 Annot (subst e) (subst t)
    DerivAnnot e1 e2 -> liftM2 DerivAnnot (subst e1) (subst e2)
    SrcAnnot e pos -> liftM (flip SrcAnnot pos) (subst e)

substDeclEnv :: MonadReader SubstEnv m => Decl -> m (Decl, SubstEnv)
substDeclEnv decl = do
  decl' <- subst decl
  case decl' of
    LetMono p rhs -> do
      (p', env) <- renamePat p
      return (LetMono p' rhs, env)
    LetPoly (v:>ty) tlam -> do
      v' <- asks $ rename v . snd
      let env = (v @> L (Left v'), v' @> ())
      return (LetPoly (v':>ty) tlam, env)
    Unpack b tv bound -> do
      ~([tv':>_], env) <- renameTBinders [tv:>idxSetKind]
      ~([b'], env') <- extendR env $ renamePat [b]
      return (Unpack b' tv' bound, env <> env')
    TAlias _ _ -> error "Shouldn't have TAlias left"

instance Subst Decl where
  subst decl = case decl of
    LetMono p bound   -> liftM2 LetMono (traverse subst p) (subst bound)
    LetPoly b tlam    -> liftM2 LetPoly (traverse subst b) (subst tlam)
    Unpack b tv bound -> liftM3 Unpack (subst b) (return tv) (subst bound)
    TAlias _ _ -> error "Shouldn't have TAlias left"

instance Subst TLam where
  subst (TLam tbs body) = do
    (tbs', env) <- renameTBinders tbs
    body' <- extendR env (subst body)
    return $ TLam tbs' body'

renamePat :: (Traversable t, MonadReader SubstEnv m) =>
                t Binder  -> m (t Binder, SubstEnv)
renamePat p = do
  scope <- asks snd
  let (p', (env, scope')) = renameBinders p scope
  return (p', (fmap (L . Left) env, scope'))

renameTBinders :: MonadReader SubstEnv m => [TBinder] -> m ([TBinder], SubstEnv)
renameTBinders tbs = do
  scope <- asks snd
  let (tbs', (env, scope')) = renameBinders tbs scope
  return (tbs', (fmap (T . TypeVar) env, scope'))

instance Subst Type where
  subst ty = case ty of
    BaseType _ -> return ty
    TypeVar v -> do
      x <- asks $ flip envLookup v . fst
      return $ case x of
        Nothing      -> ty
        Just (T ty') -> ty'
        Just (L _)   -> error $ "Shadowed type var: " ++ pprint v
    ArrType l a b -> liftM2 (ArrType l) (subst a) (subst b)
    TabType a b -> liftM2 TabType (subst a) (subst b)
    RecType k r -> liftM (RecType k) $ traverse subst r
    Exists body -> liftM Exists (subst body)
    IdxSetLit _ -> return ty
    BoundTVar _ -> return ty

instance Subst SigmaType where
  subst (Forall ks body) = liftM (Forall ks) (subst body)

instance Subst Binder where
  subst (v:>ty) = liftM (v:>) (subst ty)

instance Subst Pat where
  subst p = traverse subst p

instance (Subst a, Subst b) => Subst (a, b) where
  subst (x, y) = liftM2 (,) (subst x) (subst y)
