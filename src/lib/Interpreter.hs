-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}

module Interpreter (interpPass) where

import Data.Foldable (fold, toList)
import Data.List (mapAccumL)
import Data.Void
import Control.Monad.State
import qualified Data.Map.Strict as M

import Syntax
import Env
import Pass
import PPrint
import Cat
import Record
import Type
import Subst

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
    extend $ reduceDecl $ subst env decl
    emitOutput NoOutput
  EvalCmd (Command (EvalExpr Printed) expr) -> do
    env <- look
    emitOutput $ TextOut $ pprint $ reduce $ subst env expr
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
subReduce env expr = reduce (subst env expr)

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
evalOp Transpose _  ~[Lam _ (RecLeaf b) body, ct] =
  fst $ sepCotangent b (transpose ct body)
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

-- === Transposition ===

type CotangentVals = MonMap Name [Val]

transpose :: Val -> Expr -> CotangentVals
transpose ct expr = case expr of
  Lit _ -> mempty
  Var v _ -> MonMap $ M.singleton v [ct]
  PrimOp op ts xs -> transposeOp op ct ts xs
  Decl (LetMono p rhs) body
    | hasFVs rhs -> cts <> transpose ct' rhs
                      where (ct', cts) = sepCotangents p $ transpose ct body
  App e1 e2
    | hasFVs e2 -> cts <> transpose ct' e2
                     where
                       (Lam _ p body) = reduce e1
                       (ct', cts) = sepCotangents p $ transpose ct body
  _ -> error $ "Can't transpose in interpreter: " ++ pprint expr

transposeOp :: Builtin -> Val -> [Type] -> [Val] -> CotangentVals
transposeOp op ct ts xs = case (op, ts, xs) of
  (FAdd, _, ~[x1, x2]) -> transpose ct x1 <> transpose ct x2
  (FMul, _, ~[x1, x2]) | hasFVs x2 -> let ct' = mul ct (reduce x1)
                                      in transpose ct' x2
                       | otherwise -> let ct' = mul ct (reduce x2)
                                      in transpose ct' x1

hasFVs :: Expr -> Bool
hasFVs expr = not $ null $ envNames $ freeVars expr

sepCotangent :: Binder -> CotangentVals -> (Val, CotangentVals)
sepCotangent (v:>ty) (MonMap m) = ( sumAt ty $ M.findWithDefault [] v m
                                  , MonMap (M.delete v m))

sepCotangents :: Pat -> CotangentVals -> (Val, CotangentVals)
sepCotangents p vs = (recTreeToVal tree, cts)
  where (tree, cts) = flip runState vs $ flip traverse p $ \b -> do
                        s <- get
                        let (x, s') = sepCotangent b s
                        put s'
                        return x

mul :: Val -> Val -> Val
mul x y = realBinOp (*) [x, y]

recTreeToVal :: RecTree Val -> Val
recTreeToVal (RecLeaf v) = v
recTreeToVal (RecTree r) = RecCon Cart $ fmap recTreeToVal r

sumAt :: Type -> [Val] -> Val
sumAt ty xs = foldr (addAt ty) (zeroAt ty) xs

addAt :: Type -> Val -> Val -> Val
addAt (BaseType RealType) ~(Lit (RealLit x)) ~(Lit (RealLit y)) = Lit (RealLit (x + y))
addAt ty _ _ = error $ "Addition not implemented for type: " ++ pprint ty

zeroAt :: Type -> Val
zeroAt (BaseType RealType) = Lit (RealLit 0.0)
zeroAt ty = error $ "Zero not implemented for type: " ++ pprint ty
