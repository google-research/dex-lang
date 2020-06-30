-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module Interpreter (evalBlock, indices, indexSetSize, evalEmbed) where

import Array
import Cat
import Syntax
import Env
import PPrint
import Embed
import Type

-- TODO: can we make this as dynamic as the compiled version?
foreign import ccall "sqrt" c_sqrt :: Double -> Double
foreign import ccall "sin"  c_sin  :: Double -> Double
foreign import ccall "cos"  c_cos  :: Double -> Double
foreign import ccall "tan"  c_tan  :: Double -> Double
foreign import ccall "exp"  c_exp  :: Double -> Double
foreign import ccall "log"  c_log  :: Double -> Double
foreign import ccall "pow"  c_pow  :: Double -> Double -> Double
foreign import ccall "randunif"      c_unif     :: Int -> Double
foreign import ccall "threefry2x32"  c_threefry :: Int -> Int -> Int

evalBlock :: SubstEnv -> Block -> Atom
evalBlock env (Block decls result) = do
  let env' = catFold evalDecl env decls
  evalExpr env $ subst (env <> env', mempty) result

evalDecl :: SubstEnv -> Decl -> SubstEnv
evalDecl env (Let _ v rhs) = v @> evalExpr env rhs'
  where rhs' = subst (env, mempty) rhs

evalExpr :: SubstEnv -> Expr -> Atom
evalExpr env expr = case expr of
  App f x   -> case f of
    Lam a -> evalBlock env $ snd $ applyAbs a x
    _     -> error $ "Expected a fully evaluated function value: " ++ pprint f
  Atom atom -> atom
  Op op     -> evalOp op
  Hof _     -> error $ "Not implemented: " ++ pprint expr

evalOp :: Op -> Atom
evalOp expr = case expr of
  ScalarBinOp op x y -> case op of
    IAdd -> IntVal $ x' + y'      where (IntVal x') = x; (IntVal y') = y
    ISub -> IntVal $ x' - y'      where (IntVal x') = x; (IntVal y') = y
    IMul -> IntVal $ x' * y'      where (IntVal x') = x; (IntVal y') = y
    IDiv -> IntVal $ x' `div` y'  where (IntVal x') = x; (IntVal y') = y
    Rem  -> IntVal $ x' `rem` y'  where (IntVal x') = x; (IntVal y') = y
    FAdd -> RealVal $ x' + y'  where (RealVal x') = x; (RealVal y') = y
    FSub -> RealVal $ x' - y'  where (RealVal x') = x; (RealVal y') = y
    FMul -> RealVal $ x' * y'  where (RealVal x') = x; (RealVal y') = y
    FDiv -> RealVal $ x' / y'  where (RealVal x') = x; (RealVal y') = y
    ICmp cmp -> BoolVal $ case cmp of
      Less         -> x' <  y'
      Greater      -> x' >  y'
      Equal        -> x' == y'
      LessEqual    -> x' <= y'
      GreaterEqual -> x' >= y'
      where (IntVal x') = x; (IntVal y') = y
    _ -> error $ "Not implemented: " ++ pprint expr
  ScalarUnOp op x -> case op of
    FNeg -> RealVal (-x')  where (RealVal x') = x
    _ -> error $ "Not implemented: " ++ pprint expr
  FFICall name _ args -> case name of
    "sqrt" -> RealVal $ c_sqrt x   where [RealVal x] = args
    "sin"  -> RealVal $ c_sin  x   where [RealVal x] = args
    "cos"  -> RealVal $ c_cos  x   where [RealVal x] = args
    "tan"  -> RealVal $ c_tan  x   where [RealVal x] = args
    "exp"  -> RealVal $ c_exp  x   where [RealVal x] = args
    "log"  -> RealVal $ c_log  x   where [RealVal x] = args
    "pow"  -> RealVal $ c_pow x y  where [RealVal x, RealVal y] = args
    "randunif" -> RealVal $ c_unif x  where [IntVal x] = args
    "threefry2x32" -> IntVal $ c_threefry x y  where [IntVal x, IntVal y] = args
    _ -> error $ "FFI function not recognized: " ++ name
  ArrayOffset arrArg _ offArg -> Con $ ArrayLit (ArrayTy b) (arrayOffset arr off)
    where (ArrayVal (ArrayTy (TabTy _ b)) arr, IntVal off) = (arrArg, offArg)
  ArrayLoad arrArg -> Con $ Lit $ arrayHead arr where (ArrayVal (ArrayTy (BaseTy _)) arr) = arrArg
  IndexAsInt idxArg -> case idxArg of
    Con (AsIdx _ i)  -> i
    Con (AnyValue t) -> anyValue t
    _                -> evalEmbed (indexToIntE (getType idxArg) idxArg)
  Fst p -> x where (PairVal x _) = p
  Snd p -> y where (PairVal _ y) = p
  Select b t f -> if b' then t else f where (BoolVal b') = b
  _ -> error $ "Not implemented: " ++ pprint expr

indices :: Type -> [Atom]
indices ty = case ty of
  BoolTy                 -> [BoolVal False, BoolVal True]
  TC (IntRange _ _)      -> fmap (Con . AsIdx ty . IntVal) [0..n - 1]
  TC (IndexRange _ _ _)  -> fmap (Con . AsIdx ty . IntVal) [0..n - 1]
  TC (PairType lt rt)    -> [PairVal l r | l <- indices lt, r <- indices rt]
  TC (UnitType)          -> [UnitVal]
  TC (SumType lt rt)     -> fmap (\l -> SumVal (BoolVal True)  l (Con (AnyValue rt))) (indices lt) ++
                            fmap (\r -> SumVal (BoolVal False) (Con (AnyValue lt)) r) (indices rt)
  _ -> error $ "Not implemented: " ++ pprint ty
  where n = indexSetSize ty

indexSetSize :: Type -> Int
indexSetSize ty = i
  where (IntVal i) = evalEmbed (indexSetSizeE ty)

evalEmbed :: Embed Atom -> Atom
evalEmbed embed = evalBlock mempty $ Block decls (Atom atom)
  where (atom, (_, decls)) = runEmbed embed mempty
