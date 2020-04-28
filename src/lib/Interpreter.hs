-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module Interpreter (evalModuleInterp) where

import Syntax
import Env
import PPrint
import Subst

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

evalModuleInterp :: Module -> IO (TopEnv, [Output])
evalModuleInterp (Module _ (ModBody [] out)) = return (out, [])
evalModuleInterp (Module _ (ModBody decls results)) = do
  let env = foldl (\sub decl -> sub <> evalDecl sub decl) mempty decls
  return (subst (env, mempty) results, [])

_evalExpr :: SubstEnv -> Expr -> Atom
_evalExpr env expr = case expr of
  Decl decl body -> _evalExpr (env <> env') body
    where env' = evalDecl env decl
  CExpr op -> evalCExpr $ subst (env, mempty) op
  Atom x -> subst (env, mempty) x

evalDecl :: SubstEnv -> Decl -> SubstEnv
evalDecl env (Let v rhs) = v @> L (evalCExpr rhs')
  where rhs' = subst (env, mempty) rhs

evalCExpr :: CExpr -> Atom
evalCExpr expr = case expr of
  ScalarBinOp op x y -> case op of
    IAdd -> IntVal $ x' + y'      where (IntVal x') = x; (IntVal y') = y
    ISub -> IntVal $ x' - y'      where (IntVal x') = x; (IntVal y') = y
    IMul -> IntVal $ x' * y'      where (IntVal x') = x; (IntVal y') = y
    Rem  -> IntVal $ x' `rem` y'  where (IntVal x') = x; (IntVal y') = y
    FAdd -> RealVal $ x' + y'  where (RealVal x') = x; (RealVal y') = y
    FSub -> RealVal $ x' - y'  where (RealVal x') = x; (RealVal y') = y
    FMul -> RealVal $ x' * y'  where (RealVal x') = x; (RealVal y') = y
    FDiv -> RealVal $ x' / y'  where (RealVal x') = x; (RealVal y') = y
    _ -> error $ "Not implemented: " ++ pprint expr
  ScalarUnOp op x -> case op of
    FNeg -> RealVal (-x')  where (RealVal x') = x
    _ -> error $ "Not implemented: " ++ pprint expr
  FFICall name _ _ args -> case name of
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
  _ -> error $ "Not implemented: " ++ pprint expr
