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
import Data.Foldable
import Util (restructure)

-- TODO: can we make this as dynamic as the compiled version?
foreign import ccall "randunif"      c_unif     :: Int -> Double
foreign import ccall "threefry2x32"  c_threefry :: Int -> Int -> Int

evalBlock :: SubstEnv -> Block -> Atom
evalBlock env (Block decls result) = do
  let env' = catFold evalDecl env decls
  evalExpr env $ subst (env <> env', mempty) result

evalDecl :: SubstEnv -> Decl -> SubstEnv
evalDecl env (Let _ v rhs) = v @> evalExpr env rhs'
  where rhs' = subst (env, mempty) rhs
evalDecl _ (Unpack _ _) = error "Not implemented"

evalExpr :: SubstEnv -> Expr -> Atom
evalExpr env expr = case expr of
  App f x   -> case f of
    Lam a -> evalBlock env $ snd $ applyAbs a x
    _     -> error $ "Expected a fully evaluated function value: " ++ pprint f
  Atom atom -> atom
  Op op     -> evalOp op
  _         -> error $ "Not implemented: " ++ pprint expr

evalOp :: Op -> Atom
evalOp expr = case expr of
  -- Any ops that might have a defined result even with AnyValue arguments
  -- should be implemented here.
  Select p t f -> if (getBool p) then t else f
  _ -> if any isUndefined (toList expr)
         then Con $ AnyValue (getType $ Op expr)
         else evalOpDefined expr
  where
    isUndefined (Con (AnyValue _)) = True
    isUndefined _                  = False

evalOpDefined :: Op -> Atom
evalOpDefined expr = case expr of
  ScalarBinOp op x y -> case op of
    IAdd -> asIntVal  $ x' + y'       where x' = getInt x ; y' = getInt y
    ISub -> asIntVal  $ x' - y'       where x' = getInt x ; y' = getInt y
    IMul -> asIntVal  $ x' * y'       where x' = getInt x ; y' = getInt y
    IDiv -> asIntVal  $ x' `div` y'   where x' = getInt x ; y' = getInt y
    IRem -> asIntVal  $ x' `rem` y'   where x' = getInt x ; y' = getInt y
    FAdd -> asFloatVal $ x' + y'       where x' = getFloat x; y' = getFloat y
    FSub -> asFloatVal $ x' - y'       where x' = getFloat x; y' = getFloat y
    FMul -> asFloatVal $ x' * y'       where x' = getFloat x; y' = getFloat y
    FDiv -> asFloatVal $ x' / y'       where x' = getFloat x; y' = getFloat y
    ICmp cmp -> asBoolVal $ case cmp of
      Less         -> x' <  y'
      Greater      -> x' >  y'
      Equal        -> x' == y'
      LessEqual    -> x' <= y'
      GreaterEqual -> x' >= y'
      where x' = getInt x; y' = getInt y
    _ -> error $ "Not implemented: " ++ pprint expr
  ScalarUnOp op x -> case op of
    FNeg -> asFloatVal (-x')  where x' = getFloat x
    _ -> error $ "Not implemented: " ++ pprint expr
  FFICall name _ args -> case name of
    "randunif"     -> asFloatVal $ c_unif x         where [x]    = getInt <$> args
    "threefry2x32" -> asIntVal  $ c_threefry x y   where [x, y] = getInt <$> args
    _ -> error $ "FFI function not recognized: " ++ name
  ArrayOffset arrArg _ offArg -> Con $ ArrayLit (ArrayTy b) (arrayOffset arr off)
    where (ArrayVal (ArrayTy (TabTy _ b)) arr, off) = (arrArg, getInt offArg)
  ArrayLoad arrArg -> Con $ Lit $ arrayHead arr where (ArrayVal (ArrayTy (BaseTy _)) arr) = arrArg
  IndexAsInt idxArg -> case idxArg of
    Con (Coerce (TC (IntRange   _ _  )) i) -> i
    Con (Coerce (TC (IndexRange _ _ _)) i) -> i
    Con (AnyValue t)                       -> anyValue t
    _ -> evalEmbed (indexToIntE (getType idxArg) idxArg)
  Fst p         -> x                     where (PairVal x _) = p
  Snd p         -> y                     where (PairVal _ y) = p
  _ -> error $ "Not implemented: " ++ pprint expr

indices :: Type -> [Atom]
indices ty = case ty of
  TC (IntRange _ _)      -> fmap (Con . Coerce ty . asIntVal) [0..n - 1]
  TC (IndexRange _ _ _)  -> fmap (Con . Coerce ty . asIntVal) [0..n - 1]
  TC (PairType lt rt)    -> [PairVal l r | l <- indices lt, r <- indices rt]
  TC (UnitType)          -> [UnitVal]
  RecordTy types         -> let
    subindices = map indices (toList types)
    products = foldl (\prevs curs -> [cur:prev | cur <- curs, prev <- prevs]) [[]] subindices
    in map (\idxs -> Record $ restructure idxs types) products
  VariantTy types        -> let
    subindices = fmap indices types
    reflect = reflectLabels types
    zipped = zip (toList reflect) (toList subindices)
    in concatMap (\((label, i), args) -> Variant types label i <$> args) zipped
  _ -> error $ "Not implemented: " ++ pprint ty
  where n = indexSetSize ty

getInt :: Atom -> Int
getInt (IntLit l) = getIntLit l
getInt x = error $ "Expected an integer atom, got: " ++ pprint x

getFloat :: Atom -> Double
getFloat (FloatLit l) = getFloatLit l
getFloat x = error $ "Expected a float atom, got: " ++ pprint x

getBool :: Atom -> Bool
getBool (BoolLit l) = getBoolLit l
getBool x = error $ "Expected a bool atom, got: " ++ pprint x

indexSetSize :: Type -> Int
indexSetSize ty = getIntLit l
  where (IntLit l) = evalEmbed (indexSetSizeE ty)

evalEmbed :: Embed Atom -> Atom
evalEmbed embed = evalBlock mempty $ Block decls (Atom atom)
  where (atom, (_, decls)) = runEmbed embed mempty
