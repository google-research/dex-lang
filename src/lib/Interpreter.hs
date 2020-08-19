-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE Rank2Types #-}

module Interpreter (evalBlock, indices, indexSetSize, evalEmbed) where

import Data.Foldable
import Data.Int

import Array
import Cat
import Syntax
import Env
import PPrint
import Embed
import Type
import Util (restructure)

-- TODO: can we make this as dynamic as the compiled version?
foreign import ccall "randunif"      c_unif     :: Int64 -> Double
foreign import ccall "threefry2x32"  c_threefry :: Int64 -> Int64 -> Int64

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
    IAdd -> applyIntBinOp   (+) x y
    ISub -> applyIntBinOp   (-) x y
    IMul -> applyIntBinOp   (*) x y
    IDiv -> applyIntBinOp   div x y
    IRem -> applyIntBinOp   rem x y
    FAdd -> applyFloatBinOp (+) x y
    FSub -> applyFloatBinOp (-) x y
    FMul -> applyFloatBinOp (*) x y
    FDiv -> applyFloatBinOp (/) x y
    ICmp cmp -> case cmp of
      Less         -> applyIntCmpOp (<)  x y
      Greater      -> applyIntCmpOp (>)  x y
      Equal        -> applyIntCmpOp (==) x y
      LessEqual    -> applyIntCmpOp (<=) x y
      GreaterEqual -> applyIntCmpOp (>=) x y
    _ -> error $ "Not implemented: " ++ pprint expr
  ScalarUnOp op x -> case op of
    FNeg -> applyFloatUnOp (0-) x
    _ -> error $ "Not implemented: " ++ pprint expr
  FFICall name _ args -> case name of
    "randunif"     -> Float64Val $ c_unif x         where [Int64Val x]  = args
    "threefry2x32" -> Int64Val   $ c_threefry x y    where [Int64Val x, Int64Val y] = args
    _ -> error $ "FFI function not recognized: " ++ name
  ArrayOffset arrArg _ offArg -> Con $ ArrayLit (ArrayTy b) (arrayOffset arr $ fromIntegral off)
    where (ArrayVal (ArrayTy (TabTy _ b)) arr, IdxRepVal off) = (arrArg, offArg)
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
  TC (IntRange _ _)      -> fmap (Con . Coerce ty . IdxRepVal) [0..(fromIntegral $ n - 1)]
  TC (IndexRange _ _ _)  -> fmap (Con . Coerce ty . IdxRepVal) [0..(fromIntegral $ n - 1)]
  TC (PairType lt rt)    -> [PairVal l r | l <- indices lt, r <- indices rt]
  TC (UnitType)          -> [UnitVal]
  RecordTy (NoExt types) -> let
    subindices = map indices (toList types)
    products = foldl (\prevs curs -> [cur:prev | cur <- curs, prev <- prevs]) [[]] subindices
    in map (\idxs -> Record $ restructure idxs types) products
  VariantTy (NoExt types) -> let
    subindices = fmap indices types
    reflect = reflectLabels types
    zipped = zip (toList reflect) (toList subindices)
    in concatMap (\((label, i), args) ->
      Variant (NoExt types) label i <$> args) zipped
  _ -> error $ "Not implemented: " ++ pprint ty
  where n = indexSetSize ty

getBool :: Atom -> Bool
getBool (Con (Lit (Int8Lit p))) = p /= 0
getBool x = error $ "Expected a bool atom, got: " ++ pprint x

indexSetSize :: Type -> Int
indexSetSize ty = fromIntegral l
  where (IdxRepVal l) = evalEmbed (indexSetSizeE ty)

evalEmbed :: Embed Atom -> Atom
evalEmbed embed = evalBlock mempty $ Block decls (Atom atom)
  where (atom, (_, decls)) = runEmbed embed mempty

pattern Int64Val :: Int64 -> Atom
pattern Int64Val x = Con (Lit (Int64Lit x))

pattern Float64Val :: Double -> Atom
pattern Float64Val x = Con (Lit (Float64Lit x))
