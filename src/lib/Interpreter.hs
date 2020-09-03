-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE Rank2Types #-}

module Interpreter (evalBlock, indices, indexSetSize) where

import Control.Monad
import Data.Foldable
import Data.Int
import Foreign.Ptr
import qualified Data.List.NonEmpty as NE
import qualified Data.Map.Strict as M

import Cat
import Syntax
import Env
import PPrint
import Embed
import Type
import Util (enumerate, restructure)
import LLVMExec

-- TODO: can we make this as dynamic as the compiled version?
foreign import ccall "randunif"      c_unif     :: Int64 -> Double
foreign import ccall "threefry2x32"  c_threefry :: Int64 -> Int64 -> Int64

type InterpM = IO

evalBlock :: SubstEnv -> Block -> InterpM Atom
evalBlock env (Block decls result) = do
  env' <- catFoldM evalDecl env decls
  evalExpr env $ subst (env <> env', mempty) result

evalDecl :: SubstEnv -> Decl -> InterpM SubstEnv
evalDecl env (Let _ v rhs) = liftM (v @>) $ evalExpr env rhs'
  where rhs' = subst (env, mempty) rhs
evalDecl env (Unpack vs rhs) = do
  let rhs' = subst (env, mempty) rhs
  ans <- evalExpr env rhs'
  let atoms = case ans of
                DataCon _ _ _ atoms' -> atoms'
                Record atoms' -> toList atoms'
                _ -> error $ "Can't unpack: " <> pprint rhs'
  return $ fold $ map (uncurry (@>)) $ zip (toList vs) atoms

evalExpr :: SubstEnv -> Expr -> InterpM Atom
evalExpr env expr = case expr of
  App f x   -> case f of
    Lam a -> evalBlock env $ snd $ applyAbs a x
    _     -> error $ "Expected a fully evaluated function value: " ++ pprint f
  Atom atom -> return $ atom
  Op op     -> evalOp op
  Case e alts _ -> case e of
    DataCon _ _ con args ->
      evalBlock env $ applyNaryAbs (alts !! con) args
    Variant (NoExt types) label i x -> do
      let LabeledItems ixtypes = enumerate types
      let index = fst $ ixtypes M.! label NE.!! i
      evalBlock env $ applyNaryAbs (alts !! index) [x]
    Con (SumAsProd _ tag xss) -> case tag of
      Con (Lit x) -> let i = getIntLit x in
        evalBlock env $ applyNaryAbs (alts !! i) (xss !! i)
      _ -> error $ "Not implemented: SumAsProd with tag " ++ pprint expr
    _ -> error $ "Unexpected scrutinee: " ++ pprint e
  _ -> error $ "Not implemented: " ++ pprint expr

evalOp :: Op -> InterpM Atom
evalOp expr = case expr of
  -- Any ops that might have a defined result even with AnyValue arguments
  -- should be implemented here.
  Select p t f -> return $ if (getBool p) then t else f
  _ -> if any isUndefined (toList expr)
         then return $ Con $ AnyValue (getType $ Op expr)
         else evalOpDefined expr
  where
    isUndefined (Con (AnyValue _)) = True
    isUndefined _                  = False

evalOpDefined :: Op -> InterpM Atom
evalOpDefined expr = case expr of
  ScalarBinOp op x y -> return $ case op of
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
  ScalarUnOp op x -> return $ case op of
    FNeg -> applyFloatUnOp (0-) x
    _ -> error $ "Not implemented: " ++ pprint expr
  FFICall name _ args -> return $ case name of
    "randunif"     -> Float64Val $ c_unif x        where [Int64Val x]  = args
    "threefry2x32" -> Int64Val   $ c_threefry x y  where [Int64Val x, Int64Val y] = args
    _ -> error $ "FFI function not recognized: " ++ name
  PtrOffset (Con (Lit (PtrLit a t p))) (IdxRepVal i) ->
    return $ Con $ Lit $ PtrLit a t $ p `plusPtr` (sizeOf t * fromIntegral i)
  PtrLoad (Con (Lit (PtrLit _ t p))) -> (Con . Lit) <$> loadLitVal p t
  IndexAsInt idxArg -> case idxArg of
    Con (IntRangeVal   _ _   i) -> return i
    Con (IndexRangeVal _ _ _ i) -> return i
    Con (AnyValue t)                       -> return $ anyValue t
    _ -> evalEmbed (indexToIntE (getType idxArg) idxArg)
  Fst p -> return x  where (PairVal x _) = p
  Snd p -> return y  where (PairVal _ y) = p
  _ -> error $ "Not implemented: " ++ pprint expr

indices :: Type -> InterpM [Atom]
indices ty = do
  n <- indexSetSize ty
  case ty of
    TC (IntRange l h)      -> return $ fmap (Con . IntRangeVal     l h . IdxRepVal) [0..(fromIntegral $ n - 1)]
    TC (IndexRange t l h)  -> return $ fmap (Con . IndexRangeVal t l h . IdxRepVal) [0..(fromIntegral $ n - 1)]
    TC (PairType lt rt)    -> do
      lt' <- indices lt
      rt' <- indices rt
      return $ [PairVal l r | l <- lt', r <- rt']
    TC (UnitType)          -> return $ [UnitVal]
    RecordTy (NoExt types) -> do
      subindices <- mapM indices (toList types)
      -- Earlier indices change faster than later ones, so we need to first
      -- iterate over the current index and then over all previous ones. For
      -- efficiency we build the indices in reverse order and then reassign them
      -- at the end with `reverse`.
      let addAxisInReverse prevs curs = [cur:prev | cur <- curs, prev <- prevs]
      let products = foldl addAxisInReverse [[]] subindices
      return $ map (\idxs -> Record $ restructure (reverse idxs) types) products
    VariantTy (NoExt types) -> do
      subindices <- mapM indices types
      let reflect = reflectLabels types
      let zipped = zip (toList reflect) (toList subindices)
      return $concatMap (\((label, i), args) ->
        Variant (NoExt types) label i <$> args) zipped
    _ -> error $ "Not implemented: " ++ pprint ty

getBool :: Atom -> Bool
getBool (Con (Lit (Int8Lit p))) = p /= 0
getBool x = error $ "Expected a bool atom, got: " ++ pprint x

indexSetSize :: Type -> InterpM Int
indexSetSize ty = do
  IdxRepVal l <- evalEmbed (indexSetSizeE ty)
  return $ fromIntegral l

evalEmbed :: EmbedT InterpM Atom -> InterpM Atom
evalEmbed embed = do
  (atom, (_, decls)) <- runEmbedT embed mempty
  evalBlock mempty $ Block decls (Atom atom)

pattern Int64Val :: Int64 -> Atom
pattern Int64Val x = Con (Lit (Int64Lit x))

pattern Float64Val :: Double -> Atom
pattern Float64Val x = Con (Lit (Float64Lit x))
