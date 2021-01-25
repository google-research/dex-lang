-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE Rank2Types #-}

module Interpreter (evalBlock, indices, indicesNoIO,
                    indexSetSize) where

import Data.Int
import Foreign.Ptr
import qualified Data.List.NonEmpty as NE
import qualified Data.Map.Strict as M
import System.IO.Unsafe (unsafePerformIO)
import Foreign.Marshal.Alloc

import Preamble
import Base
import Core
import CUDA
import LLVMExec

-- TODO: can we make this as dynamic as the compiled version?
foreign import ccall "randunif"      c_unif     :: Int64 -> Double
foreign import ccall "threefry2x32"  c_threefry :: Int64 -> Int64 -> Int64

type InterpM = IO
type InterpSubst i = () -- AtomSubst i SourceNS

-- evalModuleInterp :: SubstEnv i Void -> Module i -> InterpM (Bindings o)
-- evalModuleInterp = undefined
-- evalModuleInterp env (Module _ decls bindings) = do
--   env' <- catFoldM evalDecl env $ fromNest decls
--   return $ subst (env <> env', mempty) bindings

evalBlock :: AtomSubst i Void -> Block i -> InterpM Val
evalBlock = undefined
-- evalBlock env (Block decls result) = do
--   env' <- catFoldM evalDecl env $ fromNest decls
--   evalExpr env result

-- evalDecl :: InterpSubst i -> Decl i -> InterpM (InterpSubst i)
-- evalDecl env (Let _ v rhs) = liftM (v @>) $ evalExpr env rhs

evalExpr :: InterpSubst i -> Expr i -> InterpM Val
evalExpr = undefined
-- evalExpr env expr = case expr of
  -- App f x   -> case f of
  --   Lam a -> evalBlock env $ withoutArrow $ applyAbs voidEnv a x
  --   _     -> error $ "Expected a fully evaluated function value: " ++ pprint f
  -- Atom atom -> return $ applySubst (env, voidEnv) atom
  -- Op op     -> evalOp $ fmap (applySubst (env, voidEnv)) op
  -- Case e alts _ -> case e of
    -- DataCon _ _ con args ->
    --   evalBlock env $ applyNAbs voidEnv (fromHList alts !! con) args
    -- Variant (NoExt types) label i x -> do
    --   let LabeledItems ixtypes = enumerate types
    --   let index = fst $ ixtypes M.! label NE.!! i
    --   evalBlock env $ applyNAbs (alts !! index) [x]
    -- Con (SumAsProd _ tag xss) -> case tag of
    --   Con (Lit x) -> let i = getIntLit x in
    --     evalBlock env $ applyNAbs (alts !! i) (xss !! i)
    --   _ -> error $ "Not implemented: SumAsProd with tag " ++ pprint expr
    -- _ -> error $ "Unexpected scrutinee: " ++ pprint e
  -- Hof hof -> case hof of
  --   RunIO ~(Lam (Abs _ (WithArrow _ body))) -> evalBlock env body
  --   _ -> error $ "Not implemented: " ++ pprint expr

evalOp :: PrimOp (Atom n) -> InterpM (Atom n)
evalOp = undefined
-- evalOp expr = case expr of
--   ScalarBinOp op x y -> return $ case op of
--     IAdd -> applyIntBinOp   (+) x y
--     ISub -> applyIntBinOp   (-) x y
--     IMul -> applyIntBinOp   (*) x y
--     IDiv -> applyIntBinOp   div x y
--     IRem -> applyIntBinOp   rem x y
--     FAdd -> applyFloatBinOp (+) x y
--     FSub -> applyFloatBinOp (-) x y
--     FMul -> applyFloatBinOp (*) x y
--     FDiv -> applyFloatBinOp (/) x y
--     ICmp cmp -> case cmp of
--       Less         -> applyIntCmpOp (<)  x y
--       Greater      -> applyIntCmpOp (>)  x y
--       Equal        -> applyIntCmpOp (==) x y
--       LessEqual    -> applyIntCmpOp (<=) x y
--       GreaterEqual -> applyIntCmpOp (>=) x y
--     _ -> error $ "Not implemented: " ++ pprint expr
--   ScalarUnOp op x -> return $ case op of
--     FNeg -> applyFloatUnOp (0-) x
--     _ -> error $ "Not implemented: " ++ pprint expr
--   FFICall name _ args -> return $ case name of
--     "randunif"     -> Float64Val $ c_unif x        where [Int64Val x]  = args
--     "threefry2x32" -> Int64Val   $ c_threefry x y  where [Int64Val x, Int64Val y] = args
--     _ -> error $ "FFI function not recognized: " ++ name
--   PtrOffset (Con (Lit (PtrLit (a, t) p))) (IdxRepVal i) ->
--     return $ Con $ Lit $ PtrLit (a, t) $ p `plusPtr` (sizeOf t * fromIntegral i)
--   PtrLoad (Con (Lit (PtrLit (Heap CPU, t) p))) -> Con . Lit <$> loadLitVal p t
--   PtrLoad (Con (Lit (PtrLit (Heap GPU, t) p))) ->
--     allocaBytes (sizeOf t) $ \hostPtr -> do
--       loadCUDAArray hostPtr p (sizeOf t)
--       Con . Lit <$> loadLitVal hostPtr t
--   PtrLoad (Con (Lit (PtrLit (Stack, _) _))) ->
--     error $ "Unexpected stack pointer in interpreter"
--   ToOrdinal idxArg -> case idxArg of
--     Con (IntRangeVal   _ _   i) -> return i
--     Con (IndexRangeVal _ _ _ i) -> return i
--     _ -> evalBuilder (indexToIntE idxArg)
--   _ -> error $ "Not implemented: " ++ pprint expr

-- We can use this when we know we won't be dereferencing pointers. A better
-- approach might be to have a typeclass for the pointer dereferencing that the
-- interpreter does, with a dummy instance that throws an error if you try.
indicesNoIO :: Type n -> [Atom n]
indicesNoIO = unsafePerformIO . indices

indices :: Type n -> IO [Atom n]
indices = undefined
-- indices ty = do
--   n <- indexSetSize ty
--   case ty of
--     TC (IntRange l h)      -> return $ fmap (Con . IntRangeVal     l h . IdxRepVal) [0..(fromIntegral $ n - 1)]
--     TC (IndexRange t l h)  -> return $ fmap (Con . IndexRangeVal t l h . IdxRepVal) [0..(fromIntegral $ n - 1)]
--     TC (PairType lt rt)    -> do
--       lt' <- indices lt
--       rt' <- indices rt
--       return $ [PairVal l r | l <- lt', r <- rt']
--     TC UnitType            -> return [UnitVal]
--     RecordTy (NoExt types) -> do
--       subindices <- mapM indices (toList types)
--       -- Earlier indices change faster than later ones, so we need to first
--       -- iterate over the current index and then over all previous ones. For
--       -- efficiency we build the indices in reverse order and then reassign them
--       -- at the end with `reverse`.
--       let addAxisInReverse prevs curs = [cur:prev | cur <- curs, prev <- prevs]
--       let products = foldl addAxisInReverse [[]] subindices
--       return $ map (\idxs -> Record $ restructure (reverse idxs) types) products
--     VariantTy (NoExt types) -> do
--       subindices <- mapM indices types
--       let reflect = reflectLabels types
--       let zipped = zip (toList reflect) (toList subindices)
--       return $concatMap (\((label, i), args) ->
--         Variant (NoExt types) label i <$> args) zipped
--     _ -> error $ "Not implemented: " ++ pprint ty

indexSetSize :: Type n -> InterpM Int
indexSetSize = undefined
-- indexSetSize ty = do
--   IdxRepVal l <- evalBuilder (indexSetSizeE ty)
--   return $ fromIntegral l

-- evalBuilder :: BuilderT n InterpM (Atom n) -> InterpM (Atom n)
-- evalBuilder = undefined
-- evalBuilder builder = do
--   block <- runBuilderT builder mempty
--   evalBlock mempty (Block block)

pattern Int64Val :: Int64 -> Atom n
pattern Int64Val x = PrimCon (Lit (Int64Lit x))

pattern Float64Val :: Double -> Atom n
pattern Float64Val x = PrimCon (Lit (Float64Lit x))
