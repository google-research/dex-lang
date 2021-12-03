-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE Rank2Types #-}

module Interpreter (evalBlock, indices, indexSetSize) where

import Control.Monad
import Control.Monad.IO.Class
import Data.Foldable
import Data.Int
import Foreign.Ptr
import qualified Data.List.NonEmpty as NE
import qualified Data.Map.Strict as M
import System.IO.Unsafe (unsafePerformIO)
import Foreign.Marshal.Alloc

import CUDA
import LabeledItems
import Util (enumerate, restructure)
import LLVMExec

import SaferNames.Name
import SaferNames.Syntax
import SaferNames.Type
import SaferNames.PPrint
import SaferNames.Builder

-- TODO: can we make this as dynamic as the compiled version?
foreign import ccall "randunif"      c_unif     :: Int64 -> Double

newtype InterpM (i::S) (o::S) (a:: *) = InterpM ()

class ( EnvReader AtomSubstVal m, BindingsReader2 m
      , Monad2 m, MonadIO2 m)
      => Interp m

runInterpM :: Distinct n => Bindings n -> InterpM n n a -> a
runInterpM = undefined

evalBlock :: Interp m => Block i -> m i o (Atom o)
evalBlock (Block _ decls result) = evalDecls decls $ evalExpr result

evalDecls :: Interp m => Nest Decl i i' -> m i' o a -> m i o a
evalDecls Empty cont = cont
evalDecls (Nest (Let b (DeclBinding _ _ rhs)) rest) cont = do
  result <- evalExpr rhs
  extendEnv (b @> SubstVal result) $ evalDecls rest cont

evalExpr :: Interp m => Expr i -> m i o (Atom o)
evalExpr expr = case expr of
  App f x -> do
    f' <- substM f
    x' <- substM x
    case f' of
      Lam (LamExpr b body) -> dropSubst $ extendEnv (b @> SubstVal x') $ evalBlock body
      _     -> error $ "Expected a fully evaluated function value: " ++ pprint f
  Atom atom -> substM atom
  Op op     -> evalOp op
  Case e alts _ -> do
    e' <- substM e
    case trySelectBranch e' of
      Nothing -> error "branch should be chosen at this point"
      Just (con, args) -> do
        Abs bs body <- return $ alts !! con
        extendEnv (bs @@> map SubstVal args) $ evalBlock body
  Hof hof -> case hof of
    RunIO (Lam (LamExpr b body)) ->
      extendEnv (b @> SubstVal UnitTy) $
        evalBlock body
    _ -> error $ "Not implemented: " ++ pprint expr

evalOp :: Interp m => Op i -> m i o (Atom o)
evalOp expr = mapM substM expr >>= \case
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
    _ -> error $ "FFI function not recognized: " ++ name
  PtrOffset (Con (Lit (PtrLit (a, t) p))) (IdxRepVal i) ->
    return $ Con $ Lit $ PtrLit (a, t) $ p `plusPtr` (sizeOf t * fromIntegral i)
  PtrLoad (Con (Lit (PtrLit (Heap CPU, t) p))) ->
    Con . Lit <$> liftIO (loadLitVal p t)
  PtrLoad (Con (Lit (PtrLit (Heap GPU, t) p))) ->
    liftIO $ allocaBytes (sizeOf t) $ \hostPtr -> do
      loadCUDAArray hostPtr p (sizeOf t)
      Con . Lit <$> loadLitVal hostPtr t
  PtrLoad (Con (Lit (PtrLit (Stack, _) _))) ->
    error $ "Unexpected stack pointer in interpreter"
  ToOrdinal idxArg -> case idxArg of
    Con (IntRangeVal   _ _   i) -> return i
    Con (IndexRangeVal _ _ _ i) -> return i
    _ -> evalBuilder $ indexToInt $ inject idxArg
  _ -> error $ "Not implemented: " ++ pprint expr

evalBuilder :: (Interp m, InjectableE e, SubstE AtomSubstVal e)
            => (forall l. (Emits l, Ext n l, Distinct l) => BuilderM l (e l))
            -> m i n (e n)
evalBuilder cont = dropSubst do
  Abs decls result <- liftBuilder $ fromDistinctAbs <$> buildScoped cont
  evalDecls decls $ substM result

pattern Int64Val :: Int64 -> Atom n
pattern Int64Val x = Con (Lit (Int64Lit x))

pattern Float64Val :: Double -> Atom n
pattern Float64Val x = Con (Lit (Float64Lit x))
