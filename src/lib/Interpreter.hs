-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Interpreter (
  evalBlock, evalExpr, indices, indexSetSize,
  runInterpM, liftInterpM, InterpM, Interp,
  traverseSurfaceAtomNames) where

import Control.Monad.IO.Class
import Data.Int
import Data.Foldable (toList)
import Foreign.Ptr
import Foreign.Marshal.Alloc

import CUDA
import LLVMExec
import Err

import Name
import Syntax
import Type
import PPrint ()
import Builder

-- TODO: can we make this as dynamic as the compiled version?
foreign import ccall "randunif"      c_unif     :: Int64 -> Double

newtype InterpM (i::S) (o::S) (a:: *) =
  InterpM { runInterpM' :: SubstReaderT AtomSubstVal (EnvReaderT IO) i o a }
  deriving ( Functor, Applicative, Monad
           , MonadIO, ScopeReader, EnvReader, MonadFail, Fallible
           , SubstReader AtomSubstVal)

class ( SubstReader AtomSubstVal m, EnvReader2 m
      , Monad2 m, MonadIO2 m)
      => Interp m

instance Interp InterpM

runInterpM :: Distinct n => Env n -> InterpM n n a -> IO a
runInterpM bindings cont =
  runEnvReaderT bindings $ runSubstReaderT idSubst $ runInterpM' cont

liftInterpM :: (EnvReader m, MonadIO1 m, Immut n) => InterpM n n a -> m n a
liftInterpM m = do
  DB bindings <- getDB
  liftIO $ runInterpM bindings m

evalBlock :: Interp m => Block i -> m i o (Atom o)
evalBlock (Block _ decls result) = evalDecls decls $ evalExpr result

evalDecls :: Interp m => Nest Decl i i' -> m i' o a -> m i o a
evalDecls Empty cont = cont
evalDecls (Nest (Let b (DeclBinding _ _ rhs)) rest) cont = do
  result <- evalExpr rhs
  extendSubst (b @> SubstVal result) $ evalDecls rest cont

-- XXX: this doesn't go under lambda or pi binders
traverseSurfaceAtomNames
  :: (SubstReader AtomSubstVal m, EnvReader2 m)
  => Atom i
  -> (AtomName i -> m i o (Atom o))
  -> m i o (Atom o)
traverseSurfaceAtomNames atom doWithName = case atom of
  Var v -> doWithName v
  Lam _ -> substM atom
  Pi  _ -> substM atom
  DepPair l r ty -> DepPair <$> rec l <*> rec r <*> substM ty
  DepPairTy _ -> substM atom
  Con con -> Con <$> mapM rec con
  TC  tc  -> TC  <$> mapM rec tc
  Eff _ -> substM atom
  TypeCon sn defName params -> do
    defName' <- substM defName
    TypeCon sn defName' <$> mapM rec params
  DataCon printName defName params con args -> do
    defName' <- substM defName
    DataCon printName defName' <$> mapM rec params
                               <*> pure con <*> mapM rec args
  Record items -> Record <$> mapM rec items
  RecordTy _ -> substM atom
  Variant ty l con payload ->
    Variant
       <$> (fromExtLabeledItemsE <$> substM (ExtLabeledItemsE ty))
       <*> return l <*> return con <*> rec payload
  VariantTy _      -> substM atom
  LabeledRow _     -> substM atom
  ACase _ _ _ -> error "not implemented"
  DataConRef _ _ _ -> error "Should only occur in Imp lowering"
  BoxedRef _ _     -> error "Should only occur in Imp lowering"
  DepPairRef _ _ _ -> error "Should only occur in Imp lowering"
  ProjectElt idxs v -> getProjection (toList idxs) <$> rec (Var v)
  where rec x = traverseSurfaceAtomNames x doWithName

evalAtom :: Interp m => Atom i -> m i o (Atom o)
evalAtom atom = traverseSurfaceAtomNames atom \v -> do
  env <- getSubst
  case env ! v of
    SubstVal x -> return x
    Rename v' -> do
      ~(AtomNameBinding bindingInfo) <- lookupEnv v'
      case bindingInfo of
        LetBound (DeclBinding _ _ (Atom x)) -> dropSubst $ evalAtom x
        PtrLitBound ty ptr -> return $ Con $ Lit $ PtrLit ty ptr
        _ -> error "shouldn't have irreducible atom names left"

evalExpr :: Interp m => Expr i -> m i o (Atom o)
evalExpr expr = case expr of
  App f x -> do
    f' <- evalAtom f
    x' <- evalAtom x
    case f' of
      Lam (LamExpr b body) -> dropSubst $ extendSubst (b @> SubstVal x') $ evalBlock body
      _     -> error $ "Expected a fully evaluated function value: " ++ pprint f
  Atom atom -> evalAtom atom
  Op op     -> evalOp op
  Case e alts _ -> do
    e' <- evalAtom e
    case trySelectBranch e' of
      Nothing -> error "branch should be chosen at this point"
      Just (con, args) -> do
        Abs bs body <- return $ alts !! con
        extendSubst (bs @@> map SubstVal args) $ evalBlock body
  Hof hof -> case hof of
    RunIO (Lam (LamExpr b body)) ->
      extendSubst (b @> SubstVal UnitTy) $
        evalBlock body
    _ -> error $ "Not implemented: " ++ pprint expr

evalOp :: Interp m => Op i -> m i o (Atom o)
evalOp expr = mapM evalAtom expr >>= \case
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
    _ -> evalBuilder $ indexToInt $ sink idxArg
  _ -> error $ "Not implemented: " ++ pprint expr

evalBuilder :: (Interp m, SinkableE e, SubstE AtomSubstVal e)
            => (forall l. (Emits l, Ext n l, Distinct l) => BuilderM l (e l))
            -> m i n (e n)
evalBuilder cont = dropSubst do
  Abs decls result <- liftBuilder $ fromDistinctAbs <$> buildScoped cont
  evalDecls decls $ substM result

pattern Int64Val :: Int64 -> Atom n
pattern Int64Val x = Con (Lit (Int64Lit x))

pattern Float64Val :: Double -> Atom n
pattern Float64Val x = Con (Lit (Float64Lit x))
