-- Copyright 2021 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module MLIR.Lower (coreToMLIR) where

import qualified MLIR.AST as AST
import qualified MLIR.AST.Builder as AST
import qualified MLIR.AST.Dialect.LLVM   as LLVM
import qualified MLIR.AST.Dialect.Std    as Std
import qualified MLIR.AST.Dialect.Tensor as Tensor

import Data.Functor
import Control.Monad.Reader
import Control.Monad.State.Strict
import GHC.Stack
import qualified Data.Map.Strict    as M
import qualified Data.Text.Encoding as T

import Cat (extendR)
import Env
import Syntax
import PPrint
import Type
import Util (bindM2)
import Builder


data MLIRAtomF a = Value a
                 | Pair (MLIRAtomF a) (MLIRAtomF a)
                 | Unit
                   deriving (Functor, Foldable, Traversable)
type MLIRAtom = MLIRAtomF AST.Value

type MonadLower m = (MonadReader (Env MLIRAtom) m, AST.MonadBlockBuilder m)


coreToMLIR :: Block -> (AST.Operation, Abs (Nest Binder) Atom)
coreToMLIR block@(Block decls resultExpr) = (moduleOp, resultRecon)
  where
    attrs = AST.namedAttribute "llvm.emit_c_interface" AST.UnitAttr
    (moduleOp, Just resultRecon) = flip runReader mempty $ flip runStateT Nothing $
      AST.buildModule $ do
        AST.buildSimpleFunction "entry" [] attrs $ do
          -- NB: All args are inlined in simplification for now
          unless (null $ freeVars block) $ error "MLIR backend can't handle free variables"
          _rawArgsPtr   <- AST.blockArgument $ LLVM.Ptr i64
          rawResultsPtr <- AST.blockArgument $ LLVM.Ptr i64
          blockEnv <- lowerDecls decls
          (resultVals, recon) <- case resultExpr of
            -- The special case on Atom lets us handle results that are potentially
            -- more complicated than what MLIRAtom can represent (for example
            -- type-class dictionaries).
            Atom a -> do
              let resultVars = bindingsAsVars $ freeVars a
              let resultMAtom = foldr Pair Unit $ (blockEnv !) <$> resultVars
              (resultMValues, Abs bs consList) <-
                    toCoreAtom (mkConsListTy $ varType <$> resultVars) resultMAtom
              let Right resultAtoms = fromConsList consList
              return ( resultMValues
                     , Abs bs $ subst (newEnv resultVars resultAtoms, mempty) a)
            _ -> toCoreAtom (getType resultExpr) =<< extendR blockEnv (lowerExpr resultExpr)
          put $ Just recon  -- Smuggle the reconstruction out of this block
          forM_ (zip [0..] resultVals) \(i, result) -> do
            iv <- Std.constant i32 $ AST.IntegerAttr i32 i
            rawResultPtr <- LLVM.getelementptr (LLVM.Ptr i64) rawResultsPtr [iv]
            resultPtr    <- LLVM.bitcast (LLVM.Ptr (AST.typeOf result)) rawResultPtr
            LLVM.store result resultPtr
          Std.return []


lowerDecls :: MonadLower m => Nest Decl -> m (Env MLIRAtom)
lowerDecls decls = case decls of
    Empty    -> ask
    Nest d t -> withLoweredDecl d $ lowerDecls t
  where
    withLoweredDecl :: MonadLower m => Decl -> m a -> m a
    withLoweredDecl (Let _ b bound) m = do
      vals <- lowerExpr bound
      extendR (b @> vals) m


lowerExpr :: MonadLower m => Expr -> m MLIRAtom
lowerExpr expr = case expr of
  App  _ _   -> error "Applications (array indexing) not supported in MLIR backend"
  Case _ _ _ -> error "Case expressions not supported in MLIR backend"
  Atom a     -> lowerAtom a
  Op   op    -> lowerOp op
  Hof  _     -> error "Higher-order-functions not supported in MLIR backend"


lowerOp :: MonadLower m => Op -> m MLIRAtom
lowerOp op = case op of
  TabCon (TabTy _ elTy@(BaseTy _)) els ->
    liftM Value . Tensor.from_elements tensorType =<< traverse lowerValue els
    where tensorType = AST.RankedTensorType [Just $ length els] (toMLIRType elTy) Nothing
  TabCon _ _ -> error "Multi-dimensional array literals not supported in MLIR backend"
  ScalarBinOp bop x y -> liftM Value $ bindM2 (getBinOpLowering bop) (lowerValue x) (lowerValue y)
  ScalarUnOp  uop x   -> liftM Value $ getUnOpLowering uop =<< lowerValue x
  CastOp      ty  x   -> do
    xv <- lowerValue x
    Value <$> case (ty, getType x) of
      (BaseTy (PtrType (Heap CPU, _)), BaseTy (Scalar i)) | Just _ <- intWidth i -> LLVM.inttoptr targetTy xv
      (BaseTy (Scalar st), BaseTy (Scalar ss)) -> case (st, ss) of
        -- Integral <-> Integral casts
        (t, s) | Just (_, tw) <- intWidth t, Just (_, sw) <- intWidth s, tw < sw  -> Std.trunci targetTy xv
        (t, s) | Just (_, tw) <- intWidth t, Just (_, sw) <- intWidth s, tw == sw -> return xv
        (t, s) | Just (True , _) <- intWidth t, Just (True , _) <- intWidth s -> Std.sexti targetTy xv
        (t, s) | Just (False, _) <- intWidth t, Just (False, _) <- intWidth s -> Std.zexti targetTy xv
        (t, s) | Just (False, _) <- intWidth t, Just (True , _) <- intWidth s -> Std.zexti targetTy xv
        -- Integral <-> Floating point casts
        (fp, i) | Just _ <- fpWidth fp, Just (True, _) <- intWidth i -> Std.sitofp targetTy xv
        (i, fp) | Just _ <- fpWidth fp, Just (True, _) <- intWidth i -> Std.fptosi targetTy xv
        -- Floating point <-> Floating point casts
        (fpt, fps) | Just tw <- fpWidth fpt, Just sw <- fpWidth fps -> case compare tw sw of
          GT -> Std.fpext   targetTy xv
          EQ -> return xv
          LT -> Std.fptrunc targetTy xv
        _ -> unsupported
      _ -> unsupported
    where
      targetTy = toMLIRType ty
      unsupported = error $ "Unsupported cast in MLIR lowering: " ++ pprint (getType x) ++ " to " ++ pprint ty
  _ -> error $ "Unsupported op in MLIR lowering: " ++ pprint op
  where
    getBinOpLowering bop = case bop of
      IAdd -> Std.addi
      ISub -> Std.subi
      IMul -> Std.muli
      IDiv -> Std.divi_signed
      FAdd -> Std.addf
      FSub -> Std.subf
      FMul -> Std.mulf
      FDiv -> Std.divf
      _    -> error $ "Unsupported binary operation in MLIR lowering: " ++ show bop

    getUnOpLowering uop = case uop of
      _    -> error $ "Unsupported unary operation in MLIR lowering: " ++ show uop

    fpWidth :: ScalarBaseType -> Maybe Int
    fpWidth ty = case ty of
      Float32Type  -> Just 32
      Float64Type  -> Just 64
      _            -> Nothing

    intWidth :: ScalarBaseType -> Maybe (Bool, Int)
    intWidth ty = case ty of
      Word8Type  -> Just (False, 8 )
      Word32Type -> Just (False, 32)
      Word64Type -> Just (False, 64)
      Int32Type  -> Just (True , 32)
      Int64Type  -> Just (True , 64)
      _          -> Nothing


lowerAtom :: MonadLower m => Atom -> m MLIRAtom
lowerAtom atom = case atom of
  Var n -> asks (!n)
  Con con -> case con of
    Lit (Float32Lit f) -> constant $ AST.FloatAttr   mlirType $ realToFrac f
    Lit (Float64Lit f) -> constant $ AST.FloatAttr   mlirType $ realToFrac f
    Lit (Int64Lit   i) -> constant $ AST.IntegerAttr mlirType $ fromIntegral i
    Lit (Int32Lit   i) -> constant $ AST.IntegerAttr mlirType $ fromIntegral i
    PairCon l r        -> Pair <$> lowerAtom l <*> lowerAtom r
    UnitCon            -> return Unit
    _ -> unsupported
  _ -> unsupported
  where
    constant = liftM Value . Std.constant mlirType
    unsupported = error $ "Unsupported atom in MLIR lowering: " ++ pprint atom
    mlirType = toMLIRType $ getType atom


lowerValue :: (HasCallStack, MonadLower m)=> Atom -> m AST.Value
lowerValue atom = lowerAtom atom <&> \case Value v -> v
                                           _ -> error "Expected a value"


toMLIRType :: HasCallStack => Type -> AST.Type
toMLIRType ty = case ty of
  TabTy  _ _ | Just (ns, elTy) <- rectScalarTable ty -> do
    let shape = reverse ns <&> \case
          FixedIntRange low high -> Just $ max 0 $ (fromIntegral high) - (fromIntegral low)
          _                      -> Nothing
    AST.RankedTensorType shape (toMLIRType elTy) Nothing
  BaseTy (Scalar Word8Type  )       -> AST.IntegerType AST.Signless 8
  BaseTy (Scalar Word32Type )       -> AST.IntegerType AST.Signless 32
  BaseTy (Scalar Word64Type )       -> AST.IntegerType AST.Signless 64
  BaseTy (Scalar Int32Type  )       -> AST.IntegerType AST.Signless 32
  BaseTy (Scalar Int64Type  )       -> AST.IntegerType AST.Signless 64
  BaseTy (Scalar Float32Type)       -> AST.Float32Type
  BaseTy (Scalar Float64Type)       -> AST.Float64Type
  BaseTy (PtrType (Heap CPU, elTy)) -> LLVM.Ptr $ toMLIRType $ BaseTy elTy
  _ -> unsupported
  where
    unsupported = error $ "Unsupported type in MLIR lowering: " ++ pprint ty


rectScalarTable :: Type -> Maybe ([Type], Type)
rectScalarTable ty = go [] ty
  where
    go ns elTy = case elTy of
      TabTy  (Ignore n) a -> go (n : ns) a
      BaseTy (Scalar _)   -> Just (reverse ns, elTy)
      _                   -> Nothing


toCoreAtom :: AST.MonadBlockBuilder m => Type -> MLIRAtom -> m ([AST.Value], Abs (Nest Binder) Atom)
toCoreAtom fullTy matom = do
  (neededVals, atom) <- go fullTy matom
  let valsWithTys = M.toList neededVals <&> \(name, (mty, ty)) -> (name AST.:> mty, ty)
      reconAtom = Abs (toNest [Bind (valueName v :> ty) | (v, ty) <- valsWithTys]) atom
  return (fst <$> valsWithTys, reconAtom)
  where
    --go :: MonadBlockBuilder m => Type -> MLIRAtom -> m
    go ty ma = case (ty, ma) of
      (BaseTy _    , Value v ) -> return (singleton v ty, Var $ valueName v :> ty)
      (TabTy  _ _  , Value v ) | Just (ns, BaseTy elTy) <- rectScalarTable ty -> do
        ~[vMemref] <- AST.emitOp $ AST.Operation
          { AST.opName = "memref.buffer_cast"
          , AST.opLocation = AST.UnknownLocation
          , AST.opResultTypes = AST.Explicit [bufferizeType $ AST.typeOf v]
          , AST.opOperands = [AST.operand v]
          , AST.opRegions = []
          , AST.opSuccessors = []
          , AST.opAttributes = AST.NoAttrs
          }
        vs <- LLVM.mlir_cast (llvmType $ AST.typeOf vMemref) vMemref
        -- TODO: Assert that allocPtr and basePtr are equal, or else we will be leaking data!
        ~[_allocPtr, basePtr, dataOff, _sizeArr, stridesArr] <- unpackStruct vs
        -- TODO: Substitute into ns
        unless (null $ freeVars ns) $ error "Unsupported dependent array result"
        unless (toMLIRType IdxRepTy == i32) $ error "MLIR lowering assumes that indices are i32"
        strides <- traverse (Std.trunci i32) =<< unpackArray stridesArr
        dataOffI32 <- Std.trunci i32 dataOff
        let arrayAtom = fst $ flip runBuilder mempty do
              buildNaryLam TabArrow (toNest $ Ignore <$> ns) \idxs -> do
                let strideAtoms = strides <&> \s -> Var $ valueName s :> IdxRepTy
                let dataOffAtom = Var $ valueName dataOffI32 :> IdxRepTy
                let basePtrAtom = Var $ valueName basePtr :> PtrTy (Heap CPU, elTy)
                ordinals <- traverse indexToIntE idxs
                offset   <- foldM iadd dataOffAtom =<< zipWithM imul ordinals strideAtoms
                unsafePtrLoad =<< ptrOffset basePtrAtom offset
        let mlirResults =
              [ (basePtr   , PtrTy (Heap CPU, elTy))
              , (dataOffI32, IdxRepTy              )
              ] <> (strides <&> (,IdxRepTy))
        return (results mlirResults, arrayAtom)
      (PairTy lt rt, Pair l r) -> do
        (lv, la) <- go lt l
        (rv, ra) <- go rt r
        return (lv <> rv, PairVal la ra)
      (UnitTy, Unit) -> return (mempty, UnitVal)
      _    -> error $ "Unsupported output MLIR atom for type: " ++ pprint fullTy
    singleton v ty = M.singleton (AST.operand v) ((AST.typeOf v), ty)
    results vtys = foldMap (uncurry singleton) vtys
    valueName = (\n -> Name GenName n 0) . T.decodeUtf8 . AST.operand


bufferizeType :: AST.Type -> AST.Type
bufferizeType ty = case ty of
  AST.RankedTensorType shape elTy Nothing ->
    AST.MemRefType shape elTy [] Nothing
  _ -> error "Don't know how to bufferize a type"

llvmType :: AST.Type -> AST.Type
llvmType ty = case ty of
  AST.MemRefType shape elTy [] Nothing ->
    LLVM.LiteralStruct
      [ LLVM.Ptr elTy                  -- allocated pointer
      , LLVM.Ptr elTy                  -- aligned pointer
      , i64                            -- offset between aligned pointer and data
      , LLVM.Array (length shape) i64  -- array of sizes
      , LLVM.Array (length shape) i64  -- array of strides
      ]
  _ -> error "Don't know how to get the llvm representation type"


unpackElements :: AST.MonadBlockBuilder m => AST.Value -> [AST.Type] -> m [AST.Value]
unpackElements val tys =
  forM (zip [0..] tys) \(i, ty) -> LLVM.extractvalue ty val [AST.IntegerAttr i32 i]

unpackStruct :: AST.MonadBlockBuilder m => AST.Value -> m [AST.Value]
unpackStruct val = case AST.typeOf val of
  LLVM.LiteralStruct tys -> unpackElements val tys
  _ -> error "Not a struct"

unpackArray :: AST.MonadBlockBuilder m => AST.Value -> m [AST.Value]
unpackArray val = case AST.typeOf val of
  LLVM.Array size ty -> unpackElements val $ replicate size ty
  _ -> error "Not an array"

i32 :: AST.Type
i32 = AST.IntegerType AST.Signless 32

i64 :: AST.Type
i64 = AST.IntegerType AST.Signless 64
