-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE Rank2Types #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module JIT (impToLLVM, mdImpToMulticore, mdImpToCUDA, impKernelToLLVM,
            LLVMFunction (..), LLVMKernel (..),
            ptxTargetTriple, ptxDataLayout) where

import LLVM.AST (Operand, BasicBlock, Instruction, Named, Parameter)
import LLVM.Prelude (ShortByteString, Word32)
import qualified LLVM.AST as L
import qualified LLVM.AST.AddrSpace as L
import qualified LLVM.AST.DataLayout as L
import qualified LLVM.AST.Global as L
import qualified LLVM.AST.CallingConvention as L
import qualified LLVM.AST.Type as L
import qualified LLVM.AST.Typed as L
import qualified LLVM.AST.Float as L
import qualified LLVM.AST.Constant as C
import qualified LLVM.AST.FloatingPointPredicate as FPP
import qualified LLVM.AST.IntegerPredicate as IP
import qualified LLVM.AST.ParameterAttribute as L
import qualified LLVM.AST.FunctionAttribute as FA
import LLVM.IRBuilder.Instruction       (globalStringPtr)
import LLVM.IRBuilder.Internal.SnocList (SnocList (..))
import LLVM.IRBuilder.Module            (runModuleBuilder, ModuleBuilderState (..))

import Control.Monad
import Control.Monad.State.Strict
import Control.Monad.Reader
import Control.Monad.Identity
import Data.ByteString.Short (toShort)
import Data.ByteString.Char8 (unpack, pack)
import Data.String
import Data.Foldable
import Data.Text.Prettyprint.Doc
import Foreign.Ptr (ptrToWordPtr)
import qualified Data.Set as S
import qualified Data.Map as M

import Syntax
import Env
import PPrint
import Util
import Imp

type OperandEnv = Env Operand
data CompileState = CompileState { curBlocks   :: [BasicBlock]
                                 , curInstrs   :: [Named Instruction]
                                 , scalarDecls :: [Named Instruction]
                                 , blockName   :: L.Name
                                 , usedNames   :: Env ()
                                 , funSpecs    :: S.Set ExternFunSpec
                                 , globalDefs  :: [L.Definition]
                                 }
data CompileEnv m = CompileEnv { operandEnv :: OperandEnv
                               , uiFunc     :: UIFunc m
                               , biFunc     :: BIFunc m
                               }

-- Functions used to compile prim ops that do not have a direct translation
-- in the LLVM IR.
type BIFunc m = Monad m => BinOp -> Operand -> Operand -> CompileT m Operand
type UIFunc m = Monad m => UnOp  -> Operand            -> CompileT m Operand

type CompileT m    = ReaderT (CompileEnv m) (StateT CompileState m)
type Compile       = CompileT Identity
data ExternFunSpec = ExternFunSpec L.Name L.Type [L.ParameterAttribute] [FA.FunctionAttribute] [L.Type]
                     deriving (Ord, Eq)

type Function = L.Global

data LLVMFunction = LLVMFunction [BaseType] [BaseType] L.Module
data LLVMKernel   = LLVMKernel L.Module

-- === Imp to LLVM ===

impToLLVM :: ImpFunction -> LLVMFunction
impToLLVM (ImpFunction bs prog result) =
  runIdentity $ compileFunction paramAttrs compileImpInstr bs (prog, result)
  -- Alignment and dereferenceable attributes are guaranteed by malloc_dex
  where paramAttrs = [L.NoAlias, L.NoCapture, L.NonNull, L.Alignment 64, L.Dereferenceable 64]

compileImpInstr :: ImpInstr -> Compile (Maybe Operand)
compileImpInstr instr = case instr of
  IThrowError   -> Nothing <$  throwRuntimeError
  Alloc a t numel -> Just <$> case a of
    Stack -> alloca (getIntLit l) elemTy  where ILit l = numel
    HostHeap ->
      malloc elemTy =<< mul (sizeof elemTy) =<< (`asIntWidth` i64) =<< compileExpr numel
    DeviceHeap -> error "not implemented"
    where elemTy = scalarTy t
  Free v' -> do
    lookupImpVar v' >>= free
    return Nothing
  _ -> compileGenericInstr instr

compileLoop :: Monad m => Direction -> IBinder -> Operand -> CompileT m () -> CompileT m ()
compileLoop d iBinder n compileBody = do
  let loopName = "loop_" ++ (showName $ binderNameHint iBinder)
  loopBlock <- freshName $ fromString $ loopName
  nextBlock <- freshName $ fromString $ "cont_" ++ loopName
  i <- alloca 1 $ scalarTy $ binderAnn iBinder
  i0 <- case d of Fwd -> return $ (0 `withWidthOf` n)
                  Rev -> n `sub` (1 `withWidthOf` n)
  store i i0
  entryCond <- (0 `withWidthOf` n) `ilt` n
  finishBlock (L.CondBr entryCond loopBlock nextBlock []) loopBlock
  iVal <- load i
  extendOperands (iBinder @> iVal) $ compileBody
  iValNew <- case d of Fwd -> add iVal (1 `withWidthOf` iVal)
                       Rev -> sub iVal (1 `withWidthOf` iVal)
  store i iValNew
  loopCond <- case d of Fwd -> iValNew `ilt` n
                        Rev -> iValNew `ige` (0 `withWidthOf` iValNew)
  finishBlock (L.CondBr loopCond loopBlock nextBlock []) nextBlock

compileIf :: Monad m => Operand -> CompileT m () -> CompileT m () -> CompileT m ()
compileIf cond tb fb = do
  tbName   <- freshName "if_true"
  fbName   <- freshName "if_false"
  contName <- freshName "if_cont"
  finishBlock (L.CondBr cond tbName fbName []) tbName
  tb
  finishBlock (L.Br contName []) fbName
  fb
  finishBlock (L.Br contName []) contName

compileWhile :: Monad m => CompileT m Operand -> CompileT m () -> CompileT m ()
compileWhile compileCond compileBody = do
  loopBlock <- freshName "whileLoop"
  nextBlock <- freshName "whileCont"
  entryCond <- compileCond >>= (`asIntWidth` i1)
  finishBlock (L.CondBr entryCond loopBlock nextBlock []) loopBlock
  compileBody
  loopCond <- compileCond >>= (`asIntWidth` i1)
  finishBlock (L.CondBr loopCond loopBlock nextBlock []) nextBlock

throwRuntimeError :: Compile ()
throwRuntimeError = do
  deadBlock <- freshName "deadBlock"
  finishBlock (L.Ret (Just $ 1 `withWidth` 64) []) deadBlock

compilePrimOp :: Monad m => PrimOp Operand -> CompileT m Operand
compilePrimOp pop = case pop of
  ScalarBinOp op x y -> compileBinOp op x y
  VectorBinOp op x y -> compileBinOp op x y
  ScalarUnOp  op x   -> compileUnOp  op x
  Select      p  x y -> do
    pb <- p `asIntWidth` i1
    emitInstr (L.typeOf x) $ L.Select pb x y []
  FFICall name rt xs -> do
    emitExternCall f xs
    where f = ExternFunSpec (L.Name (fromString name)) (scalarTy rt) [] [] (map L.typeOf xs)
  VectorPack elems   -> foldM fillElem undef $ zip elems [0..]
    where
      resTy = L.VectorType (fromIntegral vectorWidth) $ L.typeOf $ head elems
      fillElem v (e, i) = emitInstr resTy $ L.InsertElement v e (i `withWidth` 32) []
      undef = L.ConstantOperand $ C.Undef resTy
  VectorIndex v i    -> emitInstr resTy $ L.ExtractElement v i []
    where (L.VectorType _ resTy) = L.typeOf v
  _ -> error $ "Can't JIT primop: " ++ pprint pop

compileUnOp :: Monad m => UnOp -> Operand -> CompileT m Operand
compileUnOp op x = case op of
  -- LLVM has "fneg" but it doesn't seem to be exposed by llvm-hs-pure
  FNeg            -> emitInstr (L.typeOf x) $ L.FSub mathFlags (0.0 `withWidthOfFP` x) x []
  BNot            -> emitInstr boolTy $ L.Xor x (1 `withWidth` 8) []
  _               -> unaryIntrinsic op x

compileBinOp :: Monad m => BinOp -> Operand -> Operand -> CompileT m Operand
compileBinOp op x y = case op of
  IAdd   -> emitInstr (L.typeOf x) $ L.Add False False x y []
  ISub   -> emitInstr (L.typeOf x) $ L.Sub False False x y []
  IMul   -> emitInstr (L.typeOf x) $ L.Mul False False x y []
  IDiv   -> emitInstr (L.typeOf x) $ L.SDiv False x y []
  IRem   -> emitInstr (L.typeOf x) $ L.SRem x y []
  FPow   -> binaryIntrinsic FPow x y
  FAdd   -> emitInstr (L.typeOf x) $ L.FAdd mathFlags x y []
  FSub   -> emitInstr (L.typeOf x) $ L.FSub mathFlags x y []
  FMul   -> emitInstr (L.typeOf x) $ L.FMul mathFlags x y []
  FDiv   -> emitInstr (L.typeOf x) $ L.FDiv mathFlags x y []
  BAnd   -> emitInstr (L.typeOf x) $ L.And x y []
  BOr    -> emitInstr (L.typeOf x) $ L.Or  x y []
  ICmp c -> emitInstr i1 (L.ICmp (intCmpOp   c) x y []) >>= (`zeroExtendTo` boolTy)
  FCmp c -> emitInstr i1 (L.FCmp (floatCmpOp c) x y []) >>= (`zeroExtendTo` boolTy)
  where
    floatCmpOp :: CmpOp -> FPP.FloatingPointPredicate
    floatCmpOp cmpOp = case cmpOp of
      Less         -> FPP.OLT
      LessEqual    -> FPP.OLE
      Greater      -> FPP.OGT
      GreaterEqual -> FPP.OGE
      Equal        -> FPP.OEQ

    intCmpOp :: CmpOp -> IP.IntegerPredicate
    intCmpOp cmpOp = case cmpOp of
      Less         -> IP.SLT
      LessEqual    -> IP.SLE
      Greater      -> IP.SGT
      GreaterEqual -> IP.SGE
      Equal        -> IP.EQ

-- === MDImp to multicore LLVM ===

mdImpToMulticore :: MDImpFunction ImpKernel -> LLVMFunction
mdImpToMulticore (MDImpFunction bs prog result) =
 runIdentity $ compileFunction [] compileMDImpInstrMC bs (prog, result)

compileMDImpInstrMC :: MDImpInstr ImpKernel -> Compile (Maybe Operand)
compileMDImpInstrMC instr =
  case instr of
    MDLaunch size args kernel -> do
      -- Generate the kernel
      kernelFuncName <- freshName "kernel"
      let (kernelFunSpecs, kernelDefs) = impKernelToMC kernelFuncName kernel
      modify $ (\s -> s { globalDefs = kernelDefs ++ (globalDefs s) })
      modify $ (\s -> s { funSpecs = kernelFunSpecs <> (funSpecs s) })
      -- Run the kernel using the dex_parallel_for runtime function
      kernelParams <- packArgs =<< traverse lookupImpVar args
      s <- (`asIntWidth` i64) =<< compileExpr size
      emitVoidExternCall runKernelSpec [
          L.ConstantOperand $ C.BitCast (C.GlobalReference kernelPtrType kernelFuncName) voidp,
          s,
          kernelParams
        ]
      return Nothing
      where
        runKernelSpec = ExternFunSpec "dex_parallel_for" L.VoidType [] [] [voidp, i64, L.ptr voidp]
        kernelPtrType = L.ptr $ L.FunctionType L.VoidType [i64, i64, L.ptr $ voidp] False
    MDLoadScalar v         -> Just    <$> (load =<< lookupImpVar v)
    MDStoreScalar v val    -> Nothing <$  bindM2 store (lookupImpVar v) (compileExpr val)
    MDAlloc t s            -> compileImpInstr (Alloc DeviceHeap t s)
    MDFree   v             -> compileImpInstr (Free v)
    MDHostInstr impInstr   -> compileImpInstr impInstr

impKernelToMC :: L.Name -> ImpKernel -> (S.Set ExternFunSpec, [L.Definition])
impKernelToMC funcName (ImpKernel argBinders idxBinder prog) = runCompile cpuInitCompileEnv $ do
  (startIdxParam, startIdx) <- freshParamOpPair [] i64
  (endIdxParam, endIdx) <- freshParamOpPair [] i64
  -- TODO: Preserve pointer attributes??
  (argArrayParam, argArray) <- freshParamOpPair [] $ L.ptr voidp
  args <- unpackArgs argArray argTypes
  let argEnv = foldMap (uncurry (@>)) $ zip argBinders args

  niter <- (`asIntWidth` idxType) =<< endIdx `sub` startIdx
  compileLoop Fwd idxBinder niter $ do
    idxEnv <- case idxBinder of
      Ignore _ -> return mempty
      Bind v -> do
        innerIdx <- lookupImpVar v
        idx64 <- add startIdx =<< (innerIdx `asIntWidth` i64)
        idx <- idx64 `asIntWidth` idxType
        return $ idxBinder @> idx
    extendOperands (argEnv <> idxEnv) $ compileProg compileImpInstr prog
  kernel <- makeFunction funcName [startIdxParam, endIdxParam, argArrayParam] Nothing
  extraSpecs <- gets funSpecs
  extraDefs <- gets globalDefs
  return $ (extraSpecs, L.GlobalDefinition kernel : extraDefs)
  where
    idxType = scalarTy $ binderAnn idxBinder
    argTypes = fmap (scalarTy . binderAnn) argBinders

-- === MDImp to LLVM CUDA ===

type MDHostCompile   = Compile
data MDImpInstrCG    = EnsureHasContext -- code generation specific instructions
type MDImpInstrExt k = Either MDImpInstrCG (MDImpInstr k)

mdImpToCUDA :: MDImpFunction CUDAKernel -> LLVMFunction
mdImpToCUDA = undefined
-- mdImpToCUDA (MDImpFunction outVars inVars prog) =
--   runIdentity $ compileFunction [] compileMDImpInstrCUDA outVars inVars prog'
--   where prog' = IInstr (Nothing, Left EnsureHasContext) `Nest` fmap (fmap Right) prog

compileMDImpInstrCUDA :: MDImpInstrExt CUDAKernel -> MDHostCompile (Maybe Operand)
compileMDImpInstrCUDA instrExt = do
  case instrExt of
    Left ext -> case ext of
      EnsureHasContext -> ensureHasCUDAContext >> return Nothing
    Right instr -> case instr of
      MDLaunch size args (CUDAKernel kernel) -> do
        argOps <- traverse lookupImpVar args
        sizeOp <- (`asIntWidth` i64) =<< compileExpr size
        kernelParams <- packArgs $ sizeOp : argOps
        ptxConst <- castVoidPtr =<< declareStringConst "ptxKernel" (unpack kernel)
        launchCUDAKernel ptxConst sizeOp kernelParams
        return Nothing
      MDAlloc t s -> Just <$>
        (cuMemAlloc elemTy =<< mul (sizeof elemTy) =<< (`asIntWidth` i64) =<< compileExpr s)
        where elemTy = scalarTy t
      MDFree   v             -> lookupImpVar v >>= cuMemFree >> return Nothing
      MDLoadScalar  v        -> do
        refPtr <- castVoidPtr =<< lookupImpVar v
        ~(L.PointerType refValType _) <- L.typeOf <$> lookupImpVar v
        valPtr <- alloca 1 refValType
        cuMemcpyDToH (sizeof refValType) refPtr =<< castVoidPtr valPtr
        Just <$> load valPtr
      MDStoreScalar v val    -> do
        refPtr <- castVoidPtr =<< lookupImpVar v
        ~(L.PointerType refValType _) <- L.typeOf <$> lookupImpVar v
        valPtr <- alloca 1 refValType
        store valPtr =<< compileExpr val
        cuMemcpyHToD (sizeof refValType) refPtr =<< castVoidPtr valPtr
        return Nothing
      MDHostInstr impInstr   -> compileImpInstr impInstr

ensureHasCUDAContext :: MDHostCompile ()
ensureHasCUDAContext = emitVoidExternCall spec []
  where spec = ExternFunSpec "dex_ensure_has_cuda_context" L.VoidType [] [] []

launchCUDAKernel :: Operand -> Operand -> Operand -> MDHostCompile()
launchCUDAKernel ptx size args = emitVoidExternCall spec [ptx, size, args]
  where spec = ExternFunSpec "dex_cuLaunchKernel" L.VoidType [] [] [voidp, i64, L.ptr $ voidp]

cuMemcpyDToH :: Operand -> Operand -> Operand -> MDHostCompile ()
cuMemcpyDToH bytes refPtr valPtr = emitVoidExternCall spec [bytes, refPtr, valPtr]
  where spec = ExternFunSpec "dex_cuMemcpyDtoH" L.VoidType [] [] [i64, voidp, voidp]

cuMemcpyHToD :: Operand -> Operand -> Operand -> MDHostCompile ()
cuMemcpyHToD bytes refPtr valPtr = emitVoidExternCall spec [bytes, refPtr, valPtr]
  where spec = ExternFunSpec "dex_cuMemcpyHtoD" L.VoidType [] [] [i64, voidp, voidp]

cuMemAlloc :: L.Type -> Operand -> MDHostCompile Operand
cuMemAlloc ty bytes = castLPtr ty =<< emitExternCall spec [bytes]
  where spec = ExternFunSpec "dex_cuMemAlloc" voidp [] [] [i64]

cuMemFree :: Operand -> MDHostCompile ()
cuMemFree ptr = do
  voidPtr <- castVoidPtr ptr
  emitVoidExternCall spec [voidPtr]
  where spec = ExternFunSpec "dex_cuMemFree" L.VoidType [] [] [voidp]

declareStringConst :: Monad m => Name -> String -> CompileT m Operand
declareStringConst nameHint str = do
  name <- freshName nameHint
  let (ptr, [def]) = runModuleBuilder (ModuleBuilderState (SnocList []) mempty) $ globalStringPtr str name
  modify $ (\s -> s { globalDefs = def : (globalDefs s) })
  return $ L.ConstantOperand ptr

-- === GPU Kernel compilation ===

impKernelToLLVM :: ImpKernel -> LLVMKernel
impKernelToLLVM (ImpKernel args lvar prog) = runCompile gpuInitCompileEnv $ do
  (argParams, argOperands) <- unzip <$> mapM (freshParamOpPair ptrParamAttrs) argTypes
  (sizeParam, sizeOperand) <- freshParamOpPair [] lidxType
  tidx <- threadIdxX
  bidx <- blockIdxX
  bsz  <- blockDimX
  lidx <- mul bidx bsz >>= (add tidx) >>= (`asIntWidth` lidxType)
  outOfBounds <- emitInstr i1 $ L.ICmp IP.UGE lidx sizeOperand []
  compileIf outOfBounds (return ()) $ do
    let paramEnv = foldMap (uncurry (@>)) $ zip args argOperands
    -- TODO: Use a restricted form of compileProg that e.g. never emits FFI calls!
    extendOperands (paramEnv <> lvar @> lidx) $ compileProg compileImpKernelInstr prog
  kernel <- makeFunction "kernel" (sizeParam : argParams) Nothing
  LLVMKernel <$> makeModuleEx ptxDataLayout ptxTargetTriple [L.GlobalDefinition kernel, kernelMeta, nvvmAnnotations]
  where
    lidxType = scalarTy $ binderAnn lvar
    ptrParamAttrs = [L.NoAlias, L.NoCapture, L.NonNull, L.Alignment 256]
    argTypes = fmap (scalarTy . binderAnn) args
    kernelMetaId = L.MetadataNodeID 0
    kernelMeta = L.MetadataNodeDefinition kernelMetaId $ L.MDTuple
      [ Just $ L.MDValue $ L.ConstantOperand $ C.GlobalReference (funTy L.VoidType (lidxType : argTypes)) "kernel"
      , Just $ L.MDString "kernel"
      , Just $ L.MDValue $ L.ConstantOperand $ C.Int 32 1
      ]
    nvvmAnnotations = L.NamedMetadataDefinition "nvvm.annotations" [kernelMetaId]

ptxTargetTriple :: ShortByteString
ptxTargetTriple = "nvptx64-nvidia-cuda"

ptxDataLayout :: L.DataLayout
ptxDataLayout = (L.defaultDataLayout L.LittleEndian)
    { L.endianness     = L.LittleEndian
    , L.pointerLayouts = M.fromList [(L.AddrSpace 0, (64, L.AlignmentInfo 64 64))]
    , L.typeLayouts    = M.fromList $
        [ ((L.IntegerAlign, 1), L.AlignmentInfo 8 8) ] ++
        [ ((L.IntegerAlign, w), L.AlignmentInfo w w) | w <- [8, 16, 32, 64] ] ++
        [ ((L.FloatAlign,   w), L.AlignmentInfo w w) | w <- [32, 64] ] ++
        [ ((L.VectorAlign,  w), L.AlignmentInfo w w) | w <- [16, 32, 64, 128] ]
    , L.nativeSizes    = Just $ S.fromList [16, 32, 64]
    }

threadIdxX :: Compile Operand
threadIdxX = emitExternCall spec []
  where spec = ptxSpecialReg "llvm.nvvm.read.ptx.sreg.tid.x"

blockIdxX :: Compile Operand
blockIdxX = emitExternCall spec []
  where spec = ptxSpecialReg "llvm.nvvm.read.ptx.sreg.ctaid.x"

blockDimX :: Compile Operand
blockDimX = emitExternCall spec []
  where spec = ptxSpecialReg "llvm.nvvm.read.ptx.sreg.ntid.x"

ptxSpecialReg :: L.Name -> ExternFunSpec
ptxSpecialReg name = ExternFunSpec name i32 [] [FA.ReadNone, FA.NoUnwind] []

gpuInitCompileEnv :: Monad m => CompileEnv m
gpuInitCompileEnv = CompileEnv mempty gpuUnaryIntrinsics gpuBinaryIntrinsics
  where
    gpuUnaryIntrinsics op x = case L.typeOf x of
      L.FloatingPointType L.DoubleFP -> dispatchOp fp64 ""
      L.FloatingPointType L.FloatFP  -> dispatchOp fp32 "f"
      _ -> error $ "Unsupported GPU floating point type: " ++ show (L.typeOf x)
      where
        dispatchOp ty suffix = case op of
          Exp    -> callFloatIntrinsic ty $ "__nv_exp"    ++ suffix
          Exp2   -> callFloatIntrinsic ty $ "__nv_exp2"   ++ suffix
          Log    -> callFloatIntrinsic ty $ "__nv_log"    ++ suffix
          Log2   -> callFloatIntrinsic ty $ "__nv_log2"   ++ suffix
          Log10  -> callFloatIntrinsic ty $ "__nv_log10"  ++ suffix
          Log1p  -> callFloatIntrinsic ty $ "__nv_log1p"  ++ suffix
          Sin    -> callFloatIntrinsic ty $ "__nv_sin"    ++ suffix
          Cos    -> callFloatIntrinsic ty $ "__nv_cos"    ++ suffix
          Tan    -> callFloatIntrinsic ty $ "__nv_tan"    ++ suffix
          Sqrt   -> callFloatIntrinsic ty $ "__nv_sqrt"   ++ suffix
          Floor  -> callFloatIntrinsic ty $ "__nv_floor"  ++ suffix
          Ceil   -> callFloatIntrinsic ty $ "__nv_ceil"   ++ suffix
          Round  -> callFloatIntrinsic ty $ "__nv_round"  ++ suffix
          LGamma -> callFloatIntrinsic ty $ "__nv_lgamma" ++ suffix
          _   -> error $ "Unsupported GPU operation: " ++ show op
        floatIntrinsic ty name = ExternFunSpec (L.mkName name) ty [] [] [ty]
        callFloatIntrinsic ty name = emitExternCall (floatIntrinsic ty name) [x]

    gpuBinaryIntrinsics op x y = case L.typeOf x of
      L.FloatingPointType L.DoubleFP -> dispatchOp fp64 ""
      L.FloatingPointType L.FloatFP  -> dispatchOp fp32 "f"
      _ -> error $ "Unsupported GPU floating point type: " ++ show (L.typeOf x)
      where
        dispatchOp ty suffix = case op of
          FPow -> callFloatIntrinsic ty $ "__nv_pow" ++ suffix
          _    -> error $ "Unsupported GPU operation: " ++ show op
        floatIntrinsic ty name = ExternFunSpec (L.mkName name) ty [] [] [ty, ty]
        callFloatIntrinsic ty name = emitExternCall (floatIntrinsic ty name) [x, y]

compileImpKernelInstr :: ImpInstr -> Compile (Maybe Operand)
compileImpKernelInstr instr = case instr of
  IThrowError      -> return Nothing
  Free  _          -> return Nothing  -- Can only alloca inside a kernel
  Alloc _ t numel  -> Just <$> case numel of
    ILit l | n <- getIntLit l, n <= 256 -> alloca n (scalarTy t)
    _ -> error $ "GPU kernels can only allocate statically known amounts of memory"
  _ -> compileGenericInstr instr

-- === Helpers for Imp and MDImp programs ===

compileFunction :: Monad m
                => [L.ParameterAttribute]
                -> (instr -> CompileT m (Maybe Operand))
                -> [IBinder] -> IProgVal instr -> m LLVMFunction
compileFunction attrs compileInstr inBinders prog = runCompileT cpuInitCompileEnv $ do
  (argPtrParam   , argPtrOperand   ) <- freshParamOpPair attrs $ L.ptr i64
  (resultPtrParam, resultPtrOperand) <- freshParamOpPair attrs $ L.ptr i64
  argOperands <- forM (zip [0..] argTypes) $ \(i, ty) ->
    gep argPtrOperand (i `withWidth` 64) >>= castLPtr (scalarTy ty) >>= load
  results <- extendOperands (newEnv inBinders argOperands) $
               compileProgVal compileInstr prog
  forM_ (zip [0..] results) $ \(i, x) ->
    gep resultPtrOperand (i `withWidth` 64) >>= castLPtr (L.typeOf x) >>= flip store x
  mainFun <- makeFunction "entryFun" [argPtrParam, resultPtrParam] (Just $ 0 `withWidth` 64)
  LLVMFunction argTypes resultTypes <$> makeModule [L.GlobalDefinition mainFun]
  where
    argTypes    = map binderAnn inBinders
    resultTypes = map getIType  (snd prog)

compileProg :: Monad m => (instr -> CompileT m (Maybe Operand))
            -> IProg instr -> CompileT m ()
compileProg compileInstr prog = () <$ compileProgVal compileInstr (prog, [])

compileProgVal :: Monad m => (instr -> CompileT m (Maybe Operand))
               -> IProgVal instr -> CompileT m [Operand]
compileProgVal _ (Empty, val) = traverse compileExpr val
compileProgVal compileInstr ((Nest stmt prog), val) = do
  env <- case stmt of
    IInstr (Just b, instr) -> do
      ans <- compileInstr instr
      return $ foldMap (b@>) ans
    IInstr (Nothing, instr) -> do
      void $ compileInstr instr
      return mempty
    IFor d i n body  -> mempty <$ do
      n' <- compileExpr n
      compileLoop d i n' (rec body)
    IWhile cond body -> mempty <$ compileWhile (head <$> recVal cond) (rec body)
    ICond p cons alt -> do
      p' <- compileExpr p >>= (`asIntWidth` i1)
      compileIf p' (rec cons)
                   (rec alt)
      return mempty
  extendOperands env $ recVal (prog, val)
  where rec = compileProg compileInstr; recVal = compileProgVal compileInstr

compileExpr :: Monad m => IExpr -> CompileT m Operand
compileExpr expr = case expr of
  ILit v   -> return (litVal v)
  IVar v   -> lookupImpVar v

compileGenericInstr :: ImpInstr -> Compile (Maybe Operand)
compileGenericInstr instr = case instr of
  IPrimOp op       -> Just    <$> (traverse compileExpr op >>= compilePrimOp)
  Load ref         -> Just    <$> (load =<< compileExpr ref)
  Store dest val   -> Nothing <$  bindM2 store (compileExpr dest) (compileExpr val)
  IOffset x off    -> Just    <$> bindM2 gep   (compileExpr x)    (compileExpr off)
  ICastOp idt ix   -> Just    <$> do
    x <- compileExpr ix
    let (xt, dt) = (L.typeOf x, scalarTy idt)
    case (xt, dt) of
      (L.IntegerType _, L.IntegerType _) -> x `asIntWidth` dt
      (L.FloatingPointType fpt, L.FloatingPointType fpt') -> case compare fpt fpt' of
        LT -> emitInstr dt $ L.FPExt x dt []
        EQ -> return x
        GT -> emitInstr dt $ L.FPTrunc x dt []
      (L.FloatingPointType _, L.IntegerType _) -> emitInstr dt $ L.FPToSI x dt []
      (L.IntegerType _, L.FloatingPointType _) -> emitInstr dt $ L.SIToFP x dt []
      _ -> error $ "Unsupported cast"
  _ -> error $ "Not a generic instruction: " ++ pprint instr

packArgs :: Monad m => [Operand] -> CompileT m Operand
packArgs elems = do
  arr <- alloca (length elems) voidp
  forM_ (zip [0..] elems) $ \(i, e) -> do
    eptr <- alloca 1 $ L.typeOf e
    store eptr e
    earr <- gep arr $ i `withWidth` 32
    store earr =<< castVoidPtr eptr
  return arr

unpackArgs :: Monad m => Operand -> [L.Type] -> CompileT m [Operand]
unpackArgs argArrayPtr types =
  forM (zip [0..] types) $ \(i, ty) -> do
    argVoidPtr <- gep argArrayPtr $ i `withWidth` 64
    argPtr <- castLPtr (L.ptr ty) argVoidPtr
    load =<< load argPtr

-- === LLVM embedding ===

litVal :: LitVal -> Operand
litVal lit = case lit of
  Int64Lit x   -> (fromIntegral x) `withWidth` 64
  Int32Lit x   -> (fromIntegral x) `withWidth` 32
  Int8Lit  x   -> (fromIntegral x) `withWidth` 8
  Float64Lit x -> L.ConstantOperand $ C.Float $ L.Double x
  Float32Lit x -> L.ConstantOperand $ C.Float $ L.Single x
  VecLit l     -> L.ConstantOperand $ foldl fillElem undef $ zip consts [0..length l - 1]
    where
      consts = fmap (operandToConst . litVal) l
      undef = C.Undef $ L.VectorType (fromIntegral $ length l) $ L.typeOf $ head consts
      fillElem v (c, i) = C.InsertElement v c (C.Int 32 (fromIntegral i))
      operandToConst ~(L.ConstantOperand c) = c
  PtrLit (_, _, ty) ptr ->
    L.ConstantOperand $ C.IntToPtr (C.Int 64 ptrAsInt) (L.ptr (scalarTy ty))
    where ptrAsInt = fromIntegral $ ptrToWordPtr ptr

-- TODO: Assert that the integer can be represented in that number of bits!
withWidth :: Integer -> Word32 -> Operand
withWidth x bits = L.ConstantOperand $ C.Int bits x

withWidthOf :: Integer -> Operand -> Operand
withWidthOf x template = case L.typeOf template of
  L.IntegerType bits -> x `withWidth` (fromIntegral bits)
  _ -> error $ "Expected an integer: " ++ show template

withWidthOfFP :: Double -> Operand -> Operand
withWidthOfFP x template = case L.typeOf template of
  L.FloatingPointType L.DoubleFP -> litVal $ Float64Lit x
  L.FloatingPointType L.FloatFP  -> litVal $ Float32Lit $ realToFrac x
  _ -> error $ "Unsupported floating point type: " ++ show (L.typeOf template)

store :: Monad m => Operand -> Operand -> CompileT m ()
store ptr x =  addInstr $ L.Do $ L.Store False ptr x Nothing 0 []

load :: Monad m => Operand -> CompileT m Operand
load ptr = emitInstr ty $ L.Load False ptr Nothing 0 []
  where (L.PointerType ty _) = L.typeOf ptr

ilt :: Monad m => Operand -> Operand -> CompileT m Operand
ilt x y = emitInstr i1 $ L.ICmp IP.SLT x y []

ige :: Monad m => Operand -> Operand -> CompileT m Operand
ige x y = emitInstr i1 $ L.ICmp IP.SGE x y []

add :: Monad m => Operand -> Operand -> CompileT m Operand
add x y = emitInstr (L.typeOf x) $ L.Add False False x y []

sub :: Monad m => Operand -> Operand -> CompileT m Operand
sub x y = emitInstr (L.typeOf x) $ L.Sub False False x y []

mul :: Monad m => Operand -> Operand -> CompileT m Operand
mul x y = emitInstr (L.typeOf x) $ L.Mul False False x y []

gep :: Monad m => Operand -> Operand -> CompileT m Operand
gep ptr i = emitInstr (L.typeOf ptr) $ L.GetElementPtr False ptr [i] []

sizeof :: L.Type -> Operand
sizeof t = (L.ConstantOperand $ C.ZExt (C.sizeof t) i64)

alloca :: Monad m => Int -> L.Type -> CompileT m Operand
alloca elems ty = do
  v <- freshName "v"
  modify $ setScalarDecls ((v L.:= instr):)
  return $ L.LocalReference (L.ptr ty) v
  where instr = L.Alloca ty (Just $ (fromIntegral elems) `withWidth` 32) 0 []

malloc :: Monad m => L.Type -> Operand -> CompileT m Operand
malloc ty bytes = do
  bytes64 <- asIntWidth bytes i64
  castLPtr ty =<< emitExternCall mallocFun [bytes64]

free :: Monad m => Operand -> CompileT m ()
free ptr = do
  ptr' <- castLPtr i8 ptr
  emitVoidExternCall freeFun [ptr']

castLPtr :: Monad m => L.Type -> Operand -> CompileT m Operand
castLPtr ty ptr = emitInstr (L.ptr ty) $ L.BitCast ptr (L.ptr ty) []

castVoidPtr :: Monad m => Operand -> CompileT m Operand
castVoidPtr = castLPtr i8

zeroExtendTo :: Monad m => Operand -> L.Type -> CompileT m Operand
zeroExtendTo x t = emitInstr t $ L.ZExt x t []

callInstr :: L.CallableOperand -> [L.Operand] -> L.Instruction
callInstr fun xs = L.Call Nothing L.C [] fun xs' [] []
 where xs' = [(x ,[]) | x <- xs]

externCall :: ExternFunSpec -> [L.Operand] -> L.Instruction
externCall (ExternFunSpec fname retTy _ _ argTys) xs = callInstr fun xs
  where fun = callableOperand (funTy retTy argTys) fname

emitExternCall :: Monad m => ExternFunSpec -> [L.Operand] -> CompileT m Operand
emitExternCall f@(ExternFunSpec _ retTy _ _ _) xs = do
  modify $ setFunSpecs (S.insert f)
  emitInstr retTy $ externCall f xs

emitVoidExternCall :: Monad m => ExternFunSpec -> [L.Operand] -> CompileT m ()
emitVoidExternCall f xs = do
  modify $ setFunSpecs (S.insert f)
  addInstr $ L.Do $ externCall f xs

scalarTy :: BaseType -> L.Type
scalarTy b = case b of
  Scalar sb -> case sb of
    Int64Type   -> i64
    Int32Type   -> i32
    Int8Type    -> i8
    Float64Type -> fp64
    Float32Type -> fp32
  Vector sb -> L.VectorType (fromIntegral vectorWidth) $ scalarTy $ Scalar sb
  PtrType (_, s, t) -> L.PointerType (scalarTy t) (lAddress s)

lAddress :: AddressSpace -> L.AddrSpace
lAddress s = case s of
  Stack -> error "Stack memory should be allocated with alloca"
  HostHeap   -> L.AddrSpace 0
  DeviceHeap -> L.AddrSpace 1

callableOperand :: L.Type -> L.Name -> L.CallableOperand
callableOperand ty name = Right $ L.ConstantOperand $ C.GlobalReference ty name

showName :: Name -> String
showName (Name GenName tag counter) = asStr $ pretty tag <> "." <> pretty counter
showName _ = error $ "All names in JIT should be from the GenName namespace"

asIntWidth :: Monad m => Operand -> L.Type -> CompileT m Operand
asIntWidth op ~expTy@(L.IntegerType expWidth) = case compare expWidth opWidth of
  LT -> emitInstr expTy $ L.Trunc op expTy []
  EQ -> return op
  GT -> emitInstr expTy $ L.ZExt  op expTy []
  where ~(L.IntegerType opWidth) = L.typeOf op

freshParamOpPair :: Monad m => [L.ParameterAttribute] -> L.Type -> CompileT m (Parameter, Operand)
freshParamOpPair ptrAttrs ty = do
  v <- freshName "arg"
  let attrs = case ty of
                L.PointerType _ _ -> ptrAttrs
                _ -> []
  return (L.Parameter ty v attrs, L.LocalReference ty v)

externDecl :: ExternFunSpec -> L.Definition
externDecl (ExternFunSpec fname retTy retAttrs funAttrs argTys) =
  L.GlobalDefinition $ L.functionDefaults {
    L.name               = fname
  , L.parameters         = ([L.Parameter t (argName i) []
                            | (i, t) <- zip [0::Int ..] argTys], False)
  , L.returnType         = retTy
  , L.returnAttributes   = retAttrs
  , L.functionAttributes = fmap Right funAttrs
  }
  where argName i = L.Name $ "arg" <> fromString (show i)

cpuInitCompileEnv :: Monad m => CompileEnv m
cpuInitCompileEnv = CompileEnv mempty cpuUnaryIntrinsics cpuBinaryIntrinsics
  where
    cpuUnaryIntrinsics op x = case L.typeOf x of
      L.FloatingPointType L.DoubleFP -> dispatchOp fp64 ".f64" ""
      L.FloatingPointType L.FloatFP  -> dispatchOp fp32 ".f32" "f"
      _ -> error $ "Unsupported CPU floating point type: " ++ show (L.typeOf x)
      where
        dispatchOp ty llvmSuffix libmSuffix = case op of
          Exp             -> callFloatIntrinsic ty $ "llvm.exp"   ++ llvmSuffix
          Exp2            -> callFloatIntrinsic ty $ "llvm.exp2"  ++ llvmSuffix
          Log             -> callFloatIntrinsic ty $ "llvm.log"   ++ llvmSuffix
          Log2            -> callFloatIntrinsic ty $ "llvm.log2"  ++ llvmSuffix
          Log10           -> callFloatIntrinsic ty $ "llvm.log10" ++ llvmSuffix
          Log1p           -> callFloatIntrinsic ty $ "log1p"      ++ libmSuffix
          Sin             -> callFloatIntrinsic ty $ "llvm.sin"   ++ llvmSuffix
          Cos             -> callFloatIntrinsic ty $ "llvm.cos"   ++ llvmSuffix
          Tan             -> callFloatIntrinsic ty $ "tan"        ++ libmSuffix
          Sqrt            -> callFloatIntrinsic ty $ "llvm.sqrt"  ++ llvmSuffix
          Floor           -> callFloatIntrinsic ty $ "llvm.floor" ++ llvmSuffix
          Ceil            -> callFloatIntrinsic ty $ "llvm.ceil"  ++ llvmSuffix
          Round           -> callFloatIntrinsic ty $ "llvm.round" ++ llvmSuffix
          LGamma          -> callFloatIntrinsic ty $ "lgamma"     ++ libmSuffix
          _ -> error $ "Unsupported CPU operation: " ++ show op
        floatIntrinsic ty name = ExternFunSpec (L.mkName name) ty [] [] [ty]
        callFloatIntrinsic ty name = emitExternCall (floatIntrinsic ty name) [x]

    cpuBinaryIntrinsics op x y = case L.typeOf x of
      L.FloatingPointType L.DoubleFP -> dispatchOp fp64 ".f64"
      L.FloatingPointType L.FloatFP  -> dispatchOp fp32 ".f32"
      _ -> error $ "Unsupported CPU floating point type: " ++ show (L.typeOf x)
      where
        dispatchOp ty llvmSuffix = case op of
          FPow -> callFloatIntrinsic ty $ "llvm.pow" ++ llvmSuffix
          _ -> error $ "Unsupported CPU operation: " ++ show op
        floatIntrinsic ty name = ExternFunSpec (L.mkName name) ty [] [] [ty, ty]
        callFloatIntrinsic ty name = emitExternCall (floatIntrinsic ty name) [x, y]

-- === Compile monad utilities ===

runCompileT :: Monad m => CompileEnv m -> CompileT m a -> m a
runCompileT env m = evalStateT (runReaderT m env) initState
  where initState = CompileState [] [] [] "start_block" mempty mempty mempty

runCompile :: CompileEnv Identity -> Compile a -> a
runCompile env m = runIdentity $ runCompileT env m

extendOperands :: Monad m => OperandEnv -> CompileT m a -> CompileT m a
extendOperands openv = local $ \env -> env { operandEnv = (operandEnv env) <> openv }

lookupImpVar :: Monad m => IVar -> CompileT m Operand
lookupImpVar v = asks ((! v) . operandEnv)

finishBlock :: Monad m => L.Terminator -> L.Name -> CompileT m ()
finishBlock term newName = do
  oldName <- gets blockName
  instrs  <- gets curInstrs
  let newBlock = L.BasicBlock oldName (reverse instrs) (L.Do term)
  modify $ setCurBlocks (newBlock:)
         . setCurInstrs (const [])
         . setBlockName (const newName)

freshName :: Monad m => Name -> CompileT m L.Name
freshName v = do
  used <- gets usedNames
  let v' = genFresh v used
  modify $ \s -> s { usedNames = used <> v' @> () }
  return $ nameToLName v'
  where
    nameToLName :: Name -> L.Name
    nameToLName name = L.Name $ toShort $ pack $ showName name

-- TODO: consider getting type from instruction rather than passing it explicitly
emitInstr :: Monad m => L.Type -> Instruction -> CompileT m Operand
emitInstr ty instr = do
  v <- freshName "v"
  addInstr $ v L.:= instr
  return $ L.LocalReference ty v

addInstr :: Monad m => Named Instruction -> CompileT m ()
addInstr instr = modify $ setCurInstrs (instr:)

setScalarDecls :: ([Named Instruction] -> [Named Instruction]) -> CompileState -> CompileState
setScalarDecls update s = s { scalarDecls = update (scalarDecls s) }

setCurInstrs :: ([Named Instruction] -> [Named Instruction]) -> CompileState -> CompileState
setCurInstrs update s = s { curInstrs = update (curInstrs s) }

setCurBlocks :: ([BasicBlock] -> [BasicBlock]) -> CompileState -> CompileState
setCurBlocks update s = s { curBlocks   = update (curBlocks s) }

setBlockName :: (L.Name -> L.Name) -> CompileState -> CompileState
setBlockName update s = s { blockName = update (blockName s) }

setFunSpecs :: (S.Set ExternFunSpec -> S.Set ExternFunSpec) -> CompileState -> CompileState
setFunSpecs update s = s { funSpecs = update (funSpecs s) }

unaryIntrinsic :: Monad m => UnOp -> Operand -> CompileT m Operand
unaryIntrinsic op x = do
  uif <- asks uiFunc
  uif op x

binaryIntrinsic :: Monad m => BinOp -> Operand -> Operand -> CompileT m Operand
binaryIntrinsic op x y = do
  bif <- asks biFunc
  bif op x y

-- === Constants ===

-- FP contractions should only lead to fewer rounding points, so we allow those
mathFlags :: L.FastMathFlags
mathFlags = L.noFastMathFlags { L.allowContract = True }

mallocFun :: ExternFunSpec
mallocFun = ExternFunSpec "malloc_dex" (L.ptr i8) [L.NoAlias] [] [i64]

freeFun :: ExternFunSpec
freeFun = ExternFunSpec "free_dex" L.VoidType [] [] [L.ptr i8]

boolTy :: L.Type
boolTy = i8

fp64 :: L.Type
fp64 = L.FloatingPointType L.DoubleFP

fp32 :: L.Type
fp32 = L.FloatingPointType L.FloatFP

i64 :: L.Type
i64 = L.IntegerType 64

i32 :: L.Type
i32 = L.IntegerType 32

i8 :: L.Type
i8 = L.IntegerType 8

i1 :: L.Type
i1 = L.IntegerType 1

voidp :: L.Type
voidp = L.ptr i8

funTy :: L.Type -> [L.Type] -> L.Type
funTy retTy argTys = L.ptr $ L.FunctionType retTy argTys False

-- === Module building ===

makeFunction :: Monad m => L.Name -> [Parameter] -> Maybe L.Operand -> CompileT m Function
makeFunction name params returnVal = do
  finishBlock (L.Ret returnVal []) "<ignored>"
  decls <- gets scalarDecls
  ~((L.BasicBlock bbname instrs term):blocksTail) <- gets (reverse . curBlocks)
  let blocks = (L.BasicBlock bbname (decls ++ instrs) term):blocksTail
  let returnTy = case returnVal of Nothing -> L.VoidType
                                   Just x  -> L.typeOf x
  return $ L.functionDefaults
    { L.name        = name
    , L.parameters  = (params, False)
    , L.returnType  = returnTy
    , L.basicBlocks = blocks }

makeModule :: Monad m => [L.Definition] -> CompileT m L.Module
makeModule defs = do
  specs     <- gets funSpecs
  extraDefs <- gets globalDefs
  return $ L.defaultModule
      { L.moduleName = "dexModule"
      , L.moduleDefinitions = extraDefs ++ defs ++ fmap externDecl (toList specs) }

makeModuleEx :: Monad m => L.DataLayout -> ShortByteString -> [L.Definition] -> CompileT m L.Module
makeModuleEx dataLayout triple defs = do
  specs     <- gets funSpecs
  extraDefs <- gets globalDefs
  return $ L.defaultModule
      { L.moduleName = "dexModule"
      , L.moduleDefinitions = extraDefs ++ defs ++ fmap externDecl (toList specs)
      , L.moduleDataLayout = Just dataLayout
      , L.moduleTargetTriple = Just triple }

instance Pretty L.Operand where
  pretty x = pretty (show x)

instance PrettyPrec L.Operand where
  prettyPrec = atPrec AppPrec . pretty

instance Pretty L.Type where
  pretty x = pretty (show x)
