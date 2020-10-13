-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE Rank2Types #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module JIT (impToLLVM) where

import LLVM.AST (Operand, BasicBlock, Instruction, Named, Parameter)
import LLVM.Prelude (ShortByteString, Word32)
import qualified LLVM.AST as L
import qualified LLVM.AST.AddrSpace as L
import qualified LLVM.AST.DataLayout as L
import qualified LLVM.AST.Global as L
import qualified LLVM.AST.CallingConvention as L
import qualified LLVM.AST.Typed as L
import qualified LLVM.AST.Float as L
import qualified LLVM.AST.Constant as C
import qualified LLVM.AST.FloatingPointPredicate as FPP
import qualified LLVM.AST.IntegerPredicate as IP
import qualified LLVM.AST.ParameterAttribute as L
import qualified LLVM.AST.FunctionAttribute as FA

import System.IO.Unsafe
import System.Environment
import Control.Monad
import Control.Monad.State.Strict
import Control.Monad.Reader
import Data.ByteString.Short (toShort)
import qualified Data.ByteString.Char8 as B
import Data.List (concat)
import Data.String
import Data.Foldable
import Data.Text.Prettyprint.Doc
import GHC.Stack
import qualified Data.Set as S
import qualified Data.Text as T

import Syntax
import Env
import PPrint
import Imp
import Logging
import LLVMExec

type OperandEnv = Env Operand
data CompileState = CompileState { curBlocks   :: [BasicBlock]
                                 , curInstrs   :: [Named Instruction]
                                 , scalarDecls :: [Named Instruction]
                                 , blockName   :: L.Name
                                 , usedNames   :: Env ()
                                 , funSpecs    :: S.Set ExternFunSpec
                                 , globalDefs  :: [L.Definition]
                                 }
data CompileEnv = CompileEnv { operandEnv :: OperandEnv
                             , curDevice  :: Device }

type Compile = ReaderT CompileEnv (State CompileState)
data ExternFunSpec = ExternFunSpec L.Name L.Type [L.ParameterAttribute] [FA.FunctionAttribute] [L.Type]
                     deriving (Ord, Eq)

type Function = L.Global

-- === Imp to LLVM ===

impToLLVM :: Logger [Output] -> ImpModule -> IO L.Module
impToLLVM logger (ImpModule fs) = do
  (defns, externSpecs) <- unzip <$> mapM (compileFunction logger) fs
  let externDefns = map externDecl $ toList $ fold externSpecs
  return $ L.defaultModule
    { L.moduleName = "dexModule"
    , L.moduleDefinitions = concat defns ++ externDefns }

compileFunction :: Logger [Output] -> ImpFunction
                -> IO ([L.Definition], S.Set ExternFunSpec)
compileFunction _ (FFIFunction f) = return ([], S.singleton (makeFunSpec f))
compileFunction logger fun@(ImpFunction f bs body) = case cc of
  CEntryFun -> return $ runCompile CPU $ do
    (argParams   , argOperands   ) <- unzip <$> traverse (freshParamOpPair [] . scalarTy) argTys
    unless (null retTys) $ error "CEntryFun doesn't support returning values"
    void $ extendOperands (newEnv bs argOperands) $ compileBlock body
    mainFun <- makeFunction (asLLVMName name) argParams (Just $ i64Lit 0)
    extraSpecs <- gets funSpecs
    return ([L.GlobalDefinition mainFun], extraSpecs)
  EntryFun requiresCUDA -> return $ runCompile CPU $ do
    (argPtrParam   , argPtrOperand   ) <- freshParamOpPair attrs $ hostPtrTy i64
    (resultPtrParam, resultPtrOperand) <- freshParamOpPair attrs $ hostPtrTy i64
    argOperands <- forM (zip [0..] argTys) $ \(i, ty) ->
      gep argPtrOperand (i64Lit i) >>= castLPtr (scalarTy ty) >>= load
    when requiresCUDA ensureHasCUDAContext
    results <- extendOperands (newEnv bs argOperands) $ compileBlock body
    forM_ (zip [0..] results) $ \(i, x) ->
      gep resultPtrOperand (i64Lit i) >>= castLPtr (L.typeOf x) >>= flip store x
    mainFun <- makeFunction (asLLVMName name)
                 [argPtrParam, resultPtrParam] (Just $ i64Lit 0)
    extraSpecs <- gets funSpecs
    return ([L.GlobalDefinition mainFun], extraSpecs)
    where attrs = [L.NoAlias, L.NoCapture, L.NonNull]
  CUDAKernelLaunch -> do
    (CUDAKernel str) <- compileCUDAKernel logger $ impKernelToLLVMGPU fun
    let strFun = constStringFunction (asLLVMName name) str
    return ([L.GlobalDefinition strFun], S.singleton mallocFun)
  MCThreadLaunch -> return $ runCompile CPU $ do
    (startIdxParam, startIdx) <- freshParamOpPair [] i64
    (endIdxParam, endIdx)     <- freshParamOpPair [] i64
    -- TODO: Preserve pointer attributes??
    (argArrayParam, argArray) <- freshParamOpPair [] $ hostPtrTy hostVoidp
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
      void $ extendOperands (idxEnv <> argEnv) $ compileBlock body
    kernel <- makeFunction (asLLVMName name)
                [startIdxParam, endIdxParam, argArrayParam] Nothing
    extraSpecs <- gets funSpecs
    return ([L.GlobalDefinition kernel], extraSpecs)
    where
      (idxBinder:argBinders) = bs
      idxType = scalarTy $ binderAnn idxBinder
      argTypes = map (scalarTy . binderAnn) argBinders
  where
    name :> IFunType cc argTys retTys = f

compileInstr :: ImpInstr -> Compile [Operand]
compileInstr instr = case instr of
  IFor d i n body  -> [] <$ do
    n' <- compileExpr n
    compileLoop d i n' $ compileVoidBlock body
  IWhile cond body -> [] <$ do
    compileWhile (head <$> compileBlock cond) (compileVoidBlock body)
  ICond p cons alt -> [] <$ do
    p' <- compileExpr p >>= (`asIntWidth` i1)
    compileIf p' (compileVoidBlock cons) (compileVoidBlock alt)
  ILaunch f size args -> [] <$ do
    let IFunType cc _ _ = varAnn f
    size' <- (`asIntWidth` i64) =<< compileExpr size
    args' <- mapM compileExpr args
    let kernelFuncName = asLLVMName $ varName f
    case cc of
      MCThreadLaunch -> do
        kernelParams <- packArgs args'
        let funPtr = L.ConstantOperand $ C.BitCast
                        (C.GlobalReference mcKernelPtrType kernelFuncName) hostVoidp
        emitVoidExternCall runMCKernel [funPtr, size',kernelParams]
      CUDAKernelLaunch -> do
        let ptxPtrFun = callableOperand (funTy (hostPtrTy i8) []) kernelFuncName
        ptxPtr <- emitInstr (hostPtrTy i8) $ callInstr ptxPtrFun []
        kernelParams <- packArgs $ size' : args'
        launchCUDAKernel ptxPtr size' kernelParams
      _ -> error $ "Not a valid calling convention for a launch: " ++ pprint cc
  IThrowError   -> [] <$  throwRuntimeError
  Alloc a t s -> (:[]) <$> case a of
    Stack -> alloca (getIntLit l) elemTy  where ILit l = s
    Heap dev -> do
      numBytes <- mul (sizeof elemTy) =<< (`asIntWidth` i64) =<< compileExpr s
      case dev of
        CPU -> malloc     elemTy numBytes
        GPU -> cuMemAlloc elemTy numBytes
    where elemTy = scalarTy t
  Free ptr -> [] <$ do
    let PtrType (_, addr, _) = getIType ptr
    ptr' <- compileExpr ptr
    case addr of
      Heap CPU -> free      ptr'
      Heap GPU -> cuMemFree ptr'
      Stack -> error "Shouldn't be freeing alloca"
  MemCopy dest src numel -> [] <$ do
    let PtrType (_, destAddr, ty) = getIType dest
    let PtrType (_, srcAddr , _ ) = getIType src
    destDev <- deviceFromAddr destAddr
    srcDev  <- deviceFromAddr srcAddr
    dest' <- compileExpr dest >>= castVoidPtr
    src'  <- compileExpr src  >>= castVoidPtr
    numel' <- compileExpr numel >>= (`asIntWidth` i64)
    numBytes <- numel' `mul` sizeof (scalarTy ty)
    case (destDev, srcDev) of
      (CPU, GPU) -> cuMemcpyDToH numBytes src'  dest'
      (GPU, CPU) -> cuMemcpyHToD numBytes dest' src'
      _ -> error $ "Not implemented"
  Store dest val -> [] <$ do
    dest' <- compileExpr dest
    val'  <- compileExpr val
    store dest' val'
    return Nothing
  IPrimOp (PtrLoad ptr) -> (:[]) <$> (compileExpr ptr >>= load)
  IPrimOp op -> (:[]) <$> (traverse compileExpr op >>= compilePrimOp)
  ICastOp idt ix -> (:[]) <$> do
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
  ICall f args -> (:[]) <$> do
    args' <- mapM compileExpr args
    emitInstr retTy $ externCall (makeFunSpec f) args'
    where
      (_:> IFunType _ _ [resultTy]) = f
      retTy = scalarTy resultTy

makeFunSpec :: IFunVar -> ExternFunSpec
makeFunSpec (Name _ name _ :> IFunType _ argTys [resultTy]) =
   ExternFunSpec (L.Name (fromString $ T.unpack name)) (scalarTy resultTy)
                    [] [] (map scalarTy argTys)

compileLoop :: Direction -> IBinder -> Operand -> Compile () -> Compile ()
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

compileIf :: Operand -> Compile () -> Compile () -> Compile ()
compileIf cond tb fb = do
  tbName   <- freshName "if_true"
  fbName   <- freshName "if_false"
  contName <- freshName "if_cont"
  finishBlock (L.CondBr cond tbName fbName []) tbName
  tb
  finishBlock (L.Br contName []) fbName
  fb
  finishBlock (L.Br contName []) contName

compileWhile :: Compile Operand -> Compile () -> Compile ()
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
  finishBlock (L.Ret (Just $ i64Lit 1) []) deadBlock

compilePrimOp :: PrimOp Operand -> Compile Operand
compilePrimOp pop = case pop of
  ScalarBinOp op x y -> compileBinOp op x y
  VectorBinOp op x y -> compileBinOp op x y
  ScalarUnOp  op x   -> compileUnOp  op x
  Select      p  x y -> do
    pb <- p `asIntWidth` i1
    emitInstr (L.typeOf x) $ L.Select pb x y []
  VectorPack elems   -> foldM fillElem undef $ zip elems [0..]
    where
      resTy = L.VectorType (fromIntegral vectorWidth) $ L.typeOf $ head elems
      fillElem v (e, i) = emitInstr resTy $ L.InsertElement v e (i32Lit i) []
      undef = L.ConstantOperand $ C.Undef resTy
  VectorIndex v i    -> emitInstr resTy $ L.ExtractElement v i []
    where (L.VectorType _ resTy) = L.typeOf v
  PtrOffset ptr off -> gep ptr off
  _ -> error $ "Can't JIT primop: " ++ pprint pop

compileUnOp :: UnOp -> Operand -> Compile Operand
compileUnOp op x = case op of
  -- LLVM has "fneg" but it doesn't seem to be exposed by llvm-hs-pure
  FNeg            -> emitInstr (L.typeOf x) $ L.FSub mathFlags (0.0 `withWidthOfFP` x) x []
  BNot            -> emitInstr boolTy $ L.Xor x (i8Lit 1) []
  _               -> unaryIntrinsic op x

compileBinOp :: BinOp -> Operand -> Operand -> Compile Operand
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

deviceFromAddr :: AddressSpace -> Compile Device
deviceFromAddr addr = case addr of
  Heap dev -> return dev
  Stack -> asks curDevice

-- === MDImp to LLVM CUDA ===

ensureHasCUDAContext :: Compile ()
ensureHasCUDAContext = emitVoidExternCall spec []
  where spec = ExternFunSpec "dex_ensure_has_cuda_context" L.VoidType [] [] []

launchCUDAKernel :: Operand -> Operand -> Operand -> Compile()
launchCUDAKernel ptx size args = emitVoidExternCall spec [ptx, size, args]
  where spec = ExternFunSpec "dex_cuLaunchKernel" L.VoidType [] []
                 [hostVoidp, i64, hostPtrTy $ hostVoidp]

cuMemcpyDToH :: Operand -> Operand -> Operand -> Compile ()
cuMemcpyDToH bytes devPtr hostPtr = emitVoidExternCall spec [bytes, devPtr, hostPtr]
  where spec = ExternFunSpec "dex_cuMemcpyDtoH" L.VoidType [] [] [i64, deviceVoidp, hostVoidp]

cuMemcpyHToD :: Operand -> Operand -> Operand -> Compile ()
cuMemcpyHToD bytes devPtr hostPtr = emitVoidExternCall spec [bytes, devPtr, hostPtr]
  where spec = ExternFunSpec "dex_cuMemcpyHtoD" L.VoidType [] [] [i64, deviceVoidp, hostVoidp]

cuMemAlloc :: L.Type -> Operand -> Compile Operand
cuMemAlloc ty bytes = castLPtr ty =<< emitExternCall spec [bytes]
  where spec = ExternFunSpec "dex_cuMemAlloc" deviceVoidp [] [] [i64]

cuMemFree :: Operand -> Compile ()
cuMemFree ptr = do
  voidptr <- castVoidPtr ptr
  emitVoidExternCall spec [voidptr]
  where spec = ExternFunSpec "dex_cuMemFree" L.VoidType [] [] [deviceVoidp]

-- === GPU Kernel compilation ===

impKernelToLLVMGPU :: ImpFunction -> LLVMKernel
impKernelToLLVMGPU (ImpFunction _ ~(lvar:args) body) = runCompile GPU $ do
  (argParams, argOperands) <- unzip <$> mapM (freshParamOpPair ptrParamAttrs) argTypes
  (sizeParam, sizeOperand) <- freshParamOpPair [] lidxType
  tidx <- threadIdxX
  bidx <- blockIdxX
  bsz  <- blockDimX
  lidx <- mul bidx bsz >>= (add tidx) >>= (`asIntWidth` lidxType)
  outOfBounds <- emitInstr i1 $ L.ICmp IP.UGE lidx sizeOperand []
  compileIf outOfBounds (return ()) $ do
    let paramEnv = foldMap (uncurry (@>)) $ zip args argOperands
    -- TODO: Use a restricted form of compileBlock that e.g. never emits FFI calls!
    void $ extendOperands (paramEnv <> lvar @> lidx) $ compileBlock body
  kernel <- makeFunction "kernel" (sizeParam : argParams) Nothing
  LLVMKernel <$> makeModuleEx ptxDataLayout ptxTargetTriple
                   [L.GlobalDefinition kernel, kernelMeta, nvvmAnnotations]
  where
    lidxType = scalarTy $ binderAnn lvar
    ptrParamAttrs = [L.NoAlias, L.NoCapture, L.NonNull, L.Alignment 256]
    argTypes = fmap (scalarTy . binderAnn) args
    kernelMetaId = L.MetadataNodeID 0
    kernelMeta = L.MetadataNodeDefinition kernelMetaId $ L.MDTuple
      [ Just $ L.MDValue $ L.ConstantOperand $ C.GlobalReference
          (funTy L.VoidType (lidxType : argTypes)) "kernel"
      , Just $ L.MDString "kernel"
      , Just $ L.MDValue $ L.ConstantOperand $ C.Int 32 1
      ]
    nvvmAnnotations = L.NamedMetadataDefinition "nvvm.annotations" [kernelMetaId]

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

gpuUnaryIntrinsic :: UnOp -> Operand -> Compile Operand
gpuUnaryIntrinsic op x = case L.typeOf x of
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

gpuBinaryIntrinsic :: BinOp -> Operand -> Operand -> Compile Operand
gpuBinaryIntrinsic op x y = case L.typeOf x of
  L.FloatingPointType L.DoubleFP -> dispatchOp fp64 ""
  L.FloatingPointType L.FloatFP  -> dispatchOp fp32 "f"
  _ -> error $ "Unsupported GPU floating point type: " ++ show (L.typeOf x)
  where
    dispatchOp ty suffix = case op of
      FPow -> callFloatIntrinsic ty $ "__nv_pow" ++ suffix
      _    -> error $ "Unsupported GPU operation: " ++ show op
    floatIntrinsic ty name = ExternFunSpec (L.mkName name) ty [] [] [ty, ty]
    callFloatIntrinsic ty name = emitExternCall (floatIntrinsic ty name) [x, y]

compileBlock :: ImpBlock -> Compile [Operand]
compileBlock (ImpBlock Empty result) = traverse compileExpr result
compileBlock (ImpBlock (Nest decl rest) result) = do
  env <- compileDecl decl
  extendOperands env $ compileBlock (ImpBlock rest result)

compileDecl :: ImpDecl -> Compile OperandEnv
compileDecl (ImpLet bs instr) = do
  results <- compileInstr instr
  if length results == length bs
    then return $ foldMap (uncurry (@>)) $ zip bs results
    else error "Unexpected number of results"

compileVoidBlock :: ImpBlock -> Compile ()
compileVoidBlock = void . compileBlock

compileExpr :: IExpr -> Compile Operand
compileExpr expr = case expr of
  ILit v   -> return (litVal v)
  IVar v   -> lookupImpVar v

packArgs :: [Operand] -> Compile Operand
packArgs elems = do
  arr <- alloca (length elems) hostVoidp
  forM_ (zip [0..] elems) $ \(i, e) -> do
    eptr <- alloca 1 $ L.typeOf e
    store eptr e
    earr <- gep arr $ i32Lit i
    store earr =<< castVoidPtr eptr
  return arr

unpackArgs :: Operand -> [L.Type] -> Compile [Operand]
unpackArgs argArrayPtr types =
  forM (zip [0..] types) $ \(i, ty) -> do
    argVoidPtr <- gep argArrayPtr $ i64Lit i
    argPtr <- castLPtr (hostPtrTy ty) argVoidPtr
    load =<< load argPtr

runMCKernel :: ExternFunSpec
runMCKernel = ExternFunSpec "dex_parallel_for" L.VoidType [] [] [hostVoidp, i64, hostPtrTy hostVoidp]

mcKernelPtrType :: L.Type
mcKernelPtrType = hostPtrTy $ L.FunctionType L.VoidType [i64, i64, hostPtrTy $ hostVoidp] False

-- === LLVM embedding ===

litVal :: LitVal -> Operand
litVal lit = case lit of
  Int64Lit x   -> i64Lit $ fromIntegral x
  Int32Lit x   -> i32Lit $ fromIntegral x
  Int8Lit  x   -> i8Lit  $ fromIntegral x
  Float64Lit x -> L.ConstantOperand $ C.Float $ L.Double x
  Float32Lit x -> L.ConstantOperand $ C.Float $ L.Single x
  VecLit l     -> L.ConstantOperand $ foldl fillElem undef $ zip consts [0..length l - 1]
    where
      consts = fmap (operandToConst . litVal) l
      undef = C.Undef $ L.VectorType (fromIntegral $ length l) $ L.typeOf $ head consts
      fillElem v (c, i) = C.InsertElement v c (C.Int 32 (fromIntegral i))
      operandToConst ~(L.ConstantOperand c) = c
  PtrLit _ _ -> error "Shouldn't be compiling pointer literals"
    -- L.ConstantOperand $ C.IntToPtr (C.Int 64 ptrAsInt) (L.ptr (scalarTy ty))
    -- where ptrAsInt = fromIntegral $ ptrToWordPtr ptr

-- TODO: Assert that the integer can be represented in that number of bits!
withWidth :: Int -> Word32 -> Operand
withWidth x bits = L.ConstantOperand $ C.Int bits $ fromIntegral x

i64Lit :: Int -> Operand
i64Lit x = x `withWidth` 64

i32Lit :: Int -> Operand
i32Lit x = x `withWidth` 32

i8Lit :: Int -> Operand
i8Lit x = x `withWidth` 8

withWidthOf :: Int -> Operand -> Operand
withWidthOf x template = case L.typeOf template of
  L.IntegerType bits -> x `withWidth` (fromIntegral bits)
  _ -> error $ "Expected an integer: " ++ show template

withWidthOfFP :: Double -> Operand -> Operand
withWidthOfFP x template = case L.typeOf template of
  L.FloatingPointType L.DoubleFP -> litVal $ Float64Lit x
  L.FloatingPointType L.FloatFP  -> litVal $ Float32Lit $ realToFrac x
  _ -> error $ "Unsupported floating point type: " ++ show (L.typeOf template)

store :: Operand -> Operand -> Compile ()
store ptr x =  addInstr $ L.Do $ L.Store False ptr x Nothing 0 []

load :: Operand -> Compile Operand
load ptr = emitInstr ty $ L.Load False ptr Nothing 0 []
  where (L.PointerType ty _) = L.typeOf ptr

ilt :: Operand -> Operand -> Compile Operand
ilt x y = emitInstr i1 $ L.ICmp IP.SLT x y []

ige :: Operand -> Operand -> Compile Operand
ige x y = emitInstr i1 $ L.ICmp IP.SGE x y []

add :: Operand -> Operand -> Compile Operand
add x y = emitInstr (L.typeOf x) $ L.Add False False x y []

sub :: Operand -> Operand -> Compile Operand
sub x y = emitInstr (L.typeOf x) $ L.Sub False False x y []

mul :: Operand -> Operand -> Compile Operand
mul x y = emitInstr (L.typeOf x) $ L.Mul False False x y []

gep :: Operand -> Operand -> Compile Operand
gep ptr i = emitInstr (L.typeOf ptr) $ L.GetElementPtr False ptr [i] []

sizeof :: L.Type -> Operand
sizeof t = (L.ConstantOperand $ C.ZExt (C.sizeof t) i64)

alloca :: Int -> L.Type -> Compile Operand
alloca elems ty = do
  v <- freshName "v"
  modify $ setScalarDecls ((v L.:= instr):)
  return $ L.LocalReference (hostPtrTy ty) v
  where instr = L.Alloca ty (Just $ i32Lit elems) 0 []

malloc :: L.Type -> Operand -> Compile Operand
malloc ty bytes = do
  bytes64 <- asIntWidth bytes i64
  castLPtr ty =<< emitExternCall mallocFun [bytes64]

free :: Operand -> Compile ()
free ptr = do
 ptr' <- castLPtr i8 ptr
 emitVoidExternCall freeFun [ptr']

castLPtr :: L.Type -> Operand -> Compile Operand
castLPtr ty ptr = emitInstr newPtrTy $ L.BitCast ptr newPtrTy []
  where
    L.PointerType _ addr = L.typeOf ptr
    newPtrTy = L.PointerType ty addr

castVoidPtr :: Operand -> Compile Operand
castVoidPtr = castLPtr i8

zeroExtendTo :: Operand -> L.Type -> Compile Operand
zeroExtendTo x t = emitInstr t $ L.ZExt x t []

callInstr :: L.CallableOperand -> [L.Operand] -> L.Instruction
callInstr fun xs = L.Call Nothing L.C [] fun xs' [] []
 where xs' = [(x ,[]) | x <- xs]

externCall :: ExternFunSpec -> [L.Operand] -> L.Instruction
externCall (ExternFunSpec fname retTy _ _ argTys) xs = callInstr fun xs
  where fun = callableOperand (funTy retTy argTys) fname

emitExternCall :: ExternFunSpec -> [L.Operand] -> Compile Operand
emitExternCall f@(ExternFunSpec _ retTy _ _ _) xs = do
  modify $ setFunSpecs (S.insert f)
  emitInstr retTy $ externCall f xs

emitVoidExternCall :: ExternFunSpec -> [L.Operand] -> Compile ()
emitVoidExternCall f xs = do
  modify $ setFunSpecs (S.insert f)
  addInstr $ L.Do $ externCall f xs

scalarTy :: HasCallStack => BaseType -> L.Type
scalarTy b = case b of
  Scalar sb -> case sb of
    Int64Type   -> i64
    Int32Type   -> i32
    Int8Type    -> i8
    Float64Type -> fp64
    Float32Type -> fp32
  Vector sb -> L.VectorType (fromIntegral vectorWidth) $ scalarTy $ Scalar sb
  PtrType (_, s, t) -> L.PointerType (scalarTy t) (lAddress s)

hostPtrTy :: L.Type -> L.Type
hostPtrTy ty = L.PointerType ty $ L.AddrSpace 0

devicePtrTy :: L.Type -> L.Type
devicePtrTy ty = L.PointerType ty $ L.AddrSpace 1

lAddress :: HasCallStack => AddressSpace -> L.AddrSpace
lAddress s = case s of
  Stack    -> L.AddrSpace 0
  Heap CPU -> L.AddrSpace 0
  Heap GPU -> L.AddrSpace 1

callableOperand :: L.Type -> L.Name -> L.CallableOperand
callableOperand ty name = Right $ L.ConstantOperand $ C.GlobalReference ty name

asLLVMName :: Name -> L.Name
asLLVMName name@(Name TopFunctionName _ _) = fromString $ pprint name
asLLVMName name = error $ "Expected a top function name: " ++ show name

showName :: Name -> String
showName (Name GenName tag counter) = asStr $ pretty tag <> "." <> pretty counter
showName _ = error $ "All names in JIT should be from the GenName namespace"

asIntWidth :: Operand -> L.Type -> Compile Operand
asIntWidth op ~expTy@(L.IntegerType expWidth) = case compare expWidth opWidth of
  LT -> emitInstr expTy $ L.Trunc op expTy []
  EQ -> return op
  GT -> emitInstr expTy $ L.ZExt  op expTy []
  where ~(L.IntegerType opWidth) = L.typeOf op

freshParamOpPair :: [L.ParameterAttribute] -> L.Type -> Compile (Parameter, Operand)
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

cpuUnaryIntrinsic :: UnOp -> Operand -> Compile Operand
cpuUnaryIntrinsic op x = case L.typeOf x of
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

cpuBinaryIntrinsic :: BinOp -> Operand -> Operand -> Compile Operand
cpuBinaryIntrinsic op x y = case L.typeOf x of
  L.FloatingPointType L.DoubleFP -> dispatchOp fp64 ".f64"
  L.FloatingPointType L.FloatFP  -> dispatchOp fp32 ".f32"
  _ -> error $ "Unsupported CPU floating point type: " ++ show (L.typeOf x)
  where
    dispatchOp ty llvmSuffix = case op of
      FPow -> callFloatIntrinsic ty $ "llvm.pow" ++ llvmSuffix
      _ -> error $ "Unsupported CPU operation: " ++ show op
    floatIntrinsic ty name = ExternFunSpec (L.mkName name) ty [] [] [ty, ty]
    callFloatIntrinsic ty name = emitExternCall (floatIntrinsic ty name) [x, y]

constStringFunction :: L.Name -> B.ByteString -> Function
constStringFunction name str = runCompile CPU $ do
  let chars = map (C.Int 8) $ map (fromIntegral . fromEnum) (B.unpack str) ++ [0]
  ptr <- malloc i8 $ i64Lit $ length chars
  let strVal = L.ConstantOperand $ C.Array i8 chars
  tyPtr <- castLPtr (L.typeOf strVal) ptr
  store tyPtr strVal
  makeFunction name [] (Just ptr)

-- === Compile monad utilities ===

runCompile :: Device -> Compile a -> a
runCompile dev m = evalState (runReaderT m env) initState
  where
    env = CompileEnv mempty dev
    initState = CompileState [] [] [] "start_block" mempty mempty mempty

extendOperands :: OperandEnv -> Compile a -> Compile a
extendOperands openv = local $ \env -> env { operandEnv = (operandEnv env) <> openv }

lookupImpVar :: IVar -> Compile Operand
lookupImpVar v = asks ((! v) . operandEnv)

finishBlock :: L.Terminator -> L.Name -> Compile ()
finishBlock term newName = do
  oldName <- gets blockName
  instrs  <- gets curInstrs
  let newBlock = L.BasicBlock oldName (reverse instrs) (L.Do term)
  modify $ setCurBlocks (newBlock:)
         . setCurInstrs (const [])
         . setBlockName (const newName)

freshName :: Name -> Compile L.Name
freshName v = do
  used <- gets usedNames
  let v' = genFresh v used
  modify $ \s -> s { usedNames = used <> v' @> () }
  return $ nameToLName v'
  where
    nameToLName :: Name -> L.Name
    nameToLName name = L.Name $ toShort $ B.pack $ showName name

-- TODO: consider getting type from instruction rather than passing it explicitly
emitInstr :: L.Type -> Instruction -> Compile Operand
emitInstr ty instr = do
  v <- freshName "v"
  addInstr $ v L.:= instr
  return $ L.LocalReference ty v

addInstr :: Named Instruction -> Compile ()
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

unaryIntrinsic :: UnOp -> Operand -> Compile Operand
unaryIntrinsic op x = do
  device <- asks curDevice
  case device of
    CPU -> cpuUnaryIntrinsic op x
    GPU -> gpuUnaryIntrinsic op x

binaryIntrinsic :: BinOp -> Operand -> Operand -> Compile Operand
binaryIntrinsic op x y = do
  device <- asks curDevice
  case device of
    CPU -> cpuBinaryIntrinsic op x y
    GPU -> gpuBinaryIntrinsic op x y

-- === Constants ===

allowContractions :: Bool
allowContractions = unsafePerformIO $ (Just "0"/=) <$> lookupEnv "DEX_ALLOW_CONTRACTIONS"

-- FP contractions should only lead to fewer rounding points, so we allow those
mathFlags :: L.FastMathFlags
mathFlags = L.noFastMathFlags { L.allowContract = allowContractions }

mallocFun :: ExternFunSpec
mallocFun = ExternFunSpec "malloc_dex" (hostPtrTy i8) [L.NoAlias] [] [i64]

freeFun :: ExternFunSpec
freeFun = ExternFunSpec "free_dex" L.VoidType [] [] [hostPtrTy i8]

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

hostVoidp :: L.Type
hostVoidp = hostPtrTy i8

deviceVoidp :: L.Type
deviceVoidp = devicePtrTy i8

funTy :: L.Type -> [L.Type] -> L.Type
funTy retTy argTys = hostPtrTy $ L.FunctionType retTy argTys False

-- === Module building ===

makeFunction :: L.Name -> [Parameter] -> Maybe L.Operand -> Compile Function
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

makeModuleEx :: L.DataLayout -> ShortByteString -> [L.Definition] -> Compile L.Module
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
