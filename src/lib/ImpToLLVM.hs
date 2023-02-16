-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE DuplicateRecordFields #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module ImpToLLVM (impToLLVM) where

import LLVM.AST (Operand, BasicBlock, Instruction, Named, Parameter)
import LLVM.Prelude (ShortByteString, Word32)
import qualified LLVM.AST as L
import qualified LLVM.AST.Linkage as L
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
import qualified LLVM.IRBuilder.Module as MB

import System.IO.Unsafe
import qualified System.Environment as E
import Control.Monad
import Control.Monad.State.Strict
import Control.Monad.Reader
import Data.ByteString.Short (toShort)
import qualified Data.ByteString.Char8 as B
import Data.Functor ((<&>))
import Data.String
import Data.Foldable
import Data.Text.Prettyprint.Doc
import GHC.Stack
import qualified Data.ByteString.Char8 as C8BS
import qualified Data.ByteString.Short as SBS
import qualified Data.Set as S

import CUDA (getCudaArchitecture)

import Core
import Err
import Imp
import LLVM.CUDA (LLVMKernel (..), compileCUDAKernel, ptxDataLayout, ptxTargetTriple)
import Logging
import Subst
import Name
import PPrint
import RawName qualified as R
import Types.Core
import Types.Imp
import Types.Misc
import Types.Primitives
import Types.Source
import Util (IsBool (..), bindM2, enumerate)

-- === Compile monad ===

data OperandSubstVal (c::C) (n::S) where
  OperandSubstVal  :: L.Operand -> OperandSubstVal ImpNameC n
  PtrSubstVal      :: L.Operand -> OperandSubstVal PtrNameC n
  FunctionSubstVal :: L.Operand -> LLVMFunType -> IFunType -> OperandSubstVal TopFunNameC   n
  RenameOperandSubstVal :: Name c n -> OperandSubstVal c n -- only used for top-level FFI names

type OperandEnv     = Subst     OperandSubstVal
type OperandEnvFrag = SubstFrag OperandSubstVal

type Function = L.Global

data ExternFunSpec =
  ExternFunSpec L.Name L.Type [L.ParameterAttribute] [FA.FunctionAttribute] [L.Type]
  deriving (Ord, Eq)

data CompileState = CompileState
  { curBlocks   :: [BasicBlock]
  , curInstrs   :: [Named Instruction]
  , scalarDecls :: [Named Instruction]
  , blockName   :: L.Name
  , usedNames   :: R.RawNameMap ()
  , funSpecs    :: S.Set ExternFunSpec
  , globalDefs  :: [L.Definition]
  , curDevice   :: Device }

newtype CompileM i o a =
  CompileM { runCompileM' ::
              SubstReaderT OperandSubstVal
                (EnvReaderT (State CompileState)) i o a }
  deriving ( Functor, Applicative, Monad, ScopeReader, EnvExtender
           , EnvReader, SubstReader OperandSubstVal )

instance MonadState CompileState (CompileM i o) where
  state f = CompileM $ SubstReaderT $ lift $ EnvReaderT $ lift $ state f

class MonadState CompileState m => LLVMBuilder (m::MonadKind)

class ( SubstReader OperandSubstVal m
      , (forall i o. LLVMBuilder (m i o))
      , EnvReader2 m )
      => Compiler (m::MonadKind2)

instance LLVMBuilder (CompileM i o)
instance Compiler CompileM

-- === Imp to LLVM ===

impToLLVM :: (EnvReader m, MonadIO1 m)
          => FilteredLogger PassName [Output] -> NameHint
          -> ClosedImpFunction n
          -> m n (WithCNameInterface L.Module)
impToLLVM logger fNameHint (ClosedImpFunction funBinders ptrBinders impFun) = do
  let fName = makeMainFunName fNameHint
  (funDefns, funNames, funVals) <- makeFunDefns funBinders
  (ptrDefns, ptrNames, ptrVals) <- makePtrDefns ptrBinders
  let initEnv = idSubst <>> funBinders @@> funVals <>> ptrBinders @@> ptrVals
  (defns, externSpecs, globalDtors) <- compileFunction logger (L.Name $ fromString fName) initEnv impFun
  let externDefns = map externDecl $ toList externSpecs
  let dtorDef = defineGlobalDtors globalDtors
  let resultModule = L.defaultModule
        { L.moduleName = "dexModule"
        , L.moduleDefinitions = dtorDef : funDefns ++ ptrDefns ++ defns ++ externDefns ++ dyvarDefs }
  let dtorNames = map (\(L.Name dname) -> C8BS.unpack $ SBS.fromShort dname) globalDtors
  return $ WithCNameInterface resultModule fName funNames ptrNames dtorNames
  where
    dtorType = L.FunctionType L.VoidType [] False
    dtorRegEntryTy = L.StructureType False [ i32, hostPtrTy dtorType, hostVoidp ]
    makeDtorRegEntry dtorName = C.Struct Nothing False
                                         [ C.Int 32 1
                                         , globalReference (hostPtrTy dtorType) dtorName
                                         , C.Null hostVoidp ]
    defineGlobalDtors globalDtors =
      L.GlobalDefinition $ L.globalVariableDefaults
        { L.name = "llvm.global_dtors"
        , L.type' = L.ArrayType (fromIntegral $ length globalDtors) dtorRegEntryTy
        , L.linkage = L.Appending
        , L.initializer = Just $ C.Array dtorRegEntryTy (makeDtorRegEntry <$> globalDtors)
        }

    -- This name is only used for extracting the pointer to the main function. There
    -- are no requirements for uniqueness beyond the current LLVM module. The hint
    -- is just for readability and could be ignored without affecting correctness.
    makeMainFunName :: NameHint -> CName
    makeMainFunName hint = "dexMainFunction_" <> fromString (show hint)

    makeNames :: String -> [NameHint] -> [CName]
    makeNames prefix hints =
      [prefix <> fromString (show h) <> "_" <> fromString (show i) | (i, h) <- enumerate hints]

    makeFunDefns :: EnvReader m => Nest IFunBinder any1 any2
                 -> m n ([L.Definition], [CName], [OperandSubstVal TopFunNameC n])
    makeFunDefns bs = do
      let cnames = makeNames "dex_called_fun_" $ nestToList getNameHint bs
      let tys = nestToList (\(IFunBinder _ ty) -> ty) bs
      (defns, substVals) <- unzip <$> forM (zip cnames tys) \(v, ty) -> do
        let llvmTy@(retTy, argTys) = impFunTyToLLVMTy ty
        let v' = L.Name $ fromString v
        let defn = externDecl $ ExternFunSpec v' retTy [] [] argTys
        let op = L.ConstantOperand $ globalReference (hostPtrTy $ funTy retTy argTys) v'
        let sv = FunctionSubstVal op llvmTy ty
        return (defn, sv)
      return (defns, cnames, substVals)

    makePtrDefns :: EnvReader m => Nest PtrBinder any1 any2
                 -> m n ([L.Definition], [CName], [OperandSubstVal PtrNameC n])
    makePtrDefns bs = do
      let cnames = makeNames "dex_const_ptr_" $ nestToList getNameHint bs
      let tys = nestToList (\(PtrBinder _ t) -> t) bs
      (defns, substVals) <- unzip <$> forM (zip cnames tys) \(v, ptrTy@(_, ty)) -> do
        let v' = L.Name $ fromString v
        let ty'    = scalarTy ty
        let ptrTy' = scalarTy $ PtrType ptrTy
        let defn = L.GlobalDefinition $ L.globalVariableDefaults
                      { L.name = v'
                      , L.type' = ty'
                      , L.linkage = L.External
                      , L.initializer = Nothing }
        let sv = PtrSubstVal $ L.ConstantOperand $ globalReference ptrTy' v'
        return (defn, sv)
      return (defns, cnames, substVals)

compileFunction
  :: (EnvReader m, MonadIO1 m)
  => FilteredLogger PassName [Output] -> L.Name
  -> OperandEnv i o -> ImpFunction i
  -> m o ([L.Definition], S.Set ExternFunSpec, [L.Name])
compileFunction logger fName env fun@(ImpFunction (IFunType cc argTys retTys)
                (Abs bs body)) = case cc of
  FFICC            -> error "shouldn't be trying to compile an FFI function"
  FFIMultiResultCC -> error "shouldn't be trying to compile an FFI function"
  StandardCC -> goStandardOrXLACC
  XLACC      -> goStandardOrXLACC
  EntryFunCC requiresCUDA -> liftCompile CPU env $ do
    (streamFDParam , streamFDOperand ) <- freshParamOpPair attrs $ i32
    (argPtrParam   , argPtrOperand   ) <- freshParamOpPair attrs $ hostPtrTy i64
    (resultPtrParam, resultPtrOperand) <- freshParamOpPair attrs $ hostPtrTy i64
    initializeOutputStream streamFDOperand
    argOperands <- forM (zip [0..] argTys) \(i, ty) ->
      gep i64 argPtrOperand (i64Lit i) >>= castLPtr (scalarTy ty) >>= load (scalarTy ty)
    when (toBool requiresCUDA) ensureHasCUDAContext
    results <- extendSubst (bs @@> map opSubstVal argOperands) $ compileBlock body
    forM_ (zip [0..] results) \(i, x) ->
      gep i64 resultPtrOperand (i64Lit i) >>= castLPtr (typeOf x) >>= flip store x
    mainFun <- makeFunction fName
                 [streamFDParam, argPtrParam, resultPtrParam] (Just $ i64Lit 0)
    extraSpecs <- gets funSpecs
    return ([L.GlobalDefinition mainFun], extraSpecs, [])
    where attrs = [L.NoAlias, L.NoCapture, L.NonNull]
  CUDAKernelLaunch -> do
    arch <- liftIO $ getCudaArchitecture 0
    (CUDAKernel kernelText) <- do
      fun' <- impKernelToLLVMGPU env fun
      liftIO $ compileCUDAKernel logger fun' arch
    let chars = map (C.Int 8) $ map (fromIntegral . fromEnum) (B.unpack kernelText) ++ [0]
    let textArr = C.Array i8 chars
    let textArrTy = typeOf textArr
    let textGlobalName = qualifyName fName "text"
    let textArrDef = L.globalVariableDefaults
                          { L.name = textGlobalName
                          , L.type' = textArrTy
                          , L.linkage = L.Private
                          , L.isConstant = True
                          , L.initializer = Just textArr
                          , L.unnamedAddr = Just L.GlobalAddr
                          }
    let kernelModuleCacheName = qualifyName fName "cuModule"
    let kernelModuleCacheDef = L.globalVariableDefaults
                                    { L.name = kernelModuleCacheName
                                    , L.type' = hostVoidp
                                    , L.linkage = L.Private
                                    , L.initializer = Just $ C.Null hostVoidp }
    let kernelModuleCache = L.ConstantOperand $ globalReference (hostPtrTy hostVoidp) kernelModuleCacheName
    let kernelFuncCacheName = qualifyName fName "cuFunctioN"
    let kernelFuncCacheDef   = L.globalVariableDefaults
                                    { L.name = kernelFuncCacheName
                                    , L.type' = hostVoidp
                                    , L.linkage = L.Private
                                    , L.initializer = Just $ C.Null hostVoidp }
    let kernelFuncCache = L.ConstantOperand $ globalReference (hostPtrTy hostVoidp) kernelFuncCacheName
    let textPtr = C.GetElementPtr True
#if MIN_VERSION_llvm_hs(15,0,0)
                                  textArrTy
#endif
                                  (globalReference (hostPtrTy textArrTy) textGlobalName)
                                  [C.Int 32 0, C.Int 32 0]
    loaderDef <- liftCompile CPU env $ do
          emitVoidExternCall kernelLoaderSpec
            [ L.ConstantOperand $ textPtr, kernelModuleCache, kernelFuncCache]
          kernelFunc <- load hostVoidp kernelFuncCache
          makeFunction fName [] (Just kernelFunc)
    let dtorName = qualifyName fName "dtor"
    dtorDef <- liftCompile CPU env $ do
          emitVoidExternCall kernelUnloaderSpec
            [ kernelModuleCache, kernelFuncCache ]
          makeFunction dtorName [] Nothing
    let globals = [textArrDef, kernelModuleCacheDef, kernelFuncCacheDef, loaderDef, dtorDef]
    return ( L.GlobalDefinition <$> globals
           , S.fromList [kernelLoaderSpec, kernelUnloaderSpec]
           , [dtorName])
    where
      kernelLoaderSpec   = ExternFunSpec "dex_loadKernelCUDA" L.VoidType [] []
                                         [hostPtrTy i8, hostPtrTy hostVoidp, hostPtrTy hostVoidp]
      kernelUnloaderSpec = ExternFunSpec "dex_unloadKernelCUDA" L.VoidType [] []
                                         [hostPtrTy hostVoidp, hostPtrTy hostVoidp]
      qualifyName :: L.Name -> ShortByteString -> L.Name
      qualifyName (L.Name s) qual = L.Name $ s <> "#" <> qual
      qualifyName (L.UnName _) _ = error "can only qualify text names"

  MCThreadLaunch -> liftCompile CPU env $ do
    let numThreadInfoArgs = 4  -- [threadIdParam, nThreadParam, argArrayParam]
    let argTypes = drop numThreadInfoArgs $ nestToList (scalarTy . iBinderType) bs
    -- Set up arguments
    (argArrayParam, argArray) <- freshParamOpPair [] $ hostPtrTy hostVoidp
    args <- unpackArgs argArray argTypes
    -- Set up thread info
    wid                       <- compileExpr $ IIdxRepVal 0
    (threadIdParam, tidArg  ) <- freshParamOpPair [] i32
    (nThreadParam , nthrArg ) <- freshParamOpPair [] i32
    tid  <- tidArg  `asIntWidth` idxRepTy
    nthr <- nthrArg `asIntWidth` idxRepTy
    let subst = bs @@> map opSubstVal ([tid, wid, nthr, nthr] ++ args)
    -- Emit the body
    void $ extendSubst subst $ compileBlock body
    kernel <- makeFunction fName [threadIdParam, nThreadParam, argArrayParam] Nothing
    extraSpecs <- gets funSpecs
    return ([L.GlobalDefinition kernel], extraSpecs, [])
  where
    goStandardOrXLACC = liftCompile CPU env $ do
      (argParams, argOperands) <- unzip <$> traverse (freshParamOpPair [] . scalarTy) argTys
      unless (null retTys) $ error "StandardCC doesn't support returning values"
      void $ extendSubst (bs @@> map opSubstVal argOperands) $ compileBlock body
      mainFun <- makeFunction fName argParams (Just $ i64Lit 0)
      extraSpecs <- gets funSpecs
      return ([L.GlobalDefinition mainFun], extraSpecs, [])

compileInstr :: Compiler m => ImpInstr i -> m i o [Operand]
compileInstr instr = case instr of
  IFor d n (Abs i body)  -> [] <$ do
    n' <- compileExpr n
    compileLoop d i n' $ compileVoidBlock body
  IWhile body -> [] <$ do
    compileWhile (head <$> compileBlock body)
  ICond p cons alt -> [] <$ do
    p' <- compileExpr p >>= (`asIntWidth` i1)
    compileIf p' (compileVoidBlock cons) (compileVoidBlock alt)
  IQueryParallelism f s -> do
    let IFunType cc _ _ = snd f
    let kernelFuncName = topLevelFunName $ fst f
    n <- (`asIntWidth` i64) =<< compileExpr s
    case cc of
      MCThreadLaunch -> do
        numThreads <- emitExternCall queryParallelismMCFun [n]
        return [i32Lit 1, numThreads]
        where queryParallelismMCFun = ExternFunSpec "dex_queryParallelismMC" i32 [] [] [i64]
      CUDAKernelLaunch -> do
        let ptxPtrFunTy = funTy (hostPtrTy i8) []
        let ptxPtrFun = callableOperand (hostPtrTy ptxPtrFunTy) kernelFuncName
        kernelPtr <- emitInstr (hostPtrTy i8) $ callInstr ptxPtrFunTy ptxPtrFun []
        numWorkgroupsPtr <- alloca 1 i32
        workgroupSizePtr <- alloca 1 i32
        emitVoidExternCall queryParallelismCUDAFun [kernelPtr, n, numWorkgroupsPtr, workgroupSizePtr]
        traverse (load i32) [numWorkgroupsPtr, workgroupSizePtr]
        where
          queryParallelismCUDAFun = ExternFunSpec "dex_queryParallelismCUDA" L.VoidType [] []
                                                  [hostPtrTy i8, i64, hostPtrTy i32, hostPtrTy i32]
      _                -> error $ "Unsupported calling convention: " ++ show cc
  ISyncWorkgroup -> do
    dev <- gets curDevice
    case dev of
      CPU -> error "Not yet implemented"
      GPU -> [] <$ emitVoidExternCall barrierSpec []
        where barrierSpec = ExternFunSpec "llvm.nvvm.barrier0" L.VoidType [] [] []
  ILaunch (fname, IFunType cc _ _) size args -> [] <$ do
    size' <- (`asIntWidth` i64) =<< compileExpr size
    args' <- mapM compileExpr args
    let kernelFuncName = topLevelFunName fname
    case cc of
      MCThreadLaunch -> do
        kernelParams <- packArgs args'
        let funPtr = L.ConstantOperand $ C.BitCast
                        (globalReference mcKernelPtrType kernelFuncName) hostVoidp
        emitVoidExternCall runMCKernel [funPtr, size',kernelParams]
      CUDAKernelLaunch -> do
        let ptxPtrFunTy = funTy (hostPtrTy i8) []
        let ptxPtrFun = callableOperand (hostPtrTy ptxPtrFunTy) kernelFuncName
        kernelPtr <- emitInstr (hostPtrTy i8) $ callInstr ptxPtrFunTy ptxPtrFun []
        kernelParams <- packArgs args'
        launchCUDAKernel kernelPtr size' kernelParams
      _ -> error $ "Not a valid calling convention for a launch: " ++ pprint cc
  IThrowError   -> do
    dev <- gets curDevice
    case dev of
      CPU -> [] <$ throwRuntimeError
      -- TODO: Implement proper error handling on GPUs.
      --       For now we generate an invalid memory access, hoping that the
      --       runtime will catch it.
      GPU -> [] <$ load i8 (L.ConstantOperand $ C.Null $ devicePtrTy i8)
  Alloc dev t s -> (:[]) <$> do
    numBytes <- mul (sizeof elemTy) =<< (`asIntWidth` i64) =<< compileExpr s
    case dev of
      CPU -> malloc elemTy numBytes
      GPU -> cuMemAlloc elemTy numBytes
    where elemTy = scalarTy t
  StackAlloc t s -> do
      p <- alloca (getIntLit l) elemTy
      return [p]
    where ILit l = s
          elemTy = scalarTy t
  Free ptr -> [] <$ do
    let PtrType (addr, _) = getIType ptr
    ptr' <- compileExpr ptr
    case addr of
      CPU -> free      ptr'
      GPU -> cuMemFree ptr'
  MemCopy dest src numel -> [] <$ do
    let PtrType (destDev, ty) = getIType dest
    let PtrType (srcDev , _ ) = getIType src
    dest' <- compileExpr dest >>= castVoidPtr
    src'  <- compileExpr src  >>= castVoidPtr
    numel' <- compileExpr numel >>= (`asIntWidth` i64)
    numBytes <- sizeof (scalarTy ty) `mul` numel'
    case (destDev, srcDev) of
      (CPU, GPU) -> cuMemcpyDToH numBytes src'  dest'
      (GPU, CPU) -> cuMemcpyHToD numBytes dest' src'
      (CPU, CPU) -> memcpy dest' src' numBytes
      (GPU, GPU) -> error "not implemented"
  InitializeZeros ptr numel -> [] <$ do
    let PtrType (_, ty) = getIType ptr
    ptr' <- compileExpr ptr >>= castVoidPtr
    numel' <- compileExpr numel >>= (`asIntWidth` i64)
    numBytes <- sizeof (scalarTy ty) `mul` numel'
    initializeZeros ptr' numBytes
  GetAllocSize ptr -> do
    let PtrType (_, ty) = getIType ptr
    ptr' <- compileExpr ptr
    numBytes <- getAllocSize ptr'
    numElem <- numBytes `sdiv` sizeof (scalarTy ty) >>= (`asIntWidth` idxRepTy)
    return [numElem]
  Store dest val -> [] <$ do
    dest' <- compileExpr dest
    val'  <- compileExpr val
    store dest' val'
    return Nothing
  -- We handle pointer operations explicitly, because we need type information that
  -- might get erased by compileExpr.
  IPtrLoad ptr ->
    (:[]) <$> (load (pointeeType $ getIType ptr) =<< compileExpr ptr)
  IPtrOffset ptr off ->
    (:[]) <$> bindM2 (gep (pointeeType $ getIType ptr)) (compileExpr ptr) (compileExpr off)
  IBinOp op x' y' -> do
    x <- compileExpr x'
    y <- compileExpr y'
    (:[]) <$> compileBinOp op x y
  IUnOp  op x -> (:[]) <$> (compileUnOp  op =<< compileExpr x)
  ISelect  p' x' y' -> (:[]) <$> do
    x <- compileExpr x'
    y <- compileExpr y'
    p <- compileExpr p'
    pb <- p `asIntWidth` i1
    emitInstr (typeOf x) $ L.Select pb x y []
  IOutputStream -> (:[]) <$> getOutputStream
  IVectorBroadcast v vty -> do
    v' <- compileExpr v
    let vty'@(L.VectorType vlen _) = scalarTy vty
    tmp <- emitInstr vty' $ L.InsertElement (L.ConstantOperand $ C.Undef vty') v' (L.ConstantOperand $ C.Int 32 0) []
    ans <- emitInstr vty' $ L.ShuffleVector tmp (L.ConstantOperand $ C.Undef vty') (replicate (fromIntegral vlen) 0) []
    return [ans]
  IVectorIota vty -> case vty of
    Vector [n] sbt -> do
      let raiseConstant c = case sbt of
            Float32Type -> C.Float $ L.Single $ fromIntegral c
            Float64Type -> C.Float $ L.Double $ fromIntegral c
            _ | isIntegral sbt -> C.Int (fromIntegral $ sizeOf (Scalar sbt) * 8) $ fromIntegral c
            _ -> error "Unrecognized scalar base type"
      return [L.ConstantOperand $ C.Vector $ raiseConstant <$> [0..(n-1)]]
    _ -> error "Expected a 1D vector type"
  ICastOp idt ix -> (:[]) <$> do
    x <- compileExpr ix
    let (xt, dt) = (typeOf x, scalarTy idt)
    -- Choose instructions based on the scalar type of vectors
    let sidt = case idt of Vector [_] sbt -> Scalar sbt; _ -> idt
    let sxt = case xt of L.VectorType _ sbt -> sbt; _ -> xt
    let sdt = case dt of L.VectorType _ sbt -> sbt; _ -> dt
    case (sxt, sidt) of
      -- if upcasting to unsigned int, use zext instruction
      (L.IntegerType bits, Scalar Word64Type) | bits < 64 -> x `zeroExtendTo` dt
      (L.IntegerType bits, Scalar Word32Type) | bits < 32 -> x `zeroExtendTo` dt
      _ -> case (getIType ix, sdt) of
        -- if upcasting from unsigned int, use zext instruction
        (Scalar Word32Type, L.IntegerType bits) | bits > 32 -> x `zeroExtendTo` dt
        (Scalar Word8Type,  L.IntegerType bits) | bits > 8  -> x `zeroExtendTo` dt
        _ -> case (sxt, sdt) of
         (L.IntegerType _, L.IntegerType _) -> x `asIntWidth` dt
         (L.FloatingPointType fpt, L.FloatingPointType fpt') -> case compare fpt fpt' of
           LT -> emitInstr dt $ L.FPExt x dt []
           EQ -> return x
           GT -> emitInstr dt $ L.FPTrunc x dt []
         (L.FloatingPointType _, L.IntegerType _) -> emitInstr dt $ float_to_int x dt []
         (L.IntegerType _, L.FloatingPointType _) -> emitInstr dt $ int_to_float x dt []
#if MIN_VERSION_llvm_hs(15,0,0)
         -- Pointee casts become no-ops, because LLVM uses opaque pointers
         (L.PointerType a , L.PointerType a') | a == a' -> return x
         (L.IntegerType 64, ptrTy@(L.PointerType _)) -> emitInstr ptrTy $ L.IntToPtr x ptrTy []
         (L.PointerType _ , L.IntegerType 64) -> emitInstr i64 $ L.PtrToInt x i64 []
#else
         (L.PointerType _ _, L.PointerType eltTy _) -> castLPtr eltTy x
         (L.IntegerType 64 , ptrTy@(L.PointerType _ _)) ->
           emitInstr ptrTy $ L.IntToPtr x ptrTy []
         (L.PointerType _ _, L.IntegerType 64) -> emitInstr i64 $ L.PtrToInt x i64 []
#endif
         _ -> error $ "Unsupported cast"
         where signed ty = case ty of
                 Scalar Int64Type -> True
                 Scalar Int32Type -> True
                 Scalar Word8Type -> False
                 Scalar Word32Type -> False
                 Scalar Word64Type -> False
                 Scalar Float64Type -> True
                 Scalar Float32Type -> True
                 Vector _ ty' -> signed (Scalar ty')
                 PtrType _ -> False
               int_to_float = if signed (getIType ix) then L.SIToFP else L.UIToFP
               float_to_int = if signed idt then L.FPToSI else L.FPToUI
  IBitcastOp idt ix -> (:[]) <$> do
    x <- compileExpr ix
    let dt = scalarTy idt
    emitInstr dt $ L.BitCast x dt []
  ICall f args -> do
    args' <- mapM compileExpr args
    lookupSubstM f >>= \case
      FunctionSubstVal f' lTy (IFunType cc _ _) -> do
        case cc of
          StandardCC -> return ()
          _ -> error $ "Unsupported calling convention: " ++ show cc
        exitCode <- emitCallInstr lTy f' args' >>= (`asIntWidth` i1)
        compileIf exitCode throwRuntimeError (return ())
        return []
      RenameOperandSubstVal v -> do
        lookupTopFun v >>= \case
          DexTopFun _ _ _ _ -> error "Imp functions should be abstracted at this point"
          FFITopFun fname ty@(IFunType cc _ impResultTys) -> do
            let resultTys = map scalarTy impResultTys
            case cc of
              FFICC -> do
                ans <- emitExternCall (makeFunSpec fname ty) args'
                return [ans]
              FFIMultiResultCC -> do
                resultPtr <- makeMultiResultAlloc resultTys
                emitVoidExternCall (makeFunSpec fname ty) (resultPtr : args')
                loadMultiResultAlloc resultTys resultPtr
              _ -> error $ "Unsupported calling convention: " ++ show cc
  DebugPrint fmtStr x -> [] <$ do
    x' <- compileExpr x
    debugPrintf fmtStr x'
  IShowScalar resultPtr x -> (:[]) <$> do
    resultPtr' <- compileExpr resultPtr
    x'         <- compileExpr x
    ~(Scalar b) <- return $ getIType x
    let fname = getShowScalarFunStrName b
    let spec = ExternFunSpec (L.mkName fname) i32 [] [] [hostVoidp, typeOf x']
    emitExternCall spec [resultPtr', x']
    where
      getShowScalarFunStrName :: ScalarBaseType -> String
      getShowScalarFunStrName = \case
        Float32Type -> "showFloat32_internal"
        Float64Type -> "showFloat64_internal"
        Word8Type   -> "showWord8_internal"
        Word32Type  -> "showWord32_internal"
        Word64Type  -> "showWord64_internal"
        Int32Type   -> "showInt32_internal"
        Int64Type   -> "showInt64_internal"

-- TODO: use a careful naming discipline rather than strings
-- (this is only used on the CUDA path which is currently broken anyway)
topLevelFunName :: SourceName -> L.Name
topLevelFunName name = fromString name

makeFunSpec :: SourceName -> IFunType -> ExternFunSpec
makeFunSpec name impFunTy =
  ExternFunSpec (L.Name (fromString name)) retTy [] [] argTys
  where (retTy, argTys) = impFunTyToLLVMTy impFunTy

impFunTyToLLVMTy :: IFunType -> LLVMFunType
impFunTyToLLVMTy (IFunType FFICC argTys [resultTy]) =
  (scalarTy resultTy, map scalarTy argTys)
impFunTyToLLVMTy (IFunType FFIMultiResultCC argTys _) =
  (L.VoidType, hostPtrTy hostVoidp : map scalarTy argTys)
impFunTyToLLVMTy (IFunType StandardCC argTys _) =
  (i64, map scalarTy argTys)
impFunTyToLLVMTy (IFunType _ _ _) = error "not implemented"

compileLoop :: Compiler m => Direction -> IBinder i i' -> Operand -> m i' o () -> m i o ()
compileLoop d iBinder n compileBody = do
  let loopName = "loop_" ++ (fromString $ pprint $ binderName iBinder)
  loopBlock <- freshName $ getNameHint $ loopName
  nextBlock <- freshName $ getNameHint $ "cont_" ++ loopName
  i <- alloca 1 $ scalarTy $ iBinderType iBinder
  i0 <- case d of Fwd -> return $ (0 `withWidthOf` n)
                  Rev -> n `sub` (1 `withWidthOf` n)
  store i i0
  entryCond <- (0 `withWidthOf` n) `ilt` n
  finishBlock (L.CondBr entryCond loopBlock nextBlock []) loopBlock
  iVal <- load (scalarTy $ iBinderType iBinder) i
  extendSubst (iBinder @> opSubstVal iVal) $ compileBody
  iValNew <- case d of Fwd -> add iVal (1 `withWidthOf` iVal)
                       Rev -> sub iVal (1 `withWidthOf` iVal)
  store i iValNew
  loopCond <- case d of Fwd -> iValNew `ilt` n
                        Rev -> iValNew `ige` (0 `withWidthOf` iValNew)
  finishBlock (L.CondBr loopCond loopBlock nextBlock []) nextBlock

compileIf :: LLVMBuilder m => Operand -> m () -> m () -> m ()
compileIf cond tb fb = do
  tbName   <- freshName $ getNameHint @String "if_t"
  fbName   <- freshName $ getNameHint @String "if_f"
  contName <- freshName $ getNameHint @String "if_c"
  finishBlock (L.CondBr cond tbName fbName []) tbName
  tb
  finishBlock (L.Br contName []) fbName
  fb
  finishBlock (L.Br contName []) contName

compileWhile :: LLVMBuilder m => m Operand -> m ()
compileWhile compileBody = do
  loopBlock <- freshName $ getNameHint @String "loop"
  nextBlock <- freshName $ getNameHint @String "cont"
  entryCond <- compileBody >>= (`asIntWidth` i1)
  finishBlock (L.CondBr entryCond loopBlock nextBlock []) loopBlock
  loopCond <- compileBody >>= (`asIntWidth` i1)
  finishBlock (L.CondBr loopCond loopBlock nextBlock []) nextBlock

throwRuntimeError :: LLVMBuilder m => m ()
throwRuntimeError = do
  deadBlock <- freshName $ getNameHint @String "dead"
  finishBlock (L.Ret (Just $ i64Lit 1) []) deadBlock

compileUnOp :: LLVMBuilder m => UnOp -> Operand -> m Operand
compileUnOp op x = case op of
  -- LLVM has "fneg" but it doesn't seem to be exposed by llvm-hs-pure
  FNeg            -> emitInstr (typeOf x) $ L.FSub mathFlags (0.0 `withWidthOfFP` x) x []
  BNot            -> emitInstr boolTy $ L.Xor x (i8Lit 1) []
  _               -> unaryIntrinsic op x

compileBinOp :: LLVMBuilder m => BinOp -> Operand -> Operand -> m Operand
compileBinOp op x y = case op of
  IAdd   -> emitInstr (typeOf x) $ L.Add False False x y []
  ISub   -> emitInstr (typeOf x) $ L.Sub False False x y []
  IMul   -> emitInstr (typeOf x) $ L.Mul False False x y []
  IDiv   -> emitInstr (typeOf x) $ L.SDiv False x y []
  IRem   -> emitInstr (typeOf x) $ L.SRem x y []
  FPow   -> binaryIntrinsic FPow x y
  FAdd   -> emitInstr (typeOf x) $ L.FAdd mathFlags x y []
  FSub   -> emitInstr (typeOf x) $ L.FSub mathFlags x y []
  FMul   -> emitInstr (typeOf x) $ L.FMul mathFlags x y []
  FDiv   -> emitInstr (typeOf x) $ L.FDiv mathFlags x y []
  BAnd   -> emitInstr (typeOf x) $ L.And x y []
  BOr    -> emitInstr (typeOf x) $ L.Or  x y []
  BXor   -> emitInstr (typeOf x) $ L.Xor x y []
  BShL   -> emitInstr (typeOf x) $ L.Shl  False False x y []
  BShR   -> emitInstr (typeOf x) $ L.LShr False       x y []
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

-- === MDImp to LLVM CUDA ===

ensureHasCUDAContext :: LLVMBuilder m => m ()
ensureHasCUDAContext = emitVoidExternCall spec []
  where spec = ExternFunSpec "dex_ensure_has_cuda_context" L.VoidType [] [] []

launchCUDAKernel :: LLVMBuilder m => Operand -> Operand -> Operand -> m ()
launchCUDAKernel ptx size args = emitVoidExternCall spec [ptx, size, args]
  where spec = ExternFunSpec "dex_cuLaunchKernel" L.VoidType [] []
                 [hostVoidp, i64, hostPtrTy $ hostVoidp]

cuMemcpyDToH :: LLVMBuilder m => Operand -> Operand -> Operand -> m ()
cuMemcpyDToH bytes devPtr hostPtr = emitVoidExternCall spec [bytes, devPtr, hostPtr]
  where spec = ExternFunSpec "dex_cuMemcpyDtoH" L.VoidType [] [] [i64, deviceVoidp, hostVoidp]

cuMemcpyHToD :: LLVMBuilder m => Operand -> Operand -> Operand -> m ()
cuMemcpyHToD bytes devPtr hostPtr = emitVoidExternCall spec [bytes, devPtr, hostPtr]
  where spec = ExternFunSpec "dex_cuMemcpyHtoD" L.VoidType [] [] [i64, deviceVoidp, hostVoidp]

cuMemAlloc :: LLVMBuilder m => L.Type -> Operand -> m Operand
cuMemAlloc ty bytes = castLPtr ty =<< emitExternCall spec [bytes]
  where spec = ExternFunSpec "dex_cuMemAlloc" deviceVoidp [] [] [i64]

cuMemFree :: LLVMBuilder m => Operand -> m ()
cuMemFree ptr = do
  voidptr <- castVoidPtr ptr
  emitVoidExternCall spec [voidptr]
  where spec = ExternFunSpec "dex_cuMemFree" L.VoidType [] [] [deviceVoidp]

-- === GPU Kernel compilation ===
-- Useful docs:
-- * NVVM IR specification: https://docs.nvidia.com/cuda/nvvm-ir-spec/index.html
-- * PTX docs: https://docs.nvidia.com/cuda/ptx-writers-guide-to-interoperability/index.html

impKernelToLLVMGPU :: EnvReader m => OperandEnv i o -> ImpFunction i -> m o (LLVMKernel)
impKernelToLLVMGPU env (ImpFunction _ (Abs args body)) = do
  let numThreadInfoArgs = 4  -- [threadIdParam, nThreadParam, argArrayParam]
  let argTypes = drop numThreadInfoArgs $ nestToList (scalarTy . iBinderType) args
  let kernelMeta = L.MetadataNodeDefinition kernelMetaId $ L.MDTuple
                     [ Just $ L.MDValue $ L.ConstantOperand $ globalReference
                         (hostPtrTy $ funTy L.VoidType argTypes) "kernel"
                     , Just $ L.MDString "kernel"
                     , Just $ L.MDValue $ L.ConstantOperand $ C.Int 32 1
                     ]
  liftCompile GPU env $ do
    (argParams, argOperands) <- unzip <$> mapM (freshParamOpPair ptrParamAttrs) argTypes
    tidx <- threadIdxX >>= (`asIntWidth` idxRepTy)
    bidx <- blockIdxX  >>= (`asIntWidth` idxRepTy)
    bsz  <- blockDimX  >>= (`asIntWidth` idxRepTy)
    gsz  <- gridDimX   >>= (`asIntWidth` idxRepTy)
    nthr <- mul bsz gsz
    let subst = args @@> map opSubstVal ([tidx, bidx, bsz, nthr] ++ argOperands)
    void $ extendSubst subst $ compileBlock body
    kernel <- makeFunction "kernel" argParams Nothing
    LLVMKernel <$> makeModuleEx ptxDataLayout ptxTargetTriple
                     [L.GlobalDefinition kernel, kernelMeta, nvvmAnnotations]
  where
    ptrParamAttrs = [L.NoAlias, L.NoCapture, L.NonNull, L.Alignment 256]
    kernelMetaId = L.MetadataNodeID 0
    nvvmAnnotations = L.NamedMetadataDefinition "nvvm.annotations" [kernelMetaId]

threadIdxX :: LLVMBuilder m => m Operand
threadIdxX = emitExternCall spec []
  where spec = ptxSpecialReg "llvm.nvvm.read.ptx.sreg.tid.x"

blockIdxX :: LLVMBuilder m => m Operand
blockIdxX = emitExternCall spec []
  where spec = ptxSpecialReg "llvm.nvvm.read.ptx.sreg.ctaid.x"

blockDimX :: LLVMBuilder m => m Operand
blockDimX = emitExternCall spec []
  where spec = ptxSpecialReg "llvm.nvvm.read.ptx.sreg.ntid.x"

gridDimX :: LLVMBuilder m => m Operand
gridDimX = emitExternCall spec []
  where spec = ptxSpecialReg "llvm.nvvm.read.ptx.sreg.nctaid.x"

ptxSpecialReg :: L.Name -> ExternFunSpec
ptxSpecialReg name = ExternFunSpec name i32 [] attrs []
  where
#if MIN_VERSION_llvm_hs(16,0,0)
    attrs = [FA.Memory FA.readNone, FA.NoUnwind]
#else
    attrs = [FA.ReadNone, FA.NoUnwind]
#endif

gpuUnaryIntrinsic :: LLVMBuilder m => UnOp -> Operand -> m Operand
gpuUnaryIntrinsic op x = case typeOf x of
  L.FloatingPointType L.DoubleFP -> dispatchOp fp64 ""
  L.FloatingPointType L.FloatFP  -> dispatchOp fp32 "f"
  _ -> error $ "Unsupported GPU floating point type: " ++ show (typeOf x)
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
      Erf    -> callFloatIntrinsic ty $ "__nv_erf"    ++ suffix
      Erfc   -> callFloatIntrinsic ty $ "__nv_erfc"   ++ suffix
      _   -> error $ "Unsupported GPU operation: " ++ show op
    floatIntrinsic ty name = ExternFunSpec (L.mkName name) ty [] [] [ty]
    callFloatIntrinsic ty name = emitExternCall (floatIntrinsic ty name) [x]

gpuBinaryIntrinsic :: LLVMBuilder m => BinOp -> Operand -> Operand -> m Operand
gpuBinaryIntrinsic op x y = case typeOf x of
  L.FloatingPointType L.DoubleFP -> dispatchOp fp64 ""
  L.FloatingPointType L.FloatFP  -> dispatchOp fp32 "f"
  _ -> error $ "Unsupported GPU floating point type: " ++ show (typeOf x)
  where
    dispatchOp ty suffix = case op of
      FPow -> callFloatIntrinsic ty $ "__nv_pow" ++ suffix
      _    -> error $ "Unsupported GPU operation: " ++ show op
    floatIntrinsic ty name = ExternFunSpec (L.mkName name) ty [] [] [ty, ty]
    callFloatIntrinsic ty name = emitExternCall (floatIntrinsic ty name) [x, y]

_gpuDebugPrint :: LLVMBuilder m => Operand -> m ()
_gpuDebugPrint i32Val = do
  let chars = map (C.Int 8) $ map (fromIntegral . fromEnum) "%d\n" ++ [0]
  let formatStrArr = L.ConstantOperand $ C.Array i8 chars
  formatStrPtr <- alloca (length chars) i8
  castLPtr (typeOf formatStrArr) formatStrPtr >>= (`store` formatStrArr)
  valPtr <- alloca 1 i32
  store valPtr i32Val
  valPtri8 <- castLPtr i8 valPtr
  void $ emitExternCall vprintfSpec [formatStrPtr, valPtri8]
  where
    genericPtrTy ty = pointerType ty $ L.AddrSpace 0
    vprintfSpec = ExternFunSpec "vprintf" i32 [] [] [genericPtrTy i8, genericPtrTy i8]

-- Takes a single int64 payload. TODO: implement a varargs version
debugPrintf :: LLVMBuilder m => String -> Operand -> m ()
debugPrintf fmtStr x = do
  let chars = map (C.Int 8) $ map (fromIntegral . fromEnum) fmtStr ++ [0]
  let formatStrArr = L.ConstantOperand $ C.Array i8 chars
  formatStrPtr <- alloca (length chars) i8
  castLPtr (typeOf formatStrArr) formatStrPtr >>= (`store` formatStrArr)
  void $ emitExternCall printfSpec [formatStrPtr, x]
  where printfSpec = ExternFunSpec "printf" i32 [] [] [hostVoidp, i64]

_debugPrintfPtr :: LLVMBuilder m => String -> Operand -> m ()
_debugPrintfPtr s x = do
  x' <- emitInstr i64 $ L.PtrToInt x i64 []
  debugPrintf s x'

compileBlock :: Compiler m => ImpBlock i -> m i o [Operand]
compileBlock (ImpBlock Empty result) = traverse compileExpr result
compileBlock (ImpBlock (Nest decl rest) result) = do
  env <- compileDecl decl
  extendSubst env $ compileBlock (ImpBlock rest result)

compileDecl :: Compiler m => ImpDecl i i' -> m i o (OperandEnvFrag i i' o)
compileDecl (ImpLet bs instr) = do
  results <- compileInstr instr
  if length results == nestLength bs
    then return $ bs @@> map opSubstVal results
    else error "Unexpected number of results"

compileVoidBlock :: Compiler m => ImpBlock i -> m i o ()
compileVoidBlock = void . compileBlock

compileExpr :: Compiler m => IExpr i -> m i o Operand
compileExpr expr = case expr of
  ILit v   -> return (litVal v)
  IPtrVar v _ -> lookupSubstM v <&> \case
    PtrSubstVal x -> x
    RenameOperandSubstVal _ -> error "Shouldn't have any ptr literals left"
  IVar v _ -> lookupSubstM v <&> \case
    OperandSubstVal x -> x
    RenameOperandSubstVal _ -> error "Shouldn't have any imp vars left"

packArgs :: LLVMBuilder m => [Operand] -> m Operand
packArgs elems = do
  arr <- alloca (length elems) hostVoidp
  forM_ (zip [0..] elems) \(i, e) -> do
    eptr <- alloca 1 $ typeOf e
    store eptr e
    earr <- gep hostVoidp arr $ i32Lit i
    store earr =<< castVoidPtr eptr
  return arr

unpackArgs :: LLVMBuilder m => Operand -> [L.Type] -> m [Operand]
unpackArgs argArrayPtr types =
  forM (zip [0..] types) \(i, ty) -> do
    argVoidPtr <- gep hostVoidp argArrayPtr $ i64Lit i
    argPtr <- castLPtr (hostPtrTy ty) argVoidPtr
    load ty =<< load (hostPtrTy ty) argPtr

makeMultiResultAlloc :: LLVMBuilder m => [L.Type] -> m Operand
makeMultiResultAlloc tys = do
  resultsPtr <- alloca (length tys) hostVoidp
  forM_ (zip [0..] tys) \(i, ty) -> do
    ptr <- alloca 1 ty >>= castVoidPtr
    resultsPtrOffset <- gep hostVoidp resultsPtr $ i32Lit i
    store resultsPtrOffset ptr
  return resultsPtr

loadMultiResultAlloc :: LLVMBuilder m => [L.Type] -> Operand -> m [Operand]
loadMultiResultAlloc tys ptr =
  forM (zip [0..] tys) \(i, ty) ->
    gep hostVoidp ptr (i32Lit i) >>= load hostVoidp >>= castLPtr ty >>= load ty

runMCKernel :: ExternFunSpec
runMCKernel = ExternFunSpec "dex_launchKernelMC" L.VoidType [] [] [hostVoidp, i64, hostPtrTy hostVoidp]

mcKernelPtrType :: L.Type
mcKernelPtrType = hostPtrTy $ L.FunctionType L.VoidType [i32, i32, hostPtrTy $ hostVoidp] False

-- === LLVM embedding ===

litVal :: LitVal -> Operand
litVal lit = case lit of
  Int64Lit x   -> i64Lit $ fromIntegral x
  Int32Lit x   -> i32Lit $ fromIntegral x
  Word8Lit x   -> i8Lit  $ fromIntegral x
  Word32Lit x  -> i32Lit  $ fromIntegral x
  Word64Lit x  -> i64Lit  $ fromIntegral x
  Float64Lit x -> L.ConstantOperand $ C.Float $ L.Double x
  Float32Lit x -> L.ConstantOperand $ C.Float $ L.Single x
  PtrLit (_, baseTy) NullPtr -> L.ConstantOperand $ C.Null $ hostPtrTy $ scalarTy baseTy
  PtrLit _ _ -> error "Shouldn't be compiling pointer non-null literals"

-- TODO: Assert that the integer can be represented in that number of bits!
withWidth :: Int -> Word32 -> Operand
withWidth x bits = L.ConstantOperand $ C.Int bits $ fromIntegral x

idxRepTy :: L.Type
idxRepTy = scalarTy $ IIdxRepTy

i64Lit :: Int -> Operand
i64Lit x = x `withWidth` 64

i32Lit :: Int -> Operand
i32Lit x = x `withWidth` 32

i8Lit :: Int -> Operand
i8Lit x = x `withWidth` 8

i1Lit :: Int -> Operand
i1Lit x = x `withWidth` 1

withWidthOf :: Int -> Operand -> Operand
withWidthOf x template = case typeOf template of
  L.IntegerType bits -> x `withWidth` (fromIntegral bits)
  _ -> error $ "Expected an integer: " ++ show template

withWidthOfFP :: Double -> Operand -> Operand
withWidthOfFP x template = case typeOf template of
  L.FloatingPointType L.DoubleFP -> litVal $ Float64Lit x
  L.FloatingPointType L.FloatFP  -> litVal $ Float32Lit $ realToFrac x
  _ -> error $ "Unsupported floating point type: " ++ show (typeOf template)

store :: LLVMBuilder m => Operand -> Operand -> m ()
store ptr x =  addInstr $ L.Do $ L.Store False ptr x Nothing 0 []

load :: LLVMBuilder m => L.Type -> Operand -> m Operand
load pointeeTy ptr =
#if MIN_VERSION_llvm_hs(15,0,0)
  emitInstr pointeeTy $ L.Load False pointeeTy ptr Nothing 0 []
#else
  emitInstr pointeeTy $ L.Load False ptr Nothing 0 []
#endif

ilt :: LLVMBuilder m => Operand -> Operand -> m Operand
ilt x y = emitInstr i1 $ L.ICmp IP.SLT x y []

ige :: LLVMBuilder m => Operand -> Operand -> m Operand
ige x y = emitInstr i1 $ L.ICmp IP.SGE x y []

add :: LLVMBuilder m => Operand -> Operand -> m Operand
add x y = emitInstr (typeOf x) $ L.Add False False x y []

sub :: LLVMBuilder m => Operand -> Operand -> m Operand
sub x y = emitInstr (typeOf x) $ L.Sub False False x y []

mul :: LLVMBuilder m => Operand -> Operand -> m Operand
mul x y = emitInstr (typeOf x) $ L.Mul False False x y []

sdiv :: LLVMBuilder m => Operand -> Operand -> m Operand
sdiv x y = emitInstr (typeOf x) $ L.SDiv False x y []

gep :: LLVMBuilder m => L.Type -> Operand -> Operand -> m Operand
#if MIN_VERSION_llvm_hs(15,0,0)
gep pointeeTy ptr i =
  emitInstr (typeOf ptr) $ L.GetElementPtr False pointeeTy ptr [i] []
#else
gep _ ptr i =
  emitInstr (typeOf ptr) $ L.GetElementPtr False ptr [i] []
#endif

sizeof :: L.Type -> Operand
sizeof t = L.ConstantOperand $ C.sizeof 64 t

alloca :: LLVMBuilder m => Int -> L.Type -> m Operand
alloca elems ty = do
  v <- freshName noHint
  modify $ setScalarDecls ((v L.:= instr):)
  return $ L.LocalReference (hostPtrTy ty) v
  where instr = L.Alloca ty (Just $ i32Lit elems) 0 []

malloc :: LLVMBuilder m => L.Type -> Operand -> m Operand
malloc ty bytes = do
  bytes64 <- asIntWidth bytes i64
  ptr <- emitExternCall mallocFun [bytes64]
  castLPtr ty ptr

getAllocSize :: LLVMBuilder m => Operand ->  m Operand
getAllocSize ptr = do
  ptr' <- castLPtr i8 ptr
  emitExternCall allocSizeFun [ptr']

memcpy :: LLVMBuilder m => Operand -> Operand -> Operand -> m ()
memcpy dest src numBytes = emitVoidExternCall memcpyFun [dest, src, numBytes, i1Lit 0]

initializeZeros :: LLVMBuilder m => Operand -> Operand -> m ()
initializeZeros ptr numBytes = emitVoidExternCall memsetFun [ptr, i8Lit 0, numBytes, i1Lit 0]

free :: LLVMBuilder m => Operand -> m ()
free ptr = do
 ptr' <- castLPtr i8 ptr
 emitVoidExternCall freeFun [ptr']

castLPtr :: LLVMBuilder m => L.Type -> Operand -> m Operand
#if MIN_VERSION_llvm_hs(15,0,0)
castLPtr _ = return
#else
castLPtr ty ptr = emitInstr newPtrTy $ L.BitCast ptr newPtrTy []
  where
    L.PointerType _ addr = typeOf ptr
    newPtrTy = L.PointerType ty addr
#endif

castVoidPtr :: LLVMBuilder m => Operand -> m Operand
castVoidPtr = castLPtr i8

zeroExtendTo :: LLVMBuilder m => Operand -> L.Type -> m Operand
zeroExtendTo x t = emitInstr t $ L.ZExt x t []

callInstr :: L.Type -> L.CallableOperand -> [L.Operand] -> L.Instruction
#if MIN_VERSION_llvm_hs(15,0,0)
callInstr fty fun xs = L.Call Nothing L.C [] fty fun xs' [] []
#else
callInstr _ fun xs = L.Call Nothing L.C [] fun xs' [] []
#endif
 where xs' = [(x ,[]) | x <- xs]

type LLVMFunType = (L.Type, [L.Type])

emitCallInstr ::LLVMBuilder m => LLVMFunType -> L.Operand -> [L.Operand] -> m Operand
emitCallInstr (retTy, argTys) f xs = emitInstr retTy $ callInstr fTy' (Right f) xs
  where fTy' = funTy retTy argTys

_emitVoidCallInstr ::LLVMBuilder m => LLVMFunType -> L.Operand -> [L.Operand] -> m ()
_emitVoidCallInstr (retTy, argTys) f xs =
  addInstr $ L.Do $ callInstr fTy' (Right f) xs
  where fTy' = funTy retTy argTys

externCall :: ExternFunSpec -> [L.Operand] -> L.Instruction
externCall (ExternFunSpec fname retTy _ _ argTys) xs = callInstr ft fun xs
  where
    ft = funTy retTy argTys
    fun = callableOperand (hostPtrTy ft) fname

emitExternCall :: LLVMBuilder m => ExternFunSpec -> [L.Operand] -> m Operand
emitExternCall f@(ExternFunSpec _ retTy _ _ _) xs = do
  modify $ setFunSpecs (S.insert f)
  emitInstr retTy $ externCall f xs

emitVoidExternCall :: LLVMBuilder m => ExternFunSpec -> [L.Operand] -> m ()
emitVoidExternCall f xs = do
  modify $ setFunSpecs (S.insert f)
  addInstr $ L.Do $ externCall f xs

scalarTy :: HasCallStack => BaseType -> L.Type
scalarTy b = case b of
  Scalar sb -> case sb of
    Int64Type   -> i64
    Int32Type   -> i32
    Word8Type   -> i8
    Word32Type  -> i32
    Word64Type  -> i64
    Float64Type -> fp64
    Float32Type -> fp32
  Vector [n] sb -> L.VectorType n $ scalarTy $ Scalar sb
  Vector _   _  -> error "Expected a 1D vector type"
  PtrType (s, t) -> pointerType (scalarTy t) (lAddress s)

pointeeType :: BaseType -> L.Type
pointeeType b = case b of
  PtrType (_, t) -> scalarTy t
  _ -> error "Not a pointer type!"

hostPtrTy :: L.Type -> L.Type
hostPtrTy ty = pointerType ty $ L.AddrSpace 0

devicePtrTy :: L.Type -> L.Type
devicePtrTy ty = pointerType ty $ L.AddrSpace 1

lAddress :: HasCallStack => AddressSpace -> L.AddrSpace
lAddress s = case s of
  CPU -> L.AddrSpace 0
  GPU -> L.AddrSpace 1

callableOperand :: L.Type -> L.Name -> L.CallableOperand
callableOperand ty name = Right $ L.ConstantOperand $ globalReference ty name

asIntWidth :: LLVMBuilder m => Operand -> L.Type -> m Operand
asIntWidth op expTy@(L.IntegerType expWidth) = case compare expWidth opWidth of
  LT -> emitInstr expTy $ L.Trunc op expTy []
  EQ -> return op
  GT -> emitInstr expTy $ L.SExt  op expTy []
  where ~(L.IntegerType opWidth) = typeOf op
asIntWidth op ~expTy@(L.VectorType _ (L.IntegerType expWidth)) = case compare expWidth opWidth of
  LT -> emitInstr expTy $ L.Trunc op expTy []
  EQ -> return op
  GT -> emitInstr expTy $ L.SExt  op expTy []
  where ~(L.VectorType _ (L.IntegerType opWidth)) = typeOf op

freshParamOpPair :: LLVMBuilder m => [L.ParameterAttribute] -> L.Type -> m (Parameter, Operand)
freshParamOpPair ptrAttrs ty = do
  v <- freshName noHint
  let attrs = case ty of
#if MIN_VERSION_llvm_hs(15,0,0)
                L.PointerType _ -> ptrAttrs
#else
                L.PointerType _ _ -> ptrAttrs
#endif
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

cpuUnaryIntrinsic :: LLVMBuilder m => UnOp -> Operand -> m Operand
cpuUnaryIntrinsic op x = case typeOf x of
  L.FloatingPointType L.DoubleFP -> dispatchOp fp64 ".f64" ""
  L.FloatingPointType L.FloatFP  -> dispatchOp fp32 ".f32" "f"
  ty@(L.VectorType n (L.FloatingPointType L.DoubleFP)) ->
    let suffix = ".v" ++ show n ++ "f64"
    in dispatchOp ty suffix ""
  ty@(L.VectorType n (L.FloatingPointType L.FloatFP)) ->
    let suffix = ".v" ++ show n ++ "f32"
    in dispatchOp ty suffix ""
  _ -> error $ "Unsupported CPU floating point type: " ++ show (typeOf x)
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
      Erf             -> callFloatIntrinsic ty $ "erf"        ++ libmSuffix
      Erfc            -> callFloatIntrinsic ty $ "erfc"       ++ libmSuffix
      _ -> error $ "Unsupported CPU operation: " ++ show op
    floatIntrinsic ty name = ExternFunSpec (L.mkName name) ty [] [] [ty]
    callFloatIntrinsic ty name = emitExternCall (floatIntrinsic ty name) [x]

cpuBinaryIntrinsic :: LLVMBuilder m => BinOp -> Operand -> Operand -> m Operand
cpuBinaryIntrinsic op x y = case typeOf x of
  L.FloatingPointType L.DoubleFP -> dispatchOp fp64 ".f64"
  L.FloatingPointType L.FloatFP  -> dispatchOp fp32 ".f32"
  ty@(L.VectorType n (L.FloatingPointType L.DoubleFP)) ->
    let suffix = ".v" ++ show n ++ "f64"
    in dispatchOp ty suffix
  ty@(L.VectorType n (L.FloatingPointType L.FloatFP)) ->
    let suffix = ".v" ++ show n ++ "f32"
    in dispatchOp ty suffix
  _ -> error $ "Unsupported CPU floating point type: " ++ show (typeOf x)
  where
    dispatchOp ty llvmSuffix = case op of
      FPow -> callFloatIntrinsic ty $ "llvm.pow" ++ llvmSuffix
      _ -> error $ "Unsupported CPU operation: " ++ show op
    floatIntrinsic ty name = ExternFunSpec (L.mkName name) ty [] [] [ty, ty]
    callFloatIntrinsic ty name = emitExternCall (floatIntrinsic ty name) [x, y]

globalReference :: L.Type -> L.Name -> C.Constant
#if MIN_VERSION_llvm_hs(15,0,0)
globalReference = const C.GlobalReference
#else
globalReference = C.GlobalReference
#endif

pointerType :: L.Type -> L.AddrSpace -> L.Type
#if MIN_VERSION_llvm_hs(15,0,0)
pointerType = const L.PointerType
#else
pointerType = L.PointerType
#endif

-- === Output stream ===

getOutputStream :: LLVMBuilder m => m Operand
getOutputStream = getDyvar OutStreamDyvar

initializeOutputStream :: LLVMBuilder m => Operand -> m ()
initializeOutputStream streamFD = do
  streamPtr <- emitExternCall fdopenFun [streamFD]
  setDyvar OutStreamDyvar streamPtr

-- === Dynamically-scoped vars via thread-local pthreads vars ===

dyvarDefs :: [L.Definition]
dyvarDefs  = map makeDef [minBound..maxBound]
  where
    makeDef :: DynamicVar -> L.Definition
    makeDef v =  L.GlobalDefinition $ L.globalVariableDefaults
      { L.name = dynamicVarLName v
      , L.type' = pthreadKeyTy
      , L.linkage = L.External
      , L.initializer = Nothing }

dynamicVarLName :: DynamicVar -> L.Name
dynamicVarLName v = fromString $ dynamicVarCName v

setDyvar :: LLVMBuilder m => DynamicVar -> Operand -> m ()
setDyvar v val = do
  key <- getDyvarKey v
  void $ emitExternCall pthread_setspecific [key, val]

getDyvar :: LLVMBuilder m => DynamicVar -> m Operand
getDyvar v = do
  key <- getDyvarKey v
  emitExternCall pthread_getspecific [key]

getDyvarKey :: LLVMBuilder m => DynamicVar -> m Operand
getDyvarKey v = do
  let ref = globalReference (hostPtrTy pthreadKeyTy) $ dynamicVarLName v
  load pthreadKeyTy (L.ConstantOperand ref)

-- This is actually implementation-dependent, but we verify that it's true in dexrt.cpp
pthreadKeyTy :: L.Type
#if defined(linux_HOST_OS)
pthreadKeyTy = i32
#elif defined(darwin_HOST_OS)
pthreadKeyTy = i64
#else
# error Unsupported OS
#endif

pthread_setspecific :: ExternFunSpec
pthread_setspecific = ExternFunSpec "pthread_setspecific" i32 [] [] [pthreadKeyTy, hostVoidp]

pthread_getspecific :: ExternFunSpec
pthread_getspecific = ExternFunSpec "pthread_getspecific" hostVoidp [] [] [pthreadKeyTy]

-- === Compile monad utilities ===

liftCompile :: EnvReader m => Device -> OperandEnv i o -> CompileM i o a -> m o a
liftCompile dev subst m =
  liftM (flip evalState initState) $
    liftEnvReaderT $
     runSubstReaderT subst $
       runCompileM' m
  where
    -- TODO: figure out naming discipline properly
    initState = CompileState [] [] [] "start_block" mempty mempty mempty dev

opSubstVal :: Operand -> OperandSubstVal ImpNameC n
opSubstVal x = OperandSubstVal x

finishBlock :: LLVMBuilder m => L.Terminator -> L.Name -> m ()
finishBlock term name = do
  oldName <- gets blockName
  instrs  <- gets curInstrs
  let newBlock = L.BasicBlock oldName (reverse instrs) (L.Do term)
  modify $ setCurBlocks (newBlock:)
         . setCurInstrs (const [])
         . setBlockName (const name)

freshName :: LLVMBuilder m => NameHint -> m L.Name
freshName hint = do
  used <- gets usedNames
  let v = R.freshRawName hint used
  modify \s -> s { usedNames = R.insert v () used }
  return $ nameToLName v
  where
    nameToLName :: RawName -> L.Name
    nameToLName name = L.Name $ toShort $ B.pack $ showName name

    showName :: RawName -> String
    showName name = show name

-- TODO: consider getting type from instruction rather than passing it explicitly
emitInstr :: LLVMBuilder m => L.Type -> Instruction -> m Operand
emitInstr ty instr = do
  v <- freshName noHint
  addInstr $ v L.:= instr
  return $ L.LocalReference ty v

addInstr :: LLVMBuilder m => Named Instruction -> m ()
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

unaryIntrinsic :: LLVMBuilder m => UnOp -> Operand -> m Operand
unaryIntrinsic op x = do
  device <- gets curDevice
  case device of
    CPU -> cpuUnaryIntrinsic op x
    GPU -> gpuUnaryIntrinsic op x

binaryIntrinsic :: LLVMBuilder m => BinOp -> Operand -> Operand -> m Operand
binaryIntrinsic op x y = do
  device <- gets curDevice
  case device of
    CPU -> cpuBinaryIntrinsic op x y
    GPU -> gpuBinaryIntrinsic op x y

-- === Constants ===

allowContractions :: Bool
allowContractions = unsafePerformIO $ (Just "0"/=) <$> E.lookupEnv "DEX_ALLOW_CONTRACTIONS"

-- FP contractions should only lead to fewer rounding points, so we allow those
mathFlags :: L.FastMathFlags
mathFlags = L.noFastMathFlags { L.allowContract = allowContractions }

mallocFun :: ExternFunSpec
mallocFun = ExternFunSpec "malloc_dex" (hostPtrTy i8) [L.NoAlias] [] [i64]

allocSizeFun :: ExternFunSpec
allocSizeFun = ExternFunSpec "dex_allocation_size" i64 [L.NoAlias] [] [hostPtrTy i8]

memcpyFun :: ExternFunSpec
memcpyFun = ExternFunSpec "llvm.memcpy.p0i8.p0i8.i64" L.VoidType [] [] [hostVoidp, hostVoidp, i64, i1]

memsetFun :: ExternFunSpec
memsetFun = ExternFunSpec "llvm.memset.p0i8.i64" L.VoidType [] [] [hostVoidp, i8, i64, i1]

freeFun :: ExternFunSpec
freeFun = ExternFunSpec "free_dex" L.VoidType [] [] [hostPtrTy i8]

fdopenFun :: ExternFunSpec
fdopenFun = ExternFunSpec "fdopen_w" (hostPtrTy i8) [L.NoAlias] [] [i32]

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
funTy retTy argTys = L.FunctionType retTy argTys False

-- === Module building ===

-- XXX: this tries to simulate the older, pure, version of `typeOf` by passing
-- an empty builder state to the new monadic version. Hopefully the true builder
-- state isn't necessary for the types we need to query.
typeOf :: L.Typed a => a -> L.Type
typeOf x = case fst $ MB.runModuleBuilder emptyState $ L.typeOf x of
  Right ty -> ty
  Left e -> error e
  where emptyState = MB.ModuleBuilderState mempty mempty

-- === Module building ===

makeFunction :: LLVMBuilder m => L.Name -> [Parameter] -> Maybe L.Operand -> m Function
makeFunction name params returnVal = do
  finishBlock (L.Ret returnVal []) "<ignored>"
  decls <- gets scalarDecls
  ~((L.BasicBlock bbname instrs term):blocksTail) <- gets (reverse . curBlocks)
  let blocks = (L.BasicBlock bbname (decls ++ instrs) term):blocksTail
  let returnTy = case returnVal of Nothing -> L.VoidType
                                   Just x  -> typeOf x
  return $ L.functionDefaults
    { L.name        = name
    , L.parameters  = (params, False)
    , L.returnType  = returnTy
    , L.basicBlocks = blocks }

makeModuleEx :: LLVMBuilder m
             => L.DataLayout -> ShortByteString -> [L.Definition] -> m L.Module
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

instance SinkableV OperandSubstVal
instance SinkableE (OperandSubstVal c) where
  sinkingProofE = undefined

instance FromName OperandSubstVal where
  fromName = RenameOperandSubstVal
