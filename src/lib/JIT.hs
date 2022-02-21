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
import qualified Data.Map.Strict as M
import Data.ByteString.Short (toShort)
import qualified Data.ByteString.Char8 as B
import Data.String
import Data.Foldable
import Data.Text.Prettyprint.Doc
import GHC.Stack
import qualified Data.Set as S
-- import qualified Data.Map.Strict as M

import CUDA (getCudaArchitecture)

import Err
import Syntax
import Name
import Imp
import PPrint
import Builder (TopBuilder (..), queryObjCache)
import Logging
import LLVMExec
import Util (IsBool (..))

-- === Compile monad ===

type OperandSubstVal = SubstVal AtomNameC (LiftE Operand)
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
  , usedNames   :: M.Map RawName ()
  , funSpecs    :: S.Set ExternFunSpec
  , globalDefs  :: [L.Definition]
  , curDevice   :: Device
  -- TODO: use safe names for object files
  , _objFileDeps :: S.Set (ObjectFileName VoidS) }

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

impToLLVM :: (Mut n, TopBuilder m, MonadIO1 m, MonadLogger1 [Output] m)
          => SourceName -> ImpFunction n -> m n ([ObjectFileName n], L.Module)
impToLLVM name f =  do
  logger <- getLogger
  ([],) <$> impToLLVM' logger name f

impToLLVM' :: (EnvReader m, MonadIO1 m) => Logger [Output]
           -> SourceName -> ImpFunction n -> m n L.Module
impToLLVM' logger fName f = do
  (defns, externSpecs, globalDtors) <- compileFunction logger fName f
  let externDefns = map externDecl $ toList externSpecs
  let dtorDef = defineGlobalDtors globalDtors
  return $ L.defaultModule
    { L.moduleName = "dexModule"
    , L.moduleDefinitions = dtorDef : defns ++ externDefns }
  where
    dtorType = L.FunctionType L.VoidType [] False
    dtorRegEntryTy = L.StructureType False [ i32, hostPtrTy dtorType, hostVoidp ]
    makeDtorRegEntry dtorName = C.Struct Nothing False
                                         [ C.Int 32 1
                                         , C.GlobalReference (hostPtrTy dtorType) dtorName
                                         , C.Null hostVoidp ]
    defineGlobalDtors globalDtors =
      L.GlobalDefinition $ L.globalVariableDefaults
        { L.name = "llvm.global_dtors"
        , L.type' = L.ArrayType (fromIntegral $ length globalDtors) dtorRegEntryTy
        , L.linkage = L.Appending
        , L.initializer = Just $ C.Array dtorRegEntryTy (makeDtorRegEntry <$> globalDtors)
        }

compileFunction :: (EnvReader m, MonadIO1 m)
                => Logger [Output] -> SourceName -> ImpFunction n
                -> m n ([L.Definition], S.Set ExternFunSpec, [L.Name])
compileFunction _ _ (FFIFunction ty f) =
  return ([], S.singleton (makeFunSpec f ty), [])
compileFunction logger fName fun@(ImpFunction (IFunType cc argTys retTys)
                (Abs bs body)) = case cc of
  FFIFun            -> error "shouldn't be trying to compile an FFI function"
  FFIMultiResultFun -> error "shouldn't be trying to compile an FFI function"
  CInternalFun -> liftCompile CPU $ do
    (argParams, argOperands) <- unzip <$> traverse (freshParamOpPair [] . scalarTy) argTys
    unless (null retTys) $ error "CInternalFun doesn't support returning values"
    void $ extendSubst (bs @@> map opSubstVal argOperands) $ compileBlock body
    mainFun <- makeFunction (topLevelFunName fName) argParams (Just $ i64Lit 0)
    extraSpecs <- gets funSpecs
    return ([L.GlobalDefinition mainFun, outputStreamPtrDef], extraSpecs, [])
  CEntryFun -> liftCompile CPU $ do
    (argParams, argOperands) <- unzip <$> traverse (freshParamOpPair [] . scalarTy) argTys
    unless (null retTys) $ error "CEntryFun doesn't support returning values"
    void $ extendSubst (bs @@> map opSubstVal argOperands) $ compileBlock body
    mainFun <- makeFunction (topLevelFunName fName) argParams (Just $ i64Lit 0)
    extraSpecs <- gets funSpecs
    return ([L.GlobalDefinition mainFun], extraSpecs, [])
  EntryFun requiresCUDA -> liftCompile CPU $ do
    (streamFDParam , streamFDOperand ) <- freshParamOpPair attrs $ i32
    (argPtrParam   , argPtrOperand   ) <- freshParamOpPair attrs $ hostPtrTy i64
    (resultPtrParam, resultPtrOperand) <- freshParamOpPair attrs $ hostPtrTy i64
    initializeOutputStream streamFDOperand
    argOperands <- forM (zip [0..] argTys) \(i, ty) ->
      gep argPtrOperand (i64Lit i) >>= castLPtr (scalarTy ty) >>= load
    when (toBool requiresCUDA) ensureHasCUDAContext
    results <- extendSubst (bs @@> map opSubstVal argOperands) $ compileBlock body
    forM_ (zip [0..] results) \(i, x) ->
      gep resultPtrOperand (i64Lit i) >>= castLPtr (typeOf x) >>= flip store x
    mainFun <- makeFunction (topLevelFunName fName)
                 [streamFDParam, argPtrParam, resultPtrParam] (Just $ i64Lit 0)
    extraSpecs <- gets funSpecs
    return ([L.GlobalDefinition mainFun, outputStreamPtrDef], extraSpecs, [])
    where attrs = [L.NoAlias, L.NoCapture, L.NonNull]
  CUDAKernelLaunch -> do
    arch <- liftIO $ getCudaArchitecture 0
    (CUDAKernel kernelText) <- do
      fun' <- impKernelToLLVMGPU fun
      liftIO $ compileCUDAKernel logger fun' arch
    let chars = map (C.Int 8) $ map (fromIntegral . fromEnum) (B.unpack kernelText) ++ [0]
    let textArr = C.Array i8 chars
    let textArrTy = typeOf textArr
    let textGlobalName = fromString $ pprint fName ++ "#text"
    let textArrDef = L.globalVariableDefaults
                          { L.name = textGlobalName
                          , L.type' = textArrTy
                          , L.linkage = L.Private
                          , L.isConstant = True
                          , L.initializer = Just textArr
                          , L.unnamedAddr = Just L.GlobalAddr
                          }
    let kernelModuleCacheName = fromString $ pprint fName ++ "#cuModule"
    let kernelModuleCacheDef = L.globalVariableDefaults
                                    { L.name = kernelModuleCacheName
                                    , L.type' = hostVoidp
                                    , L.linkage = L.Private
                                    , L.initializer = Just $ C.Null hostVoidp }
    let kernelModuleCache = L.ConstantOperand $ C.GlobalReference (hostPtrTy hostVoidp) kernelModuleCacheName
    let kernelFuncCacheName = fromString $ pprint fName ++ "#cuFunction"
    let kernelFuncCacheDef   = L.globalVariableDefaults
                                    { L.name = kernelFuncCacheName
                                    , L.type' = hostVoidp
                                    , L.linkage = L.Private
                                    , L.initializer = Just $ C.Null hostVoidp }
    let kernelFuncCache = L.ConstantOperand $ C.GlobalReference (hostPtrTy hostVoidp) kernelFuncCacheName
    let textPtr = C.GetElementPtr True
                                  (C.GlobalReference (hostPtrTy textArrTy) textGlobalName)
                                  [C.Int 32 0, C.Int 32 0]
    loaderDef <- liftCompile CPU $ do
          emitVoidExternCall kernelLoaderSpec
            [ L.ConstantOperand $ textPtr, kernelModuleCache, kernelFuncCache]
          kernelFunc <- load kernelFuncCache
          makeFunction (topLevelFunName fName) [] (Just kernelFunc)
    let dtorName = fromString $ pprint fName ++ "#dtor"
    dtorDef <- liftCompile CPU $ do
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
  MCThreadLaunch -> liftCompile CPU $ do
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
    kernel <- makeFunction (topLevelFunName fName)
                [threadIdParam, nThreadParam, argArrayParam] Nothing
    extraSpecs <- gets funSpecs
    return ([L.GlobalDefinition kernel], extraSpecs, [])
    where
      idxRepTy = scalarTy $ IIdxRepTy

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
        let ptxPtrFun = callableOperand (funTy (hostPtrTy i8) []) kernelFuncName
        kernelPtr <- emitInstr (hostPtrTy i8) $ callInstr ptxPtrFun []
        numWorkgroupsPtr <- alloca 1 i32
        workgroupSizePtr <- alloca 1 i32
        emitVoidExternCall queryParallelismCUDAFun [kernelPtr, n, numWorkgroupsPtr, workgroupSizePtr]
        traverse load [numWorkgroupsPtr, workgroupSizePtr]
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
                        (C.GlobalReference mcKernelPtrType kernelFuncName) hostVoidp
        emitVoidExternCall runMCKernel [funPtr, size',kernelParams]
      CUDAKernelLaunch -> do
        let ptxPtrFun = callableOperand (funTy (hostPtrTy i8) []) kernelFuncName
        kernelPtr <- emitInstr (hostPtrTy i8) $ callInstr ptxPtrFun []
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
      GPU -> [] <$ load (L.ConstantOperand $ C.Null $ devicePtrTy i8)
  Alloc a t s -> (:[]) <$> case a of
    Stack -> alloca (getIntLit l) elemTy  where ILit l = s
    Heap dev -> do
      numBytes <- mul (sizeof elemTy) =<< (`asIntWidth` i64) =<< compileExpr s
      case dev of
        CPU -> case t of
          -- XXX: it's important to initialize pointers to zero so that we don't
          --      try to dereference them when we serialize.
          PtrType _ -> malloc True  elemTy numBytes
          _         -> malloc False elemTy numBytes
        -- TODO: initialize GPU pointers too, once we handle serialization
        GPU -> cuMemAlloc elemTy numBytes
    where elemTy = scalarTy t
  Free ptr -> [] <$ do
    let PtrType (addr, _) = getIType ptr
    ptr' <- compileExpr ptr
    case addr of
      Heap CPU -> free      ptr'
      Heap GPU -> cuMemFree ptr'
      Stack -> error "Shouldn't be freeing alloca"
  MemCopy dest src numel -> [] <$ do
    let PtrType (destAddr, ty) = getIType dest
    let PtrType (srcAddr , _ ) = getIType src
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
    let (xt, dt) = (typeOf x, scalarTy idt)
    case (xt, idt) of
      -- if upcasting to unsigned int, use zext instruction
      (L.IntegerType _,    Scalar Word64Type)             -> x `zeroExtendTo` dt
      (L.IntegerType bits, Scalar Word32Type) | bits < 32 -> x `zeroExtendTo` dt
      _ -> case (xt, dt) of
       (L.IntegerType _, L.IntegerType _) -> x `asIntWidth` dt
       (L.FloatingPointType fpt, L.FloatingPointType fpt') -> case compare fpt fpt' of
         LT -> emitInstr dt $ L.FPExt x dt []
         EQ -> return x
         GT -> emitInstr dt $ L.FPTrunc x dt []
       (L.FloatingPointType _, L.IntegerType _) -> emitInstr dt $ L.FPToSI x dt []
       (L.IntegerType _, L.FloatingPointType _) -> emitInstr dt $ L.SIToFP x dt []
       (L.PointerType _ _, L.PointerType eltTy _) -> castLPtr eltTy x
       (L.IntegerType 64 , ptrTy@(L.PointerType _ _)) ->
         emitInstr ptrTy $ L.IntToPtr x ptrTy []
       (L.PointerType _ _, L.IntegerType 64) -> emitInstr i64 $ L.PtrToInt x i64 []
       _ -> error $ "Unsupported cast"
  ICall f args -> do
    fImpName <- substM f
    f' <- lookupImpFun fImpName
    let ty@(IFunType cc argTys resultTys) = impFunType f'
    fname <- case f' of
      FFIFunction _ fname -> return fname
      ImpFunction _ _ -> do
        ~(Just (CFun cname _)) <- queryObjCache fImpName
        -- TODO: track deps!
        return cname
    args' <- mapM compileExpr args
    let resultTys' = map scalarTy resultTys
    case cc of
      FFIFun -> do
        ans <- emitExternCall (makeFunSpec fname ty) args'
        return [ans]
      FFIMultiResultFun -> do
        resultPtr <- makeMultiResultAlloc resultTys'
        emitVoidExternCall (makeFunSpec fname ty) (resultPtr : args')
        loadMultiResultAlloc resultTys' resultPtr
      CEntryFun -> do
        exitCode <- emitInstr i64 (callInstr fun args') >>= (`asIntWidth` i1)
        compileIf exitCode throwRuntimeError (return ())
        return []
          where
            fTy = funTy i64 $ map scalarTy argTys
            fun = callableOperand fTy $ topLevelFunName fname
      CInternalFun -> do
        exitCode <- emitExternCall (makeFunSpec fname ty) args' >>= (`asIntWidth` i1)
        compileIf exitCode throwRuntimeError (return ())
        return []
      _ -> error $ "Unsupported calling convention: " ++ show cc

-- TODO: use a careful naming discipline rather than strings
topLevelFunName :: SourceName -> L.Name
topLevelFunName name = fromString name

makeFunSpec :: SourceName -> IFunType -> ExternFunSpec
makeFunSpec name (IFunType FFIFun argTys [resultTy]) =
   ExternFunSpec (L.Name (fromString name)) (scalarTy resultTy)
                    [] [] (map scalarTy argTys)
makeFunSpec name (IFunType FFIMultiResultFun argTys _) =
   ExternFunSpec (L.Name (fromString name)) L.VoidType [] []
     (hostPtrTy hostVoidp : map scalarTy argTys)
makeFunSpec name (IFunType CInternalFun argTys _) =
   ExternFunSpec (L.Name (fromString name)) i64 [] [] (map scalarTy argTys)
makeFunSpec _ (IFunType _ _ _) = error "not implemented"

compileLoop :: Compiler m => Direction -> IBinder i i' -> Operand -> m i' o () -> m i o ()
compileLoop d iBinder n compileBody = do
  let loopName = "loop_" ++ (fromString $ pprint $ binderName iBinder)
  loopBlock <- freshName $ fromString $ loopName
  nextBlock <- freshName $ fromString $ "cont_" ++ loopName
  i <- alloca 1 $ scalarTy $ iBinderType iBinder
  i0 <- case d of Fwd -> return $ (0 `withWidthOf` n)
                  Rev -> n `sub` (1 `withWidthOf` n)
  store i i0
  entryCond <- (0 `withWidthOf` n) `ilt` n
  finishBlock (L.CondBr entryCond loopBlock nextBlock []) loopBlock
  iVal <- load i
  extendSubst (iBinder @> opSubstVal iVal) $ compileBody
  iValNew <- case d of Fwd -> add iVal (1 `withWidthOf` iVal)
                       Rev -> sub iVal (1 `withWidthOf` iVal)
  store i iValNew
  loopCond <- case d of Fwd -> iValNew `ilt` n
                        Rev -> iValNew `ige` (0 `withWidthOf` iValNew)
  finishBlock (L.CondBr loopCond loopBlock nextBlock []) nextBlock

compileIf :: LLVMBuilder m => Operand -> m () -> m () -> m ()
compileIf cond tb fb = do
  tbName   <- freshName "if_true"
  fbName   <- freshName "if_false"
  contName <- freshName "if_cont"
  finishBlock (L.CondBr cond tbName fbName []) tbName
  tb
  finishBlock (L.Br contName []) fbName
  fb
  finishBlock (L.Br contName []) contName

compileWhile :: LLVMBuilder m => m Operand -> m ()
compileWhile compileBody = do
  loopBlock <- freshName "whileLoop"
  nextBlock <- freshName "whileCont"
  entryCond <- compileBody >>= (`asIntWidth` i1)
  finishBlock (L.CondBr entryCond loopBlock nextBlock []) loopBlock
  loopCond <- compileBody >>= (`asIntWidth` i1)
  finishBlock (L.CondBr loopCond loopBlock nextBlock []) nextBlock

throwRuntimeError :: LLVMBuilder m => m ()
throwRuntimeError = do
  deadBlock <- freshName "deadBlock"
  finishBlock (L.Ret (Just $ i64Lit 1) []) deadBlock

compilePrimOp :: LLVMBuilder m => PrimOp Operand -> m Operand
compilePrimOp pop = case pop of
  ScalarBinOp op x y -> compileBinOp op x y
  VectorBinOp op x y -> compileBinOp op x y
  ScalarUnOp  op x   -> compileUnOp  op x
  Select      p  x y -> do
    pb <- p `asIntWidth` i1
    emitInstr (typeOf x) $ L.Select pb x y []
  VectorPack elems   -> foldM fillElem undef $ zip elems [0..]
    where
      resTy = L.VectorType (fromIntegral vectorWidth) $ typeOf $ head elems
      fillElem v (e, i) = emitInstr resTy $ L.InsertElement v e (i32Lit i) []
      undef = L.ConstantOperand $ C.Undef resTy
  VectorIndex v i    -> emitInstr resTy $ L.ExtractElement v i []
    where (L.VectorType _ resTy) = typeOf v
  PtrOffset ptr off -> gep ptr off
  OutputStreamPtr -> return outputStreamPtr

  _ -> error $ "Can't JIT primop: " ++ pprint pop

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

deviceFromAddr :: LLVMBuilder m => AddressSpace -> m Device
deviceFromAddr addr = case addr of
  Heap dev -> return dev
  Stack -> gets curDevice

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

impKernelToLLVMGPU :: EnvReader m => ImpFunction n -> m n (LLVMKernel)
impKernelToLLVMGPU (ImpFunction _ (Abs args body)) = do
  let numThreadInfoArgs = 4  -- [threadIdParam, nThreadParam, argArrayParam]
  let argTypes = drop numThreadInfoArgs $ nestToList (scalarTy . iBinderType) args
  let kernelMeta = L.MetadataNodeDefinition kernelMetaId $ L.MDTuple
                     [ Just $ L.MDValue $ L.ConstantOperand $ C.GlobalReference
                         (funTy L.VoidType argTypes) "kernel"
                     , Just $ L.MDString "kernel"
                     , Just $ L.MDValue $ L.ConstantOperand $ C.Int 32 1
                     ]
  liftCompile GPU $ do
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
    idxRepTy = scalarTy $ IIdxRepTy
    ptrParamAttrs = [L.NoAlias, L.NoCapture, L.NonNull, L.Alignment 256]
    kernelMetaId = L.MetadataNodeID 0
    nvvmAnnotations = L.NamedMetadataDefinition "nvvm.annotations" [kernelMetaId]
impKernelToLLVMGPU _ = error "not implemented"

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
ptxSpecialReg name = ExternFunSpec name i32 [] [FA.ReadNone, FA.NoUnwind] []

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
    genericPtrTy ty = L.PointerType ty $ L.AddrSpace 0
    vprintfSpec = ExternFunSpec "vprintf" i32 [] [] [genericPtrTy i8, genericPtrTy i8]

-- Takes a single int64 payload. TODO: implement a varargs version
_debugPrintf :: LLVMBuilder m => String -> Operand -> m ()
_debugPrintf fmtStr x = do
  let chars = map (C.Int 8) $ map (fromIntegral . fromEnum) fmtStr ++ [0]
  let formatStrArr = L.ConstantOperand $ C.Array i8 chars
  formatStrPtr <- alloca (length chars) i8
  castLPtr (typeOf formatStrArr) formatStrPtr >>= (`store` formatStrArr)
  void $ emitExternCall printfSpec [formatStrPtr, x]
  where printfSpec = ExternFunSpec "printf" i32 [] [] [hostVoidp, i64]

_debugPrintfPtr :: LLVMBuilder m => String -> Operand -> m ()
_debugPrintfPtr s x = do
  x' <- emitInstr i64 $ L.PtrToInt x i64 []
  _debugPrintf s x'

compileBlock :: Compiler m => ImpBlock i -> m i o [Operand]
compileBlock (ImpBlock Empty result) = traverse compileExpr result
compileBlock (ImpBlock (Nest decl rest) result) = do
  env <- compileDecl decl
  extendSubst env $ compileBlock (ImpBlock rest result)

compileDecl :: Compiler m => ImpDecl i i' -> m i o (OperandEnvFrag i i' o)
compileDecl (ImpLet bs instr) = do
  results <- compileInstr instr
  if length results == nestLength bs
    then return $ bs @@> map (SubstVal . LiftE) results
    else error "Unexpected number of results"

compileVoidBlock :: Compiler m => ImpBlock i -> m i o ()
compileVoidBlock = void . compileBlock

compileExpr :: Compiler m => IExpr i -> m i o Operand
compileExpr expr = case expr of
  ILit v   -> return (litVal v)
  IVar v _ -> lookupImpVar v

packArgs :: LLVMBuilder m => [Operand] -> m Operand
packArgs elems = do
  arr <- alloca (length elems) hostVoidp
  forM_ (zip [0..] elems) \(i, e) -> do
    eptr <- alloca 1 $ typeOf e
    store eptr e
    earr <- gep arr $ i32Lit i
    store earr =<< castVoidPtr eptr
  return arr

unpackArgs :: LLVMBuilder m => Operand -> [L.Type] -> m [Operand]
unpackArgs argArrayPtr types =
  forM (zip [0..] types) \(i, ty) -> do
    argVoidPtr <- gep argArrayPtr $ i64Lit i
    argPtr <- castLPtr (hostPtrTy ty) argVoidPtr
    load =<< load argPtr

makeMultiResultAlloc :: LLVMBuilder m => [L.Type] -> m Operand
makeMultiResultAlloc tys = do
  resultsPtr <- alloca (length tys) hostVoidp
  forM_ (zip [0..] tys) \(i, ty) -> do
    ptr <- alloca 1 ty >>= castVoidPtr
    resultsPtrOffset <- gep resultsPtr $ i32Lit i
    store resultsPtrOffset ptr
  return resultsPtr

loadMultiResultAlloc :: LLVMBuilder m => [L.Type] -> Operand -> m [Operand]
loadMultiResultAlloc tys ptr =
  forM (zip [0..] tys) \(i, ty) ->
    gep ptr (i32Lit i) >>= load >>= castLPtr ty >>= load

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
  VecLit l     -> L.ConstantOperand $ foldl fillElem undef $ zip consts [0..length l - 1]
    where
      consts = fmap (operandToConst . litVal) l
      undef = C.Undef $ L.VectorType (fromIntegral $ length l) $ typeOf $ head consts
      fillElem v (c, i) = C.InsertElement v c (C.Int 32 (fromIntegral i))
      operandToConst ~(L.ConstantOperand c) = c
  PtrLit _ -> error "Shouldn't be compiling pointer literals"

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

load :: LLVMBuilder m => Operand -> m Operand
load ptr = emitInstr ty $ L.Load False ptr Nothing 0 []
  where (L.PointerType ty _) = typeOf ptr

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

gep :: LLVMBuilder m => Operand -> Operand -> m Operand
gep ptr i = emitInstr (typeOf ptr) $ L.GetElementPtr False ptr [i] []

sizeof :: L.Type -> Operand
sizeof t = L.ConstantOperand $ C.sizeof 64 t

alloca :: LLVMBuilder m => Int -> L.Type -> m Operand
alloca elems ty = do
  v <- freshName "v"
  modify $ setScalarDecls ((v L.:= instr):)
  return $ L.LocalReference (hostPtrTy ty) v
  where instr = L.Alloca ty (Just $ i32Lit elems) 0 []

malloc :: LLVMBuilder m => Bool -> L.Type -> Operand -> m Operand
malloc initialize ty bytes = do
  bytes64 <- asIntWidth bytes i64
  ptr <- if initialize
    then emitExternCall mallocInitializedFun [bytes64]
    else emitExternCall mallocFun            [bytes64]
  castLPtr ty ptr

free :: LLVMBuilder m => Operand -> m ()
free ptr = do
 ptr' <- castLPtr i8 ptr
 emitVoidExternCall freeFun [ptr']

castLPtr :: LLVMBuilder m => L.Type -> Operand -> m Operand
castLPtr ty ptr = emitInstr newPtrTy $ L.BitCast ptr newPtrTy []
  where
    L.PointerType _ addr = typeOf ptr
    newPtrTy = L.PointerType ty addr

castVoidPtr :: LLVMBuilder m => Operand -> m Operand
castVoidPtr = castLPtr i8

zeroExtendTo :: LLVMBuilder m => Operand -> L.Type -> m Operand
zeroExtendTo x t = emitInstr t $ L.ZExt x t []

callInstr :: L.CallableOperand -> [L.Operand] -> L.Instruction
callInstr fun xs = L.Call Nothing L.C [] fun xs' [] []
 where xs' = [(x ,[]) | x <- xs]

externCall :: ExternFunSpec -> [L.Operand] -> L.Instruction
externCall (ExternFunSpec fname retTy _ _ argTys) xs = callInstr fun xs
  where fun = callableOperand (funTy retTy argTys) fname

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
  Vector sb -> L.VectorType (fromIntegral vectorWidth) $ scalarTy $ Scalar sb
  PtrType (s, t) -> L.PointerType (scalarTy t) (lAddress s)

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

asIntWidth :: LLVMBuilder m => Operand -> L.Type -> m Operand
asIntWidth op ~expTy@(L.IntegerType expWidth) = case compare expWidth opWidth of
  LT -> emitInstr expTy $ L.Trunc op expTy []
  EQ -> return op
  GT -> emitInstr expTy $ L.SExt  op expTy []
  where ~(L.IntegerType opWidth) = typeOf op

freshParamOpPair :: LLVMBuilder m => [L.ParameterAttribute] -> L.Type -> m (Parameter, Operand)
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

cpuUnaryIntrinsic :: LLVMBuilder m => UnOp -> Operand -> m Operand
cpuUnaryIntrinsic op x = case typeOf x of
  L.FloatingPointType L.DoubleFP -> dispatchOp fp64 ".f64" ""
  L.FloatingPointType L.FloatFP  -> dispatchOp fp32 ".f32" "f"
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
      _ -> error $ "Unsupported CPU operation: " ++ show op
    floatIntrinsic ty name = ExternFunSpec (L.mkName name) ty [] [] [ty]
    callFloatIntrinsic ty name = emitExternCall (floatIntrinsic ty name) [x]

cpuBinaryIntrinsic :: LLVMBuilder m => BinOp -> Operand -> Operand -> m Operand
cpuBinaryIntrinsic op x y = case typeOf x of
  L.FloatingPointType L.DoubleFP -> dispatchOp fp64 ".f64"
  L.FloatingPointType L.FloatFP  -> dispatchOp fp32 ".f32"
  _ -> error $ "Unsupported CPU floating point type: " ++ show (typeOf x)
  where
    dispatchOp ty llvmSuffix = case op of
      FPow -> callFloatIntrinsic ty $ "llvm.pow" ++ llvmSuffix
      _ -> error $ "Unsupported CPU operation: " ++ show op
    floatIntrinsic ty name = ExternFunSpec (L.mkName name) ty [] [] [ty, ty]
    callFloatIntrinsic ty name = emitExternCall (floatIntrinsic ty name) [x, y]

-- === Output stream ===

-- TODO: replace all of this with a built-in print

outputStreamPtrLName :: L.Name
outputStreamPtrLName  = "*OUT_STREAM_PTR*"

outputStreamPtrDef :: L.Definition
outputStreamPtrDef = L.GlobalDefinition $ L.globalVariableDefaults
  { L.name = outputStreamPtrLName
  , L.type' = hostVoidp
  , L.linkage = L.Private
  , L.initializer = Just $ C.Null hostVoidp }

outputStreamPtr :: Operand
outputStreamPtr = L.ConstantOperand $ C.GlobalReference
 (hostPtrTy hostVoidp) outputStreamPtrLName

initializeOutputStream :: LLVMBuilder m => Operand -> m ()
initializeOutputStream streamFD = do
  streamPtr <- emitExternCall fdopenFun [streamFD]
  store outputStreamPtr streamPtr

-- === Compile monad utilities ===

liftCompile :: EnvReader m => Device -> CompileM n n a -> m n a
liftCompile dev m =
  liftM (flip evalState initState) $
    liftEnvReaderT $
     runSubstReaderT idSubst $
       runCompileM' m
  where
    -- TODO: figure out naming discipline properly
    initState = CompileState [] [] [] "start_block" mempty mempty mempty dev mempty

opSubstVal :: Operand -> OperandSubstVal AtomNameC n
opSubstVal x = SubstVal (LiftE x)

lookupImpVar :: Compiler m => AtomName i -> m i o Operand
lookupImpVar v = do
  subst <- getSubst
  case subst ! v of
    SubstVal (LiftE x) -> return x
    Rename _ -> error "shouldn't happen?"

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
  let v = freshRawName hint used
  modify \s -> s { usedNames = used <> M.singleton v () }
  return $ nameToLName v
  where
    nameToLName :: RawName -> L.Name
    nameToLName name = L.Name $ toShort $ B.pack $ showName name

    showName :: RawName -> String
    showName (RawName tag counter) = docAsStr $ pretty tag <> "." <> pretty counter

-- TODO: consider getting type from instruction rather than passing it explicitly
emitInstr :: LLVMBuilder m => L.Type -> Instruction -> m Operand
emitInstr ty instr = do
  v <- freshName "v"
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

mallocInitializedFun :: ExternFunSpec
mallocInitializedFun =
  ExternFunSpec "dex_malloc_initialized" (hostPtrTy i8) [L.NoAlias] [] [i64]

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
funTy retTy argTys = hostPtrTy $ L.FunctionType retTy argTys False

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
