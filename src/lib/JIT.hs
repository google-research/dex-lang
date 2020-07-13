-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module JIT (impToLLVM, mdImpToLLVM, impKernelToLLVM) where

import LLVM.AST (Operand, BasicBlock, Instruction, Named, Parameter)
import LLVM.Prelude (ShortByteString)
import qualified LLVM.AST as L
import qualified LLVM.AST.AddrSpace as L
import qualified LLVM.AST.DataLayout as L
import qualified LLVM.AST.Global as L
import qualified LLVM.AST.CallingConvention as L
import qualified LLVM.AST.Type as L
import qualified LLVM.AST.Typed as L
import qualified LLVM.AST.Float as L
import qualified LLVM.AST.Constant as C
import qualified LLVM.AST.FloatingPointPredicate as L
import qualified LLVM.AST.IntegerPredicate as L
import qualified LLVM.AST.ParameterAttribute as L
import qualified LLVM.AST.FunctionAttribute as FA

import Control.Monad
import Control.Monad.State.Strict
import Control.Monad.Reader
import Data.Maybe (fromJust)
import Data.ByteString.Short (toShort)
import Data.ByteString.Char8 (pack)
import Data.String
import Data.Foldable
import Data.Text.Prettyprint.Doc
import qualified Data.Set as S
import qualified Data.Map as M

import Array (vectorWidth)
import LLVMExec
import Syntax
import Env
import PPrint
import Cat

type CompileEnv = Env Operand
-- TODO: consider using LLVM.IRBuilder.Monad instead of rolling our own here
data CompileState = CompileState { curBlocks   :: [BasicBlock]
                                 , curInstrs   :: [NInstr]
                                 , scalarDecls :: [NInstr]
                                 , blockName   :: L.Name
                                 , usedNames   :: Env ()
                                 , progOutputs :: Env Operand  -- Maps Imp values to the output pointer operands
                                 , funSpecs    :: S.Set ExternFunSpec
                                 , allocas     :: S.Set L.Name
                                 }

type CompileM a = ReaderT CompileEnv (State CompileState) a
data ExternFunSpec = ExternFunSpec L.Name L.Type [L.ParameterAttribute] [FA.FunctionAttribute] [L.Type]
                     deriving (Ord, Eq)

type Long = Operand
type NInstr = Named Instruction
type Function = L.Global

-- === Imp to LLVM ===

impToLLVM :: ImpFunction -> LLVMFunction
impToLLVM f = runCompileM mempty (compileTopProg f)

compileTopProg :: ImpFunction -> CompileM LLVMFunction
compileTopProg (ImpFunction outVars inVars (ImpProg prog)) = do
  -- Set up the argument list. Note that all outputs are pointers to pointers.
  let inVarTypes  = map (        fromArrType . varAnn) inVars
  let outVarTypes = map (L.ptr . fromArrType . varAnn) outVars
  (inParams, inOperands)   <- unzip <$> mapM (freshParamOpPair extraAttrs) inVarTypes
  (outParams, outOperands) <- unzip <$> mapM (freshParamOpPair extraAttrs) outVarTypes

  -- Emit the program
  let paramEnv = newEnv inVars inOperands
  modify (\s -> s { progOutputs = zipEnv outVars outOperands })
  extendR paramEnv $ compileProg prog

  let params = outParams ++ inParams
  let paramTypes = fmap L.typeOf params
  mainFun <- makeFunction "mainFun" params

  let mainFunOp = callableOperand (funTy L.VoidType paramTypes) "mainFun"
  let entryFun = makeEntryPoint "entryFun" paramTypes mainFunOp
  LLVMFunction numOutputs <$> makeModule [L.GlobalDefinition mainFun,
                                          L.GlobalDefinition entryFun]
  where
    dropArray t = case t of ArrayTy t' -> t'; _ -> t
    fromArrType = (fromIType $ L.AddrSpace 0) . IRefType . dropArray
    numOutputs = length outVars
    extraAttrs = [L.Alignment 64, L.Dereferenceable 64]

freshParamOpPair :: [L.ParameterAttribute] -> L.Type -> CompileM (Parameter, Operand)
freshParamOpPair extraAttrs ty = do
  v <- freshName "arg"
  return (L.Parameter ty v attrs, L.LocalReference ty v)
  -- TODO: Add nofree once we bump the LLVM version
  where attrs = extraAttrs ++ [L.NoAlias, L.NoCapture, L.NonNull]

compileProg :: [ImpStatement] -> CompileM ()
compileProg [] = return ()
compileProg ((maybeName, instr):prog) = do
  outputs <- gets progOutputs
  let isOutput = case maybeName of
                    Just name -> name `isin` outputs
                    Nothing   -> False
  maybeAns <- compileInstr (not isOutput) instr
  let env = case (maybeName, maybeAns) of
              (Nothing, Nothing) -> mempty
              (Just v, Just ans) -> v @> ans
              _ -> error "Void mismatch"
  if isOutput
    then do
      case instr of
        Alloc _ _ -> return ()
        _         -> error $ "Non-alloc instruction writing to a program output: " ++ pprint instr
      store (outputs ! (fromJust maybeName)) (fromJust maybeAns)
    else return ()
  extendR env $ compileProg prog

compileInstr :: Bool -> ImpInstr -> CompileM (Maybe Operand)
compileInstr allowAlloca instr = case instr of
  IPrimOp op -> do
    op' <- traverse compileExpr op
    liftM Just $ compilePrimOp op'
  Load ref -> do
    ref' <- compileExpr ref
    liftM Just $ load ref'
  Store dest val -> do
    dest' <- compileExpr dest
    val'  <- compileExpr val
    store dest' val'
    return Nothing
  Alloc t numel -> Just <$> case numel of
    ILit (IntLit n) | allowAlloca && n <= 256 -> alloca n elemTy
    _ -> malloc elemTy =<< mul (sizeof elemTy) =<< compileExpr numel
    where elemTy = scalarTy $ scalarTableBaseType t
  Free v' -> do
    ~v@(L.LocalReference _ vn) <- lookupImpVar v'
    stackAllocated <- gets allocas
    if vn `S.member` stackAllocated
      then return ()
      else do
        ptr' <- castLPtr charTy v
        emitVoidExternCall freeFun [ptr']
    return Nothing
  IOffset x off _ -> do
    x' <- compileExpr x
    off' <- compileExpr off
    Just <$> gep x' off'
  Loop d i n body -> do
    n' <- compileExpr n
    compileLoop d i n' body
    return Nothing
  IWhile cond body -> do
    compileWhile cond body
    return Nothing

compileExpr :: IExpr -> CompileM Operand
compileExpr expr = case expr of
  ILit v   -> return (litVal v)
  IVar v   -> lookupImpVar v

compileLoop :: Direction -> IVar -> Operand -> ImpProg -> CompileM ()
compileLoop d iVar n (ImpProg body) = do
  let loopName = "loop_" ++ (showName $ varName iVar)
  loopBlock <- freshName $ fromString $ loopName
  nextBlock <- freshName $ fromString $ "cont_" ++ loopName
  i <- alloca 1 longTy
  i0 <- case d of Fwd -> return $ litInt 0
                  Rev -> n `sub` litInt 1
  store i i0
  entryCond <- litInt 0 `lessThan` n
  finishBlock (L.CondBr entryCond loopBlock nextBlock []) loopBlock
  iVal <- load i
  extendR (iVar @> iVal) $ compileProg body
  iValNew <- case d of Fwd -> add iVal $ litInt 1
                       Rev -> sub iVal $ litInt 1
  store i iValNew
  loopCond <- case d of Fwd -> iValNew `lessThan` n
                        Rev -> iValNew `greaterOrEq` litInt 0
  finishBlock (L.CondBr loopCond loopBlock nextBlock []) nextBlock

compileWhile :: IExpr -> ImpProg -> CompileM ()
compileWhile cond (ImpProg body) = do
  cond' <- compileExpr cond
  loopBlock <- freshName "whileLoop"
  nextBlock <- freshName "whileCont"
  entryCond <- load cond' >>= intToBool
  finishBlock (L.CondBr entryCond loopBlock nextBlock []) loopBlock
  compileProg body
  loopCond <- load cond' >>= intToBool
  finishBlock (L.CondBr loopCond loopBlock nextBlock []) nextBlock

compilePrimOp :: PrimOp Operand -> CompileM Operand
compilePrimOp (ScalarBinOp op x y) = compileBinOp op x y
compilePrimOp (VectorBinOp op x y) = compileBinOp op x y
compilePrimOp (ScalarUnOp op x) = case op of
  BoolToInt       -> return x -- bools stored as ints
  UnsafeIntToBool -> return x -- bools stored as ints
  Exp             -> callRealIntrinsic "llvm.exp.f64"
  Exp2            -> callRealIntrinsic "llvm.exp2.f64"
  Log             -> callRealIntrinsic "llvm.log.f64"
  Log2            -> callRealIntrinsic "llvm.log2.f64"
  Log10           -> callRealIntrinsic "llvm.log10.f64"
  Sin             -> callRealIntrinsic "llvm.sin.f64"
  Cos             -> callRealIntrinsic "llvm.cos.f64"
  Tan             -> callRealIntrinsic "tan"  -- Technically not an intrinsic, but it works!
  Sqrt            -> callRealIntrinsic "llvm.sqrt.f64"
  Floor           -> do
    x' <- callRealIntrinsic "llvm.floor.f64"
    emitInstr longTy $ L.FPToSI x' longTy []
  Ceil            -> do
    x' <- callRealIntrinsic "llvm.ceil.f64"
    emitInstr longTy $ L.FPToSI x' longTy []
  Round           -> do
    x' <- callRealIntrinsic "llvm.round.f64"
    emitInstr longTy $ L.FPToSI x' longTy []
  IntToReal       -> emitInstr realTy $ L.SIToFP x realTy []
  -- LLVM has "fneg" but it doesn't seem to be exposed by llvm-hs-pure
  FNeg            -> emitInstr realTy $ L.FSub mathFlags (litReal 0.0) x []
  BNot            -> emitInstr boolTy $ L.Xor x (litInt 1) []
  where
    realIntrinsic name = ExternFunSpec name realTy [] [] [realTy]
    callRealIntrinsic name = emitExternCall (realIntrinsic name) [x]
compilePrimOp (Select p x y) = do
  p' <- intToBool p
  emitInstr (L.typeOf x) $ L.Select p' x y []
compilePrimOp (FFICall name ansTy xs) = do
  emitExternCall f xs
  where f = ExternFunSpec (L.Name (fromString name)) (scalarTy ansTy) [] [] (map L.typeOf xs)
compilePrimOp (VectorPack elems) = foldM fillElem undef $ zip elems [0..]
  where
    resTy = L.VectorType (fromIntegral vectorWidth) $ L.typeOf $ head elems
    fillElem v (e, i) = emitInstr resTy $ L.InsertElement v e (litInt i) []
    undef = L.ConstantOperand $ C.Undef resTy
compilePrimOp (VectorIndex v i) = emitInstr resTy $ L.ExtractElement v i []
  where (L.VectorType _ resTy) = L.typeOf v
compilePrimOp op = error $ "Can't JIT primop: " ++ pprint op

compileBinOp :: BinOp -> Operand -> Operand -> CompileM Operand
compileBinOp op x y = case op of
  IAdd   -> emitInstr longTy $ L.Add False False x y []
  ISub   -> emitInstr longTy $ L.Sub False False x y []
  IMul   -> emitInstr longTy $ L.Mul False False x y []
  IDiv   -> emitInstr longTy $ L.SDiv False x y []
  IRem   -> emitInstr longTy $ L.SRem x y []
  IPow   -> error "Not implemented"
  FPow   -> emitExternCall (realIntrinsic "llvm.pow.f64") [x, y]
  FAdd   -> emitInstr realTy $ L.FAdd mathFlags x y []
  FSub   -> emitInstr realTy $ L.FSub mathFlags x y []
  FMul   -> emitInstr realTy $ L.FMul mathFlags x y []
  FDiv   -> emitInstr realTy $ L.FDiv mathFlags x y []
  BAnd   -> emitInstr boolTy $ L.And x y []
  BOr    -> emitInstr boolTy $ L.Or  x y []
  ICmp c -> emitInstr boolTy (L.ICmp (intCmpOp   c) x y []) >>= (`zeroExtendTo` boolTy)
  FCmp c -> emitInstr boolTy (L.FCmp (floatCmpOp c) x y []) >>= (`zeroExtendTo` boolTy)
  where
    realIntrinsic name = ExternFunSpec name realTy [] [] [realTy, realTy]

    floatCmpOp :: CmpOp -> L.FloatingPointPredicate
    floatCmpOp cmpOp = case cmpOp of
      Less         -> L.OLT
      LessEqual    -> L.OLE
      Greater      -> L.OGT
      GreaterEqual -> L.OGE
      Equal        -> L.OEQ

    intCmpOp :: CmpOp -> L.IntegerPredicate
    intCmpOp cmpOp = case cmpOp of
      Less         -> L.SLT
      LessEqual    -> L.SLE
      Greater      -> L.SGT
      GreaterEqual -> L.SGE
      Equal        -> L.EQ

-- === MDImp to LLVM ===

mdImpToLLVM :: MDImpFunction PTXKernel -> LLVMFunction
mdImpToLLVM f = undefined

impKernelToLLVM :: ImpKernel -> LLVMKernel
impKernelToLLVM (ImpKernel args lvar (ImpProg prog)) = runCompileM mempty $ do
  (argParams, argOperands) <- unzip <$> mapM (freshParamOpPair [L.Alignment 256]) argTypes
  tidx <- threadIdxX
  bidx <- blockIdxX
  bsz  <- blockDimX
  lidx <- mul bidx bsz >>= (add tidx)
  let paramEnv = foldMap (uncurry (@>)) $ zip args argOperands
  -- TODO: Use a restricted form of compileProg that e.g. never emits FFI calls!
  extendR (paramEnv <> lvar @> lidx) $ compileProg prog
  kernel <- makeFunction "kernel" argParams
  LLVMKernel <$> makeModuleEx ptxDataLayout targetTriple [L.GlobalDefinition kernel, kernelMeta, nvvmAnnotations]

  where
    argTypes = fmap ((fromIType $ L.AddrSpace 1). varAnn) args
    kernelMetaId = L.MetadataNodeID 0
    kernelMeta = L.MetadataNodeDefinition kernelMetaId $ L.MDTuple
      [ Just $ L.MDValue $ L.ConstantOperand $ C.GlobalReference (funTy L.VoidType argTypes) "kernel"
      , Just $ L.MDString "kernel"
      , Just $ L.MDValue $ L.ConstantOperand $ C.Int 32 1
      ]
    nvvmAnnotations = L.NamedMetadataDefinition "nvvm.annotations" [kernelMetaId]
    targetTriple = "nvptx64-nvidia-cuda"
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

threadIdxX :: CompileM Operand
threadIdxX = emitExternCall spec [] >>= (`zeroExtendTo` longTy)
  where spec = ptxSpecialReg "llvm.nvvm.read.ptx.sreg.tid.x"

blockIdxX :: CompileM Operand
blockIdxX = emitExternCall spec [] >>= (`zeroExtendTo` longTy)
  where spec = ptxSpecialReg "llvm.nvvm.read.ptx.sreg.ctaid.x"

blockDimX :: CompileM Operand
blockDimX = emitExternCall spec [] >>= (`zeroExtendTo` longTy)
  where spec = ptxSpecialReg "llvm.nvvm.read.ptx.sreg.ntid.x"

ptxSpecialReg :: L.Name -> ExternFunSpec
ptxSpecialReg name = ExternFunSpec name i32 [] [FA.ReadNone, FA.NoUnwind] []

i32 :: L.Type
i32 = L.IntegerType 32

-- === LLVM embedding ===

litVal :: LitVal -> Operand
litVal lit = case lit of
  IntLit  x -> litInt x
  RealLit x -> litReal x
  BoolLit True  -> litInt 1
  BoolLit False -> litInt 0
  VecLit l  -> L.ConstantOperand $ foldl fillElem undef $ zip consts [0..length l - 1]
    where
      consts = fmap (operandToConst . litVal) l
      undef = C.Undef $ L.VectorType (fromIntegral $ length l) $ L.typeOf $ head consts
      fillElem v (c, i) = C.InsertElement v c (C.Int 64 (fromIntegral i))
  StrLit _ -> error "Not implemented"

litInt :: Int -> Operand
litInt x = L.ConstantOperand $ C.Int 64 (fromIntegral x)

litReal :: Double -> Operand
litReal x = L.ConstantOperand $ C.Float $ L.Double x

store :: Operand -> Operand -> CompileM ()
store ptr x =  addInstr $ L.Do $ L.Store False ptr x Nothing 0 []

load :: Operand -> CompileM Operand
load ptr = emitInstr ty $ L.Load False ptr Nothing 0 []
  where (L.PointerType ty _) = L.typeOf ptr

lessThan :: Long -> Long -> CompileM Long
lessThan x y = emitInstr longTy $ L.ICmp L.SLT x y []

greaterOrEq :: Long -> Long -> CompileM Long
greaterOrEq x y = emitInstr longTy $ L.ICmp L.SGE x y []

add :: Long -> Long -> CompileM Long
add x y = emitInstr longTy $ L.Add False False x y []

sub :: Long -> Long -> CompileM Long
sub x y = emitInstr longTy $ L.Sub False False x y []

mul :: Operand -> Operand -> CompileM Operand
mul x y = emitInstr longTy $ L.Mul False False x y []

gep :: Operand -> Operand -> CompileM Operand
gep ptr i = emitInstr (L.typeOf ptr) $ L.GetElementPtr False ptr [i] []

sizeof :: L.Type -> Operand
sizeof t = (L.ConstantOperand $ C.ZExt (C.sizeof t) longTy)

alloca :: Int -> L.Type -> CompileM Operand
alloca elems ty = do
  v <- freshName "v"
  modify $ setScalarDecls ((v L.:= instr):)
  modify $ setAllocas (S.insert v)
  return $ L.LocalReference (L.ptr ty) v
  where instr = L.Alloca ty (Just $ litInt elems) 0 []

malloc :: L.Type -> Operand -> CompileM Operand
malloc ty bytes = do
  voidPtr <- emitExternCall mallocFun [bytes]
  castLPtr ty voidPtr

castLPtr :: L.Type -> Operand -> CompileM Operand
castLPtr ty ptr = emitInstr (L.ptr ty) $ L.BitCast ptr (L.ptr ty) []

zeroExtendTo :: Operand -> L.Type -> CompileM Operand
zeroExtendTo x t = emitInstr t $ L.ZExt x t []

intToBool :: Operand -> CompileM Operand
intToBool x = emitInstr (L.IntegerType 1) $ L.Trunc x (L.IntegerType 1) []

externCall :: ExternFunSpec -> [L.Operand] -> L.Instruction
externCall (ExternFunSpec fname retTy _ _ argTys) xs = callInstr fun xs
  where fun = callableOperand (funTy retTy argTys) fname

emitExternCall :: ExternFunSpec -> [L.Operand] -> CompileM Operand
emitExternCall f@(ExternFunSpec _ retTy _ _ _) xs = do
  modify $ setFunSpecs (S.insert f)
  emitInstr retTy $ externCall f xs

emitVoidExternCall :: ExternFunSpec -> [L.Operand] -> CompileM ()
emitVoidExternCall f xs = do
  modify $ setFunSpecs (S.insert f)
  addInstr $ L.Do $ externCall f xs

callInstr :: L.CallableOperand -> [L.Operand] -> L.Instruction
callInstr fun xs = L.Call Nothing L.C [] fun xs' [] []
 where xs' = [(x ,[]) | x <- xs]

scalarTy :: BaseType -> L.Type
scalarTy b = case b of
  Scalar sb -> case sb of
    IntType  -> longTy
    RealType -> realTy
    BoolType -> boolTy -- Still storing in 64-bit arrays TODO: use 8 bits (or 1)
    StrType  -> error "Not implemented"
  Vector sb -> L.VectorType (fromIntegral vectorWidth) $ scalarTy $ Scalar sb

fromIType :: L.AddrSpace -> IType -> L.Type
fromIType addrSpace it = case it of
  IValType b -> scalarTy b
  IRefType t -> L.PointerType (scalarTy $ scalarTableBaseType t) addrSpace

operandToConst :: Operand -> C.Constant
operandToConst (L.ConstantOperand c) = c
operandToConst op = error $ "Not a constant: " ++ show op

callableOperand :: L.Type -> L.Name -> L.CallableOperand
callableOperand ty name = Right $ L.ConstantOperand $ C.GlobalReference ty name

showName :: Name -> String
showName (Name GenName tag counter) = asStr $ pretty tag <> "." <> pretty counter
showName _ = error $ "All names in JIT should be from the GenName namespace"

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

-- === CompileM monad utilities ===

runCompileM :: CompileEnv -> CompileM a -> a
runCompileM env m = evalState (runReaderT m env) initState
  where initState = CompileState [] [] [] "start_block" mempty mempty mempty mempty

lookupImpVar :: IVar -> CompileM Operand
lookupImpVar v = asks (! v)

finishBlock :: L.Terminator -> L.Name -> CompileM ()
finishBlock term newName = do
  oldName <- gets blockName
  instrs  <- gets curInstrs
  let newBlock = L.BasicBlock oldName (reverse instrs) (L.Do term)
  modify $ setCurBlocks (newBlock:)
         . setCurInstrs (const [])
         . setBlockName (const newName)

freshName :: Name -> CompileM L.Name
freshName v = do
  used <- gets usedNames
  let v'@(name:>_) = rename (v:>()) used
  modify $ \s -> s { usedNames = used <> v'@>() }
  return $ nameToLName name
  where
    nameToLName :: Name -> L.Name
    nameToLName name = L.Name $ toShort $ pack $ showName name

-- TODO: consider getting type from instruction rather than passing it explicitly
emitInstr :: L.Type -> Instruction -> CompileM Operand
emitInstr ty instr = do
  v <- freshName "v"
  addInstr $ v L.:= instr
  return $ L.LocalReference ty v

addInstr :: Named Instruction -> CompileM ()
addInstr instr = modify $ setCurInstrs (instr:)

setScalarDecls :: ([NInstr] -> [NInstr]) -> CompileState -> CompileState
setScalarDecls update s = s { scalarDecls = update (scalarDecls s) }

setAllocas :: (S.Set L.Name -> S.Set L.Name) -> CompileState -> CompileState
setAllocas update s = s { allocas = update (allocas s) }

setCurInstrs :: ([NInstr] -> [NInstr]) -> CompileState -> CompileState
setCurInstrs update s = s { curInstrs = update (curInstrs s) }

setCurBlocks :: ([BasicBlock] -> [BasicBlock]) -> CompileState -> CompileState
setCurBlocks update s = s { curBlocks   = update (curBlocks s) }

setBlockName :: (L.Name -> L.Name) -> CompileState -> CompileState
setBlockName update s = s { blockName = update (blockName s) }

setFunSpecs :: (S.Set ExternFunSpec -> S.Set ExternFunSpec) -> CompileState -> CompileState
setFunSpecs update s = s { funSpecs = update (funSpecs s) }

-- === Constants ===

-- FP contractions should only lead to fewer rounding points, so we allow those
mathFlags :: L.FastMathFlags
mathFlags = L.noFastMathFlags { L.allowContract = True }

mallocFun :: ExternFunSpec
mallocFun  = ExternFunSpec "malloc_dex" charPtrTy [L.NoAlias] [] [longTy]

freeFun :: ExternFunSpec
freeFun = ExternFunSpec "free_dex" L.VoidType [] [] [charPtrTy]

charPtrTy :: L.Type
charPtrTy = L.ptr charTy

charTy :: L.Type
charTy = L.IntegerType 8

boolTy :: L.Type
boolTy = L.IntegerType 64

longTy :: L.Type
longTy = L.IntegerType 64

realTy :: L.Type
realTy = L.FloatingPointType L.DoubleFP

funTy :: L.Type -> [L.Type] -> L.Type
funTy retTy argTys = L.ptr $ L.FunctionType retTy argTys False

-- === Module building ===

makeFunction :: L.Name -> [Parameter] -> CompileM Function
makeFunction name params = do
  finishBlock (L.Ret Nothing []) "<ignored>"
  decls <- gets scalarDecls
  ~((L.BasicBlock bbname instrs term):blocksTail) <- gets (reverse . curBlocks)
  let blocks = (L.BasicBlock bbname (decls ++ instrs) term):blocksTail
  return $ L.functionDefaults
    { L.name        = name
    , L.parameters  = (params, False)
    , L.returnType  = L.VoidType
    , L.basicBlocks = blocks }

makeModule :: [L.Definition] -> CompileM L.Module
makeModule defs = do
  specs <- gets funSpecs
  return $ L.defaultModule
      { L.moduleName = "dexModule"
      , L.moduleDefinitions = defs ++ fmap externDecl (toList specs) }

makeModuleEx :: L.DataLayout -> ShortByteString -> [L.Definition] -> CompileM L.Module
makeModuleEx dataLayout triple defs = do
  specs <- gets funSpecs
  return $ L.defaultModule
      { L.moduleName = "dexModule"
      , L.moduleDefinitions = defs ++ fmap externDecl (toList specs)
      , L.moduleDataLayout = Just dataLayout
      , L.moduleTargetTriple = Just triple }

makeEntryPoint :: L.Name -> [L.Type] -> L.CallableOperand -> Function
makeEntryPoint wrapperName argTypes f = runCompileM mempty $ do
  (argParam, argOperand) <- freshParamOpPair [] (L.ptr charPtrTy)
  args <- forM (zip [0..] argTypes) $ \(i, ty) -> do
    curPtr <- gep argOperand $ litInt i
    arg <- case ty of
      L.PointerType (L.PointerType _ _) _ -> return curPtr
      L.PointerType _ _                   -> load curPtr
      _                                   -> error "Expected a pointer type"
    emitInstr ty $ L.BitCast arg ty []
  addInstr $ L.Do $ callInstr f args
  makeFunction wrapperName [argParam]

instance Pretty L.Operand where
  pretty x = pretty (show x)

instance Pretty L.Type where
  pretty x = pretty (show x)
