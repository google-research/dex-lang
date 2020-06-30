-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module JIT (impToLLVM) where

import LLVM.AST (Operand, BasicBlock, Instruction, Named, Parameter)
import qualified LLVM.AST as L
import qualified LLVM.AST.Global as L
import qualified LLVM.AST.CallingConvention as L
import qualified LLVM.AST.Type as L
import qualified LLVM.AST.Typed as L
import qualified LLVM.AST.Float as L
import qualified LLVM.AST.Constant as C
import qualified LLVM.AST.FloatingPointPredicate as L
import qualified LLVM.AST.IntegerPredicate as L

import Control.Monad
import Control.Monad.State.Strict
import Control.Monad.Reader
import Data.List (nub)
import Data.Maybe (fromJust)
import Data.ByteString.Short (toShort)
import Data.ByteString.Char8 (pack)
import Data.String
import Data.Text.Prettyprint.Doc

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
                                 , funSpecs :: [ExternFunSpec] -- TODO: use a set
                                 }

type CompileM a = ReaderT CompileEnv (State CompileState) a
data ExternFunSpec = ExternFunSpec L.Name L.Type [L.Type] deriving (Ord, Eq)

type Long = Operand
type NInstr = Named Instruction
type Function = L.Global

impToLLVM :: ImpFunction -> LLVMFunction
impToLLVM f = runCompileM mempty (compileTopProg f)

runCompileM :: CompileEnv -> CompileM a -> a
runCompileM env m = evalState (runReaderT m env) initState
  where initState = CompileState [] [] [] "start_block" mempty mempty []

compileTopProg :: ImpFunction -> CompileM LLVMFunction
compileTopProg (ImpFunction outVars inVars (ImpProg prog)) = do
  -- Set up the argument list. Note that all outputs are pointers to pointers.
  let inVarTypes  = map (        L.ptr . arrayBaseType . varAnn) inVars
  let outVarTypes = map (L.ptr . L.ptr . arrayBaseType . varAnn) outVars
  (inParams, inOperands)   <- unzip <$> mapM freshParamOpPair inVarTypes
  (outParams, outOperands) <- unzip <$> mapM freshParamOpPair outVarTypes

  -- Emit the program
  let paramEnv = newEnv inVars inOperands
  modify (\s -> s { progOutputs = zipEnv outVars outOperands })
  extendR paramEnv $ compileProg prog
  finishBlock (L.Ret Nothing []) "<ignored>"

  -- Grab the current state and construct LLVMFunction
  specs <- gets funSpecs
  decls <- gets scalarDecls
  blocks <- gets (reverse . curBlocks)
  return $ LLVMFunction numOutputs $ makeModule (outParams ++ inParams) decls blocks specs
  where
    arrayBaseType = scalarTy . scalarTableBaseType . (\(ArrayTy t) -> t)
    numOutputs = length outVars

freshParamOpPair :: L.Type -> CompileM (Parameter, Operand)
freshParamOpPair ty = do
  v <- freshName "arg"
  return (L.Parameter ty v [], L.LocalReference ty v)

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
  Alloc t numel -> Just <$> case t of
    BaseTy b | allowAlloca -> alloca b
    _  -> do
      let elemTy = scalarTy $ scalarTableBaseType t
      bytes <- mul (L.ConstantOperand $ C.ZExt (C.sizeof elemTy) longTy) =<< compileExpr numel
      malloc elemTy bytes
  Free (_:> IRefType (BaseTy _)) -> return Nothing  -- Don't free allocas
  Free v -> do
    v' <- lookupImpVar v
    ptr' <- castLPtr charTy v'
    addInstr $ L.Do (externCall freeFun [ptr'])
    return Nothing
  IOffset x _ off -> do
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

lookupImpVar :: IVar -> CompileM Operand
lookupImpVar v = asks (! v)

gep :: Operand -> Operand -> CompileM Operand
gep ptr i = emitInstr (L.typeOf ptr) $ L.GetElementPtr False ptr [i] []

finishBlock :: L.Terminator -> L.Name -> CompileM ()
finishBlock term newName = do
  oldName <- gets blockName
  instrs  <- gets curInstrs
  let newBlock = L.BasicBlock oldName (reverse instrs) (L.Do term)
  modify $ setCurBlocks (newBlock:)
         . setCurInstrs (const [])
         . setBlockName (const newName)

compileLoop :: Direction -> IVar -> Operand -> ImpProg -> CompileM ()
compileLoop d iVar n (ImpProg body) = do
  loopBlock <- freshName "loop"
  nextBlock <- freshName "cont"
  i <- alloca (Scalar IntType)
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

freshName :: Name -> CompileM L.Name
freshName v = do
  used <- gets usedNames
  let v'@(name:>_) = rename (v:>()) used
  modify $ \s -> s { usedNames = used <> v'@>() }
  return $ nameToLName name

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

operandToConst :: Operand -> C.Constant
operandToConst (L.ConstantOperand c) = c
operandToConst op = error $ "Not a constant: " ++ show op

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

-- TODO: consider getting type from instruction rather than passing it explicitly
emitInstr :: L.Type -> Instruction -> CompileM Operand
emitInstr ty instr = do
  v <- freshName "v"
  addInstr $ v L.:= instr
  return $ L.LocalReference ty v

alloca :: BaseType -> CompileM Operand
alloca ty = do
  v <- freshName "v"
  modify $ setScalarDecls ((v L.:= instr):)
  return $ L.LocalReference (L.ptr ty') v
  where ty' = scalarTy ty
        instr = L.Alloca ty' Nothing 0 []

malloc :: L.Type -> Operand -> CompileM Operand
malloc ty bytes = do
  voidPtr <- emitInstr charPtrTy (externCall mallocFun [bytes])
  castLPtr ty voidPtr

castLPtr :: L.Type -> Operand -> CompileM Operand
castLPtr ty ptr = emitInstr (L.ptr ty) $ L.BitCast ptr (L.ptr ty) []

mul :: Operand -> Operand -> CompileM Operand
mul x y = emitInstr longTy $ L.Mul False False x y []

addInstr :: Named Instruction -> CompileM ()
addInstr instr = modify $ setCurInstrs (instr:)

scalarTy :: BaseType -> L.Type
scalarTy b = case b of
  Scalar sb -> case sb of
    IntType  -> longTy
    RealType -> realTy
    BoolType -> boolTy -- Still storing in 64-bit arrays TODO: use 8 bits (or 1)
    StrType  -> error "Not implemented"
  Vector sb -> L.VectorType (fromIntegral vectorWidth) $ scalarTy $ Scalar sb

extendOneBit :: Operand -> CompileM Operand
extendOneBit x = emitInstr boolTy (L.ZExt x boolTy [])

intToBool :: Operand -> CompileM Operand
intToBool x = emitInstr (L.IntegerType 1) $ L.Trunc x (L.IntegerType 1) []

compileFFICall :: String -> L.Type -> [Operand] -> CompileM Operand
compileFFICall name retTy xs = do
  modify $ setFunSpecs (f:)
  emitInstr retTy $ externCall f xs
  where f = ExternFunSpec (L.Name (fromString name)) retTy (map L.typeOf xs)

compilePrimOp :: PrimOp Operand -> CompileM Operand
compilePrimOp (ScalarBinOp op x y) = compileBinOp op x y
compilePrimOp (VectorBinOp op x y) = compileBinOp op x y
compilePrimOp (ScalarUnOp op x) = case op of
  -- LLVM has "fneg" but it doesn't seem to be exposed by llvm-hs-pure
  FNeg      -> emitInstr realTy $ L.FSub L.noFastMathFlags (litReal 0.0) x []
  Not       -> emitInstr boolTy $ L.Xor x (litInt 1) []
  BoolToInt -> return x -- bools stored as ints
  UnsafeIntToBool -> return x -- bools stored as ints
  IntToReal -> emitInstr realTy $ L.SIToFP x realTy []
compilePrimOp (Select p x y) = do
  p' <- intToBool p
  emitInstr (L.typeOf x) $ L.Select p' x y []
compilePrimOp (FFICall name ansTy xs) =
  compileFFICall name (scalarTy ansTy) xs
compilePrimOp (VectorBroadcast x) = foldM fillElem undef [0..vectorWidth - 1]
  where
    resTy = L.VectorType (fromIntegral vectorWidth) $ L.typeOf x
    fillElem v i = emitInstr resTy $ L.InsertElement v x (litInt i) []
    undef = L.ConstantOperand $ C.Undef resTy
compilePrimOp op = error $ "Can't JIT primop: " ++ pprint op

compileBinOp :: ScalarBinOp -> Operand -> Operand -> CompileM Operand
compileBinOp op x y = case op of
  IAdd   -> emitInstr longTy $ L.Add False False x y []
  ISub   -> emitInstr longTy $ L.Sub False False x y []
  IMul   -> emitInstr longTy $ L.Mul False False x y []
  IDiv   -> emitInstr longTy $ L.SDiv False x y []
  Rem    -> emitInstr longTy $ L.SRem x y []
  FAdd   -> emitInstr realTy $ L.FAdd L.noFastMathFlags x y []
  FSub   -> emitInstr realTy $ L.FSub L.noFastMathFlags x y []
  FMul   -> emitInstr realTy $ L.FMul L.noFastMathFlags x y []
  FDiv   -> emitInstr realTy $ L.FDiv L.noFastMathFlags x y []
  And    -> emitInstr boolTy $ L.And x y []
  Or     -> emitInstr boolTy $ L.Or  x y []
  ICmp c -> emitInstr boolTy (L.ICmp (intCmpOp   c) x y []) >>= extendOneBit
  FCmp c -> emitInstr boolTy (L.FCmp (floatCmpOp c) x y []) >>= extendOneBit
  _ -> error "Not implemented"

floatCmpOp :: CmpOp -> L.FloatingPointPredicate
floatCmpOp op = case op of
  Less         -> L.OLT
  LessEqual    -> L.OLE
  Greater      -> L.OGT
  GreaterEqual -> L.OGE
  Equal        -> L.OEQ

intCmpOp :: CmpOp -> L.IntegerPredicate
intCmpOp op = case op of
  Less         -> L.SLT
  LessEqual    -> L.SLE
  Greater      -> L.SGT
  GreaterEqual -> L.SGE
  Equal        -> L.EQ

mallocFun :: ExternFunSpec
mallocFun  = ExternFunSpec "malloc_dex"    charPtrTy [longTy]

freeFun :: ExternFunSpec
freeFun = ExternFunSpec "free_dex" L.VoidType [charPtrTy]

builtinFFISpecs :: [ExternFunSpec]
builtinFFISpecs = [mallocFun, freeFun]

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

makeModule :: [Parameter] -> [NInstr] -> [BasicBlock] -> [ExternFunSpec] -> L.Module
makeModule params decls (fstBlock:blocks) userSpecs = m
  where
    L.BasicBlock name instrs term = fstBlock
    fstBlock' = L.BasicBlock name (decls ++ instrs) term
    ffiSpecs = nub $ userSpecs ++ builtinFFISpecs
    paramTypes = map L.typeOf params
    mainFun = L.functionDefaults
      { L.name        = "mainFun"
      , L.parameters  = (params, False)
      , L.returnType  = L.VoidType
      , L.basicBlocks = (fstBlock':blocks) }
    wrapperFun = wrapVariadic paramTypes $
                   callableOperand (funTy L.VoidType paramTypes) "mainFun"
    m = L.defaultModule
      { L.moduleName = "mainModule"
      , L.moduleDefinitions =
          L.GlobalDefinition mainFun
        : L.GlobalDefinition (wrapperFun { L.name = "entryFun" })
        : map externDecl ffiSpecs }
makeModule _ _ [] _ = error $ "Expected at least one block"

wrapVariadic :: [L.Type] -> L.CallableOperand -> Function
wrapVariadic argTypes f = runCompileM mempty $ do
  (argParam, argOperand) <- freshParamOpPair (L.ptr charPtrTy)
  args <- forM (zip [0..] argTypes) $ \(i, ty) -> do
    curPtr <- gep argOperand $ litInt i
    arg <- case ty of
      L.PointerType (L.PointerType _ _) _ -> return curPtr
      L.PointerType _ _                   -> load curPtr
      _                                   -> error "Expected a pointer type"
    emitInstr ty $ L.BitCast arg ty []
  addInstr $ L.Do $ callInstr f args
  instrs <- liftM reverse $ gets curInstrs
  return $ L.functionDefaults
    { L.parameters = ([argParam], False)
    , L.returnType = L.VoidType
    , L.basicBlocks = [L.BasicBlock "mainblock" instrs (L.Do (L.Ret Nothing []))] }

callableOperand :: L.Type -> L.Name -> L.CallableOperand
callableOperand ty name = Right $ L.ConstantOperand $ C.GlobalReference ty name

externCall :: ExternFunSpec -> [L.Operand] -> L.Instruction
externCall (ExternFunSpec fname retTy argTys) xs = callInstr fun xs
  where fun = callableOperand (funTy retTy argTys) fname

callInstr :: L.CallableOperand -> [L.Operand] -> L.Instruction
callInstr fun xs = L.Call Nothing L.C [] fun xs' [] []
 where xs' = [(x ,[]) | x <- xs]

externDecl :: ExternFunSpec -> L.Definition
externDecl (ExternFunSpec fname retTy argTys) =
  L.GlobalDefinition $ L.functionDefaults {
    L.name        = fname
  , L.parameters  = ([L.Parameter t (argName i) []
                     | (i, t) <- zip [0::Int ..] argTys], False)
  , L.returnType  = retTy
  , L.basicBlocks = []
  }
  where argName i = L.Name $ "arg" <> fromString (show i)

nameToLName :: Name -> L.Name
nameToLName v = L.Name (toShort $ pack (pprint v))

setScalarDecls :: ([NInstr] -> [NInstr]) -> CompileState -> CompileState
setScalarDecls update s = s { scalarDecls = update (scalarDecls s) }

setCurInstrs :: ([NInstr] -> [NInstr]) -> CompileState -> CompileState
setCurInstrs update s = s { curInstrs = update (curInstrs s) }

setCurBlocks :: ([BasicBlock] -> [BasicBlock]) -> CompileState -> CompileState
setCurBlocks update s = s { curBlocks   = update (curBlocks s) }

setBlockName :: (L.Name -> L.Name) -> CompileState -> CompileState
setBlockName update s = s { blockName = update (blockName s) }

setFunSpecs :: ([ExternFunSpec] -> [ExternFunSpec]) -> CompileState -> CompileState
setFunSpecs update s = s { funSpecs = update (funSpecs s) }

instance Pretty L.Operand where
  pretty x = pretty (show x)

instance Pretty L.Type where
  pretty x = pretty (show x)
