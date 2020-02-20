-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module JIT (evalModuleJIT) where

import LLVM.AST (Operand, BasicBlock, Instruction, Named)
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
import Data.Foldable (fold)
import Data.List (nub)
import Data.ByteString.Short (toShort)
import Data.ByteString.Char8 (pack)
import Data.String
import Data.Text.Prettyprint.Doc
import Foreign.Ptr

import Syntax
import Env
import PPrint
import Cat
import Imp
import Array
import Subst
import LLVMExec

type CompileEnv = Env Operand
data CompileState = CompileState { curBlocks   :: [BasicBlock]
                                 , curInstrs   :: [NInstr]
                                 , scalarDecls :: [NInstr]
                                 , blockName :: L.Name
                                 , usedNames :: Scope
                                 , funSpecs :: [ExternFunSpec] -- TODO: use a set
                                 }

type CompileM a = ReaderT CompileEnv (State CompileState) a
data ExternFunSpec = ExternFunSpec L.Name L.Type [L.Type] deriving (Ord, Eq)

type Long = Operand
type NInstr = Named Instruction

evalModuleJIT :: ImpModule -> IO Module
evalModuleJIT (Module ty (ImpModBody [] (ImpProg []) result)) =
  return $ Module ty $ ModBody [] result
evalModuleJIT (Module ty (ImpModBody vs prog result)) = do
  dests <- liftM fold $ mapM allocIRef vs
  let compileEnv = fmap arrayToOperand dests
  evalJit $ runCompileM compileEnv (compileTopProg prog)
  let substEnv = (fmap (L . impExprToAtom . IRef) dests, mempty)
  return $ Module ty $ ModBody [] (subst substEnv result)

allocIRef :: IVar -> IO (Env Array)
allocIRef v@(_:> IRefType (b, shape)) = do
  ref <- allocateArray b (map fromILitInt shape)
  return $ v @> ref
allocIRef _ = error "Destination should have a reference type"

-- TODO: consider making an Integral instance
fromILitInt :: IExpr -> Int
fromILitInt (ILit (IntLit x)) = x
fromILitInt expr = error $ "Not an int: " ++ pprint expr

runCompileM :: CompileEnv -> CompileM a -> a
runCompileM env m = evalState (runReaderT m env) initState
  where initState = CompileState [] [] [] "start_block" mempty []

compileTopProg :: ImpProg -> CompileM L.Module
compileTopProg prog = do
  compileProg prog
  finishBlock (L.Ret Nothing []) "<ignored>"
  specs <- gets funSpecs
  decls <- gets scalarDecls
  blocks <- gets (reverse . curBlocks)
  return $ makeModule decls blocks specs

compileProg :: ImpProg -> CompileM ()
compileProg (ImpProg []) = return ()
compileProg (ImpProg ((maybeName, instr):prog)) = do
  maybeAns <- compileInstr instr
  let env = case (maybeName, maybeAns) of
              (Nothing, Nothing)         -> mempty
              (Just v, Just ans) -> v @> ans
              _ -> error "Void mismatch"
  extendR env $ compileProg $ ImpProg prog

compileInstr :: ImpInstr -> CompileM (Maybe Operand)
compileInstr instr = case instr of
  IPrimOp op -> do
    op' <- traverseExpr op (return . scalarTy) compileExpr (return . const ())
    liftM Just $ compilePrimOp op'
  Load ref -> do
    ref' <- compileExpr ref
    liftM Just $ load ref'
  Store dest val -> do
    dest' <- compileExpr dest
    val'  <- compileExpr val
    store dest' val'
    return Nothing
  Copy dest source -> do
    let (IRefType (_, shape)) = impExprType source
    shape' <- mapM compileExpr shape
    dest'    <- compileExpr dest
    source'  <- compileExpr source
    case shape of
      [] -> do
        x <- load source'
        store dest' x
      _  -> do
        numScalars <- sizeOf shape'
        numBytes <- mul (litInt 8) numScalars
        copy numBytes dest' source'
    return Nothing
  Alloc (ty, shape) -> liftM Just $ case shape of
    [] -> alloca ty
    _  -> do
      shape' <- mapM compileExpr shape
      malloc ty shape' ""
  Free (_:> IRefType (_, [])) -> return Nothing  -- Don't free allocas
  Free v -> do
    v' <- lookupImpVar v
    ptr' <- castLPtr charTy v'
    addInstr $ L.Do (externCall freeFun [ptr'])
    return Nothing
  Loop i n body -> do
    n' <- compileExpr n
    compileLoop i n' body
    return Nothing

compileExpr :: IExpr -> CompileM Operand
compileExpr expr = case expr of
  ILit v   -> return (litVal v)
  IRef x   -> return $ arrayToOperand x
  IVar v   -> lookupImpVar v
  IGet x i -> do
    let (IRefType (_, (_:shape))) = impExprType x
    shape' <- mapM compileExpr shape
    x' <- compileExpr x
    i' <- compileExpr i
    indexPtr x' shape' i'

arrayToOperand :: Array -> Operand
arrayToOperand (Array _ b ptr) = refLiteral b ptr

lookupImpVar :: IVar -> CompileM Operand
lookupImpVar v = asks (! v)

indexPtr :: Operand -> [Operand] -> Operand -> CompileM Operand
indexPtr ptr shape i = do
  stride <- foldM mul (litInt 1) shape
  n <- mul stride i
  emitInstr (L.typeOf ptr) $ L.GetElementPtr False ptr [n] []

finishBlock :: L.Terminator -> L.Name -> CompileM ()
finishBlock term newName = do
  oldName <- gets blockName
  instrs  <- gets curInstrs
  let newBlock = L.BasicBlock oldName (reverse instrs) (L.Do term)
  modify $ setCurBlocks (newBlock:)
         . setCurInstrs (const [])
         . setBlockName (const newName)

compileLoop :: IVar -> Operand -> ImpProg -> CompileM ()
compileLoop iVar n body = do
  loopBlock <- freshName "loop"
  nextBlock <- freshName "cont"
  i <- alloca IntType
  store i (litInt 0)
  entryCond <- load i >>= (`lessThan` n)
  finishBlock (L.CondBr entryCond loopBlock nextBlock []) loopBlock
  iVal <- load i
  extendR (iVar @> iVal) $ compileProg body
  iValInc <- add iVal (litInt 1)
  store i iValInc
  loopCond <- iValInc `lessThan` n
  finishBlock (L.CondBr loopCond loopBlock nextBlock []) nextBlock

freshName :: Name -> CompileM L.Name
freshName v = do
  used <- gets usedNames
  let v'@(name:>_) = rename (v:>()) used
  modify $ \s -> s { usedNames = used <> v'@>() }
  return $ nameToLName name

copy :: Operand -> Operand -> Operand -> CompileM ()
copy numBytes dest src = do
  src'  <- castLPtr charTy src
  dest' <- castLPtr charTy dest
  addInstr $ L.Do (externCall memcpyFun [dest', src', numBytes])

refLiteral :: BaseType -> Ptr () -> Operand
refLiteral ty ptr = L.ConstantOperand $ C.IntToPtr (C.Int 64 ptrAsInt) (L.ptr (scalarTy ty))
   where ptrAsInt = fromIntegral $ ptrToWordPtr ptr

litVal :: LitVal -> Operand
litVal lit = case lit of
  IntLit  x -> litInt x
  RealLit x -> litReal x
  BoolLit True  -> litInt 1
  BoolLit False -> litInt 0
  StrLit _ -> error "Not implemented"

litInt :: Int -> Operand
litInt x = L.ConstantOperand $ C.Int 64 (fromIntegral x)

litReal :: Double -> Operand
litReal x = L.ConstantOperand $ C.Float $ L.Double x

store :: Operand -> Operand -> CompileM ()
store ptr x =  addInstr $ L.Do $ L.Store False ptr x Nothing 0 []

load :: Operand -> CompileM Operand
load ptr = emitInstr valTy $ L.Load False ptr Nothing 0 []
  where (L.PointerType valTy _) = L.typeOf ptr

lessThan :: Long -> Long -> CompileM Long
lessThan x y = emitInstr longTy $ L.ICmp L.SLT x y []

add :: Long -> Long -> CompileM Long
add x y = emitInstr longTy $ L.Add False False x y []

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

malloc :: BaseType -> [Operand] -> Tag -> CompileM Operand
malloc ty shape _ = do
    size <- sizeOf shape
    n <- mul (litInt 8) size
    voidPtr <- emitInstr charPtrTy (externCall mallocFun [n])
    castLPtr (scalarTy ty) voidPtr

castLPtr :: L.Type -> Operand -> CompileM Operand
castLPtr ty ptr = emitInstr (L.ptr ty) $ L.BitCast ptr (L.ptr ty) []

sizeOf :: [Operand] -> CompileM Operand
sizeOf shape = foldM mul (litInt 1) shape

mul :: Operand -> Operand -> CompileM Operand
mul x y = emitInstr longTy $ L.Mul False False x y []

addInstr :: Named Instruction -> CompileM ()
addInstr instr = modify $ setCurInstrs (instr:)

scalarTy :: BaseType -> L.Type
scalarTy ty = case ty of
  IntType  -> longTy
  RealType -> realTy
  BoolType -> boolTy -- Still storing in 64-bit arrays TODO: use 8 bits (or 1)
  StrType  -> error "Not implemented"

extendOneBit :: Operand -> CompileM Operand
extendOneBit x = emitInstr boolTy (L.ZExt x boolTy [])

compileFFICall :: String -> [L.Type] -> L.Type -> [Operand] -> CompileM Operand
compileFFICall name argTys retTy xs = do
  modify $ setFunSpecs (f:)
  emitInstr retTy $ externCall f xs
  where f = ExternFunSpec (L.Name (fromString name)) retTy argTys

compilePrimOp :: PrimOp L.Type Operand () -> CompileM Operand
compilePrimOp (ScalarBinOp op x y) = case op of
  IAdd   -> emitInstr longTy $ L.Add False False x y []
  ISub   -> emitInstr longTy $ L.Sub False False x y []
  IMul   -> emitInstr longTy $ L.Mul False False x y []
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
compilePrimOp (ScalarUnOp op x) = case op of
  -- LLVM has "fneg" but it doesn't seem to be exposed by llvm-hs-pure
  FNeg      -> emitInstr realTy $ L.FSub L.noFastMathFlags (litReal 0.0) x []
  Not       -> emitInstr boolTy $ L.Xor x (litInt 1) []
  BoolToInt -> return x -- bools stored as ints
  IntToReal -> emitInstr realTy $ L.SIToFP x realTy []
  _ -> error "Not implemented"
compilePrimOp (Select ty p x y) = do
  p' <- emitInstr (L.IntegerType 1) $ L.Trunc p (L.IntegerType 1) []
  emitInstr ty $ L.Select p' x y []
compilePrimOp (FFICall name argTys ansTy xs) =
  compileFFICall name argTys ansTy xs
compilePrimOp op = error $ "Can't JIT primop: " ++ pprint op

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
freeFun = ExternFunSpec "free_dex"      charPtrTy [charPtrTy]

memcpyFun :: ExternFunSpec
memcpyFun  = ExternFunSpec "memcpy_dex" L.VoidType [charPtrTy, charPtrTy, longTy]

builtinFFISpecs :: [ExternFunSpec]
builtinFFISpecs = [mallocFun, freeFun, memcpyFun]

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

makeModule :: [NInstr] -> [BasicBlock] -> [ExternFunSpec] -> L.Module
makeModule decls (fstBlock:blocks) userSpecs = m
  where
    L.BasicBlock name instrs term = fstBlock
    fstBlock' = L.BasicBlock name (decls ++ instrs) term
    ffiSpecs = nub $ userSpecs ++ builtinFFISpecs
    m = L.defaultModule
      { L.moduleName = "test"
      , L.moduleDefinitions = L.GlobalDefinition fundef : map externDecl ffiSpecs }
    fundef = L.functionDefaults
      { L.name        = L.Name "thefun"
      , L.parameters  = ([], False)
      , L.returnType  = L.VoidType
      , L.basicBlocks = (fstBlock':blocks) }
makeModule _ [] _ = error $ "Expected at least one block"

externCall :: ExternFunSpec -> [L.Operand] -> L.Instruction
externCall (ExternFunSpec fname retTy argTys) xs =
  L.Call Nothing L.C [] fun xs' [] []
  where fun = Right $ L.ConstantOperand $ C.GlobalReference
                         (funTy retTy argTys) fname
        xs' = [(x ,[]) | x <- xs]

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
