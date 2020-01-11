-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE OverloadedStrings #-}

module JIT (jitPass) where

import LLVM.AST (Operand, BasicBlock, Instruction, Module, Named)
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
import Data.Void
import Data.List (nub)
import Data.Time.Clock (getCurrentTime, diffUTCTime)
import Data.ByteString.Short (toShort)
import Data.ByteString.Char8 (pack)
import Data.String
import Foreign.Ptr

import Syntax
import Env
import Pass
import Fresh hiding (freshName)
import PPrint
import Cat
import Imp
import Serialize
import Subst

import LLVMExec

type CompileEnv = Env Operand
type CompileEnvTop = Env IVal
data CompileState = CompileState { curBlocks   :: [BasicBlock]
                                 , curInstrs   :: [NInstr]
                                 , scalarDecls :: [NInstr]
                                 , blockName :: L.Name
                                 , funSpecs :: [ExternFunSpec] -- TODO: use a set
                                 }

type CompileM a = ReaderT CompileEnv (StateT CompileState (FreshT (Either Err))) a
data CompiledProg = CompiledProg Module
data ExternFunSpec = ExternFunSpec L.Name L.Type [L.Type] deriving (Ord, Eq)

type Long = Operand
type NInstr = Named Instruction

jitPass :: TopPass ImpDecl Void
jitPass = TopPass jitPass'

jitPass' :: ImpDecl -> TopPassM CompileEnvTop [Void]
jitPass' decl = case decl of
  ImpTopLet bs prog -> do
    env <- look
    let bs' = map (fmap (substIType env)) bs
    xs <- evalProg bs' prog
    xs' <- liftIO $ mapM loadIfScalar xs
    extend $ bindFold $ zipWith replaceAnnot bs' xs'
    emitOutput NoOutput
  ImpEvalCmd (Command cmd (ty, bs, prog)) -> do
    env <- look
    let bs' = map (fmap (substIType env)) bs
    let ty' = substTyTop env ty
    case cmd of
      ShowLLVM -> do
        (_, CompiledProg m) <- toLLVM bs' prog
        llvm <- liftIO $ showLLVM m
        emitOutput $ TextOut llvm
      ShowAsm -> do
        (_, CompiledProg m) <- toLLVM bs' prog
        asm <- liftIO $ showAsm m
        emitOutput $ TextOut asm
      EvalExpr fmt -> do
        impRefs <- evalProg bs' prog
        arrays <- liftIO $ mapM (loadArray . fromIRef) impRefs
        emitOutput $ ValOut fmt (FlatVal ty' arrays)
      TimeIt -> do
        t1 <- liftIO getCurrentTime
        _ <- evalProg bs' prog
        t2 <- liftIO getCurrentTime
        emitOutput $ TextOut $ show (t2 `diffUTCTime` t1)
      Dump fmt s -> do
        impRefs <- evalProg bs' prog
        let val = FlatVal ty' (map fromIRef impRefs)
        liftIO (dumpDataFile s fmt val)
        emitOutput NoOutput
      _ -> error $ "Unexpected command: " ++ show cmd

evalProg :: [IBinder] -> ImpProg -> TopPassM CompileEnvTop [IVal]
evalProg bs prog = do
  (cells, CompiledProg m) <- toLLVM bs prog
  liftIO $ evalJit m
  return cells

-- TODO: pass destinations as args rather than baking pointers into LLVM
toLLVM :: [IBinder] -> ImpProg -> TopPassM CompileEnvTop ([IVal], CompiledProg)
toLLVM bs prog = do
  env <- look
  destCells <- liftIO $ mapM allocIRef bs
  -- TODO just substitute top env up-front instead
  let env' = fmap iValAsOperand $ env <> bindFold destCells
  let initState = CompileState [] [] [] "start_block" []
  prog' <- liftExceptTop $ flip runFreshT mempty $ flip evalStateT initState $
                flip runReaderT env' $ compileTopProg prog
  return (map binderAnn destCells, prog')

allocIRef :: IBinder -> IO (BinderP IVal)
allocIRef (v :> IRefType (b, shape)) = do
  ref <- allocateArray b (map fromILitInt shape)
  return $ v :> IRef ref
allocIRef _ = error "Destination should have a reference type"

-- TODO: consider distinguishing sizes from ints in Imp
substTyTop :: CompileEnvTop -> Type -> Type
substTyTop env ty = subst (envMapMaybe iValToType env, mempty) ty
   where
     iValToType :: IExpr -> Maybe (LorT a Type)
     iValToType expr = case expr of
       ILit (IntLit n) -> Just (T (IdxSetLit n))
       _               -> Nothing

fromIRef :: IVal -> ArrayRef
fromIRef (IRef x) = x
fromIRef v = error $ "Not an iref " ++ pprint v

loadIfScalar :: IVal -> IO IVal
loadIfScalar val@(IRef (Array shape ref)) = case shape of
  [] -> liftM (ILit . readScalar) $ loadArray (Array [] ref)
  _  -> return val
loadIfScalar _ = error "Expected reference"

-- TODO: consider making an Integral instance
fromILitInt :: IExpr -> Int
fromILitInt (ILit (IntLit x)) = x
fromILitInt expr = error $ "Not an int: " ++ pprint expr

compileTopProg :: ImpProg -> CompileM CompiledProg
compileTopProg prog = do
  compileProg prog
  finishBlock (L.Ret Nothing []) "<ignored>"
  specs <- gets funSpecs
  decls <- gets scalarDecls
  blocks <- gets (reverse . curBlocks)
  return $ CompiledProg (makeModule decls blocks specs)

compileProg :: ImpProg -> CompileM ()
compileProg (ImpProg []) = return ()
compileProg (ImpProg ((maybeName, instr):prog)) = do
  maybeAns <- compileInstr instr
  let env = case (maybeName, maybeAns) of
              (Nothing, Nothing)         -> mempty
              (Just (name:>_), Just ans) -> name @> ans
              _ -> error "Void mismatch"
  extendR env $ compileProg $ ImpProg prog

compileInstr :: ImpInstr -> CompileM (Maybe Operand)
compileInstr instr = case instr of
  IPrimOp b tys xs -> do
    xs' <- mapM compileExpr xs
    liftM Just $ compileBuiltin b tys xs'
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
    [] -> alloca ty ""
    _  -> do
      shape' <- mapM compileExpr shape
      malloc ty shape' ""
  Free v ty -> do
    v' <- lookupImpVar v
    case ty of
      (_, []) -> return Nothing  -- Don't free allocas
      _ -> do
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
  IRef (Array _ ptr) -> return (vecRefToOperand ptr)
  IVar v _ -> lookupImpVar v
  IGet x i -> do
    let (IRefType (_, (_:shape))) = impExprType x
    shape' <- mapM compileExpr shape
    x' <- compileExpr x
    i' <- compileExpr i
    indexPtr x' shape' i'

vecRefToOperand :: VecRef -> Operand
vecRefToOperand ref = refLiteral b ptr
  where (_, b, ptr) = vecRefInfo ref

lookupImpVar :: Name -> CompileM Operand
lookupImpVar v = asks (! v)

indexPtr :: Operand -> [Operand] -> Operand -> CompileM Operand
indexPtr ptr shape i = do
  stride <- foldM mul (litInt 1) shape
  n <- mul stride i
  emitInstr "ptr" (L.typeOf ptr) $ L.GetElementPtr False ptr [n] []

finishBlock :: L.Terminator -> L.Name -> CompileM ()
finishBlock term newName = do
  oldName <- gets blockName
  instrs  <- gets curInstrs
  let newBlock = L.BasicBlock oldName (reverse instrs) (L.Do term)
  modify $ setCurBlocks (newBlock:)
         . setCurInstrs (const [])
         . setBlockName (const newName)

compileLoop :: Name -> Operand -> ImpProg -> CompileM ()
compileLoop iVar n body = do
  loopBlock <- freshName "loop"
  nextBlock <- freshName "cont"
  i <- alloca IntType "i"
  store i (litInt 0)
  entryCond <- load i >>= (`lessThan` n)
  finishBlock (L.CondBr entryCond loopBlock nextBlock []) loopBlock
  iVal <- load i
  extendR (iVar @> iVal) $ compileProg body
  iValInc <- add iVal (litInt 1)
  store i iValInc
  loopCond <- iValInc `lessThan` n
  finishBlock (L.CondBr loopCond loopBlock nextBlock []) nextBlock

freshName :: Tag -> CompileM L.Name
freshName s = do
  name <- fresh s'
  return $ nameToLName name
  where s' = case s of "" -> "v"
                       _  -> s

copy :: Operand -> Operand -> Operand -> CompileM ()
copy numBytes dest src = do
  src'  <- castLPtr charTy src
  dest' <- castLPtr charTy dest
  addInstr $ L.Do (externCall memcpyFun [dest', src', numBytes])

iValAsOperand :: IVal -> Operand
iValAsOperand val = case val of
  ILit x             -> litVal x
  IRef (Array _ ref) -> vecRefToOperand ref
  _ -> error $ "Not a value: " ++ pprint val

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
load ptr = emitInstr "" valTy $ L.Load False ptr Nothing 0 []
  where (L.PointerType valTy _) = L.typeOf ptr

lessThan :: Long -> Long -> CompileM Long
lessThan x y = emitInstr "lt" longTy $ L.ICmp L.SLT x y []

add :: Long -> Long -> CompileM Long
add x y = emitInstr "add" longTy $ L.Add False False x y []

-- TODO: consider getting type from instruction rather than passing it explicitly
emitInstr :: Tag -> L.Type -> Instruction -> CompileM Operand
emitInstr s ty instr = do
  v <- freshName s
  addInstr $ v L.:= instr
  return $ L.LocalReference ty v

alloca :: BaseType -> Tag -> CompileM Operand
alloca ty s = do
  v <- freshName s
  modify $ setScalarDecls ((v L.:= instr):)
  return $ L.LocalReference (L.ptr ty') v
  where ty' = scalarTy ty
        instr = L.Alloca ty' Nothing 0 []

malloc :: BaseType -> [Operand] -> Tag -> CompileM Operand
malloc ty shape _ = do
    size <- sizeOf shape
    n <- mul (litInt 8) size
    voidPtr <- emitInstr "" charPtrTy (externCall mallocFun [n])
    castLPtr (scalarTy ty) voidPtr

castLPtr :: L.Type -> Operand -> CompileM Operand
castLPtr ty ptr = emitInstr "ptrcast" (L.ptr ty) $ L.BitCast ptr (L.ptr ty) []

sizeOf :: [Operand] -> CompileM Operand
sizeOf shape = foldM mul (litInt 1) shape

mul :: Operand -> Operand -> CompileM Operand
mul x y = emitInstr "mul" longTy $ L.Mul False False x y []

addInstr :: Named Instruction -> CompileM ()
addInstr instr = modify $ setCurInstrs (instr:)

scalarTy :: BaseType -> L.Type
scalarTy ty = case ty of
  IntType  -> longTy
  RealType -> realTy
  BoolType -> boolTy -- Still storing in 64-bit arrays TODO: use 8 bits (or 1)
  StrType  -> error "Not implemented"

extendOneBit :: Operand -> CompileM Operand
extendOneBit x = emitInstr "" boolTy (L.ZExt x boolTy [])

compileFFICall :: Tag -> [BaseType] -> [Operand] -> CompileM Operand
compileFFICall name tys xs = do
  modify $ setFunSpecs (f:)
  emitInstr name retTy $ externCall f xs
  where
    retTy:argTys = map scalarTy tys
    f = ExternFunSpec (L.Name (fromString (tagToStr name))) retTy argTys

compileBuiltin :: Builtin -> [BaseType] -> [Operand] -> CompileM Operand
compileBuiltin IAdd [] [x, y] = emitInstr "" longTy $ L.Add False False x y []
compileBuiltin ISub [] [x, y] = emitInstr "" longTy $ L.Sub False False x y []
compileBuiltin IMul [] [x, y] = emitInstr "" longTy $ L.Mul False False x y []
compileBuiltin Rem  [] [x, y] = emitInstr "" longTy $ L.SRem x y []
compileBuiltin FAdd [] [x, y] = emitInstr "" realTy $ L.FAdd L.noFastMathFlags x y []
compileBuiltin FSub [] [x, y] = emitInstr "" realTy $ L.FSub L.noFastMathFlags x y []
compileBuiltin FMul [] [x, y] = emitInstr "" realTy $ L.FMul L.noFastMathFlags x y []
compileBuiltin FDiv [] [x, y] = emitInstr "" realTy $ L.FDiv L.noFastMathFlags x y []
  -- LLVM has "fneg" but it doesn't seem to be exposed by llvm-hs-pure
compileBuiltin FNeg [] [x] = emitInstr "" realTy $ L.FSub L.noFastMathFlags (litReal 0.0) x []
compileBuiltin (Cmp op) [IntType]  [x, y] = emitInstr "" boolTy (L.ICmp (intCmpOp   op) x y []) >>= extendOneBit
compileBuiltin (Cmp op) [RealType] [x, y] = emitInstr "" boolTy (L.FCmp (floatCmpOp op) x y []) >>= extendOneBit
compileBuiltin And [] [x, y] = emitInstr "" boolTy $ L.And x y []
compileBuiltin Or  [] [x, y] = emitInstr "" boolTy $ L.Or  x y []
compileBuiltin Not [] [x]    = emitInstr "" boolTy $ L.Xor x (litInt 1) []
compileBuiltin Select [ty] [p, x, y] = do
  p' <- emitInstr "" (L.IntegerType 1) $ L.Trunc p (L.IntegerType 1) []
  emitInstr "" (scalarTy ty) $ L.Select p' x y []
compileBuiltin BoolToInt [] [x] = return x -- bools stored as ints
compileBuiltin IntToReal [] [x] = emitInstr "" realTy $ L.SIToFP x realTy []
compileBuiltin (FFICall _ name) ts xs = compileFFICall (fromString name) ts xs
compileBuiltin Todo _ _ = throw MiscErr "Can't compile 'todo'"
compileBuiltin b ts _ = error $ "Can't JIT primop: " ++ pprint (b, ts)

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

makeModule :: [NInstr] -> [BasicBlock] -> [ExternFunSpec] -> Module
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
