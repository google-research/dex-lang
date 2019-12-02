-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE OverloadedStrings #-}

module JIT (jitPass) where

import LLVM.AST hiding (Type, Add, Mul, Sub, FAdd, FSub, FMul, FDiv, Name, Select, dest)
import qualified LLVM.AST as L
import qualified LLVM.AST.Global as L
import qualified LLVM.AST.CallingConvention as L
import qualified LLVM.AST.Type as L
import qualified LLVM.AST.Float as L
import qualified LLVM.AST.Constant as C
import qualified LLVM.AST.IntegerPredicate as L
import qualified LLVM.AST.FloatingPointPredicate as L

import Control.Monad
import Control.Monad.State.Strict
import Control.Monad.Reader
import Control.Applicative (liftA, liftA2)

import Data.Void
import Data.List (nub)
import Data.Traversable
import Data.Time.Clock (getCurrentTime, diffUTCTime)

import Data.ByteString.Short (toShort)
import Data.ByteString.Char8 (pack)
import Data.String
import Data.Word (Word64)

import Data.Binary.IEEE754 (wordToDouble)

import Type
import Syntax
import Env
import Pass
import Fresh hiding (freshName)
import PPrint
import Cat

import LLVMExec

-- TODO: figure out whether we actually need type everywhere here
data Ptr w = Ptr w BaseType  deriving (Show)

data JitVal w = ScalarVal w BaseType
              | ArrayVal (Ptr w) [w]  deriving (Show)

data PCell w = Cell (Ptr w) [w]
type Cell        = PCell Operand
type PersistCell = PCell Word64

type CompileVal  = JitVal Operand
type PersistVal  = JitVal Word64
type PersistEnv = Env PersistVal
type ImpVarEnv = Env (Either CompileVal Cell)

data CompileState = CompileState { curBlocks   :: [BasicBlock]
                                 , curInstrs   :: [NInstr]
                                 , scalarDecls :: [NInstr]
                                 , blockName :: L.Name
                                 , funSpecs :: [ExternFunSpec] -- TODO: use a set
                                 }

type CompileM a = ReaderT ImpVarEnv (StateT CompileState (FreshT (Either Err))) a
data CompiledProg = CompiledProg Module
data ExternFunSpec = ExternFunSpec L.Name L.Type [L.Type] deriving (Ord, Eq)

type Long = Operand
type NInstr = Named Instruction

jitPass :: TopPass ImpDecl Void
jitPass = TopPass jitPass'

jitPass' :: ImpDecl -> TopPassM PersistEnv Void
jitPass' decl = case decl of
  ImpTopLet bs prog -> do
    vals <- evalProg bs prog
    extend $ bindFold $ zipWith replaceAnnot bs vals
    emitOutput NoOutput
  ImpEvalCmd cont bs (Command cmd prog) -> case cmd of
    ShowLLVM -> do
      (_, CompiledProg m) <- toLLVM bs prog
      llvm <- liftIO $ showLLVM m
      emitOutput $ TextOut llvm
    ShowAsm -> do
      (_, CompiledProg m) <- toLLVM bs prog
      asm <- liftIO $ showAsm m
      emitOutput $ TextOut asm
    EvalExpr fmt -> do
      vals <- evalProg bs prog
      vecs <- liftIO $ mapM asVec vals
      env <- look
      let tenv = flip envMapMaybe env $ \v ->
                   case v of
                 ScalarVal w _ -> Just (fromIntegral w)
                 _ -> Nothing
      emitOutput $ ValOut fmt $ cont tenv vecs
    TimeIt -> do
      t1 <- liftIO getCurrentTime
      _ <- evalProg bs prog
      t2 <- liftIO getCurrentTime
      emitOutput $ TextOut $ show (t2 `diffUTCTime` t1)
    _ -> error $ "Unexpected command: " ++ show cmd

evalProg :: [IBinder] -> ImpProg -> TopPassM PersistEnv [PersistVal]
evalProg bs prog = do
  (cells, CompiledProg m) <- toLLVM bs prog
  liftIO $ evalJit m
  liftIO $ mapM readPersistCell cells

-- This doesn't work with types derived from existentials, because the
-- existentially quantified variable isn't in scope yet
makeDestCell :: PersistEnv -> IBinder -> IO (BinderP PersistCell)
makeDestCell env (v :> IType ty shape) = do
  ptr <- liftM ptrAsWord $ mallocBytes $ fromIntegral $ 8 * product shape'
  return $ v :> Cell (Ptr ptr ty) shape'
  where
    getSize size = case size of
      IVar v' -> scalarVal (env ! v')
      ILit (IntLit n) -> fromIntegral n
      _ -> error $ "Not a valid size: " ++ pprint size
    shape' = map getSize shape

-- TODO: pass destinations as args rather than baking pointers into LLVM
toLLVM :: [IBinder] -> ImpProg -> TopPassM PersistEnv ([PersistCell], CompiledProg)
toLLVM bs prog = do
  env <- look
  destCells <- liftIO $ mapM (makeDestCell env) bs
  let env' =    fmap (Left  . asCompileVal) env
             <> fmap (Right . asCompileCell) (bindFold destCells)
  let initState = CompileState [] [] [] "start_block" []
  prog' <- liftExceptTop $ flip runFreshT mempty $ flip evalStateT initState $
                flip runReaderT env' $ compileTopProg prog
  return (map binderAnn destCells, prog')

asCompileVal :: PersistVal -> CompileVal
asCompileVal (ScalarVal word ty) = ScalarVal (constOperand ty word) ty
asCompileVal (ArrayVal ptr shape) = ArrayVal (ptrLiteral ptr) shape'
  where shape' = map (constOperand IntType) shape

asCompileCell :: PersistCell -> Cell
asCompileCell (Cell ptr shape) = Cell (ptrLiteral ptr) shape'
  where shape' = map (constOperand IntType) shape

ptrLiteral :: Ptr Word64 -> Ptr Operand
ptrLiteral (Ptr ptr ty) = Ptr ptr' ty
  where ptr' = L.ConstantOperand $
                  C.IntToPtr (C.Int 64 (fromIntegral ptr)) (L.ptr (scalarTy ty))

readPersistCell :: PersistCell -> IO PersistVal
readPersistCell (Cell (Ptr ptr ty) []) = do [word] <- readPtrs 1 (wordAsPtr ptr)
                                            return $ ScalarVal word ty
readPersistCell (Cell p shape) = return $ ArrayVal p shape

asVec :: PersistVal -> IO Vec
asVec v = case v of
  ScalarVal x ty ->  return $ cast ty [x]
  ArrayVal (Ptr ptr ty) shape -> do
    let size = fromIntegral $ foldr (*) 1 shape
    xs <- readPtrs size (wordAsPtr ptr)
    return $ cast ty xs
  where cast IntType  xs = IntVec $ map fromIntegral xs
        cast BoolType xs = IntVec $ map fromIntegral xs
        cast RealType xs = RealVec $ map interpret_ieee_64 xs
        cast StrType _ = error "Not implemented"

-- From the data-binary-ieee754 package; is there a more standard way
-- to do this?  This is also janky because we are just assuming that
-- LLVM stores its floats in the ieee format.
interpret_ieee_64 :: Word64 -> Double
interpret_ieee_64 = wordToDouble

constOperand :: BaseType -> Word64 -> Operand
constOperand IntType  x = litInt (fromIntegral x)
constOperand RealType x = litReal (interpret_ieee_64 x)
constOperand BoolType _ = error "Not implemented"
constOperand StrType  _ = error "Not implemented"

compileTopProg :: ImpProg -> CompileM CompiledProg
compileTopProg prog = do
  compileProg prog
  finishBlock (L.Ret Nothing []) "<ignored>"
  specs <- gets funSpecs
  decls <- gets scalarDecls
  blocks <- gets (reverse . curBlocks)
  return $ CompiledProg (makeModule decls blocks specs)

compileProg :: ImpProg -> CompileM ()
compileProg (ImpProg statements) = mapM_ compileStatement statements

compileStatement :: Statement -> CompileM ()
compileStatement statement = case statement of
  Update v idxs b tys exprs -> do
    vals <- mapM compileExpr exprs
    cell <- lookupCellVar v
    idxs' <- mapM compileExpr idxs
    cell' <- idxCell cell idxs'
    outVal <- case b of Copy -> let [val] = vals in return val
                        _ -> compileBuiltin b tys vals
    writeCell cell' outVal
  Alloc (v :> IType b shape) body -> do
    shape' <- mapM compileExpr shape
    cell <- allocate b shape' (nameTag v)
    extendR (v @> Right cell) (compileProg body)
    free cell
  Loop i n body -> do n' <- compileExpr n
                      compileLoop i n' body

compileExpr :: IExpr -> CompileM CompileVal
compileExpr expr = case expr of
  ILit v -> return $ ScalarVal (litVal v) (litType v)
  IVar v -> do x <- lookupImpVar v
               case x of
                 Left val -> return val
                 Right cell@(Cell ptr shape) -> case shape of
                    [] -> readScalarCell cell
                    _  -> return $ ArrayVal ptr shape
  IGet v i -> do ~(ArrayVal ptr (_:shape)) <- compileExpr v
                 ~(ScalarVal i' _) <- compileExpr i
                 ptr'@(Ptr _ ty) <- indexPtr ptr shape i'
                 case shape of
                   [] -> do x <- load ptr'
                            return $ ScalarVal x ty
                   _  -> return $ ArrayVal ptr' shape

lookupImpVar :: Name -> CompileM (Either CompileVal Cell)
lookupImpVar v = asks (! v)

readScalarCell :: Cell -> CompileM CompileVal
readScalarCell (Cell ptr@(Ptr _ ty) []) = do op <- load ptr
                                             return $ ScalarVal op ty
readScalarCell _ = error "Not a scalar cell"

lookupCellVar :: Name -> CompileM Cell
lookupCellVar v = do { ~(Right cell) <- lookupImpVar v; return cell }

indexPtr :: Ptr Operand -> [Operand] -> Operand -> CompileM (Ptr Operand)
indexPtr (Ptr ptr ty) shape i = do
  stride <- foldM mul (litInt 1) shape
  n <- mul stride i
  ptr' <- evalInstr "ptr" (L.ptr (scalarTy ty)) $ L.GetElementPtr False ptr [n] []
  return (Ptr ptr' ty)

finishBlock :: L.Terminator -> L.Name -> CompileM ()
finishBlock term newName = do
  oldName <- gets blockName
  instrs  <- gets curInstrs
  let newBlock = L.BasicBlock oldName (reverse instrs) (L.Do term)
  modify $ setCurBlocks (newBlock:)
         . setCurInstrs (const [])
         . setBlockName (const newName)

compileLoop :: Name -> CompileVal -> ImpProg -> CompileM ()
compileLoop iVar (ScalarVal n _) body = do
  loopBlock <- freshName "loop"
  nextBlock <- freshName "cont"
  Cell i _ <- alloca IntType "i"
  store i (litInt 0)
  entryCond <- load i >>= (`lessThan` n)
  finishBlock (L.CondBr entryCond loopBlock nextBlock []) loopBlock
  iVal <- load i
  extendR (iVar @> (Left $ ScalarVal iVal IntType)) $
    compileProg body
  iValInc <- add iVal (litInt 1)
  store i iValInc
  loopCond <- iValInc `lessThan` n
  finishBlock (L.CondBr loopCond loopBlock nextBlock []) nextBlock
compileLoop _ (ArrayVal _ _) _ = error "Array-valued loop max"

freshName :: Tag -> CompileM L.Name
freshName s = do name <- fresh s
                 return $ nameToLName name

idxCell :: Cell -> [CompileVal] -> CompileM Cell
idxCell cell [] = return cell
idxCell (Cell ptr (_:shape)) (i:idxs) = do
  size <- sizeOf shape
  step <- mul size (scalarVal i)
  ptr' <- addPtr ptr step
  idxCell (Cell ptr' shape) idxs
idxCell _ _ = error "Index mismatch"

writeCell :: Cell -> CompileVal -> CompileM ()
writeCell (Cell ptr []) (ScalarVal x _) = store ptr x
writeCell (Cell (Ptr dest _) shape) (ArrayVal (Ptr src _) _) = do
  numScalars <- sizeOf shape
  numBytes <- mul (litInt 8) numScalars
  src'  <- castPtr charTy src
  dest' <- castPtr charTy dest
  addInstr $ L.Do (externCall memcpyFun [dest', src', numBytes])
writeCell _ _ = error $ "Bad value type for cell"

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

store :: Ptr Operand -> Operand -> CompileM ()
store (Ptr ptr _) x =  addInstr $ L.Do $ L.Store False ptr x Nothing 0 []

load :: Ptr Operand -> CompileM Operand
load (Ptr ptr ty) = evalInstr "" (scalarTy ty) $ L.Load False ptr Nothing 0 []

lessThan :: Long -> Long -> CompileM Long
lessThan x y = evalInstr "lt" longTy $ L.ICmp L.SLT x y []

add :: Long -> Long -> CompileM Long
add x y = evalInstr "add" longTy $ L.Add False False x y []

evalInstr :: Tag -> L.Type -> Instruction -> CompileM Operand
evalInstr s ty instr = do
  v <- freshName s'
  addInstr $ v L.:= instr
  return $ L.LocalReference ty v
  where s' = case s of "" -> "v"
                       _  -> s

addPtr :: Ptr Operand -> Long -> CompileM (Ptr Operand)
addPtr (Ptr ptr ty) i = do ptr' <- evalInstr "ptr" (L.ptr (scalarTy ty)) instr
                           return $ Ptr ptr' ty
  where instr = L.GetElementPtr False ptr [i] []

alloca :: BaseType -> Tag -> CompileM Cell
alloca ty s = do v <- freshName s
                 modify $ setScalarDecls ((v L.:= instr):)
                 return $ Cell (Ptr (L.LocalReference (L.ptr ty') v) ty) []
  where ty' = scalarTy ty
        instr = L.Alloca ty' Nothing 0 []

malloc :: BaseType -> [CompileVal] -> Tag -> CompileM Cell
malloc ty shape _ = do
    size <- sizeOf shape'
    n <- mul (litInt 8) size
    voidPtr <- evalInstr "" charPtrTy (externCall mallocFun [n])
    ptr <- castPtr ty' voidPtr
    return $ Cell (Ptr ptr ty) shape'
  where shape' = map scalarVal shape
        ty' = scalarTy ty

allocate :: BaseType -> [CompileVal] -> Tag -> CompileM Cell
allocate b shape s = case shape of [] -> alloca b s
                                   _ -> malloc b shape s

free :: Cell -> CompileM ()
free (Cell (Ptr ptr _) shape) =
  case shape of
    [] -> return ()
    _  -> do ptr' <- castPtr charTy ptr
             addInstr $ L.Do (externCall freeFun [ptr'])

castPtr :: L.Type -> Operand -> CompileM Operand
castPtr ty ptr = evalInstr "ptrcast" (L.ptr ty) $ L.BitCast ptr (L.ptr ty) []

sizeOf :: [Operand] -> CompileM Operand
sizeOf shape = foldM mul (litInt 1) shape

mul :: Operand -> Operand -> CompileM Operand
mul x y = evalInstr "mul" longTy $ L.Mul False False x y []

scalarVal :: JitVal a -> a
scalarVal (ScalarVal x _) = x
scalarVal (ArrayVal _ _) = error "Not a scalar val"

addInstr :: Named Instruction -> CompileM ()
addInstr instr = modify $ setCurInstrs (instr:)

scalarTy :: BaseType -> L.Type
scalarTy ty = case ty of
  IntType  -> longTy
  RealType -> realTy
  BoolType -> boolTy -- Still storing in 64-bit arrays TODO: use 8 bits (or 1)
  StrType -> error "Not implemented"

compileBinop :: BaseType -> (Operand -> Operand -> L.Instruction)
                -> [CompileVal]
                -> CompileM CompileVal
compileBinop ty makeInstr [ScalarVal x _, ScalarVal y _] =
  liftM (flip ScalarVal ty) $ evalInstr "" (scalarTy ty) (makeInstr x y)
compileBinop _ _ xs = error $ "Bad args: " ++ show xs

compileUnop :: BaseType -> (Operand -> L.Instruction)
                -> [CompileVal]
                -> CompileM CompileVal
compileUnop ty makeInstr [ScalarVal x _] =
  liftM (flip ScalarVal ty) $ evalInstr "" (scalarTy ty) (makeInstr x)
compileUnop _ _ xs = error $ "Bad args: " ++ show xs

compileFCmp :: L.FloatingPointPredicate -> [CompileVal] -> CompileM CompileVal
compileFCmp p ~[ScalarVal x _, ScalarVal y _] = do
  boolResult <- evalInstr "" (L.IntegerType 1) (L.FCmp p x y [])
  intResult <- evalInstr "" boolTy (L.ZExt boolResult boolTy [])
  return $ ScalarVal intResult BoolType

compileFFICall :: Tag -> [IType] -> [CompileVal] -> CompileM CompileVal
compileFFICall name tys xs = do
  ans <- evalInstr name retTy' $ externCall f (map scalarVal xs)
  modify $ setFunSpecs (f:)
  return $ ScalarVal ans retTy
  where
    fromScalarIType :: IType -> BaseType
    fromScalarIType (IType b []) = b
    fromScalarIType ty = error $ "Not a scalar: " ++ pprint ty
    retTy:argTys = map fromScalarIType tys
    retTy':argTys' = map scalarTy (retTy:argTys)
    f = ExternFunSpec (L.Name name) retTy' argTys'

compileSelect :: [IType] -> [CompileVal] -> CompileM CompileVal
compileSelect ~[IType ty shape] ~[ScalarVal p _, x, y] = do
  p' <- evalInstr "" (L.IntegerType 1) $ L.Trunc p (L.IntegerType 1) []
  case (shape, x, y) of
    ([], ~(ScalarVal x' _), (ScalarVal y' _)) ->
        liftM (flip ScalarVal ty) $ evalInstr "" (scalarTy ty) $ L.Select p' x' y' []
    (_, ~(ArrayVal (Ptr x' ty') shape'), ~(ArrayVal (Ptr y' _) _)) -> do
        z <- evalInstr "" (L.ptr (scalarTy ty)) $ L.Select p' x' y' []
        return $ ArrayVal (Ptr z ty') shape'

compileBuiltin :: Builtin -> [IType] -> [CompileVal] -> CompileM CompileVal
compileBuiltin b ts = case b of
  IAdd     -> compileBinop IntType (\x y -> L.Add False False x y [])
  ISub     -> compileBinop IntType (\x y -> L.Sub False False x y [])
  IMul     -> compileBinop IntType (\x y -> L.Mul False False x y [])
  Mod      -> compileBinop IntType (\x y -> L.URem x y [])
  FAdd     -> compileBinop RealType (\x y -> L.FAdd noFastMathFlags x y [])
  FSub     -> compileBinop RealType (\x y -> L.FSub noFastMathFlags x y [])
  FMul     -> compileBinop RealType (\x y -> L.FMul noFastMathFlags x y [])
  FDiv     -> compileBinop RealType (\x y -> L.FDiv noFastMathFlags x y [])
  FLT      -> compileFCmp L.OLT
  FGT      -> compileFCmp L.OGT
  Select   -> compileSelect ts
  Todo     -> const $ throw MiscErr "Can't compile 'todo'"
  BoolToInt -> \(~[x]) -> return x  -- bools stored as ints
  IntToReal -> compileUnop RealType (\x -> L.SIToFP x realTy [])
  FFICall _ name -> compileFFICall (fromString name) ts
  Scan     -> error "Scan should have been lowered away by now."
  _ -> error $ "Primop not implemented: " ++ pprint b

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

instance Functor JitVal where
  fmap = fmapDefault

instance Foldable JitVal where
  foldMap = foldMapDefault

instance Traversable JitVal where
  traverse f val = case val of
    ScalarVal x ty -> liftA (\x' -> ScalarVal x' ty) (f x)
    ArrayVal (Ptr ptr ty) shape ->
      liftA2 newVal (f ptr) (traverse f shape)
      where newVal ptr' shape' = ArrayVal (Ptr ptr' ty) shape'

instance Functor JitVals where
  fmap = fmapDefault

instance Foldable JitVals where
  foldMap = foldMapDefault

instance Traversable JitVals where
  traverse f (JitVals vals) = liftA JitVals $ traverse (traverse f) vals

newtype JitVals w = JitVals [JitVal w]
