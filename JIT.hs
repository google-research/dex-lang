{-# LANGUAGE OverloadedStrings #-}

module JIT (jitPass) where

import LLVM.AST hiding (Type, Add, Mul, Sub, FAdd, FSub, FMul, FDiv)
import qualified LLVM.AST as L
import qualified LLVM.AST.Global as L
import qualified LLVM.AST.CallingConvention as L
import qualified LLVM.AST.Type as L
import qualified LLVM.AST.Float as L
import qualified LLVM.AST.Constant as C
import qualified LLVM.AST.IntegerPredicate as L

import Control.Monad
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Except (liftEither)
import Control.Applicative (liftA, liftA2)

import Data.Traversable
import Data.Time.Clock (getCurrentTime, diffUTCTime)

import Data.ByteString.Short (ShortByteString, toShort, fromShort)
import Data.ByteString.Char8 (pack, unpack)
import Data.Word (Word64)

import Data.Binary.IEEE754 (wordToDouble)

import Type
import Syntax
import Env
import Record
import Util
import Pass
import Fresh hiding (Name, freshName)
import PPrint

import LLVMExec

-- TODO: figure out whether we actually need type everywhere here
data Ptr w = Ptr w L.Type  deriving (Show)

data JitVal w = ScalarVal w L.Type
              | ArrayVal (Ptr w) [w]  deriving (Show)

data GenCell w = Cell (Ptr w) [w]
type Cell        = GenCell Operand
type PersistCell = GenCell Word64

type CompileVal  = JitVal Operand
type PersistVal  = JitVal Word64
type PersistEnv = Env PersistVal
type ImpVarEnv = Env (Either CompileVal Cell)

data CompileState = CompileState { curBlocks   :: [BasicBlock]
                                 , curInstrs   :: [NInstr]
                                 , scalarDecls :: [NInstr]
                                 , blockName :: L.Name
                                 }

type CompileM a = Pass ImpVarEnv CompileState a
data CompiledProg = CompiledProg Module
data ExternFunSpec = ExternFunSpec ShortByteString L.Type [L.Type] [ShortByteString]

type Long = Operand
type NInstr = Named Instruction

jitPass :: ImpDecl -> TopPass PersistEnv ()
jitPass decl = case decl of
  ImpTopLet bs prog -> do
    vals <- evalProg bs prog
    putEnv $ bindFold $ zipWith replaceAnnot bs vals
  ImpEvalCmd _ _ NoOp -> return ()
  ImpEvalCmd ty bs (Command cmd prog) -> case cmd of
    Passes -> do (_, CompiledProg m) <- toLLVM bs prog
                 llvm <- liftIO $ showLLVM m
                 writeOut $ "\n\nLLVM\n" ++ llvm
    EvalExpr -> do vals <- evalProg bs prog
                   vecs <- liftIO $ mapM asVec vals
                   writeOut $ pprint (restructureVal ty vecs)
    TimeIt -> do t1 <- liftIO getCurrentTime
                 evalProg bs prog
                 t2 <- liftIO getCurrentTime
                 writeOut $ show (t2 `diffUTCTime` t1)
    _ -> return ()

evalProg :: [IBinder] -> ImpProg -> TopPass PersistEnv [PersistVal]
evalProg bs prog = do
  (cells, CompiledProg mod) <- toLLVM bs prog
  liftIO $ evalJit mod
  liftIO $ mapM readPersistCell cells

-- This doesn't work with types derived from existentials, because the
-- existentially quantified variable isn't in scope yet
makeDestCell :: PersistEnv -> IBinder -> IO (GenBinder PersistCell)
makeDestCell env (Bind v (IType ty shape)) = do
  ptr <- liftM ptrAsWord $ mallocBytes $ fromIntegral $ 8 * product shape'
  return $ Bind v (Cell (Ptr ptr ty') shape')
  where shape' = map (scalarVal . (env !)) shape
        ty' = scalarTy ty

-- TODO: pass destinations as args rather than baking pointers into LLVM
toLLVM :: [IBinder] -> ImpProg -> TopPass PersistEnv ([PersistCell], CompiledProg)
toLLVM bs prog = do
  env <- getEnv
  destCells <- liftIO $ mapM (makeDestCell env) bs
  let env' =    fmap (Left  . asCompileVal) env
             <> fmap (Right . asCompileCell) (bindFold destCells)
  let initState = CompileState [] [] [] "start_block"
  prog <- liftEither $ evalPass env' initState mempty (compileTopProg prog)
  return (map binderAnn destCells, prog)

asCompileVal :: PersistVal -> CompileVal
asCompileVal (ScalarVal word ty) = ScalarVal (constOperand (baseTy ty) word) ty
asCompileVal (ArrayVal ptr shape) = ArrayVal (ptrLiteral ptr) shape'
  where shape' = map (constOperand IntType) shape

asCompileCell :: PersistCell -> Cell
asCompileCell (Cell ptr shape) = Cell (ptrLiteral ptr) shape'
  where shape' = map (constOperand IntType) shape

ptrLiteral :: Ptr Word64 -> Ptr Operand
ptrLiteral (Ptr ptr ty) = Ptr ptr' ty
  where ptr' = L.ConstantOperand $
                   C.IntToPtr (C.Int 64 (fromIntegral ptr)) (L.ptr ty)

readPersistCell :: PersistCell -> IO PersistVal
readPersistCell (Cell (Ptr ptr ty) []) = do [word] <- readPtrs 1 (wordAsPtr ptr)
                                            return $ ScalarVal word ty
readPersistCell (Cell p shape) = return $ ArrayVal p shape

-- TODO: concretize type with actual index set
restructureVal :: Type -> [Vec] -> Value
restructureVal ty vecs = Value ty $ restructure vecs (typeLeaves ty)
  where
    typeLeaves :: Type -> RecTree ()
    typeLeaves ty = case ty of BaseType _ -> RecLeaf ()
                               TabType _ valTy -> typeLeaves valTy
                               RecType r -> RecTree $ fmap typeLeaves r
                               _ -> error $ "can't show " ++ pprint ty

asVec :: PersistVal -> IO Vec
asVec v = case v of
  ScalarVal x ty ->  return $ cast (baseTy ty) [x]
  ArrayVal (Ptr ptr ty) shape -> do let size = fromIntegral $ foldr (*) 1 shape
                                    words <- readPtrs size (wordAsPtr ptr)
                                    return $ cast (baseTy ty) words
  where cast IntType xs = IntVec $ map fromIntegral xs
        cast RealType xs = RealVec $ map interpret_ieee_64 xs

-- From the data-binary-ieee754 package; is there a more standard way
-- to do this?  This is also janky because we are just assuming that
-- LLVM stores its floats in the ieee format.
interpret_ieee_64 :: Word64 -> Double
interpret_ieee_64 = wordToDouble

constOperand :: BaseType -> Word64 -> Operand
constOperand IntType  x = litInt (fromIntegral x)
constOperand RealType x = litReal (interpret_ieee_64 x)

compileTopProg :: ImpProg -> CompileM CompiledProg
compileTopProg prog = do
  compileProg prog
  finishBlock (L.Ret Nothing []) (L.Name "")
  decls <- gets scalarDecls
  blocks <- gets (reverse . curBlocks)
  return $ CompiledProg (makeModule decls blocks)

compileProg :: ImpProg -> CompileM ()
compileProg (ImpProg statements) = mapM_ compileStatement statements

compileStatement :: Statement -> CompileM ()
compileStatement statement = case statement of
  Update v idxs b exprs -> do
    vals <- mapM compileExpr exprs
    cell <- lookupCellVar v
    idxs' <- mapM lookupScalar idxs
    cell' <- idxCell cell idxs'
    outVal <- case b of Copy -> let [val] = vals in return val
                        _ -> compileBuiltin b vals
    writeCell cell' outVal
  Alloc (Bind v (IType b shape)) body -> do
    shape' <- mapM lookupScalar shape
    cell <- allocate b shape' (nameTag v)
    extendWith (v @> Right cell) (compileProg body)
    free cell
  Loop i n body -> do n' <- lookupScalar n
                      compileLoop i n' body

compileExpr :: IExpr -> CompileM CompileVal
compileExpr expr = case expr of
  ILit v -> return $ ScalarVal (litVal v) (scalarTy (litType v))
  IVar v -> do x <- lookupImpVar v
               case x of
                 Left val -> return val
                 Right cell@(Cell ptr shape) -> case shape of
                    [] -> readScalarCell cell
                    _  -> return $ ArrayVal ptr shape
  IGet v i -> do ArrayVal ptr (_:shape) <- compileExpr v
                 ScalarVal i' _ <- lookupScalar i
                 ptr'@(Ptr _ ty) <- indexPtr ptr shape i'
                 case shape of
                   [] -> do x <- load ptr'
                            return $ ScalarVal x ty
                   _  -> return $ ArrayVal ptr' shape

lookupImpVar :: Var -> CompileM (Either CompileVal Cell)
lookupImpVar v = asks (! v)

readScalarCell :: Cell -> CompileM CompileVal
readScalarCell (Cell ptr@(Ptr _ ty) []) = do op <- load ptr
                                             return $ ScalarVal op ty

lookupScalar :: Var -> CompileM CompileVal
lookupScalar v = do x <- lookupImpVar v
                    case x of Left val -> return val
                              Right cell -> readScalarCell cell

lookupCellVar :: Var -> CompileM Cell
lookupCellVar v = do { Right cell <- lookupImpVar v; return cell }

indexPtr :: Ptr Operand -> [Operand] -> Operand -> CompileM (Ptr Operand)
indexPtr (Ptr ptr ty) shape i = do
  stride <- foldM mul (litInt 1) shape
  n <- mul stride i
  ptr' <- evalInstr "ptr" (L.ptr ty) $ L.GetElementPtr False ptr [n] []
  return (Ptr ptr' ty)

finishBlock :: L.Terminator -> L.Name -> CompileM ()
finishBlock term newName = do
  oldName <- gets blockName
  instrs  <- gets curInstrs
  let newBlock = L.BasicBlock oldName (reverse instrs) (L.Do term)
  modify $ setCurBlocks (newBlock:)
         . setCurInstrs (const [])
         . setBlockName (const newName)

compileLoop :: Var -> CompileVal -> ImpProg -> CompileM ()
compileLoop iVar (ScalarVal n _) body = do
  loopBlock <- freshName "loop"
  nextBlock <- freshName "cont"
  Cell i [] <- alloca IntType "i"
  store i (litInt 0)
  entryCond <- load i >>= (`lessThan` n)
  finishBlock (L.CondBr entryCond loopBlock nextBlock []) loopBlock
  iVal <- load i
  extendWith (iVar @> (Left $ ScalarVal iVal longTy)) $
    compileProg body
  iValInc <- add iVal (litInt 1)
  store i iValInc
  loopCond <- iValInc `lessThan` n
  finishBlock (L.CondBr loopCond loopBlock nextBlock []) nextBlock

freshName :: String -> CompileM L.Name
freshName s = do name <- fresh s
                 return $ Name (toShort (pack (pprint name)))

idxCell :: Cell -> [CompileVal] -> CompileM Cell
idxCell cell [] = return cell
idxCell (Cell ptr (_:shape)) (i:idxs) = do
  size <- sizeOf shape
  step <- mul size (scalarVal i)
  ptr' <- addPtr ptr step
  idxCell (Cell ptr' shape) idxs

writeCell :: Cell -> CompileVal -> CompileM ()
writeCell (Cell ptr []) (ScalarVal x _) = store ptr x
writeCell (Cell (Ptr dest _) shape) (ArrayVal (Ptr src _) _) = do
  numScalars <- sizeOf shape
  numBytes <- mul (litInt 8) numScalars
  addInstr $ L.Do (externCall memcpyFun [dest, src, numBytes])

litVal :: LitVal -> Operand
litVal lit = case lit of
  IntLit  x -> L.ConstantOperand $ C.Int 64 (fromIntegral x)
  RealLit x -> L.ConstantOperand $ C.Float (L.Double x)

litInt :: Int -> Operand
litInt x = L.ConstantOperand $ C.Int 64 (fromIntegral x)

litReal :: Double -> Operand
litReal x = L.ConstantOperand $ C.Float $ L.Double x

store :: Ptr Operand -> Operand -> CompileM ()
store (Ptr ptr _) x =  addInstr $ L.Do $ L.Store False ptr x Nothing 0 []

load :: Ptr Operand -> CompileM Operand
load (Ptr ptr ty) = evalInstr "" ty $ L.Load False ptr Nothing 0 []

lessThan :: Long -> Long -> CompileM Long
lessThan x y = evalInstr "lt" longTy $ L.ICmp L.SLT x y []

add :: Long -> Long -> CompileM Long
add x y = evalInstr "add" longTy $ L.Add False False x y []

evalInstr :: String -> L.Type -> Instruction -> CompileM Operand
evalInstr s ty instr = do v <- freshName s
                          addInstr $ v L.:= instr
                          return $ L.LocalReference ty v

addPtr :: Ptr Operand -> Long -> CompileM (Ptr Operand)
addPtr (Ptr ptr ty) i = do ptr' <- evalInstr "ptr" (L.ptr ty) instr
                           return $ Ptr ptr' ty
  where instr = L.GetElementPtr False ptr [i] []

alloca :: BaseType -> String -> CompileM Cell
alloca ty s = do v <- freshName s
                 modify $ setScalarDecls ((v L.:= instr):)
                 return $ Cell (Ptr (L.LocalReference (L.ptr ty') v) ty') []
  where ty' = scalarTy ty
        instr = L.Alloca ty' Nothing 0 []

malloc :: BaseType -> [CompileVal] -> String -> CompileM Cell
malloc ty shape s = do
    size <- sizeOf shape'
    n <- mul (litInt 8) size
    voidPtr <- evalInstr "" charPtrTy (externCall mallocFun [n])
    ptr <- evalInstr s (L.ptr ty') $ L.BitCast voidPtr (L.ptr ty') []
    return $ Cell (Ptr ptr ty') shape'
  where shape' = map scalarVal shape
        ty' = scalarTy ty

allocate :: BaseType -> [CompileVal] -> String -> CompileM Cell
allocate b shape s = case shape of [] -> alloca b s
                                   _ -> malloc b shape s

free :: Cell -> CompileM ()
free (Cell (Ptr ptr _) shape) =
  case shape of [] -> return ()
                _  -> addInstr $ L.Do (externCall freeFun [ptr])

sizeOf :: [Operand] -> CompileM Operand
sizeOf shape = foldM mul (litInt 1) shape

mul :: Operand -> Operand -> CompileM Operand
mul x y = evalInstr "mul" longTy $ L.Mul False False x y []

scalarVal :: JitVal a -> a
scalarVal (ScalarVal x _) = x

addInstr :: Named Instruction -> CompileM ()
addInstr instr = modify $ setCurInstrs (instr:)

scalarTy :: BaseType -> L.Type
scalarTy ty = case ty of IntType  -> longTy
                         RealType -> realTy

baseTy :: L.Type -> BaseType
baseTy ty = case ty of
  L.IntegerType 64 -> IntType
  L.FloatingPointType L.DoubleFP -> RealType

compileBinop :: L.Type -> (Operand -> Operand -> L.Instruction)
                -> [CompileVal]
                -> CompileM CompileVal
compileBinop ty makeInstr [ScalarVal x _, ScalarVal y _] =
  liftM (flip ScalarVal ty) $ evalInstr "" ty (makeInstr x y)

compileUnop :: L.Type -> (Operand -> L.Instruction)
                -> [CompileVal]
                -> CompileM CompileVal
compileUnop ty makeInstr [ScalarVal x _] =
  liftM (flip ScalarVal ty) $ evalInstr "" ty (makeInstr x)

externalMono :: ExternFunSpec -> BaseType -> [CompileVal] -> CompileM CompileVal
externalMono f@(ExternFunSpec name retTy _ _) baseTy args = do
  ans <- evalInstr name' retTy $ externCall f (map scalarVal args)
  return $ ScalarVal ans (scalarTy baseTy)
  where name' = unpack (fromShort name)

compileBuiltin :: Builtin -> [CompileVal] -> CompileM CompileVal
compileBuiltin b = case b of
  Add      -> compileBinop longTy (\x y -> L.Add False False x y [])
  Sub      -> compileBinop longTy (\x y -> L.Sub False False x y [])
  Mul      -> compileBinop longTy (\x y -> L.Mul False False x y [])
  FAdd     -> compileBinop realTy (\x y -> L.FAdd noFastMathFlags x y [])
  FSub     -> compileBinop realTy (\x y -> L.FSub noFastMathFlags x y [])
  FMul     -> compileBinop realTy (\x y -> L.FMul noFastMathFlags x y [])
  FDiv     -> compileBinop realTy (\x y -> L.FDiv noFastMathFlags x y [])
  Exp      -> externalMono expFun     RealType
  Log      -> externalMono logFun     RealType
  Sqrt     -> externalMono sqrtFun    RealType
  Sin      -> externalMono sinFun     RealType
  Cos      -> externalMono cosFun     RealType
  Tan      -> externalMono tanFun     RealType
  Hash     -> externalMono hashFun    IntType
  Rand     -> externalMono randFun    RealType
  Randint  -> externalMono randIntFun IntType
  IntToReal -> compileUnop realTy (\x -> L.SIToFP x realTy [])
  Iota     -> error "Iota should have been lowered away by now."
  Fold     -> error "Fold should have been lowered away by now."


randFun    = ExternFunSpec "randunif"      realTy [longTy] ["keypair"]
randIntFun = ExternFunSpec "randint"       longTy [longTy, longTy] ["keypair", "nmax"]
hashFun    = ExternFunSpec "threefry_2x32" longTy [longTy, longTy] ["keypair", "count"]
mallocFun  = ExternFunSpec "malloc_cod" charPtrTy [longTy] ["nbytes"]
freeFun    = ExternFunSpec "free_cod" charPtrTy [charPtrTy] ["ptr"]
memcpyFun  = ExternFunSpec "memcpy_cod" L.VoidType [charPtrTy, charPtrTy, longTy]
                                                   ["dest", "src", "nbytes"]

expFun     = ExternFunSpec "exp"           realTy [realTy] ["x"]
logFun     = ExternFunSpec "log"           realTy [realTy] ["x"]
sqrtFun    = ExternFunSpec "sqrt"          realTy [realTy] ["x"]
sinFun     = ExternFunSpec "sin"           realTy [realTy] ["x"]
cosFun     = ExternFunSpec "cos"           realTy [realTy] ["x"]
tanFun     = ExternFunSpec "tan"           realTy [realTy] ["x"]

charPtrTy = L.ptr (L.IntegerType 8)
longTy = L.IntegerType 64
realTy = L.FloatingPointType L.DoubleFP

funTy :: L.Type -> [L.Type] -> L.Type
funTy retTy argTys = L.ptr $ L.FunctionType retTy argTys False

makeModule :: [NInstr] -> [BasicBlock] -> Module
makeModule decls (fstBlock:blocks) = mod
  where
    L.BasicBlock name instrs term = fstBlock
    fstBlock' = L.BasicBlock name (decls ++ instrs) term
    mod = L.defaultModule { L.moduleName = "test"
                          , L.moduleDefinitions =
                                L.GlobalDefinition fundef
                              : map externDecl
                                  [mallocFun, freeFun, memcpyFun,
                                   hashFun, randFun, randIntFun,
                                   expFun, logFun, sqrtFun,
                                   sinFun, cosFun, tanFun]
                          }
    fundef = L.functionDefaults { L.name        = L.Name "thefun"
                                , L.parameters  = ([], False)
                                , L.returnType  = L.VoidType
                                , L.basicBlocks = (fstBlock':blocks) }

externCall :: ExternFunSpec -> [L.Operand] -> L.Instruction
externCall (ExternFunSpec fname retTy argTys _) args =
  L.Call Nothing L.C [] fun args' [] []
  where fun = Right $ L.ConstantOperand $ C.GlobalReference
                         (funTy retTy argTys) (L.Name fname)
        args' = [(x ,[]) | x <- args]

externDecl :: ExternFunSpec -> L.Definition
externDecl (ExternFunSpec fname retTy argTys argNames) =
  L.GlobalDefinition $ L.functionDefaults {
    L.name        = L.Name fname
  , L.parameters  = ([L.Parameter t (L.Name s) []
                     | (t, s) <- zip argTys argNames], False)
  , L.returnType  = retTy
  , L.basicBlocks = []
  }

setScalarDecls update state = state { scalarDecls = update (scalarDecls state) }
setCurInstrs   update state = state { curInstrs   = update (curInstrs   state) }
setCurBlocks   update state = state { curBlocks   = update (curBlocks   state) }
setBlockName   update state = state { blockName   = update (blockName   state) }

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
