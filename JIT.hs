{-# LANGUAGE OverloadedStrings #-}

module JIT (jitPass, PersistVal, PWord, PersistEnv) where

import LLVM.AST hiding (Add, Mul, Sub)
import qualified LLVM.AST as L
import qualified LLVM.AST.Global as L
import qualified LLVM.AST.CallingConvention as L
import qualified LLVM.AST.Type as L
import qualified LLVM.AST.Float as L
import qualified LLVM.AST.Constant as C
import qualified LLVM.AST.IntegerPredicate as L

import Control.Monad
import Control.Monad.Except (throwError)
import Control.Monad.State

import qualified Data.Map.Strict as M
import Data.Foldable (toList)
import Data.List (intercalate, transpose)
import Data.Traversable
import Data.Functor.Identity

import qualified Foreign.Ptr as F
import Data.ByteString.Short (ShortByteString)
import Data.Word (Word64 (..))

import Type
import Syntax
import Env
import Record
import Util
import Imp
import LLVMExec

import Debug.Trace


-- TODO: figure out whether we actually need type everywhere here
data Ptr w = Ptr w L.Type  deriving (Show)

data JitVal w = ScalarVal w L.Type
              | ArrayVal (Ptr w) [w]  deriving (Show)
data Cell = Cell (Ptr Operand) [Operand]
type CompileVal  = JitVal Operand
type PersistVal  = JitVal PWord
data CompileState = CompileState { nameCounter :: Int
                                 , curBlocks   :: [BasicBlock]
                                 , curInstrs   :: [NInstr]
                                 , scalarDecls :: [NInstr]
                                 , blockName :: L.Name
                                 , impVarEnv  :: M.Map IVar CompileVal
                                 , impCellEnv :: M.Map CellVar Cell
                                 }

type CompileM a = StateT CompileState (Either Err) a
data CompiledProg = CompiledProg [CompileVal] Module
data ExternFunSpec = ExternFunSpec ShortByteString L.Type [L.Type] [ShortByteString]

data PWord = PScalar BaseType Word64
           | PPtr    BaseType (F.Ptr ())  deriving (Show)
type PersistEnv = FullEnv [PersistVal] PWord
type Long = Operand

type NInstr = Named Instruction

jitPass :: Pass ImpProgram () [PersistVal] PWord
jitPass = Pass jitExpr undefined jitCmd

jitExpr :: ImpProgram -> PersistEnv -> IO ([PersistVal], ())
jitExpr prog env = undefined -- do let compiled = toLLVM prog env
                      -- val <- uncurry evalJit (lower expr env)
                      -- return ((val, ty), ())

jitCmd :: Command ImpProgram -> PersistEnv -> IO (Command ())
jitCmd (CmdResult s) _ = return $ CmdResult s
jitCmd (CmdErr e)    _ = return $ CmdErr e
jitCmd (Command cmdName prog) env =
  case cmdName of
    GetLLVM -> liftM textResult $ showLLVM m
    EvalExpr -> do rawVals <- evalJit (length vs) m
                   return $ textResult $ show rawVals
    _ -> return $ Command cmdName ()
  where
     CompiledProg vs m = toLLVM prog env
     textResult = CmdResult . TextOut

-- printPersistVal :: PersistVal -> IO String
-- printPersistVal (JitVal x _ _ ) = return $ show x

toLLVM :: ImpProgram -> env_type -> CompiledProg
toLLVM prog _ = ignoreExcept $ evalStateT (compileProg prog) initState
  where initState = CompileState 0 [] [] [] "start_block" mempty mempty

compileProg :: ImpProgram -> CompileM CompiledProg
compileProg (ImpProgram statements outExprs) = do
  mapM compileStatement statements
  vals <- mapM compileExpr outExprs
  finalReturn vals
  decls <- gets scalarDecls
  blocks <- gets curBlocks
  return $ CompiledProg vals (makeModule decls blocks)

compileStatement :: Statement -> CompileM ()
compileStatement statement = case statement of
  Update v idxs expr -> do val <- compileExpr expr
                           cell <- lookupImpCell v
                           idxs' <- mapM lookupImpVar idxs
                           cell' <- idxCell cell idxs'
                           writeCell cell' val
  ImpLet (v, _) expr -> do val <- compileExpr expr
                           modify $ setImpVarEnv (M.insert v val)
  Alloc v (IType b shape) -> do
    shape' <- mapM lookupIVar shape
    cell <- case shape' of [] -> alloca b
                           _ -> malloc b shape'
    modify $ setImpCellEnv (M.insert v cell)

  Loop i n body -> do n' <- lookupImpVar n
                      compileLoop i n' body

compileExpr :: IExpr -> CompileM CompileVal
compileExpr expr = case expr of
  ILit v -> return $ ScalarVal (litVal v) (scalarTy (litType v))
  IVar v -> lookupIVar v
  IRead v -> do Cell ptr@(Ptr _ ty) shape <- lookupImpCell v
                case shape of
                  [] -> do op <- load ptr
                           return $ ScalarVal op ty
                  _ -> return $ ArrayVal ptr shape
  IGet v i -> do ArrayVal ptr (_:shape) <- compileExpr v
                 ScalarVal i' _ <- lookupIVar i
                 ptr'@(Ptr _ ty) <- indexPtr ptr shape i'
                 case shape of
                   [] -> do x <- load ptr'
                            return $ ScalarVal x ty
                   _  -> return $ ArrayVal ptr' shape

  IBuiltinApp b exprs -> do vals <- mapM compileExpr exprs
                            compileBuiltin b vals

lookupIVar :: IVar -> CompileM CompileVal
lookupIVar v = gets $ unJust . M.lookup v . impVarEnv

indexPtr :: Ptr Operand -> [Operand] -> Operand -> CompileM (Ptr Operand)
indexPtr (Ptr ptr ty) shape i = do
  stride <- foldM mul (litInt 8) shape
  n <- mul stride i
  ptr' <- evalInstr (L.ptr ty) $ L.GetElementPtr False ptr [n] []
  return (Ptr ptr' ty)

finalReturn :: [CompileVal] -> CompileM ()
finalReturn vals = do
  voidPtr <- evalInstr charPtrTy (externCall mallocFun [litInt numBytes])
  outPtr <- evalInstr intPtrTy $ L.BitCast voidPtr intPtrTy []
  sequence $ zipWith (writeComponent (Ptr outPtr longTy)) vals [0..]
  finishBlock (L.Ret (Just outPtr) []) (L.Name "")
  where numBytes = 8 * length vals
        writeComponent :: Ptr Operand -> CompileVal -> Int -> CompileM ()
        writeComponent ptr val i = case val of
          ScalarVal x _ -> do ptr' <- addPtr ptr (litInt i)
                              store ptr' x

finishBlock :: L.Terminator -> L.Name -> CompileM ()
finishBlock term newName = do
  oldName <- gets blockName
  instrs  <- gets curInstrs
  let newBlock = L.BasicBlock oldName (reverse instrs) (L.Do term)
  modify $ setCurBlocks (newBlock:)
         . setCurInstrs (const [])
         . setBlockName (const newName)

compileLoop :: IVar -> CompileVal -> [Statement] -> CompileM ()
compileLoop iVar (ScalarVal n _) body = do
  loopBlock <- freshName
  nextBlock <- freshName
  Cell i [] <- alloca IntType
  store i (litInt 0)
  entryCond <- load i >>= (`lessThan` n)
  finishBlock (L.CondBr entryCond loopBlock nextBlock []) loopBlock
  iVal <- load i
  modify $ setImpVarEnv $ M.insert iVar (ScalarVal iVal longTy) -- shadows...
  mapM compileStatement body
  iValInc <- add iVal (litInt 1)
  store i iValInc
  loopCond <- iValInc `lessThan` n
  finishBlock (L.CondBr loopCond loopBlock nextBlock []) nextBlock

freshName :: CompileM L.Name
freshName = do i <- gets nameCounter
               modify (\state -> state {nameCounter = i + 1})
               return $ L.UnName (fromIntegral i)

idxCell :: Cell -> [CompileVal] -> CompileM Cell
idxCell cell [] = return cell
idxCell (Cell ptr (_:shape)) (i:idxs) = do
  size <- numBytes shape
  step <- mul size (scalarOp i)
  ptr' <- addPtr ptr step
  idxCell (Cell ptr' shape) idxs

readCell :: Cell -> CompileM CompileVal
readCell (Cell ptr@(Ptr _ ty) []) = do x <- load ptr
                                       return $ ScalarVal x ty

writeCell :: Cell -> CompileVal -> CompileM ()
writeCell (Cell ptr []) (ScalarVal x _) = store ptr x


litVal :: LitVal -> Operand
litVal lit = case lit of
  IntLit  x -> L.ConstantOperand $ C.Int 64 (fromIntegral x)
  RealLit x -> L.ConstantOperand $ C.Float (L.Double x)

litInt :: Int -> Operand
litInt x = L.ConstantOperand $ C.Int 64 (fromIntegral x)

store :: Ptr Operand -> Operand -> CompileM ()
store (Ptr ptr _) x =  addInstr $ L.Do $ L.Store False ptr x Nothing 0 []

load :: Ptr Operand -> CompileM Operand
load (Ptr ptr ty) = evalInstr ty $ L.Load False ptr Nothing 0 []

lessThan :: Long -> Long -> CompileM Long
lessThan x y = evalInstr longTy $ L.ICmp L.SLT x y []

add :: Long -> Long -> CompileM Long
add x y = evalInstr longTy $ L.Add False False x y []

evalInstr :: L.Type -> Instruction -> CompileM Operand
evalInstr ty instr = do v <- freshName
                        addInstr $ v L.:= instr
                        return $ L.LocalReference ty v

addPtr :: Ptr Operand -> Long -> CompileM (Ptr Operand)
addPtr (Ptr ptr ty) i = do ptr' <- evalInstr (L.ptr ty) instr
                           return $ Ptr ptr' ty
  where instr = L.GetElementPtr False ptr [i] []

alloca :: BaseType -> CompileM Cell
alloca ty = do v <- freshName
               modify $ setScalarDecls ((v L.:= instr):)
               return $ Cell (Ptr (L.LocalReference (L.ptr ty') v) ty') []
  where ty' = scalarTy ty
        instr = L.Alloca ty' Nothing 0 []

malloc :: BaseType -> [CompileVal] -> CompileM Cell
malloc ty shape = do
    n <- numBytes shape'
    voidPtr <- evalInstr charPtrTy (externCall mallocFun [n])
    ptr <- evalInstr (L.ptr ty') $ L.BitCast voidPtr (L.ptr ty') []
    return $ Cell (Ptr ptr ty') shape'
  where shape' = map scalarOp shape
        ty' = scalarTy ty

numBytes :: [Operand] -> CompileM Operand
numBytes shape = foldM mul (litInt 8) shape

mul :: Operand -> Operand -> CompileM Operand
mul x y = evalInstr longTy $ L.Mul False False x y []

scalarOp :: CompileVal -> Operand
scalarOp (ScalarVal op _) = op

addInstr :: Named Instruction -> CompileM ()
addInstr instr = modify $ setCurInstrs (instr:)

scalarTy :: BaseType -> L.Type
scalarTy ty = case ty of IntType  -> longTy
                         RealType -> realTy

compileBinop ::    L.Type -> (Operand -> Operand -> L.Instruction)
                -> [CompileVal]
                -> CompileM CompileVal
compileBinop ty makeInstr [ScalarVal x _, ScalarVal y _] =
  liftM (flip ScalarVal ty) $ evalInstr ty (makeInstr x y)

compileBuiltin :: Builtin -> [CompileVal] -> CompileM CompileVal
compileBuiltin b = case b of
  Add      -> compileBinop longTy (\x y -> L.Add False False x y [])
  Mul      -> compileBinop longTy (\x y -> L.Mul False False x y [])
  Sub      -> compileBinop longTy (\x y -> L.Sub False False x y [])
  _ -> error (show b)
  -- Doubleit -> externalMono doubleFun  IntType
  -- Hash     -> externalMono hashFun    IntType
  -- Rand     -> externalMono randFun    RealType
  -- Randint  -> externalMono randIntFun IntType

doubleFun  = ExternFunSpec "doubleit"      longTy [longTy] ["x"]
randFun    = ExternFunSpec "randunif"      realTy [longTy] ["keypair"]
randIntFun = ExternFunSpec "randint"       longTy [longTy, longTy] ["keypair", "nmax"]
hashFun    = ExternFunSpec "threefry_2x32" longTy [longTy, longTy] ["keypair", "count"]
mallocFun  = ExternFunSpec "malloc_cod" charPtrTy [longTy] ["nbytes"]
memcpyFun  = ExternFunSpec "memcpy_cod" L.VoidType [charPtrTy, charPtrTy, longTy]
                                                   ["dest", "src", "nbytes"]

charPtrTy = L.ptr (L.IntegerType 8)
intPtrTy = L.ptr longTy
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
                                  [doubleFun, mallocFun, memcpyFun,
                                   hashFun, randFun, randIntFun]
                          }
    fundef = L.functionDefaults { L.name        = L.Name "thefun"
                                , L.parameters  = ([], False)
                                , L.returnType  = longTy
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

lookupImpVar :: IVar -> CompileM CompileVal
lookupImpVar v = gets $ unJust . M.lookup v . impVarEnv

lookupImpCell :: CellVar -> CompileM Cell
lookupImpCell v = gets $ unJust . M.lookup v . impCellEnv

setScalarDecls update state = state { scalarDecls = update (scalarDecls state) }
setCurInstrs   update state = state { curInstrs   = update (curInstrs   state) }
setCurBlocks   update state = state { curBlocks   = update (curBlocks   state) }
setImpVarEnv   update state = state { impVarEnv   = update (impVarEnv   state) }
setImpCellEnv  update state = state { impCellEnv  = update (impCellEnv  state) }
setBlockName   update state = state { blockName   = update (blockName   state) }
