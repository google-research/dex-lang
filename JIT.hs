{-# LANGUAGE OverloadedStrings #-}

module JIT (jitPass, PersistVal, PWord, PersistEnv) where

import LLVM.AST hiding (Add, Mul, Sub)
import qualified LLVM.AST as L
import qualified LLVM.AST.Global as L
import qualified LLVM.AST.CallingConvention as L
import qualified LLVM.AST.Type as L
import qualified LLVM.AST.Float as L
import qualified LLVM.AST.Constant as C

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


-- TODO: figure out whether we actually need type everywhere here
data Ptr w = Ptr w L.Type

data JitVal w = ScalarVal w L.Type
              | ArrayVal (Ptr w) [w]
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
  ImpLet v _ expr -> do val <- compileExpr expr
                        modify $ setImpVarEnv (M.insert v val)
  Alloc v (IType b shape) -> case shape of
                               [] -> do cell <- alloca b
                                        modify $ setImpCellEnv (M.insert v cell)
  Loop i n body -> do n' <- lookupImpVar n
                      compileLoop i n' body

compileExpr :: IExpr -> CompileM CompileVal
compileExpr expr = case expr of
  ILit v -> return $ ScalarVal (litVal v) (scalarTy (litType v))
  IVar v -> lookupIVar v
  IRead v -> do Cell ptr@(Ptr _ ty) shape <- gets $ unJust . M.lookup v . impCellEnv
                case shape of
                  [] -> do op <- load ptr
                           return $ ScalarVal op ty
                  _ -> return $ ArrayVal ptr shape
  IGet v i -> do ArrayVal ptr (_:shape) <- compileExpr v
                 ScalarVal i' _ <- lookupIVar i
                 return $ ArrayVal (indexPtr ptr shape i') shape
  IBuiltinApp b exprs -> do vals <- mapM compileExpr exprs
                            compileBuiltin b vals

lookupIVar :: IVar -> CompileM CompileVal
lookupIVar v = gets $ unJust . M.lookup v . impVarEnv

indexPtr :: Ptr Operand -> [Operand] -> Operand -> Ptr Operand
indexPtr = undefined

finalReturn :: [CompileVal] -> CompileM ()
finalReturn vals = do
  voidPtr <- evalInstr charPtrTy (externCall mallocFun [litInt numBytes])
  outPtr <- evalInstr intPtrTy $ L.BitCast voidPtr intPtrTy []
  sequence $ zipWith (writeComponent outPtr) vals [0..]
  finishBlock (L.Ret (Just outPtr) []) (L.Name "")
  where numBytes = 8 * length vals
        writeComponent :: Operand -> CompileVal -> Int -> CompileM ()
        writeComponent ptr val i = case val of
          ScalarVal x _ -> do
            ptr' <- evalInstr intPtrTy $ L.GetElementPtr False ptr [litInt i] []
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
compileLoop = undefined

freshName :: CompileM L.Name
freshName = do i <- gets nameCounter
               modify (\state -> state {nameCounter = i + 1})
               return $ L.UnName (fromIntegral i)

-- locPtr :: Loc -> CompileM Operand
-- locPtr = undefined

-- readLocScalar :: Loc -> CompileM Operand
-- readLocScalar = undefined

-- writeLocScalar :: Loc -> Operand -> CompileM ()
-- writeLocScalar (Loc v []) x = do JitVal cell _ [] <- lookupImpVar v
--                                  writeCell cell x

idxCell :: Cell -> [CompileVal] -> CompileM Cell
idxCell = undefined

readCell :: Cell -> CompileM Operand
readCell = undefined
-- readCell (Cell ptr ty) = load ptr ty

writeCell :: Cell -> CompileVal -> CompileM ()
writeCell = undefined -- (Cell ptr _) x = store ptr x

litVal :: LitVal -> Operand
litVal lit = case lit of
  IntLit  x -> L.ConstantOperand $ C.Int 64 (fromIntegral x)
  RealLit x -> L.ConstantOperand $ C.Float (L.Double x)

litInt :: Int -> Operand
litInt x = L.ConstantOperand $ C.Int 64 (fromIntegral x)

store :: Operand -> Operand -> CompileM ()
store ptr x =  addInstr $ L.Do $ L.Store False ptr x Nothing 0 []

load :: Ptr Operand -> CompileM Operand
load (Ptr ptr ty) = evalInstr ty $ L.Load False ptr Nothing 0 []

evalInstr :: L.Type -> Instruction -> CompileM Operand
evalInstr ty instr = do v <- freshName
                        addInstr $ v L.:= instr
                        return $ L.LocalReference ty v

alloca :: BaseType -> CompileM Cell
alloca ty = undefined -- do v <- freshName
  --              modify $ setScalarDecls ((v L.:= instr):)
  --              return $ Cell (L.LocalReference (L.ptr lTy) v) lTy
  -- where lTy = scalarTy ty
  --       instr = L.Alloca lTy Nothing 0 []

malloc :: BaseType -> [Cell] -> CompileM Cell
malloc = undefined

addImpVar :: Var -> CompileVal -> CompileM ()
addImpVar = undefined -- v val = modify $ setImpVarEnv (M.insert v val)

addInstr :: Named Instruction -> CompileM ()
addInstr instr = modify $ setCurInstrs (instr:)

lookupImpVar :: IVar -> CompileM CompileVal
lookupImpVar = undefined -- v = gets $ unJust . M.lookup v . impVarEnv

lookupImpCell :: CellVar -> CompileM Cell
lookupImpCell = undefined -- v = gets $ unJust . M.lookup v . impVarEnv

lookupSize :: Size -> CompileM Cell
lookupSize = undefined

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

setScalarDecls update state = state { scalarDecls = update (scalarDecls state) }
setCurInstrs   update state = state { curInstrs   = update (curInstrs   state) }
setCurBlocks   update state = state { curBlocks   = update (curBlocks   state) }
setImpVarEnv   update state = state { impVarEnv   = update (impVarEnv   state) }
setImpCellEnv  update state = state { impCellEnv  = update (impCellEnv  state) }
setBlockName   update state = state { blockName   = update (blockName   state) }
