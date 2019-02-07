{-# LANGUAGE OverloadedStrings #-}

module JIT (lowerLLVM, showLLVM, evalJit, Compiled, jitExpr, jitCmd) where

import Control.Monad
import Control.Monad.Except (throwError)
import Control.Monad.Reader (ReaderT, runReaderT, local, ask, asks)
import Control.Monad.State (StateT, execStateT, put, get, gets, modify)

import qualified Data.Map.Strict as M
import Data.Foldable (toList)

import qualified LLVM.AST as L
import qualified LLVM.AST.Type as L
import qualified LLVM.AST.Global as L
import qualified LLVM.AST.Float as L
import qualified LLVM.AST.IntegerPredicate as L
import qualified LLVM.AST.Constant as C
import qualified LLVM.Module as Mod
import qualified LLVM.Analysis as Mod
import qualified LLVM.ExecutionEngine as EE
import LLVM.Internal.Context

import Data.Int
import Foreign.Ptr hiding (Ptr)
import Data.ByteString.Char8 (unpack)

import Syntax
import Env

foreign import ccall "dynamic" haskFun :: FunPtr Int32 -> Int32

type Compiled = L.Module
type JITEnv = FullEnv CompileVal RangeVal
data CompileVal = Operand L.Operand
                | Pointer Ptr
                | Builtin BuiltinFun [CompileVal]
                | LamVal JITEnv Expr
                | ExPackage L.Operand CompileVal

data RangeVal = RangeVal L.Operand | NoRange

type CompileApp = [CompileVal] -> CompileM CompileVal

type Operand = L.Operand
newtype Ptr = Ptr Operand


data BuiltinFun = BuiltinFun Int CompileApp
type Instr = L.Named L.Instruction
type Block = L.BasicBlock
data CompileState = CompileState { nameCounter :: Int
                                 , curBlocks :: [Block]
                                 , curInstrs :: [Instr]
                                 , curBlockName :: L.Name }

type CompileM a = ReaderT JITEnv (StateT CompileState (Either Err)) a

jitExpr :: Expr -> FullEnv () () -> IO ((), ())
jitExpr expr env = return ((),())

jitCmd :: Command Expr -> FullEnv () () -> IO (Command ())
jitCmd (Command cmdName expr) env = case cmdName of
    GetLLVM -> case lowerLLVM expr of
                 Left e -> return $ CmdErr e
                 Right m -> liftM CmdResult (showLLVM m)
    EvalExpr -> case lowerLLVM expr of
                 Left e -> return $ CmdErr e
                 Right m -> liftM CmdResult (evalJit m)
    _ -> return $ Command cmdName ()

jitCmd (CmdResult s) _ = return $ CmdResult s
jitCmd (CmdErr e)    _ = return $ CmdErr e

lowerLLVM :: Expr -> Except L.Module
lowerLLVM expr = do
  blocks <- runCompileM builtinEnv (compileModule expr)
  return (makeModule blocks)

showLLVM :: L.Module -> IO String
showLLVM m = withContext $ \c ->
               Mod.withModuleFromAST c m $ \m ->
                 fmap unpack $ Mod.moduleLLVMAssembly m

evalJit :: L.Module -> IO String
evalJit m =
  withContext $ \c ->
    Mod.withModuleFromAST c m $ \m -> do
      jit c $ \ee ->
        EE.withModuleInEngine ee m $ \eee -> do
          fn <- EE.getFunction eee (L.Name "thefun")
          case fn of
            Just fn -> do let x = show $ runJitted fn
                          putStr $ x `seq` ""  -- segfaults without this
                          return x
            Nothing -> return "Failed - couldn't find function"

makeModule :: [Block] -> L.Module
makeModule blocks = mod
  where
    mod = L.defaultModule { L.moduleName = "test"
                          , L.moduleDefinitions = [L.GlobalDefinition fundef] }
    fundef = L.functionDefaults { L.name        = L.Name "thefun"
                                , L.parameters  = ([], False)
                                , L.returnType  = intTy
                                , L.basicBlocks = blocks }


runCompileM :: JITEnv -> CompileM a -> Except [Block]
runCompileM env m = do
  CompileState _ blocks [] _ <- execStateT (runReaderT m env) initState
  return $ reverse blocks
  where initState = CompileState 0 [] [] (L.Name "main_block")

runJitted :: FunPtr a -> Int32
runJitted fn = haskFun (castFunPtr fn :: FunPtr Int32)

jit :: Context -> (EE.MCJIT -> IO a) -> IO a
jit c = EE.withMCJIT c (Just 3) Nothing Nothing Nothing

compileModule :: Expr -> CompileM ()
compileModule expr = compile expr >>= finalReturn

compile :: Expr -> CompileM CompileVal
compile expr = case expr of
  Lit x -> return . Operand . L.ConstantOperand . litVal $ x
  Var v -> asks $ (! v) . lEnv
  Let _ bound body -> do x <- compile bound
                         local (setLEnv $ addBVar x) (compile body)
  Lam _ body -> do env <- ask
                   return $ LamVal env body
  App e1 e2  -> do f <- compile e1
                   x <- compile e2
                   case f of
                     LamVal env body ->
                       withEnv (setLEnv (addBVar x) env) (compile body)
                     Builtin b vs -> compileBuiltin b (x:vs)
  For a body          -> throwError $ NotImplementedErr "for"
  Get e ie            -> throwError $ NotImplementedErr "get"
  TLam kinds expr     -> compile expr
  TApp expr ts        -> compile expr
  Unpack t bound body -> do
    ExPackage i x <- compile bound
    let updateEnv = setLEnv (addBVar x) . setTEnv (addBVar (RangeVal i))
    local updateEnv (compile body)

  where
    withEnv :: JITEnv -> CompileM a -> CompileM a
    withEnv env = local (\_ -> env)

compileBuiltin :: BuiltinFun -> [CompileVal] -> CompileM CompileVal
compileBuiltin b@(BuiltinFun numArgs compileRule) args =
    if length args < numArgs
      then return $ Builtin b args
      else compileRule args

litVal :: LitVal -> C.Constant
litVal lit = case lit of
  IntLit x -> C.Int 32 (fromIntegral x)
  RealLit x -> C.Float (L.Single x)

-- --- utilities ---

addLoop :: CompileM Operand -> CompileM () -> CompileM ()
addLoop cond body = do block <- newBlock
                       body
                       c <- cond
                       maybeLoop c block

newBlock :: CompileM L.Name
newBlock = do next <- freshName
              finishBlock (L.Br next []) next
              return next

maybeLoop :: Operand -> L.Name -> CompileM ()
maybeLoop c loop = do next <- freshName
                      finishBlock (L.CondBr c loop next []) next

addForILoop :: Operand -> (Ptr -> CompileM ()) -> CompileM ()
addForILoop n body = do
  i <- newIntCell 0
  let cond  = loadCell i >>= (`lessThan` n)
      body' = body i >> inc i
  addLoop cond body'
  where inc i = updateCell i $ add (litInt 1)

compileSum :: [CompileVal] -> CompileM CompileVal
compileSum [Pointer ptr] = do
  sum <- newIntCell 0
  let body iPtr = do i <- loadCell iPtr
                     x <- readArray ptr i
                     updateCell sum (add x)
  addForILoop (litInt 100) body
  ans <- loadCell sum
  return $ Operand ans

finalReturn :: CompileVal -> CompileM ()
finalReturn (Operand ret) = finishBlock (L.Ret (Just ret) []) (L.Name "")

appendInstr :: Instr -> CompileM ()
appendInstr instr = modify updateState
  where updateState state = state {curInstrs = instr : curInstrs state}

freshName :: CompileM L.Name
freshName = do i <- gets nameCounter
               modify (\state -> state {nameCounter = i + 1})
               return $ L.UnName (fromIntegral i)

finishBlock :: L.Terminator -> L.Name -> CompileM ()
finishBlock term newName = do
  CompileState count blocks instrs oldName <- get
  let newBlock = L.BasicBlock oldName (reverse instrs) (L.Do term)
  put $ CompileState count (newBlock:blocks) [] newName

evalInstr :: L.Type -> L.Instruction -> CompileM Operand
evalInstr ty instr = do
  x <- freshName
  appendInstr $ x L.:= instr
  return $ L.LocalReference ty x

litInt :: Int -> Operand
litInt x = L.ConstantOperand $ C.Int 32 (fromIntegral x)

add :: Operand -> Operand -> CompileM Operand
add x y = evalInstr intTy $ L.Add False False x y []

newIntCell :: Int -> CompileM Ptr
newIntCell x = do
  ptr <- liftM Ptr $ evalInstr intTy $ L.Alloca intTy Nothing 0 [] -- TODO: add to top block!
  writeCell ptr (litInt x)
  return ptr

loadCell :: Ptr -> CompileM Operand
loadCell (Ptr ptr) = evalInstr intTy $ L.Load False ptr Nothing 0 []

writeCell :: Ptr -> Operand -> CompileM ()
writeCell (Ptr ptr) x = appendInstr $ L.Do $ L.Store False ptr x Nothing 0 []

updateCell :: Ptr -> (Operand -> CompileM Operand) -> CompileM ()
updateCell ptr f = loadCell ptr >>= f >>= writeCell ptr

newArray :: Operand -> CompileM Ptr
newArray n = liftM Ptr $ evalInstr intPtrTy $ L.Alloca intTy (Just n) 0 []

readArray :: Ptr -> Operand -> CompileM Operand
readArray ptr idx = arrayPtr ptr idx >>= loadCell

writeArray :: Ptr -> Operand -> Operand -> CompileM ()
writeArray ptr idx val = arrayPtr ptr idx >>= flip writeCell val

arrayPtr :: Ptr -> Operand -> CompileM Ptr
arrayPtr (Ptr ptr) idx = liftM Ptr $ evalInstr intPtrTy $
                            L.GetElementPtr False ptr [idx] []

lessThan :: Operand -> Operand -> CompileM Operand
lessThan x y = evalInstr intTy $ L.ICmp L.SLT x y []

intTy :: L.Type
intTy = L.IntegerType 32

intPtrTy :: L.Type
intPtrTy = L.ptr intTy

-- --- builtins ---

builtinEnv :: JITEnv
builtinEnv = FullEnv builtins mempty

builtins :: Env Var CompileVal
builtins = newEnv
  [ ("add" , asBuiltin 2 $ compileBinop (\x y -> L.Add False False x y []))
  , ("mul" , asBuiltin 2 $ compileBinop (\x y -> L.Mul False False x y []))
  , ("sub" , asBuiltin 2 $ compileBinop (\x y -> L.Sub False False x y []))
  , ("iota", asBuiltin 1 $ compileIota)
  , ("sum" , asBuiltin 1 $ compileSum)
  ]

compileIota :: [CompileVal] -> CompileM CompileVal
compileIota [Operand n] = do
  ptr <- newArray n
  let body iPtr = do i <- loadCell iPtr
                     writeArray ptr i i
  addForILoop n body
  return $ ExPackage (litInt 100) (Pointer ptr)

asBuiltin :: Int -> CompileApp -> CompileVal
asBuiltin n f = Builtin (BuiltinFun n f) []

compileBinop :: (Operand -> Operand -> L.Instruction) -> CompileApp
compileBinop makeInstr = compile
  where
    compile :: [CompileVal] -> CompileM CompileVal
    compile [Operand x, Operand y] = liftM Operand $ evalInstr intTy (makeInstr y x)
