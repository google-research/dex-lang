{-# LANGUAGE OverloadedStrings #-}

module JIT (lowerLLVM, showLLVM, evalJit, Compiled, jitExpr, jitCmd) where

import Control.Monad
import Control.Monad.Except (throwError)
import Control.Monad.Reader (ReaderT, runReaderT, local, ask, asks)
import Control.Monad.Writer (WriterT, runWriterT, tell)
import Control.Monad.State (StateT, evalStateT, put, get)

import qualified Data.Map.Strict as M
import Data.Foldable (toList)

import qualified LLVM.AST as L
import qualified LLVM.AST.Global as L
import qualified LLVM.AST.Float as L
import qualified LLVM.AST.Constant as C
import qualified LLVM.Module as Mod
import qualified LLVM.Analysis as Mod
import qualified LLVM.ExecutionEngine as EE
import LLVM.Internal.Context

import Data.Int
import Foreign.Ptr
import Data.ByteString.Char8 (unpack)

import Syntax
import Env

foreign import ccall "dynamic" haskFun :: FunPtr Int32 -> Int32

type Compiled = L.Module
type JITEnv = FullEnv CompileVal ()
data CompileVal = Operand L.Operand
         | Builtin BuiltinVal [CompileVal]
         | LamVal JITEnv Expr

type Instr = L.Named L.Instruction
type BuiltinVal = (Int, [CompileVal] -> L.Instruction)

type CompileMonad a = ReaderT JITEnv (
                        WriterT [Instr] (
                          StateT Int (Either Err))) a

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
  (Operand out, instrs) <- runCompileMonad builtinEnv (compile expr)
  return $ makeModule instrs out

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

makeModule :: [Instr] -> L.Operand -> L.Module
makeModule instrs ret = mod
  where
    mod = L.defaultModule { L.moduleName = "test"
                          , L.moduleDefinitions = [L.GlobalDefinition fundef] }
    fundef = L.functionDefaults { L.name        = L.Name "thefun"
                                , L.parameters  = ([], False)
                                , L.returnType  = int
                                , L.basicBlocks = [block] }
    block = L.BasicBlock (L.Name "theblock") instrs (L.Do $ L.Ret (Just ret) [])

runCompileMonad :: JITEnv -> CompileMonad a -> Except (a, [Instr])
runCompileMonad env m = evalStateT (runWriterT (runReaderT m env)) 0

compile :: Expr -> CompileMonad CompileVal
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
  TApp expr ts        -> throwError $ NotImplementedErr "TApp"
  Unpack t bound body -> throwError $ NotImplementedErr "Unpack"

compileBuiltin :: BuiltinVal -> [CompileVal] -> CompileMonad CompileVal
compileBuiltin b@(numArgs, makeInstr) args =
    if length args < numArgs
      then return $ Builtin b args
      else do out <- fresh
              addInstr $ (L.:=) out (makeInstr (reverse args))
              return $ Operand $ L.LocalReference int out

litVal :: LitVal -> C.Constant
litVal lit = case lit of
  IntLit x -> C.Int 32 (fromIntegral x)
  RealLit x -> C.Float (L.Single x)

withEnv :: JITEnv -> CompileMonad a -> CompileMonad a
withEnv env = local (\_ -> env)

fresh :: CompileMonad L.Name
fresh = do i <- get
           put $ i + 1
           return $ L.UnName (fromIntegral i)

addInstr :: Instr -> CompileMonad ()
addInstr instr = tell [instr]

int :: L.Type
int = L.IntegerType 32

runJitted :: FunPtr a -> Int32
runJitted fn = haskFun (castFunPtr fn :: FunPtr Int32)

jit :: Context -> (EE.MCJIT -> IO a) -> IO a
jit c = EE.withMCJIT c (Just 3) Nothing Nothing Nothing

builtinEnv :: JITEnv
builtinEnv = FullEnv builtins mempty

builtins :: Env Var CompileVal
builtins = newEnv [(name, Builtin builtin []) | (name, builtin) <-
  [ ("add", (2, \[Operand x, Operand y]-> L.Add False False x y []))
  , ("mul", (2, \[Operand x, Operand y]-> L.Mul False False x y [])) ]
  ]
