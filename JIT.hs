{-# LANGUAGE OverloadedStrings #-}

module JIT (lowerLLVM, showLLVM, evalJit, Compiled) where

import Control.Monad
import Control.Monad.Identity
import Control.Monad.Reader (ReaderT, runReaderT, local, ask)
import Control.Monad.Writer (WriterT, runWriterT, tell)
import Control.Monad.State (StateT, evalState, put, get)

import qualified LLVM.AST as L
import qualified LLVM.AST.Global as L
import qualified LLVM.AST.Constant as C
import qualified LLVM.Module as Mod
import qualified LLVM.Analysis as Mod
import qualified LLVM.ExecutionEngine as EE
import LLVM.Internal.Context

import Data.Int
import Foreign.Ptr
import Data.ByteString.Char8 (unpack)

import qualified Syntax as S
import qualified Interpreter as I

foreign import ccall "dynamic" haskFun :: FunPtr (Int32 -> Int32) -> (Int32 -> Int32)

type Compiled = L.Module
type Env = [Val]
data Val = Operand L.Operand
         | Builtin BuiltinVal [Val]
         | LamVal Env S.Expr
type Instr = L.Named L.Instruction
data BuiltinVal = Add | Mul


lowerLLVM :: I.ValEnv -> S.Expr -> L.Module
lowerLLVM interpEnv e =
  let env = map fromInterpVal interpEnv
      (finalVal, instrs) = runCompileMonad env (compile e)
  in case finalVal of Operand x -> makeModule instrs x

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

type CompileMonad a = ReaderT Env (
                        WriterT [Instr] (
                          StateT Int Identity)) a

runCompileMonad :: Env -> CompileMonad a -> (a, [Instr])
runCompileMonad env m = evalState (runWriterT (runReaderT m env)) 0

compile :: S.Expr -> CompileMonad Val
compile expr = case expr of
  S.Lit (S.IntLit x) -> return $ Operand $ L.ConstantOperand $ C.Int 32 (fromIntegral x)
  S.Var v            -> lookupEnv v
  S.Let p bound body -> do x <- compile bound
                           local (updateEnv $ valPatMatch p x) (compile body)
  S.Lam S.VarPat body -> do env <- ask
                            return $ LamVal env body
  S.App e1 e2        ->
    do f <- compile e1
       x <- compile e2
       case f of
         LamVal env body -> local (\_ -> x:env) (compile body)
         Builtin b [] -> return $ Builtin b [x]
         Builtin b [y] -> case (x, y) of
           (Operand x, Operand y) -> do
             out <- fresh
             case b of
               Add -> addInstr $ (L.:=) out (L.Add False False x y [])
               Mul -> addInstr $ (L.:=) out (L.Mul False False x y [])
             return $ Operand $ L.LocalReference int out




valPatMatch :: S.Pat -> Val -> [Val]
valPatMatch S.VarPat v = [v]

updateEnv :: [Val] -> Env -> Env
updateEnv = (++)

fresh :: CompileMonad L.Name
fresh = do i <- get
           put $ i + 1
           return $ L.UnName (fromIntegral i)

addInstr :: Instr -> CompileMonad ()
addInstr instr = tell [instr]


fromInterpVal :: I.Val -> Val
fromInterpVal v = case v of
  I.IntVal x -> Operand $ L.ConstantOperand $ C.Int 32 (fromIntegral x)
  I.Builtin b [] | I.builtinName b == "add" -> Builtin Add []
                 | I.builtinName b == "mul" -> Builtin Mul []
  I.LamVal (S.VarPat) (env, _) body -> LamVal (map fromInterpVal env) body
  x -> error $ "Can't compile value " ++ show x


lookupEnv :: Int -> CompileMonad Val
lookupEnv i = do env <- ask
                 return $ env !! i

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
            Just fn -> do let x = show $ runJitted fn 100
                          putStr $ x `seq` ""  -- segfaults without this
                          return x
            Nothing -> return "Failed - couldn't find function"

int :: L.Type
int = L.IntegerType 32

runJitted :: FunPtr a -> Int32 -> Int32
runJitted fn = haskFun (castFunPtr fn :: FunPtr (Int32 -> Int32))

jit :: Context -> (EE.MCJIT -> IO a) -> IO a
jit c = EE.withMCJIT c (Just 3) Nothing Nothing Nothing
