{-# LANGUAGE OverloadedStrings #-}

module JIT (lowerLLVM, showLLVM, evalJit, Compiled) where

import Control.Monad
import Control.Monad.Identity
import Control.Monad.Reader (ReaderT, runReaderT, local, ask)
import Control.Monad.Writer (WriterT, runWriterT, tell)
import Control.Monad.State (StateT, evalState, put, get)

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

import qualified Syntax as S
import qualified Interpreter as I
import Record
import qualified Env as E

foreign import ccall "dynamic" haskFun :: FunPtr Int32 -> Int32

type Compiled = L.Module
type Env = E.Env S.LetVar Val
data Val = Operand L.Operand
         | Builtin BuiltinVal [Val]
         | LamVal S.Pat Env S.Expr
         | RecVal (Record Val)

type Instr = L.Named L.Instruction
type BuiltinVal = (Int, [Val] -> L.Instruction)

lowerLLVM :: E.FreeEnv I.Val -> S.Expr -> L.Module
lowerLLVM interpEnv e =
  let env = fmap fromInterpVal (E.envFromFree interpEnv)
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
  S.Lit x -> return . Operand . L.ConstantOperand . litVal $ x
  S.Var v -> lookupEnv v
  S.Let p bound body -> do x <- compile bound
                           local (updateEnv $ valPatMatch p x) (compile body)
  S.Lam p body -> do env <- ask
                     return $ LamVal p env body
  S.App e1 e2  -> do f <- compile e1
                     x <- compile e2
                     case f of
                       LamVal p env body ->
                         withEnv (E.catEnv env $ valPatMatch p x) (compile body)
                       Builtin b vs -> compileBuiltin b (x:vs)
  S.RecCon r   -> liftM RecVal $ mapM compile r

compileBuiltin :: BuiltinVal -> [Val] -> CompileMonad Val
compileBuiltin b@(numArgs, makeInstr) args =
    if length args < numArgs
      then return $ Builtin b args
      else do out <- fresh
              addInstr $ (L.:=) out (makeInstr (reverse args))
              return $ Operand $ L.LocalReference int out

litVal :: S.LitVal -> C.Constant
litVal lit = case lit of
  S.IntLit x -> C.Int 32 (fromIntegral x)
  S.RealLit x -> C.Float (L.Single x)

withEnv :: Env -> CompileMonad a -> CompileMonad a
withEnv env = local (\_ -> env)

valPatMatch :: S.Pat -> Val -> [Val]
valPatMatch (S.VarPat _) v = [v]
valPatMatch (S.RecPat p) (RecVal v) = let vs = toList v
                                          ps = toList p
                                      in concat $ zipWith valPatMatch ps vs

updateEnv :: [Val] -> Env -> Env
updateEnv = flip E.catEnv

fresh :: CompileMonad L.Name
fresh = do i <- get
           put $ i + 1
           return $ L.UnName (fromIntegral i)

addInstr :: Instr -> CompileMonad ()
addInstr instr = tell [instr]


fromInterpVal :: I.Val -> Val
fromInterpVal v = case v of
  I.IntVal x -> Operand $ L.ConstantOperand $ C.Int 32 (fromIntegral x)
  I.Builtin b vs -> case M.lookup (I.builtinName b) builtins of
                      Just b -> Builtin b (map fromInterpVal vs)
  I.LamVal p (env, _) body -> LamVal p (fmap fromInterpVal env) body
  I.RecVal r -> RecVal $ fmap fromInterpVal r
  x -> error $ "Can't compile value " ++ show x


lookupEnv :: S.LetVar -> CompileMonad Val
lookupEnv i = do env <- ask
                 return $ env E.!! i

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

int :: L.Type
int = L.IntegerType 32

runJitted :: FunPtr a -> Int32
runJitted fn = haskFun (castFunPtr fn :: FunPtr Int32)

jit :: Context -> (EE.MCJIT -> IO a) -> IO a
jit c = EE.withMCJIT c (Just 3) Nothing Nothing Nothing


builtins :: M.Map String BuiltinVal
builtins = M.fromList $
  [ ("add", (2, \[Operand x, Operand y]-> L.Add False False x y []))
  , ("mul", (2, \[Operand x, Operand y]-> L.Mul False False x y [])) ]
