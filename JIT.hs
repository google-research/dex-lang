{-# LANGUAGE OverloadedStrings #-}

module JIT (lowerLLVM, showLLVM, evalJit) where

import qualified LLVM.AST as L
import qualified LLVM.AST.Global as L
import qualified LLVM.Module as Mod
import qualified LLVM.Analysis as Mod
import qualified LLVM.ExecutionEngine as EE
import LLVM.Internal.Context

import Data.Int
import Foreign.Ptr
import Data.ByteString.Char8 (unpack)

import qualified Syntax as S

foreign import ccall "dynamic" haskFun :: FunPtr (Int32 -> Int32) -> (Int32 -> Int32)


lowerLLVM :: S.Expr -> L.Module
lowerLLVM e = lm

showLLVM :: L.Module -> IO String
showLLVM m = withContext $ \c ->
               Mod.withModuleFromAST c lm $ \m ->
                 fmap unpack $ Mod.moduleLLVMAssembly m

evalJit :: L.Module -> IO String
evalJit lm =
  withContext $ \c ->
    Mod.withModuleFromAST c lm $ \m -> do
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

lm :: L.Module
lm = L.defaultModule
    { L.moduleName = "test"
    , L.moduleDefinitions = [L.GlobalDefinition fundef] }

fundef = L.functionDefaults
  { L.name        = L.Name "thefun"
  , L.parameters  = ([L.Parameter int (L.UnName 0) []], False)
  , L.returnType  = int
  , L.basicBlocks = [block] }

ret = L.LocalReference int (L.UnName 2)

block :: L.BasicBlock
block = L.BasicBlock (L.UnName 1) [instr] (L.Do $ L.Ret (Just ret) [])

instr :: L.Named L.Instruction
instr = (L.:=) (L.UnName 2)
  (L.Add False False (L.LocalReference int $ L.UnName 0)
                     (L.LocalReference int $ L.UnName 0) [])

runJitted :: FunPtr a -> Int32 -> Int32
runJitted fn = haskFun (castFunPtr fn :: FunPtr (Int32 -> Int32))

jit :: Context -> (EE.MCJIT -> IO a) -> IO a
jit c = EE.withMCJIT c (Just 3) Nothing Nothing Nothing
