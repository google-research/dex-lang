-- Copyright 2021 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module MLIR.Eval where

import Data.Functor

import qualified MLIR.AST                    as AST
import qualified MLIR.AST.Serialize          as AST
import qualified MLIR.Native                 as Native
import qualified MLIR.Native.Pass            as Native
import qualified MLIR.Native.ExecutionEngine as Native


import Syntax
-- TODO(apaszke): Separate the LitVal operations from LLVMExec
import LLVMExec

evalModule :: AST.Operation -> [LitVal] -> [BaseType] -> IO [LitVal]
evalModule mOp args resultTypes =
  Native.withContext \ctx -> do
    Native.registerAllDialects ctx
    Just m <- Native.moduleFromOperation =<< AST.fromAST ctx (mempty, mempty) mOp
    Native.withPassManager ctx \pm -> do
      Native.addConvertStandardToLLVMPass pm
      Native.runPasses pm m <&> \case
        Native.Success -> ()
        Native.Failure -> error "Failed to lower to LLVM"
    Native.withExecutionEngine m \(Just eng)-> do
      Native.withStringRef "entry" \name -> do
        allocaCells (length args) \argsPtr ->
          allocaCells (length resultTypes) \resultPtr -> do
            storeLitVals argsPtr args
            Just () <- Native.executionEngineInvoke @() eng name
              [Native.SomeStorable argsPtr, Native.SomeStorable resultPtr]
            loadLitVals resultPtr resultTypes
