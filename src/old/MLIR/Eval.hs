-- Copyright 2021 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module MLIR.Eval where

import Data.Function
import qualified Data.ByteString.Char8       as BSC8
import qualified Data.ByteString             as BS
import GHC.Stack

import qualified MLIR.AST                    as AST
import qualified MLIR.AST.Serialize          as AST
import qualified MLIR.Native                 as Native
import qualified MLIR.Native.Pass            as Native
import qualified MLIR.Native.ExecutionEngine as Native


import Syntax
-- TODO(apaszke): Separate the LitVal operations from LLVMExec
import LLVMExec

evalModule :: AST.Operation -> [LitVal] -> [BaseType] -> IO [LitVal]
evalModule ast args resultTypes =
  Native.withContext \ctx -> do
    Native.registerAllDialects ctx
    mOp     <- AST.fromAST ctx (mempty, mempty) ast
    Just m  <- Native.moduleFromOperation mOp
    verifyModule m
    Native.withPassManager ctx \pm -> do
      throwOnFailure "Failed to parse pass pipeline" $
        (Native.addParsedPassPipeline pm $ BS.intercalate ","
          [ "func(tensor-bufferize,std-bufferize,finalizing-bufferize)"
          , "convert-memref-to-llvm"
          , "convert-std-to-llvm"
          ])
      Native.runPasses pm m & throwOnFailure "Failed to lower module"
    verifyModule m
    Native.withExecutionEngine m \(Just eng) -> do
      Native.withStringRef "entry" \name -> do
        allocaCells (length args) \argsPtr ->
          allocaCells (length resultTypes) \resultPtr -> do
            storeLitVals argsPtr args
            Just () <- Native.executionEngineInvoke @() eng name
              [Native.SomeStorable argsPtr, Native.SomeStorable resultPtr]
            loadLitVals resultPtr resultTypes

verifyModule :: HasCallStack => Native.Module -> IO ()
verifyModule m = do
  correct <- Native.verifyOperation =<< Native.moduleAsOperation m
  case correct of
    True  -> return ()
    False -> do
      modStr <- BSC8.unpack <$> Native.showModule m
      error $ "Invalid module:\n" ++ modStr

throwOnFailure :: String -> IO Native.LogicalResult -> IO ()
throwOnFailure msg m = do
  result <- m
  case result of
    Native.Success -> return ()
    Native.Failure -> error msg
