-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE OverloadedStrings #-}

import Control.Monad
import qualified Hedgehog as H
import Control.Monad.Reader
import GHC.Stack
import qualified Data.Map.Strict as M

import Syntax hiding (Result)
import Parser
import PPrint
import GenExpr
import TestPass

main :: IO ()
main = void tests

prop_jitEval :: TypeEnv -> Evaluator -> Evaluator -> H.Property
prop_jitEval tenv jit interp =
  H.property $ do
    srcBlk <- H.forAllWith pprint (runReaderT genSourceBlock (makeGenEnv tenv defaultGenOptions))
    interres <- H.evalIO (interp srcBlk)
    H.annotate ("Interpreter result: " ++ pprint interres)
    jitres <- H.evalIO (jit srcBlk)
    pprint interres H.=== pprint jitres


getExpr :: TopDeclP b -> ExprP b
getExpr ~(EvalCmd (Command _ e)) = e

prop_pprint :: H.Property
prop_pprint =
  H.property $ do
    expr <- H.forAllWith pprint (runReaderT sampleExpr (makeGenEnv mempty defaultGenOptions))
    H.tripping expr pprintEsc (\s -> (getExpr . stripSrcAnnotTopDecl) <$> parseTopDecl s)

tests :: IO Bool
tests = do
  let prelude = "prelude.dx"
  jit <- runTestPass prelude fullPassJit
  interp <- runTestPass prelude fullPassInterp
  preludeEnv <- loadTypeEnv prelude
  let tyEnv = M.fromListWith (++) [(ty, [name]) | (ty, name) <- preludeEnv]
  H.checkParallel $ H.Group "TypeCheck" [
        ("prop_jitEval", prop_jitEval tyEnv jit interp)
      , ("prop_pprint", prop_pprint)
    ]
