-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module TestPass (typeCheckPass, fullPassInterp, fullPassJit,
                 runTestPass, Evaluator, loadTypeEnv) where

import Data.Void
import Control.Monad.State.Strict
import qualified Data.Map.Strict as M
import Unsafe.Coerce

import Pass
import DeShadow
import Inference
import Imp
import Syntax
import Type
import JIT
import Flops
import Normalize
import Simplify
import Interpreter
import Parser
import Env

typeCheckPass :: TopPass SourceBlock TopDecl
typeCheckPass = sourcePass >+> deShadowPass >+> typePass >+> checkTyped

fullPassInterp :: TopPass SourceBlock Void
fullPassInterp = typeCheckPass >+> interpPass

fullPassJit :: TopPass SourceBlock Void
fullPassJit = typeCheckPass >+> normalizePass >+> checkNExpr
                >+> derivPass     >+> checkNExpr
                >+> simpPass      >+> checkNExpr
                >+> impPass       >+> checkImp
                >+> flopsPass
                >+> jitPass


type TestFullPass env b =  SourceBlock -> TopPassM env b

evalDecl :: Monoid env => TestFullPass env b -> SourceBlock -> StateT env IO ()
evalDecl pass block = do
  env <- get
  (_, env') <- liftIO (runTopPassM env (pass block))
  modify (<> env')

loadFile :: (Monoid env) => String -> TestFullPass env b -> IO env
loadFile fname pass = do
    source <- readFile fname
    let sourceBlocks = parseProg source
    execStateT (mapM (evalDecl pass) sourceBlocks) mempty

type Evaluator = SourceBlock -> IO Result'

runTestPass :: String -> TopPass SourceBlock Void -> IO Evaluator
runTestPass fname (TopPass pass) = do
    env <- loadFile fname pass
    let eval source = do
            ~(Left res, _) <- runTopPassM env (pass source)
            return res
    return eval


loadTypeEnv :: String -> IO [(SigmaType, Name)]
loadTypeEnv fname =
    case sourcePass >+> deShadowPass >+> typePass of
        TopPass pass -> do
            envs <- loadFile fname pass
            let env = (snd (unsafeCoerce envs)) :: TypeEnv
            return $ case env of
                Env m -> [(ty, name) | (name, L ty) <- M.toList m]
