-- Copyright 2023 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module JaxADTSpec (spec) where

import Data.Aeson (encode, decode)
import Test.Hspec

import Name
import JAX.Concrete
import JAX.Rename
import JAX.ToSimp
import Runtime
import TopLevel
import Types.Imp
import Types.Primitives hiding (Sin)
import Types.Source hiding (SourceName)

x_nm, y_nm :: JSourceName
x_nm = JSourceName 0 0 "x"
y_nm = JSourceName 1 0 "y"

float :: JVarType
float = (JArrayName [] F32)

ten_vec :: JVarType
ten_vec = (JArrayName [DimSize 10] F32)

a_jaxpr :: JVarType -> Jaxpr VoidS
a_jaxpr ty = Jaxpr
  (Nest (JBindSource x_nm ty) Empty)
  Empty
  (Nest (JEqn
    (Nest (JBindSource y_nm ty) Empty)
    Sin
    [JVariable $ JVar (SourceName x_nm) ty]) Empty)
  [JVariable $ JVar (SourceName y_nm) ty]

compile :: Jaxpr VoidS -> IO LLVMCallable
compile jaxpr = do
  let cfg = EvalConfig LLVM [LibBuiltinPath] Nothing Nothing Nothing NoOptimize PrintCodegen
  env <- initTopState
  fst <$> runTopperM cfg env do
    -- TODO Implement GenericE for jaxprs, derive SinkableE, and properly sink
    -- the jaxpr instead of just coercing it.
    Distinct <- getDistinct
    jRename <- liftRenameM $ renameJaxpr (unsafeCoerceE jaxpr)
    jSimp <- liftJaxSimpM $ simplifyJaxpr jRename
    compileTopLevelFun (EntryFunCC CUDANotRequired) jSimp >>= packageLLVMCallable

spec :: Spec
spec = do
  describe "JaxADT" do
    it "round-trips to json" do
      let first = encode $ a_jaxpr ten_vec
      let (Just decoded) = (decode first :: Maybe (Jaxpr VoidS))
      let second = encode decoded
      second `shouldBe` first
    it "executes" do
      jLLVM <- compile $ a_jaxpr float
      result <- callEntryFun jLLVM [Float32Lit 3.0]
      result `shouldBe` [Float32Lit $ sin 3.0]
