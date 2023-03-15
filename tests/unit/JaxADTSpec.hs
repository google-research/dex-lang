-- Copyright 2023 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module JaxADTSpec (spec) where

import qualified Data.ByteString.Lazy.Char8 as B
import Data.Aeson (encode)
import Data.Aeson.Encode.Pretty (encodePretty)
import Test.Hspec

import JAX.Concrete

a_jaxpr = Jaxpr
  [Binder "x" (JArrayName [DimSizeName $ JLitInt 10] F32)]
  [JVar $ JVariable "x" (JArrayName [DimSizeName $ JLitInt 10] F32)]
  [JDecl
    [Binder "y" (JArrayName [DimSizeName $ JLitInt 10] F32)]
    Sin
    [JVar $ JVariable "x" (JArrayName [DimSizeName $ JLitInt 10] F32)]]

spec :: Spec
spec = do
  describe "JaxADT" do
    it "jsonifies" do
      putStrLn $ B.unpack $ encodePretty a_jaxpr
      encode a_jaxpr `shouldBe` "foo"
