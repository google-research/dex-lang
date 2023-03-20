-- Copyright 2023 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module JaxADTSpec (spec) where

import qualified Data.ByteString.Lazy.Char8 as B
import Data.Aeson (encode, decode)
import Data.Aeson.Encode.Pretty (encodePretty)
import Test.Hspec

import Name
import JAX.Concrete

x_nm, y_nm :: JSourceName
x_nm = JSourceName 0 0 "x"
y_nm = JSourceName 1 0 "y"

ten_vec :: JVarType
ten_vec = (JArrayName [DimSize 10] F32)

a_jaxpr :: Jaxpr
a_jaxpr = Jaxpr
  (Nest (JBindSource x_nm ten_vec) Empty)
  Empty
  (Nest (JEqn
    (Nest (JBindSource y_nm ten_vec) Empty)
    Sin
    [JVariable $ JVar (SourceName x_nm) ten_vec]) Empty)
  [JVariable $ JVar (SourceName y_nm) ten_vec]

spec :: Spec
spec = do
  describe "JaxADT" do
    it "round-trips to json" do
      -- putStrLn $ B.unpack $ encodePretty a_jaxpr
      let first = encode a_jaxpr
      let (Just decoded) = (decode first :: Maybe Jaxpr)
      let second = encode decoded
      second `shouldBe` first
