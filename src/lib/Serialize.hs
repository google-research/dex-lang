-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE OverloadedStrings #-}

module Serialize (serialize, deSerialize, loadDataLiteral) where

import Control.Monad
import Data.Word (Word64)
import Data.Binary.IEEE754 (doubleToWord)

import Syntax
import Parser
import Pass
import Inference
import PPrint

-- TODO: use TopPassM instead of IO after we stop treating outputs like errors
-- TODO: get rid of Vec and use this general-purpose ser-des instead
-- TODO: break into separate normalization (unzipping) and serialization passes

loadDataLiteral :: String -> IO (Type, [BinVal])
loadDataLiteral fname = do
  source <- readFile fname
  let uval = ignoreExcept $ parseData source
  let (ty, val) = ignoreExcept $ inferExpr uval
  xs <- serialize (stripSrcAnnot val)
  return (ty, xs)

serialize :: Val -> IO [BinVal]
serialize val = case val of
  Lit x -> return [uncurry ScalarVal (serializeScalar x)]
  RecCon _ r -> liftM concat $ traverse serialize r
  TabCon ~(TabType (IdxSetLit n) eltTy) xs -> error "Not implemented"
  _ -> error $ "Not implemented: " ++ pprint val

serializeScalar :: LitVal -> (Word64, BaseType)
serializeScalar val = case val of
  IntLit  x -> (fromIntegral x, IntType)
  RealLit x -> (doubleToWord x, RealType)
  BoolLit True  -> (fromIntegral (1::Int), BoolType)
  BoolLit False -> (fromIntegral (0::Int), BoolType)
  _ -> error "Not implemented"

deSerialize :: Type -> [BinVal] -> IO Val
deSerialize = undefined
