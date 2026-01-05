-- Copyright 2025 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module Proto (
  Env,
  Name,
  Doc,
  BS.ByteString,
  ArgParser (..),
  OptionPayload (..),
  bs2str,
  str2bs,
  parseit,
  lexit,
  oneLiner,
  ProtoM (..),
  liftProtoM,
  getCtx,
  ParseTree (..),
  ParseTree' (..),
  ParseTreeAnn,
  runParser,
  ParseTreePath,
  Token (..),
  Token,
  throw,
  logM,
  runProtoM,
  AppendRef,
  newAppendRef,
  readAppendRef,
  append,
  parseArgsIO,
  readFile,
  parseTestFile,
  TestCase (..),
  Tests (..),
  captureLog,
  runTest,
  ) where

import Prelude hiding (readFile)
import Proto.Util
import Proto.Doc
import Proto.Parser
import Proto.Monad
import Proto.Testing
import qualified Data.ByteString as BS
