-- Copyright 2022 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module AbstractSyntax (
  parseUModule, parseUModuleDeps,
  finishUModuleParse, preludeImportBlock,
  parseTopDeclRepl) where

import Data.Text (Text)
import Data.Text.Encoding qualified as T

import ConcreteSyntax
import Types.Source
import Util

-- TODO: implement this more efficiently rather than just parsing the whole
-- thing and then extracting the deps.
parseUModuleDeps :: ModuleSourceName -> File -> [ModuleSourceName]
parseUModuleDeps name file = deps
  where UModule _ deps _ = parseUModule name $ T.decodeUtf8 $ fContents file
{-# SCC parseUModuleDeps #-}

finishUModuleParse :: UModulePartialParse -> UModule
finishUModuleParse (UModulePartialParse name _ file) =
  parseUModule name (T.decodeUtf8 $ fContents file)

parseUModule :: ModuleSourceName -> Text -> UModule
parseUModule name s = do
  let blocks = mustParseit s sourceBlocks
  let blocks' = map undefined blocks  -- Convert to abstract syntax and error on failure
  let blocks'' = if name == Prelude
        then blocks'
        else preludeImportBlock : blocks'
  let imports = flip foldMap blocks'' \b -> case sbContents b of
                  (Misc (ImportModule moduleName)) -> [moduleName]
                  _ -> []
  UModule name imports blocks'
{-# SCC parseUModule #-}

preludeImportBlock :: SourceBlock
preludeImportBlock = SourceBlockP 0 0 LogNothing ""
  $ Misc $ ImportModule Prelude

parseTopDeclRepl :: Text -> Maybe SourceBlock
parseTopDeclRepl s = case sbContents b of
  UnParseable True _ -> Nothing
  _ -> Just b
  where b = undefined $ mustParseit s sourceBlock
{-# SCC parseTopDeclRepl #-}

