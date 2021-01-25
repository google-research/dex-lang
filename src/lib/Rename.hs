-- Copyright 2021 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module Rename (renameUModule) where

import Preamble
import Base
import Core


-- TODO: this could toposort too
--    * should those errors be finer-grained?









renameUModule :: MonadLogger m
              => SourceNameMap n -> UModule SourceNS -> m (UModule n)
renameUModule = undefined
