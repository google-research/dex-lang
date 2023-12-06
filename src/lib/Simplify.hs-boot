-- Copyright 2023 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module Simplify (linearizeTopFun) where

import Name
import Builder
import Types.Core
import Types.Top

linearizeTopFun :: (Mut n, Fallible1 m, TopBuilder m) => LinearizationSpec n -> m n (TopFunName n, TopFunName n)
