-- Copyright 2021 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module Inference (trySynthTerm) where

import Name
import Syntax

trySynthTerm :: (Fallible1 m, EnvReader m) => Type n -> m n (Atom n)
