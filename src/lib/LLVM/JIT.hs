-- Copyright 2021 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE OverloadedStrings #-}

module LLVM.JIT (
  JIT, createJIT, destroyJIT, withJIT,
  NativeModule, compileModule, unloadNativeModule, withNativeModule,
  getFunctionPtr
  ) where

import LLVM.HEAD.JIT