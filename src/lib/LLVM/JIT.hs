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

#if DEX_LLVM_VERSION == 9
import LLVM.V9.JIT
#elif DEX_LLVM_VERSION == HEAD
import LLVM.HEAD.JIT
#else
#error "Unknown LLVM version"
#endif
