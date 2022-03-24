-- Copyright 2022 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE RoleAnnotations #-}

module Types.Core where

import Name

data Atom (n::S)
type role Atom nominal

type AtomName = Name AtomNameC
type AtomSubstVal = SubstVal AtomNameC Atom :: V

instance SinkableE Atom
