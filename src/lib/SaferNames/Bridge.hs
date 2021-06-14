-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module SaferNames.Bridge
  ( BridgeState, BridgeModule, emptyBridgeState, updateBridgeState
  , moduleToSafe) where

import qualified            Syntax as D
import qualified SaferNames.Syntax as S

type BridgeState = ()

type BridgeModule = ()

emptyBridgeState :: BridgeState
emptyBridgeState = undefined

updateBridgeState :: D.Bindings -> BridgeState -> BridgeState
updateBridgeState = undefined

moduleToSafe :: BridgeState -> D.Module -> BridgeModule
moduleToSafe = undefined
