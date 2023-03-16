-- Copyright 2023 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module Dex.Foreign.JAX where

import Data.Aeson (encode, eitherDecode')
import qualified Data.ByteString.Lazy.Char8 as B
import Foreign.C

import JAX.Concrete

dexRoundtripJaxprJson :: CString -> IO CString
dexRoundtripJaxprJson jsonPtr = do
  json <- B.pack <$> peekCString jsonPtr
  let maybeJaxpr :: Either String Jaxpr = eitherDecode' json
  case maybeJaxpr of
    Right jaxpr -> do
      let redumped = encode jaxpr
      newCString $ B.unpack redumped
    Left err -> newCString err
