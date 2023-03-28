-- Copyright 2023 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module Dex.Foreign.JAX where

import Control.Monad.IO.Class
import Data.Aeson (encode, eitherDecode')
import qualified Data.ByteString.Lazy.Char8 as B
import Foreign.C
import Foreign.Ptr

import Dex.Foreign.Context
import Export
import JAX.Concrete
import JAX.Rename
import JAX.ToSimp
import Name

-- TODO newCString just mallocs the string; we have to
-- arrange for the caller to free it.
dexRoundtripJaxprJson :: CString -> IO CString
dexRoundtripJaxprJson jsonPtr = do
  json <- B.pack <$> peekCString jsonPtr
  let maybeJaxpr :: Either String (ClosedJaxpr VoidS) = eitherDecode' json
  case maybeJaxpr of
    Right jaxpr -> do
      let redumped = encode jaxpr
      newCString $ B.unpack redumped
    Left err -> newCString err

dexCompileJaxpr :: Ptr Context -> CInt -> CString -> IO ExportNativeFunctionAddr
dexCompileJaxpr ctxPtr ccInt jsonPtr = do
  json <- B.pack <$> peekCString jsonPtr
  let maybeJaxpr :: Either String (ClosedJaxpr VoidS) = eitherDecode' json
  case maybeJaxpr of
    Right jaxpr -> runTopperMFromContext ctxPtr do
      Distinct <- getDistinct
      jRename <- liftRenameM $ renameClosedJaxpr (unsafeCoerceE jaxpr)
      sLam <- liftJaxSimpM $ simplifyClosedJaxpr jRename
      func <- prepareSLamForExport (intAsCC ccInt) sLam
      liftIO $ emitExport ctxPtr func
    Left err -> error err
