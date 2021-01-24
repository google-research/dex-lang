{-# LANGUAGE TemplateHaskell #-}

module Resources (dexrtBC, preludeSource, cssSource, staticOnloadJavascriptSource, curResourceVersion) where

import qualified Data.ByteString.Char8 as B
import Data.FileEmbed

curResourceVersion :: String
curResourceVersion = __TIME__

dexrtBC :: B.ByteString
dexrtBC = $(embedFile "src/lib/dexrt.bc")

-- The Dex prelude source code.
preludeSource :: String
preludeSource = B.unpack $(embedFile "lib/prelude.dx")

-- The CSS source code used for rendering Dex programs as static HTML.
cssSource :: String
cssSource = B.unpack $(embedFile "static/style.css")

-- The "document onload" JavaScript source code used for rendering Dex programs as static HTML.
staticOnloadJavascriptSource :: String
staticOnloadJavascriptSource = B.unpack $(embedFile "static/static-onload.js")