{-# LANGUAGE TemplateHaskell #-}

module Resources (dexrtBC, preludeSource, cssSource, curResourceVersion) where

import qualified Data.ByteString.Char8 as B
import Data.FileEmbed

curResourceVersion :: String
curResourceVersion = __TIME__

dexrtBC :: B.ByteString
dexrtBC = $(embedFile "src/lib/dexrt.bc")

-- The Dex prelude source code.
preludeSource :: String
preludeSource = B.unpack $(embedFile "lib/prelude.dx")

-- The source code of the CSS used for rendering Dex programs as HTML.
cssSource :: String
cssSource = B.unpack $(embedFile "static/style.css")