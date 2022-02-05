{-# LANGUAGE TemplateHaskell #-}

module Resources (dexrtBC, preludeSource, cssSource, javascriptSource, curResourceVersion) where

import qualified Data.ByteString.Char8 as B
import Data.FileEmbed
import Util (addHash, File)

curResourceVersion :: String
curResourceVersion = __TIME__

dexrtBC :: B.ByteString
dexrtBC = $(embedFile "src/lib/dexrt.bc")

-- The Dex prelude source code.
preludeSource :: File
preludeSource = addHash $(embedFile "lib/prelude.dx")

-- The CSS source code used for rendering Dex programs as HTML.
cssSource :: String
cssSource = B.unpack $(embedFile "static/style.css")

-- The JavaScript source code used for rendering Dex programs as HTML.
javascriptSource :: String
javascriptSource = B.unpack $(embedFile "static/index.js")
