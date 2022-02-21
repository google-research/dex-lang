{-# LANGUAGE TemplateHaskell #-}

module Resources (dexrtBC, cssSource, javascriptSource, curResourceVersion) where

import qualified Data.ByteString.Char8 as B
import Data.FileEmbed

curResourceVersion :: String
curResourceVersion = __TIME__

dexrtBC :: B.ByteString
dexrtBC = $(embedFile "src/lib/dexrt.bc")

-- The CSS source code used for rendering Dex programs as HTML.
cssSource :: String
cssSource = B.unpack $(embedFile "static/style.css")

-- The JavaScript source code used for rendering Dex programs as HTML.
javascriptSource :: String
javascriptSource = B.unpack $(embedFile "static/index.js")
