{-# LANGUAGE TemplateHaskell #-}

module Resources (dexrtBC, preludeSource, curResourceVersion) where

import qualified Data.ByteString.Char8 as B
import Data.FileEmbed

curResourceVersion :: String
curResourceVersion = __TIME__

dexrtBC :: B.ByteString
dexrtBC = $(embedFile "src/lib/dexrt.bc")

preludeSource :: String
preludeSource = B.unpack $ $(embedFile "lib/prelude.dx")
