{-# LANGUAGE TemplateHaskell #-}

module Resources (dexrtBC, preludeSource) where

import qualified Data.ByteString.Char8 as B
import Data.FileEmbed

dexrtBC :: B.ByteString
dexrtBC = $(embedFile "src/lib/dexrt.bc")

preludeSource :: String
preludeSource = B.unpack $ $(embedFile "prelude.dx")
