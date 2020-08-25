{-# LANGUAGE TemplateHaskell #-}

module Resources (dexrtBC) where

import qualified Data.ByteString as BS
import Data.FileEmbed

dexrtBC :: BS.ByteString
dexrtBC = $(embedFile "src/lib/dexrt.bc")
