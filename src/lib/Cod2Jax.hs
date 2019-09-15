{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE ForeignFunctionInterface #-}

module Cod2Jax where

import Foreign.C.String
import Data.Aeson
import GHC.Generics
import Data.ByteString.Lazy.Char8 (pack, unpack)

foreign export ccall loadSource :: CString -> IO CString

loadSource :: CString -> IO CString
loadSource = callSerialized loadSource'

data Jaxpr = JaxprSin | JaxprCos  deriving (Generic, Show)

loadSource' :: String -> IO [(String, Jaxpr)]
loadSource' source =
  case source of
    "f = sin" -> return [("f", JaxprSin)]
    "f = cos" -> return [("f", JaxprCos)]
    _ -> error "don't recognized this program"

-- automatically derived serialization
instance ToJSON Jaxpr
instance FromJSON Jaxpr

callSerialized :: (ToJSON a, FromJSON a, ToJSON b, FromJSON b) =>
                    (a -> IO b) -> CString -> IO CString
callSerialized f arg = do
  arg' <- peekCString arg
  case eitherDecode (pack arg') of
    Left e -> do
      putStrLn $ "Can't decode:\n" ++ arg' ++ "\n"
      error e  -- TODO: handle errors more gracefully
    Right arg'' -> do
      ans <- f arg''
      newCString $ unpack $ encode ans
