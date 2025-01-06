-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE NoFieldSelectors #-}

module PPrint (
  Pretty (..), indent, emitLine, hcat, hlist, pprint, app, pprintStr,
  (<+>), BSBuilder, forceOneLine) where

import Data.ByteString.Internal (w2c)
import Data.Int
import Data.Word
import Data.List (intersperse)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Builder as BS
import Data.String
import Control.Monad.State.Strict

pprint :: Pretty a => a -> BString
pprint x = runPrinter $ prLines x
{-# SCC pprint #-}

pprintStr :: Pretty a => a -> String
pprintStr x = bs2str $ pprint x

bs2str :: BString -> String
bs2str s = map w2c $ BS.unpack s

-- === printing doc ===

type BString = BS.ByteString
type Indent = BS.Builder
type BSBuilder = BS.Builder

data PrinterState = PrinterState {indent :: Indent, curString  :: BS.Builder }
newtype PrinterM a = PrinterM { inner :: State PrinterState a }
        deriving (Functor, Applicative, Monad)

class Pretty a where
  pr :: a -> BSBuilder

  prLines :: a -> PrinterM ()
  prLines x = emitLine $ pr x

  prList :: [a] -> BS.Builder
  prList xs = hlist "[,]" $ map pr xs

runPrinter :: PrinterM a -> BString
runPrinter cont = BS.toStrict $ BS.toLazyByteString $ (.curString) $
  execState cont.inner $ PrinterState mempty mempty

-- This is a fallback and we shouldn't see its output much
forceOneLine :: PrinterM () -> BSBuilder
forceOneLine x = "\n{" <> BS.byteString (runPrinter x) <> "}\n"

indent :: PrinterM a -> PrinterM a
indent cont = PrinterM do
  prev <- gets (.indent)
  modify \s -> s {indent = prev <> "  "}
  ans <- cont.inner
  modify \s -> s {indent = prev}
  return ans

emitLine :: BS.Builder -> PrinterM ()
emitLine b = PrinterM do
  s <- get
  put $ s {curString = s.curString <> "\n" <> s.indent <> b}

hlist :: String -> [BS.Builder] -> BS.Builder
hlist [l,sep,r] xs = hcat [pr l, hcat (intersperse (pr sep) xs), pr r]
hlist _ _ = error "expected left bracket, separator, right bracket"

hcat :: [BS.Builder] -> BS.Builder
hcat = mconcat

app :: BS.Builder -> [BS.Builder] -> BS.Builder
app f xs = hcat [f, hlist "(,)" xs]

infixr 6 <+>
(<+>) :: BS.Builder -> BS.Builder -> BS.Builder
(<+>) x y = hcat [x, " ", y]

-- === instances ===

instance IsString (PrinterM ()) where
  fromString s = emitLine $ fromString s

instance Pretty Char where
  pr c = fromString [c]
  prList s = fromString s

instance Pretty a => Pretty [a] where
  pr xs = prList xs

instance Pretty BString where
  pr s = BS.byteString s

instance (Pretty a, Pretty b) => Pretty (a, b) where
  pr (x, y) = hcat ["(", pr x, ", ", pr y, ")"]

instance Pretty a => Pretty (Maybe a) where
  pr = \case
    Nothing -> ""
    Just x -> pr x

instance Pretty Int    where pr x = pr $ show x
instance Pretty Int32  where pr x = pr $ show x
instance Pretty Int64  where pr x = pr $ show x
instance Pretty Float  where pr x = pr $ show x
instance Pretty Double where pr x = pr $ show x
instance Pretty Word64 where pr x = pr $ show x
