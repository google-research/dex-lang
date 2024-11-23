-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module PPrint (Pretty (..), Doc (..), indent, hcat, hlist, vcat, pprint, app) where

import Data.Int
import Data.Word
import Data.List (intersperse)
import Data.String
import Data.Text (Text, unpack)
import Control.Monad.Reader
import Control.Monad.State.Strict

pprint :: Pretty a => a -> String
pprint x = printDoc $ pr x
{-# SCC pprint #-}

-- === printing doc ===

newtype PrinterM a = PrinterM { runPrinterM :: ReaderT Int (State [(Int, String)]) a }
        deriving (Functor, Applicative, Monad)

runPrinter :: PrinterM a -> String
runPrinter cont = do
  let indentedLines = reverse $ execState (runReaderT (runPrinterM cont) 0) []
  concat [replicate (2 * indents) ' ' <> s <> "\n"| (indents, s) <- indentedLines]

printDoc :: Doc -> String
printDoc d = runPrinter $ printDocM d

emitLine :: String -> PrinterM ()
emitLine s = do
  curIndent <- PrinterM ask
  PrinterM $ modify \indentedLines -> (curIndent, s) : indentedLines

increaseIndent :: PrinterM a -> PrinterM a
increaseIndent cont = PrinterM $ local (+ 1) $ runPrinterM cont

printDocM :: Doc -> PrinterM ()
printDocM = \case
  DocLine s -> emitLine s
  DocIndent d -> increaseIndent $ printDocM d
  DocItems ds -> mapM_ printDocM ds

-- === constructing doc ===

class Pretty a where
  pr :: a -> Doc

  prList :: [a] -> Doc
  prList xs = hlist "[,]" $ map pr xs

data Doc =
   DocLine   String
 | DocItems  [Doc]
 | DocIndent Doc
   deriving (Show)

vcat :: [Doc] -> Doc
vcat = DocItems

hlist :: String -> [Doc] -> Doc
hlist [l,sep,r] xs = hcat [pr l, hcat (intersperse (pr sep) xs), pr r]

hlist _ _ = error "expected left bracket, separator, right bracket"

hcat :: [Doc] -> Doc
hcat docs = rec "" docs
 where
  rec :: String -> [Doc] -> Doc
  rec s = \case
    [] -> DocLine s
    d:ds -> case d of
      DocLine s' -> rec (s <> s') ds
      _ -> vcat [DocLine s, d, hcat ds]

indent :: Doc -> Doc
indent = DocIndent

app :: Doc -> [Doc] -> Doc
app f xs = hcat [f, hlist "(,)" xs]

-- === instances ===

instance IsString Doc where
  fromString = DocLine

instance Pretty Char where
  pr c = DocLine [c]
  prList = DocLine

instance Pretty a => Pretty [a] where
  pr xs = prList xs

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
instance Pretty Text   where pr x = pr $ unpack x
