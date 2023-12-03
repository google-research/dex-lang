-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE IncoherentInstances #-}  -- due to `ConRef`
{-# LANGUAGE UndecidableInstances #-}

module PPrint (
  Pretty (..), Doc, DocPrec, (<+>), pprint, pprintList, asStr , atPrec,
  pAppArg, pApp, pArg, hardline, PrettyPrec(..), PrecedenceLevel (..),
  docAsStr, parensSep, prettyLines, sep, pLowest, prettyFromPrettyPrec,
  indented, commaSep, spaced, spaceIfColinear, encloseSep) where

import Data.Foldable (toList, fold)
import Data.Text.Prettyprint.Doc.Render.Text
import Data.Text.Prettyprint.Doc
import Data.Text (unpack)
import System.IO.Unsafe
import qualified System.Environment as E

-- === small pretty-printing utils ===

pprint :: Pretty a => a -> String
pprint x = docAsStr $ pretty x
{-# SCC pprint #-}

docAsStr :: Doc ann -> String
docAsStr doc = unpack $ renderStrict $ layoutPretty layout $ doc

layout :: LayoutOptions
layout = if unbounded then LayoutOptions Unbounded else defaultLayoutOptions
  where unbounded = unsafePerformIO $ (Just "1"==) <$> E.lookupEnv "DEX_PPRINT_UNBOUNDED"

-- === DocPrec ===

-- A DocPrec is a slightly context-aware Doc, specifically one that
-- knows the precedence level of the immediately enclosing operation,
-- and can decide to parenthesize itself accordingly.
-- For example, when printing `x = f (g 1)`, we know that
-- - We need parens around `(g 1)` because applying `f` binds
--   tighter than applying `g` (because application is left-associative)
-- - We do not need parens around `g` or 1, because there is nothing
--   there that may bind less tightly than the function applications.
-- - We also do not need parens around the whole RHS `f (g 1)`, because
--   the `=` binds less tightly than applying `f`.
--
-- This is accomplished in the `Expr` instance of `PrettyPrec` by
-- coding function application to require `ArgPrec` from the arguments
-- (via the default behavior of `prettyFromPrettyPrec`), but to
-- provide only `AppPrec` for the application expression itself.  The
-- outer application is not wrapped in parens because the let binding
-- prints its RHS at `LowestPrec`.
type DocPrec ann = PrecedenceLevel -> Doc ann

-- Specifies what kinds of operations are allowed to be printed at
-- this point without wrapping in parens.
data PrecedenceLevel =
    -- Any subexpression is allowed without parens
    LowestPrec
    -- Function application is allowed without parens, but nothing
    -- that binds less tightly
  | AppPrec
    -- Only single symbols and parens allowed
  | ArgPrec
  deriving (Eq, Ord)

class PrettyPrec a where
  prettyPrec :: a -> DocPrec ann

-- `atPrec prec doc` will ensure that the precedence level is at most
-- `prec` when running `doc`, wrapping with parentheses if needed.
-- To wit,
-- - `atPrec LowestPrec` means "wrap unless the context permits all
--   subexpressions unwrapped"
-- - `atPrec AppPrec` means "wrap iff the context requires ArgPrec"
-- - `atPrec ArgPrec` means "never wrap" (unless the
--   `PrecedenceLevel` ADT is extended later).
atPrec :: PrecedenceLevel -> Doc ann -> DocPrec ann
atPrec prec doc requestedPrec =
  if requestedPrec > prec then parens (align doc) else doc

prettyFromPrettyPrec :: PrettyPrec a => a -> Doc ann
prettyFromPrettyPrec = pArg

pAppArg :: (PrettyPrec a, Foldable f) => Doc ann -> f a -> Doc ann
pAppArg name as = align $ name <> group (nest 2 $ foldMap (\a -> line <> pArg a) as)

pprintList :: Pretty a => [a] -> String
pprintList xs = asStr $ vsep $ punctuate "," (map pretty xs)

asStr :: Doc ann -> String
asStr doc = unpack $ renderStrict $ layoutPretty layout $ doc

pLowest :: PrettyPrec a => a -> Doc ann
pLowest a = prettyPrec a LowestPrec

pApp :: PrettyPrec a => a -> Doc ann
pApp a = prettyPrec a AppPrec

pArg :: PrettyPrec a => a -> Doc ann
pArg a = prettyPrec a ArgPrec

prettyLines :: (Foldable f, Pretty a) => f a -> Doc ann
prettyLines xs = foldMap (\d -> hardline <> pretty d) $ toList xs

parensSep :: Doc ann -> [Doc ann] -> Doc ann
parensSep separator items = encloseSep "(" ")" separator items

spaceIfColinear :: Doc ann
spaceIfColinear = flatAlt "" space

instance PrettyPrec a => PrettyPrec [a] where
  prettyPrec xs = atPrec ArgPrec $ hsep $ map pLowest xs

instance PrettyPrec () where prettyPrec = atPrec ArgPrec . pretty

spaced :: (Foldable f, Pretty a) => f a -> Doc ann
spaced xs = hsep $ map pretty $ toList xs

commaSep :: (Foldable f, Pretty a) => f a -> Doc ann
commaSep xs = fold $ punctuate "," $ map pretty $ toList xs

indented :: Doc ann -> Doc ann
indented doc = nest 2 (hardline <> doc) <> hardline
