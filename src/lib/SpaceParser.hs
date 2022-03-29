-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module SpaceParser where

-- This is white-space sensitive part of the Dex parser, which can be
-- resued for both AST building in Parser.hs and for
-- indentation-preserving renaming in Renamer.hs.

import Control.Monad
import Data.Scientific qualified as Scientific
import Data.Void
import Text.Megaparsec hiding (Label, State)
import Text.Megaparsec.Char hiding (space)
import Text.Megaparsec.Char.Lexer qualified as L

type Parser = Parsec Void String

upperName :: Parser String
upperName = checkNotKeyword $ (:) <$> upperChar <*> many nameTailChar

lowerName :: Parser String
lowerName = checkNotKeyword $ (:) <$> lowerChar <*> many nameTailChar

fieldLabel :: Parser String
fieldLabel = checkNotKeyword $ (:) <$> (lowerChar <|> upperChar) <*> many nameTailChar

primName :: Parser String
primName = try $ char '%' >> some alphaNumChar

charLit :: Parser Char
charLit = char '\'' >> L.charLiteral <* char '\''

strLit :: Parser String
strLit = char '"' >> manyTill L.charLiteral (char '"')

intLit :: Parser Int
intLit = try $ L.decimal <* notFollowedBy (char '.')

doubleLit :: Parser Double
doubleLit = try L.float
  <|> try (fromIntegral <$> (L.decimal :: Parser Int) <* char '.')
  <|> try do
    s <- L.scientific
    case Scientific.toBoundedRealFloat s of
      Right f -> return f
      Left  _ -> fail "Non-representable floating point literal"

nameTailChar :: Parser Char
nameTailChar = alphaNumChar <|> char '\'' <|> char '_'

symChar :: Parser Char
symChar = choice $ map char symChars

symChars :: [Char]
symChars = ".,!$^&*:-~+/=<>|?\\@"

symName :: Parser String
symName = try $ between (char '(') (char ')') $ some symChar

backquoteName :: Parser String
backquoteName = try $ between (char '`') (char '`') (upperName <|> lowerName)

unitCon :: Parser String
unitCon = string "()"

lParen :: Parser Char
lParen = notFollowedBy symName >> notFollowedBy unitCon >> char '('

punctuation :: Parser Char
punctuation = lParen <|> (choice $ map char ")[]{};_")

keyWordStrs :: [String]
keyWordStrs = ["def", "for", "for_", "rof", "rof_", "case", "of", "llam",
               "Read", "Write", "Accum", "Except", "IO", "data", "interface",
               "instance", "named-instance", "where", "if", "then", "else",
               "do", "view", "import", "foreign"]

checkNotKeyword :: Parser String -> Parser String
checkNotKeyword p = try $ do
  s <- p
  failIf (s `elem` keyWordStrs) $ show s ++ " is a reserved word"
  return s

failIf :: Bool -> String -> Parser ()
failIf True s = fail s
failIf False _ = return ()

consumeTillBreak :: Parser ()
consumeTillBreak = void $ manyTill anySingle $ eof <|> void (try (eol >> eol))

proseBlock :: Parser String
proseBlock = char '\'' >> fmap fst (withSource consumeTillBreak)

withSource :: Parser a -> Parser (String, a)
withSource p = do
  s <- getInput
  (x, (start, end)) <- withPos p
  return (take (end - start) s, x)

withPos :: Parser a -> Parser (a, (Int, Int))
withPos p = do
  n <- getOffset
  x <- p
  n' <- getOffset
  return $ (x, (n, n'))

