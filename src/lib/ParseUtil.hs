-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module ParseUtil (runTheParser, sc, blankLines, stringLiteral, failIf,
                  space, num, uint, lexeme, symbol, parens, brackets, Parser,
                  emptyLines, nonBlankLines, outputLines, withPos, withSource,
                  getLineNum, mayBreak, mayNotBreak, bracketed) where

import Control.Monad
import Control.Monad.Reader
import Data.Void
import Text.Megaparsec
import Text.Megaparsec.Char hiding (space)
import qualified Text.Megaparsec.Char.Lexer as L


-- Boolean specifies whether to consume newlines (True)
type Parser = ReaderT Bool (Parsec Void String)

runTheParser :: String -> Parser a -> Either (ParseErrorBundle String Void) a
runTheParser s p =  parse (runReaderT p False) "" s

sc :: Parser ()
sc = L.space space lineComment empty

lineComment :: Parser ()
lineComment = do
  try $ string "--" >> notFollowedBy (void (char 'o'))
  void (takeWhileP (Just "char") (/= '\n'))

blankLines :: Parser ()
blankLines = void $ many eol

nonBlankLines :: Parser ()
nonBlankLines = void $ many $ takeWhile1P Nothing (/= '\n') >> eol

emptyLines :: Parser ()
emptyLines = void $ many (sc >> eol)

outputLines :: Parser ()
outputLines = void $ many (symbol ">" >> takeWhileP Nothing (/= '\n') >> eol)

stringLiteral :: Parser String
stringLiteral = char '"' >> manyTill L.charLiteral (char '"') <* sc

space :: Parser ()
space = do
  consumeNewLines <- ask
  if consumeNewLines
    then space1
    else void $ takeWhile1P (Just "white space") (`elem` " \t")

mayBreak :: Parser a -> Parser a
mayBreak p = local (const True) p

mayNotBreak :: Parser a -> Parser a
mayNotBreak p = local (const False) p

num :: Parser (Either Double Int)
num =    liftM Left (try (L.signed (return ()) L.float) <* sc)
     <|> (do x <- L.signed (return ()) L.decimal
             trailingPeriod <- optional (char '.')
             sc
             return $ case trailingPeriod of
               Just _  -> Left (fromIntegral x)
               Nothing -> Right x)

uint :: Parser Int
uint = L.decimal <* sc

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: String -> Parser ()
symbol s = void $ L.symbol sc s

bracketed :: String -> String -> Parser a -> Parser a
bracketed left right p = between (mayBreak (symbol left)) (symbol right) $ mayBreak p

parens :: Parser a -> Parser a
parens p = bracketed "(" ")" p

brackets :: Parser a -> Parser a
brackets p = bracketed "[" "]" p

withPos :: Parser a -> Parser (a, (Int, Int))
withPos p = do
  n <- getOffset
  x <- p
  n' <- getOffset
  return $ (x, (n, n'))

withSource :: Parser a -> Parser (String, a)
withSource p = do
  s <- getInput
  (x, (start, end)) <- withPos p
  return (take (end - start) s, x)

getLineNum :: Parser Int
getLineNum = liftM (unPos . sourceLine) getSourcePos

failIf :: Bool -> String -> Parser ()
failIf True s = fail s
failIf False _ = return ()
