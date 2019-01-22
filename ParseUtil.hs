module ParseUtil (lineof, sc, blankLines, stringLiteral, makeIdentifier,
                  space, int, real, lexeme, symbol, parens, Parser,
                  emptyLines, captureSource) where

import Control.Monad (void)
import Data.Void
import Text.Megaparsec
import Text.Megaparsec.Char hiding (space)
import qualified Text.Megaparsec.Char.Lexer as L

type Parser = Parsec Void String

lineof :: Parser a -> Parser a
lineof = (<* (sc >> eol))

sc :: Parser ()
sc = L.space space (L.skipLineComment "--") empty

blankLines :: Parser ()
blankLines = void $ many eol

emptyLines :: Parser ()
emptyLines = void $ many (sc >> eol)

stringLiteral :: Parser String
stringLiteral = char '"' >> manyTill L.charLiteral (char '"')

makeIdentifier :: [String] -> Parser String
makeIdentifier reserved = lexeme . try $ do
  w <- (:) <$> letterChar <*> many alphaNumChar
  if w `elem` reserved
    then fail $ show w ++ " is a reserved word"
    else return w

rws :: [String] -- list of reserved words
rws = ["if","then","else","while","do","skip","true","false","not","and","or"]

space :: Parser ()
space = void $ takeWhile1P (Just "white space") (`elem` " \t")

int :: Parser Int
int = L.signed (return ()) L.decimal

real :: Parser Float
real = L.signed (return ()) L.float

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: String -> Parser String
symbol = L.symbol sc

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

captureSource :: Parser a -> Parser (a, String)
captureSource p = do
  s <- getInput
  offset <- getOffset
  val <- p
  offset' <- getOffset
  return (val, take (offset' - offset) s)
