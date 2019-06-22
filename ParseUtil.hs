module ParseUtil (lineof, sc, blankLines, stringLiteral, makeIdentifier,
                  space, int, real, lexeme, symbol, parens, brackets, Parser,
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
  w <- (:) <$> lowerChar <*> many alphaNumChar
  if w `elem` reserved
    then fail $ show w ++ " is a reserved word"
    else return w

space :: Parser ()
space = void $     takeWhile1P (Just "white space") (`elem` " \t")
               <|> string "\n "

int :: Parser Int
int = L.signed (return ()) L.decimal

real :: Parser Double
real = L.signed (return ()) L.float

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: String -> Parser String
symbol = L.symbol sc

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

brackets :: Parser a -> Parser a
brackets = between (symbol "[") (symbol "]")

captureSource :: Parser a -> Parser (String, a)
captureSource p = do
  s <- getInput
  offset <- getOffset
  val <- p
  offset' <- getOffset
  return (take (offset' - offset) s ++ "\n", val)
