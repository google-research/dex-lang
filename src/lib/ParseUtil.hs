module ParseUtil (sc, blankLines, stringLiteral, failIf,
                  space, int, real, lexeme, symbol, parens, brackets, Parser,
                  emptyLines, outputLines, withPos, withSource, getLineNum) where

import Control.Monad
import Data.Void
import Text.Megaparsec
import Text.Megaparsec.Char hiding (space)
import qualified Text.Megaparsec.Char.Lexer as L

type Parser = Parsec Void String

sc :: Parser ()
sc = L.space space (L.skipLineComment "--") empty

blankLines :: Parser ()
blankLines = void $ many eol

emptyLines :: Parser ()
emptyLines = void $ many (sc >> eol)

outputLines :: Parser ()
outputLines = void $ many (symbol ">" >> takeWhileP Nothing (/= '\n') >> eol)

stringLiteral :: Parser String
stringLiteral = char '"' >> manyTill L.charLiteral (char '"')

space :: Parser ()
space = void $ do _ <- takeWhile1P (Just "white space") (`elem` " \t")
                  optional (symbol "..\n")

int :: Parser Int
int = L.signed (return ()) L.decimal

real :: Parser Double
real = L.signed (return ()) L.float

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: String -> Parser ()
symbol s = void $ L.symbol sc s

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

brackets :: Parser a -> Parser a
brackets = between (symbol "[") (symbol "]")

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
