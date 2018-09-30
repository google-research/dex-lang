module Parser (parseExpr) where

import Control.Monad
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Language
import qualified Text.ParserCombinators.Parsec.Token as Token

import Interpreter

parseExpr = parse expr ""

expr :: Parser Expr
expr = buildExpressionParser ops (whiteSpace >> term)

opNames = ["+", "*", "/", "-"]
resNames = ["let", "in"]
languageDef = haskellStyle { Token.reservedOpNames = opNames
                           , Token.reservedNames   = resNames
                           , Token.commentLine     = "--"
                           }

lexer = Token.makeTokenParser languageDef
identifier = Token.identifier lexer
parens     = Token.parens     lexer
lexeme     = Token.lexeme     lexer
brackets   = Token.brackets   lexer
integer    = Token.integer    lexer
whiteSpace = Token.whiteSpace lexer
reservedOp = Token.reservedOp lexer

appRule = Infix (whiteSpace
                 *> notFollowedBy (choice . map reservedOp $ opNames ++ resNames)
                 >> return App) AssocLeft
binOpRule opchar opname = Infix (reservedOp opchar
                                 >> return (BinOp opname)) AssocLeft

getRule = Postfix $ do
  v  <- brackets $ liftM id identifier
  return $ \body -> Get body v

ops = [ [getRule, appRule],
        [binOpRule "*" Mul, binOpRule "/" Div],
        [binOpRule "+" Add, binOpRule "-" Sub]
      ]

term =   parens expr
     <|> liftM Var identifier
     <|> liftM Lit integer
     <|> letExpr
     <|> lamExpr
     <|> arrExpr
     <?> "term"

str = lexeme . string

letExpr = do
  try $ str "let"
  v <- liftM id identifier
  str "="
  bound <- expr
  str "in"
  body <- expr
  return $ Let v bound body

lamExpr = do
  try $ str "\\"
  v <- liftM id identifier
  str "->"
  body <- expr
  return $ Lam v body

arrExpr = do
  try $ str "["
  v <- liftM id identifier
  str ":"
  body <- expr
  str "]"
  return $ Arr v body
