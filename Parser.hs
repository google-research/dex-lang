module Parser (VarName, IdxVarName, Expr (..), parseCommand, Command (..)) where
import Util
import Control.Monad
import Test.HUnit
import Text.ParserCombinators.Parsec hiding (lower)
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Language
import qualified Text.ParserCombinators.Parsec.Token as Token

data Expr = Lit Int
          | Var VarName
          | Let VarName Expr Expr
          | Lam VarName Expr
          | App Expr Expr
          | For IdxVarName Expr
          | Get Expr IdxVarName
          deriving (Show, Eq)

data Command = GetType    Expr
             | GetParse   Expr
             | GetLowered Expr
             | EvalExpr   Expr
             | EvalDecl   VarName Expr deriving (Show, Eq)

type VarName = String
type IdxVarName = String
type Decl = (VarName, Expr)

parseCommand :: String -> Either ParseError Command
parseCommand s = parse command "" s

command :: Parser Command
command =   explicitCommand
        <|> liftM (uncurry EvalDecl) (try decl)
        <|> liftM EvalExpr expr
        <?> "command"

opNames = ["+", "*", "/", "-"]
resNames = ["for", "lam", "let", "in"]
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
                                 >> return (binOpApp opname)) AssocLeft

binOpApp :: String -> Expr -> Expr -> Expr
binOpApp s e1 e2 = App (App (Var s) e1) e2

getRule = Postfix $ do
  vs  <- many $ str "." >> liftM id identifier
  return $ \body -> foldr (flip Get) body (reverse vs)

ops = [ [getRule, appRule],
        [binOpRule "*" "mul", binOpRule "/" "div"],
        [binOpRule "+" "add", binOpRule "-" "sub"]
      ]

term =   parens expr
     <|> liftM Var identifier
     <|> liftM (Lit . fromIntegral) integer
     <|> letExpr
     <|> lamExpr
     <|> forExpr
     <?> "term"

str = lexeme . string
var = liftM id identifier

expr :: Parser Expr
expr = buildExpressionParser ops (whiteSpace >> term)

decl :: Parser Decl
decl = do
  v <- var
  wrap <- idxLhsArgs <|> lamLhsArgs
  str "="
  body <- expr
  return (v, wrap body)

explicitCommand :: Parser Command
explicitCommand = do
  try $ str ":"
  cmd <- identifier
  e <- expr
  case cmd of
    "t" -> return $ GetType e
    "p" -> return $ GetParse e
    "l" -> return $ GetLowered e
    otherwise -> fail $ "unrecognized command: " ++ show cmd

idxLhsArgs = do
  try $ str "."
  args <- var `sepBy` str "."
  return $ \body -> foldr For body args

lamLhsArgs = do
  args <- var `sepBy` whiteSpace
  return $ \body -> foldr Lam body args

letExpr = do
  try $ str "let"
  bindings <- decl `sepBy` str ";"
  str "in"
  body <- expr
  return $ foldr (uncurry Let) body bindings

lamExpr = do
  try $ str "lam"
  vs <- var `sepBy` whiteSpace
  str ":"
  body <- expr
  return $ foldr Lam body vs

forExpr = do
  try $ str "for"
  vs <- var `sepBy` whiteSpace
  str ":"
  body <- expr
  return $ foldr For body vs



escapeChars :: String -> String
escapeChars [] = []
escapeChars (x:xs) = case x of
                     '\\' -> escapeChars $ drop 1 xs
                     otherwise -> x : escapeChars xs
