module Parser (VarName, IdxVarName, Expr (..), parseCommand, Command (..), tests) where
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
             | EvalDecl   VarName Expr

type VarName = String
type IdxVarName = String
type Decl = (VarName, Expr)

parseCommand :: String -> Either String Command
parseCommand s = case parse command "" s of
                 Left e  -> Left $ show e
                 Right p -> Right p

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

testParses =
  [ ("1 + 2"        , App (App (Var "add") (Lit 1)) (Lit 2))
  , ("for i: 10"    , For "i" (Lit 10))
  , ("lam x: x"     , Lam "x" (Var "x"))
  , ("y x"          , App (Var "y") (Var "x"))
  , ("x.i"          , Get (Var "x") "i")
  , ("f x y"        , App (App (Var "f") (Var "x")) (Var "y"))
  , ("x.i.j"        , Get (Get (Var "x") "i") "j")
  , ("let x = 1 in x"        , Let "x" (Lit 1) (Var "x"))
  , ("let x = 1; y = 2 in x" , Let "x" (Lit 1) (Let "y" (Lit 2) (Var "x")))
  , ("for i j: 10"           , For "i" (For "j" (Lit 10)))
  , ("lam x y: x"            , Lam "x" (Lam "y" (Var "x")))
  , ("let f x = x in f"      , Let "f" (Lam "x" (Var "x")) (Var "f"))
  , ("let x . i = y in x"    , Let "x" (For "i" (Var "y")) (Var "x"))
  , ("let f x y = x in f"    , Let "f" (Lam "x" (Lam "y" (Var "x"))) (Var "f"))
  , ("let x.i.j = y in x"    , Let "x" (For "i" (For "j" (Var "y"))) (Var "x"))
  ]

tests = TestList $ [
    let msg = "  tried: " ++ s
        p = parse expr "" s
    in TestCase $ assertEqual msg (Right e) p
    | (s, e) <- testParses]
