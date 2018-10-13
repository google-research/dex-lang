module Parser (parseExpr) where

import Prelude hiding (lookup)
import Control.Monad
import Text.ParserCombinators.Parsec hiding (lower)
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Language
import qualified Text.ParserCombinators.Parsec.Token as Token

import qualified Interpreter as I

data Expr = BinOp I.BinOpName Expr Expr
          | Lit Int
          | Var VarName
          | Let VarName Expr Expr
          | Lam VarName Expr
          | App Expr Expr
          | IdxComp IdxVarName Expr
          | Get Expr IdxVarName
          deriving (Show)

type VarName = String
type IdxVarName = String

parseExpr s = do
  r <- parse expr "" s
  return $ lower r builtinVars []

builtinVars = ["iota"]

lower :: Expr -> [VarName] -> [IdxVarName] -> I.Expr
lower (Lit c)   _  _ = I.Lit c
lower (Var v) env _  = case lookup v env of
    Just i  -> I.Var i
    Nothing -> error $ "Variable not in scope: " ++ show v
lower (BinOp b e1 e2) env ienv = let l1 = lower e1 env ienv
                                     l2 = lower e2 env ienv
                                     f = I.Var (I.binOpIdx b + length env)
                                 in I.App (I.App f l1) l2
lower (Let v bound body) env ienv = lower (App (Lam v body) bound) env ienv
lower (Lam v body) env ienv = I.Lam $ lower body (v:env) ienv
lower (App fexpr arg) env ienv = let f = lower fexpr env ienv
                                     x = lower arg env ienv
                                 in I.App f x
lower (IdxComp iv body) env ienv = I.IdxComp $ lower body env (iv:ienv)
lower (Get e iv) env ienv = let e' = lower e env ienv
                            in case lookup iv ienv of
                    Just i  -> I.Get e' i
                    Nothing -> error $ "Index variable not in scopr: " ++ show iv


lookup :: (Eq a) => a -> [a] -> Maybe Int
lookup _ [] = Nothing
lookup target (x:xs) | x == target = Just 0
                     | otherwise = do
                         ans <- lookup target xs
                         return (ans + 1)

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
        [binOpRule "*" I.Mul, binOpRule "/" I.Div],
        [binOpRule "+" I.Add, binOpRule "-" I.Sub]
      ]

term =   parens expr
     <|> liftM Var identifier
     <|> liftM (Lit . fromIntegral) integer
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
  return $ IdxComp v body
