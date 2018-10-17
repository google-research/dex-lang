module Parser (parseExpr, tests) where

import Test.HUnit
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
          deriving (Show, Eq)

type VarName = String
type IdxVarName = String

parseExpr :: String -> Either ParseError I.Expr
parseExpr s = do
  r <- parse expr "" s
  return $ lower r builtinVars []

builtinVars = ["iota", "reduce", "add", "sub", "mul", "div"]
numBinOps = 4

lower :: Expr -> [VarName] -> [IdxVarName] -> I.Expr
lower (Lit c)   _  _ = I.Lit c
lower (Var v) env _  = case lookup v env of
    Just i  -> I.Var i
    Nothing -> error $ "Variable not in scope: " ++ show v
lower (BinOp b e1 e2) env ienv = let l1 = lower e1 env ienv
                                     l2 = lower e2 env ienv
                                     f = I.Var (I.binOpIdx b + length env - numBinOps)
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
                                 >> return (BinOp opname)) AssocLeft

getRule = Postfix $ do
  vs  <- many $ str "." >> liftM id identifier
  return $ \body -> foldr (flip Get) body (reverse vs)

ops = [ [getRule, appRule],
        [binOpRule "*" I.Mul, binOpRule "/" I.Div],
        [binOpRule "+" I.Add, binOpRule "-" I.Sub]
      ]

term =   parens expr
     <|> liftM Var identifier
     <|> liftM (Lit . fromIntegral) integer
     <|> letExpr
     <|> lamExpr
     <|> forExpr
     <?> "term"

str = lexeme . string

assignment = do
  v <- liftM id identifier
  str "="
  bound <- expr
  return (v, bound)

letExpr = do
  try $ str "let"
  bindings <- assignment `sepBy` str ";"
  str "in"
  body <- expr
  return $ foldr (uncurry Let) body bindings

lamExpr = do
  try $ str "lam"
  v <- liftM id identifier
  str ":"
  body <- expr
  return $ Lam v body

forExpr = do
  try $ str "for"
  v <- liftM id identifier
  str ":"
  body <- expr
  return $ IdxComp v body


testParses =
  [ ("1 + 2"        , BinOp I.Add (Lit 1) (Lit 2))
  , ("for i: 10"    , IdxComp "i" (Lit 10))
  , ("lam x: x"     , Lam "x" (Var "x"))
  , ("y x"          , App (Var "y") (Var "x"))
  , ("x.i"          , Get (Var "x") "i")
  , ("f x y"        , App (App (Var "f") (Var "x")) (Var "y"))
  , ("x.i.j"        , Get (Get (Var "x") "i") "j")
  , ("let x = 1 in x"        ,  Let "x" (Lit 1) (Var "x"))
  , ("let x = 1; y = 2 in x" ,  Let "x" (Lit 1) (Let "y" (Lit 2) (Var "x")))
  -- , ("let f x = x in f"      , Lit 1)
  -- , ("let x.i = y.i in x"    , Lit 1)
  -- , ("let f x y = x + y in f", Lit 1)
  -- , ("let x.i.j = y.j.i in x", Lit 1)
  ]

tests = TestList $ [
    let msg = "  tried: " ++ s
        p = parse expr "" s
    in TestCase $ assertEqual msg (Right e) p
    | (s, e) <- testParses]
