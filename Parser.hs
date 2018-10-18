module Parser (parseProg, tests) where

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
          | For IdxVarName Expr
          | Get Expr IdxVarName
          deriving (Show, Eq)

type Binding = (VarName, Expr)
type VarName = String
type IdxVarName = String

parseBinding :: [String] -> Either ParseError I.Expr
parseProg lines =
  r <- parse prog "" s
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
lower (For iv body) env ienv = I.For $ lower body env (iv:ienv)
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

prog :: Parser Expr
prog = do
  whiteSpace
  bindings <- binding `sepBy` str ";"
  case bindings of
    [] -> fail "Empty program"
    bindings -> let (_, finalExpr) = last bindings
                in return $ foldr (uncurry Let) finalExpr (init bindings)

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

binding = do
  v <- var
  wrap <- idxLhsArgs <|> lamLhsArgs
  str "="
  body <- expr
  return (v, wrap body)

str = lexeme . string
var = liftM id identifier

idxLhsArgs = do
  try $ str "."
  args <- var `sepBy` str "."
  return $ \body -> foldr For body args

lamLhsArgs = do
  args <- var `sepBy` whiteSpace
  return $ \body -> foldr Lam body args

letExpr = do
  try $ str "let"
  bindings <- binding `sepBy` str ";"
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
  [ ("1 + 2"        , BinOp I.Add (Lit 1) (Lit 2))
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
