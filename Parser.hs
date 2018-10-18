module Parser (parseProg, tests, VarEnv, parseLine, lookup, builtinVars) where
import Control.Monad (liftM, ap)
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
type VarEnv = [VarName]

parseProg :: String -> Either String I.Expr
parseProg s = do
  r <- parse' prog s
  r' <- runLower (lower r) builtinVars []
  return r'

parse' :: Parser a -> String -> Either String a
parse' p s = case parse p "" s of
               Left e -> Left (show e)
               Right r -> Right r

builtinVars = ["iota", "reduce", "add", "sub", "mul", "div"]
numBinOps = 4

parseLine :: String -> VarEnv -> Either String (Either (VarName, I.Expr) I.Expr)
parseLine line env = do
  result <- parse' bindingOrExpr line
  case result of
    Left (v, e) -> do r <- runLower (lower e) env []
                      return $ Left (v, r)
    Right e     -> do r <- runLower (lower e) env []
                      return $ Right r


bindingOrExpr :: Parser (Either Binding Expr)
bindingOrExpr =   try (binding >>= return . Left)
              <|> (expr >>= return . Right)


newtype Lower a = Lower { runLower :: VarEnv -> [IdxVarName] -> Either String a }

instance Monad Lower where
  return x = Lower $ \_ _ -> Right x
  x >>= f  = Lower $ \env ienv -> case runLower x env ienv
                                      of Left e  -> Left e
                                         Right y -> runLower (f y) env ienv

instance Functor Lower where
  fmap = liftM

instance Applicative Lower where
  pure  = return
  (<*>) = ap


lower :: Expr -> Lower I.Expr
lower (Lit c) = return $ I.Lit c
lower (Var v) = Lower $ \env ienv ->
    case lookup v env of
        Nothing -> Left $ "Variable not in scope: " ++ show v
        Just i  -> Right $ I.Var i
lower (BinOp b e1 e2) = do l1 <- lower e1
                           l2 <- lower e2
                           Lower $ \env ienv ->
                               let f = I.Var (I.binOpIdx b + length env - numBinOps)
                               in Right $ I.App (I.App f l1) l2
lower (Let v bound body) = lower $ App (Lam v body) bound
lower (Lam v body) = do
    e <- Lower $ \env ienv -> runLower (lower body) (v:env) ienv
    return $ I.Lam e
lower (App fexpr arg) = do f <- lower fexpr
                           x <- lower arg
                           return $ I.App f x
lower (For iv body) = do
    e <- Lower $ \env ienv -> runLower (lower body) env (iv:ienv)
    return $ I.For e
lower (Get e iv) = do
    e' <- lower e
    Lower $ \env ienv ->
      case lookup iv ienv of
          Nothing -> Left $ "Index variable not in scope: " ++ show iv
          Just i  -> Right $ I.Get e' i


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
