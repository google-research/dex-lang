module Parser (parseProg, tests, VarEnv, parseLine, lookup, builtinVars) where
import Control.Monad (liftM, ap)
import Control.Monad.Trans.Reader
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
  r' <- runReaderT (lower r) (builtinVars, [])
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
    Left (v, e) -> do r <- runReaderT (lower e) (env, [])
                      return $ Left (v, r)
    Right e     -> do r <- runReaderT (lower e) (env, [])
                      return $ Right r


bindingOrExpr :: Parser (Either Binding Expr)
bindingOrExpr =   try (binding >>= return . Left)
              <|> (expr >>= return . Right)


type LoweringEnv = (VarEnv, [IdxVarName])
type Lower a = ReaderT LoweringEnv (Either String) a

lower :: Expr -> Lower I.Expr
lower (Lit c) = return $ I.Lit c
lower (Var v) = liftM I.Var $ lookupEnv v
lower (BinOp b e1 e2) = do l1 <- lower e1; l2 <- lower e2
                           (env, _) <- ask
                           return $ let i = length env + I.binOpIdx b - numBinOps
                                    in I.App (I.App (I.Var i) l1) l2
lower (Let v bound body) = lower $ App (Lam v body) bound
lower (Lam v body)    = liftM  I.Lam $ local (updateEnv v) (lower body)
lower (App fexpr arg) = liftM2 I.App (lower fexpr) (lower arg)
lower (For iv body)   = liftM  I.For $ local (updateIEnv iv) (lower body)
lower (Get e iv)      = liftM2 I.Get (lower e) (lookupIEnv iv)


lookup :: (Eq a) => a -> [a] -> Maybe Int
lookup _ [] = Nothing
lookup target (x:xs) | x == target = Just 0
                     | otherwise = do
                         ans <- lookup target xs
                         return (ans + 1)

updateEnv :: VarName -> LoweringEnv -> LoweringEnv
updateEnv v (env,ienv) = (v:env,ienv)

updateIEnv :: IdxVarName -> LoweringEnv -> LoweringEnv
updateIEnv i (env,ienv) = (env,i:ienv)

lookupEnv :: VarName -> Lower Int
lookupEnv v = do
    (env,_) <- ask
    case lookup v env of
      Nothing -> pfail $ "Variable not in scope: " ++ show v
      Just i  -> return $ i

lookupIEnv :: IdxVarName -> Lower Int
lookupIEnv iv = do
    (_,ienv) <- ask
    case lookup iv ienv of
      Nothing -> pfail $ "Index variable not in scope: " ++ show iv
      Just i  -> return $ i


pfail :: String -> Lower a
pfail s = ReaderT $ \_ -> Left s


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
