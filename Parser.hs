module Parser (VarName, VarEnv, parseExpr, parseDeclOrExpr, initVarEnv, tests) where
import Util
import Test.HUnit
import Prelude hiding (lookup)
import Control.Monad
import Control.Monad.Reader (ReaderT (..), runReaderT, local, ask)
import Text.ParserCombinators.Parsec hiding (lower)
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Language
import qualified Text.ParserCombinators.Parsec.Token as Token

import qualified Syntax as S

data Expr = BinOp BinOpName Expr Expr
          | Lit Int
          | Var VarName
          | Let VarName Expr Expr
          | Lam VarName Expr
          | App Expr Expr
          | For IdxVarName Expr
          | Get Expr IdxVarName
          deriving (Show, Eq)

data BinOpName = Add | Mul | Sub | Div  deriving (Show, Eq)
type VarName = String
type IdxVarName = String
type VarEnv = [VarName]

data ParseErr = ParseErr String
              | UnboundVarErr VarName
              | UnboundIdxVarErr IdxVarName deriving (Show)
type Except a = Either ParseErr a

parseExpr :: String -> VarEnv -> Except S.Expr
parseExpr s env = runParse expr s >>= runLower env

parseDeclOrExpr :: String -> VarEnv -> Except (Maybe VarName, S.Expr)
parseDeclOrExpr s env = do (v, e) <- runParse declOrExpr s
                           e' <- runLower env e
                           return (v, e')

runParse :: Parser a -> String -> Except a
runParse p s = liftErr $ parse p "" s

runLower :: VarEnv -> Expr -> Except S.Expr
runLower env expr = runReaderT (lower expr) (env, [])

initVarEnv :: VarEnv
initVarEnv = ["iota", "reduce", "add", "sub", "mul", "div"]

liftErr :: Either ParseError a -> Except a
liftErr (Left  e) = Left $ ParseErr (show e)
liftErr (Right x) = Right x

type LoweringEnv = (VarEnv, [IdxVarName])
type Lower a = ReaderT LoweringEnv (Either ParseErr) a

lower :: Expr -> Lower S.Expr
lower (Lit c) = return $ S.Lit c
lower (Var v) = liftM S.Var $ lookupEnv v
lower (BinOp b e1 e2)    = lower $ App (App (Var $ binOpName b) e1) e2
lower (Let v bound body) = liftM2 S.Let (lower bound) $
                               local (updateEnv v) (lower body)
lower (Lam v body)    = liftM  S.Lam $ local (updateEnv v) (lower body)
lower (App fexpr arg) = liftM2 S.App (lower fexpr) (lower arg)
lower (For iv body)   = liftM  S.For $ local (updateIEnv iv) (lower body)
lower (Get e iv)      = liftM2 S.Get (lower e) (lookupIEnv iv)

binOpName :: BinOpName -> String
binOpName b = case b of  Add -> "add";  Mul -> "mul"
                         Sub -> "sub";  Div -> "div"

updateEnv  v (env,ienv) = (v:env,ienv)
updateIEnv i (env,ienv) = (env,i:ienv)

lookupEnv :: VarName -> Lower Int
lookupEnv v = do
    (env,_) <- ask
    maybeReturn (lookup v env) $ UnboundVarErr v

lookupIEnv :: IdxVarName -> Lower Int
lookupIEnv iv = do
    (_,ienv) <- ask
    maybeReturn (lookup iv ienv) $ UnboundIdxVarErr iv

maybeReturn :: Maybe a -> ParseErr -> Lower a
maybeReturn (Just x) _ = return x
maybeReturn Nothing  e = ReaderT $ \_ -> Left e

expr :: Parser Expr
expr = buildExpressionParser ops (whiteSpace >> term)

declOrExpr :: Parser (Maybe VarName, Expr)
declOrExpr =   liftM (\(v,e)-> (Just v , e)) (try binding)
           <|> liftM (\   e -> (Nothing, e)) expr

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
        [binOpRule "*" Mul, binOpRule "/" Div],
        [binOpRule "+" Add, binOpRule "-" Sub]
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

binding = do
  v <- var
  wrap <- idxLhsArgs <|> lamLhsArgs
  str "="
  body <- expr
  return (v, wrap body)

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
  [ ("1 + 2"        , BinOp Add (Lit 1) (Lit 2))
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
