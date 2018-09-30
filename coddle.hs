import System.Console.Haskeline
import System.IO
import Control.Monad
import Control.Monad.IO.Class
import Data.List
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Language
import qualified Text.ParserCombinators.Parsec.Token as Token
import qualified Data.Map.Strict as Map
import qualified Data.Array as A


-- -------------------- language --------------------

data Expr = BinOp BinOpName Expr Expr
          | Lit Integer
          | Var VarName
          | Let VarName Expr Expr
          | Lam VarName Expr
          | App Expr Expr
          | Arr IdxVarName Expr
          | Get Expr IdxVarName
          deriving (Show)

data BinOpName = Add | Mul | Sub | Div deriving (Show)

data Val = IntVal Integer
         | LamVal Env VarName Expr
         | ArrayVal Array deriving (Show)

type VarName = String
type IdxVarName = String

type Env = Map.Map VarName Val

eval :: Expr -> Env -> Val
eval (BinOp b e1 e2) env = IntVal $ case (eval e1 env, eval e2 env) of
                                     (IntVal v1, IntVal v2) -> evalBinOp b v1 v2
eval (Lit c) _ = IntVal c
eval (Var v) env = case Map.lookup v env of
                     Just val -> val
                     Nothing -> error $ "Undefined variable: " ++ show v
eval (Let v bound body) env = let boundVal = eval bound env
                                  newEnv = Map.insert v boundVal env
                              in eval body newEnv
eval (Lam v body) env = LamVal env v body
eval (App f arg) env = case eval f env of
  LamVal closureEnv v body ->
    let argVal = eval arg env
    in eval body (Map.insert v argVal env)

evalBinOp :: BinOpName -> Integer -> Integer -> Integer
evalBinOp Add = (+)
evalBinOp Mul = (*)
evalBinOp Sub = (-)

-- -------------------- vector operations --------------------

type DType   = Int
type Shape   = ([Int], Map.Map IdxVarName Int)
type Strides = ([Int], Map.Map IdxVarName Int)
data Array = Array Shape Strides (A.Array Int DType)

instance Show Array where
  show (Array shape _ _) = "<array>"

-- vlen :: Array -> Int
-- vlen (Array shape _ _) = foldr (*) 1 shape

toList :: Array -> [DType]
toList = undefined

fromList :: Shape -> [DType] -> Array
fromList = undefined

binop :: (DType -> DType -> DType) -> Array -> Array -> Array
binop f x y = let (Array shape _ _) = x
              in fromList shape $ zipWith f (toList x) (toList y)

-- -------------------- parser --------------------

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

expr :: Parser Expr
expr = buildExpressionParser ops (whiteSpace >> term)

parseExpr = parse expr ""

-- -------------------- try it out --------------------

-- showParse _ = ""
showParse p = "Parse: " ++ (show $ p) ++ "\n"

evalSource :: String -> String
evalSource line =
  case parseExpr line of
    Left e ->  "Parse error:\n" ++ show e
    Right r -> showParse r ++ (show $ eval r Map.empty)

splitString :: Char -> String -> [String]
splitString c s = case dropWhile (== c) s of
             ""   -> []
             rest -> prefix : splitString c rest'
                     where (prefix, rest') = break (== c) rest

evalMultiSource :: String -> String
evalMultiSource s = let results = map evalSource $ splitString '~' s
                    in concat $ intersperse "\n\n" results


repl :: IO ()
repl = runInputT defaultSettings loop
  where
  loop = do
    minput <- getInputLine "> "
    case minput of
      Nothing -> return ()
      Just line -> (liftIO . putStrLn . evalSource $ line)
                   >> loop

evalFile :: IO ()
evalFile = do
    source <- readFile "examples.cd"
    putStrLn $ evalMultiSource source
    return ()

main :: IO ()
main = evalFile


-- ---------- TODO ----------

-- alpha abstraction and application
--   syntax
--   eval

-- handle multiple vars (desugaring to single ones)
-- indentation and top-level functions?

-- types (syntax)
-- type checking/inference

-- optional script arg (that switches interaction mode or not)


-- think about
--   reduce
--   binary op loop
