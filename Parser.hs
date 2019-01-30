module Parser (parseProg, checkBoundVarsCmd, checkBoundVarsExpr) where

import Util
import Record
import ParseUtil
import Syntax
import Env

import Control.Monad
import Control.Monad.Combinators.Expr
import Control.Monad.Identity
import Control.Monad.Reader (ReaderT, runReaderT, local, ask, asks)
import Control.Monad.State (StateT, runState, modify)
import Text.Megaparsec
import qualified Text.Megaparsec.Char.Lexer as L
import Test.HUnit
import Data.Foldable (toList)

type UTopDecl = TopDecl UExpr
type UInstr = DeclInstr UExpr
type Prog = [UTopDecl]

parseProg :: String -> Except Prog
parseProg = parseit prog

parseit :: Parser a -> String -> Except a
parseit p s = case parse (p <* eof) "" s of
                Left e -> Left $ ParseErr (errorBundlePretty e)
                Right x -> Right x

prog :: Parser Prog
prog = emptyLines >> many (topDecl <*emptyLines)

topDecl :: Parser UTopDecl
topDecl = do
  (instr, source) <- captureSource topDeclInstr
  let instr' = lowerInstr instr
      freeVars = setLEnv (`envDiff` builtinVars) $ foldMap fvsUExpr instr
  return $ TopDecl source freeVars instr'

topDeclInstr :: Parser UInstr
topDeclInstr =   explicitCommand
             <|> typedAssignment
             <|> liftM (uncurry TopAssign) simpleDecl
             <|> liftM (EvalCmd . (Command EvalExpr)) expr
             <?> "top-level declaration"

explicitCommand :: Parser UInstr
explicitCommand = do
  try $ symbol ":"
  cmdName <- identifier
  cmd <- case cmdName of
           "p"     -> return EvalExpr
           "t"     -> return GetType
           "sysf"  -> return GetTyped
           "parse" -> return GetParse
           "llvm"  -> return GetLLVM
           "jit"   -> return EvalJit
           _   -> fail $ "unrecognized command: " ++ show cmdName
  e <- expr
  return $ EvalCmd (Command cmd e)

typedAssignment :: Parser UInstr
typedAssignment = do
  v <- try (identifier <* symbol "::")
  ty <- typeExpr
  (v', e) <- simpleDecl
  if v' == v
    then return $ TopAssign v (UAnnot e ty)
    else fail $ "Type declaration variable must match assignment variable."

simpleDecl :: Parser (VarName, UExpr)
simpleDecl = do (VarPat (v, _), expr) <- decl
                return (v, expr)

expr :: Parser UExpr
expr = makeExprParser (sc >> term >>= maybeAnnot) ops

term :: Parser UExpr
term =   parenRaw
     <|> liftM (UVar . FV) identifier
     <|> liftM ULit literal
     <|> letExpr
     <|> lamExpr
     <|> forExpr
     <?> "term"

maybeAnnot :: UExpr -> Parser UExpr
maybeAnnot e = do
  t <- optional typeAnnot
  return $ case t of
             Nothing -> e
             Just t -> UAnnot e t

typeAnnot :: Parser Type
typeAnnot = try (symbol "::") >> typeExpr

parenRaw = do
  elts <- parens $ maybeNamed expr `sepBy` symbol ","
  return $ case elts of
    [(Nothing, expr)] -> expr
    elts -> URecCon $ mixedRecord elts

maybeNamed :: Parser a -> Parser (Maybe String, a)
maybeNamed p = do
  v <- optional $ try $
    do v <- identifier
       symbol "="
       return v
  x <- p
  return (v, x)

letExpr :: Parser UExpr
letExpr = do
  try $ symbol "let"
  bindings <- decl `sepBy` symbol ";"
  symbol "in"
  body <- expr
  return $ foldr (uncurry ULet) body bindings

lamExpr :: Parser UExpr
lamExpr = do
  try $ symbol "lam"
  ps <- pat `sepBy` sc
  symbol ":"
  body <- expr
  return $ foldr ULam body ps

forExpr :: Parser UExpr
forExpr = do
  try $ symbol "for"
  vs <- some idxPat -- `sepBy` sc
  symbol ":"
  body <- expr
  return $ foldr UFor body vs

decl :: Parser (UPat, UExpr)
decl = do
  p <- pat
  wrap <- idxLhsArgs <|> lamLhsArgs
  symbol "="
  body <- expr
  return (p, wrap body)

idxLhsArgs = do
  try $ symbol "."
  args <- idxPat `sepBy` symbol "."
  return $ \body -> foldr UFor body args

lamLhsArgs = do
  args <- pat `sepBy` sc
  return $ \body -> foldr ULam body args

literal :: Parser LitVal
literal = lexeme $  fmap IntLit  (try (int <* notFollowedBy (symbol ".")))
                <|> fmap RealLit real
                <|> fmap StrLit stringLiteral

opNames = ["+", "*", "/", "-", "^"]
resNames = ["for", "lam", "let", "in"]


identifier = makeIdentifier resNames

appRule = InfixL (sc
                  *> notFollowedBy (choice . map symbol $ opNames ++ resNames)
                  >> return UApp)
binOpRule opchar opname = InfixL (symbol opchar >> return (binOpApp opname))

binOpApp :: String -> UExpr -> UExpr -> UExpr
binOpApp s e1 e2 = UApp (UApp (UVar (FV s)) e1) e2

getRule = Postfix $ do
  vs  <- many $ symbol "." >> idxExpr
  return $ \body -> foldr (flip UGet) body (reverse vs)

ops = [ [getRule, appRule]
      , [binOpRule "^" "pow"]
      , [binOpRule "*" "mul", binOpRule "/" "div"]
      , [binOpRule "+" "add", binOpRule "-" "sub"]
      ]

idxExpr =   parenIdxExpr
        <|> liftM (RecLeaf . FV) identifier

parenIdxExpr = do
  elts <- parens $ maybeNamed idxExpr `sepBy` symbol ","
  return $ case elts of
    [(Nothing, expr)] -> expr
    elts -> RecTree $ mixedRecord elts

idxPat = pat

pat :: Parser UPat
pat =   parenPat
    <|> liftM2 (curry VarPat) identifier (optional typeAnnot)

parenPat :: Parser UPat
parenPat = do
  xs <- parens $ maybeNamed pat `sepBy` symbol ","
  return $ case xs of
    [(Nothing, x)] -> x
    xs -> RecPat $ mixedRecord xs

typeExpr :: Parser Type
typeExpr = makeExprParser (sc >> typeExpr') typeOps

typeVar :: Parser TVar
typeVar = liftM FV $ makeIdentifier ["Int", "Real", "Bool", "Str", "A", "E"]

-- forallType :: Parser Type
-- forallType = do
--   try $ symbol "A"
--   vars <- identifier `sepBy` sc
--   symbol "."
--   body <- typeExpr
--   return $ NamedForall vars body

-- existsType :: Parser Type
-- existsType = do
--   try $ symbol "E"
--   var <- identifier
--   symbol "."
--   body <- typeExpr
--   return $ NamedExists var body

baseType :: Parser BaseType
baseType = (try (symbol "Int")  >> return IntType)
       <|> (try (symbol "Real") >> return RealType)
       <|> (try (symbol "Bool") >> return BoolType)
       <|> (try (symbol "Str")  >> return StrType)
       <?> "base type"

-- typeOps = [ [InfixR (symbol "=>" >> return TabType)]
--           , [InfixR (symbol "->" >> return ArrType)]]
typeOps = [ [InfixR (symbol "->" >> return ArrType)]]

typeExpr' =   parens typeExpr
          <|> liftM TypeVar typeVar
          <|> liftM BaseType baseType
          -- <|> forallType
          -- <|> existsType
          <?> "term"

data BoundVars = BoundVars { lVars :: [VarName]
                           , iVars :: [VarName]
                           , tVars :: [VarName] }

lowerInstr :: UInstr -> UInstr
lowerInstr = fmap (lower empty)
  where empty = BoundVars [] [] []

lower :: BoundVars -> UExpr -> UExpr
lower env expr = case expr of
  ULit c         -> ULit c
  UVar v         -> UVar $ toDeBruijn (lVars env) v
  ULet p e body  -> ULet p (recur e) $ lower (updateLVars p env) body
  ULam p body    -> ULam p           $ lower (updateLVars p env) body
  UApp fexpr arg -> UApp (recur fexpr) (recur arg)
  UFor p body    -> UFor p           $ lower (updateIVars p env) body
  UGet e ie      -> UGet (recur e) $ fmap (toDeBruijn (iVars env)) ie
  URecCon r      -> URecCon $ fmap recur r
  UAnnot e t     -> UAnnot (recur e) (lowerType env t)
  where recur = lower env

lowerType :: BoundVars -> Type -> Type
lowerType env ty = case ty of
  BaseType b    -> BaseType b
  TypeVar v     -> TypeVar $ toDeBruijn (tVars env) v
  ArrType t1 t2 -> ArrType (recur t1) (recur t2)
  -- TabType t1 t2 -> TabType (recur t1) (recur t2)
  -- RecType r     -> RecType $ fmap recur r
  MetaTypeVar m -> MetaTypeVar m
  -- NamedForall vs t -> Forall (length vs) $ lowerType (updateTVars vs  env) t
  -- NamedExists v t  -> Exists             $ lowerType (updateTVars [v] env) t
  -- Forall _ _ -> error "Shouldn't see deBruijn Forall in source text"
  -- Exists   _ -> error "Shouldn't see deBruijn Exists in source text"
  where recur = lowerType env

updateLVars :: UPat -> BoundVars -> BoundVars
updateLVars pat env = env {lVars = patVars pat ++ lVars env}

updateIVars :: UPat -> BoundVars -> BoundVars
updateIVars pat env = env {iVars = patVars pat ++ iVars env}

updateTVars :: [VarName] -> BoundVars -> BoundVars
updateTVars vs env = env {tVars = vs ++ tVars env}

patVars :: UPat -> [VarName]
patVars pat = map fst (toList pat)

checkBoundVarsCmd :: Command UExpr -> Vars -> Command UExpr
checkBoundVarsCmd (Command cmdName expr) envVars =
  case checkBoundVarsExpr expr envVars of
    Left err         -> CmdErr err
    Right ((), expr) -> Command cmdName expr
checkBoundVarsCmd x _ = x

checkBoundVarsExpr :: UExpr -> Vars -> Except ((), UExpr)
checkBoundVarsExpr expr envVars = do
  let freeVars = setLEnv (`envDiff` builtinVars) (fvsUExpr expr)
  checkVars (lEnv freeVars) (lEnv envVars)
  checkVars (iEnv freeVars) (iEnv envVars)
  checkVars (tEnv freeVars) (tEnv envVars)
  return ((), expr)
  where checkVars :: Env i a -> Env i a -> Except ()
        checkVars e1 e2 = case fVars (e1 `envDiff` e2) of
                            v:_ -> Left $ UnboundVarErr v
                            [] -> Right ()

builtinVars :: Env Var ()
builtinVars = newEnv [(v, ()) | v <-
  ["add", "sub", "mul", "pow", "exp", "log",
   "sqrt", "sin", "cos", "tan", "reduce", "iota"] ]
