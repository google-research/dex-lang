module Parser (parseProg, parseTopDecl, Prog) where

import Control.Monad
import Control.Monad.Combinators.Expr
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Data.Map.Strict as M
import Data.Char (isLower)

import Env
import Record
import ParseUtil
import Syntax
import Fresh
import Type
import Inference
import PPrint

type Prog = [(String, UTopDecl)]

parseProg :: String -> Except Prog
parseProg s = parseit s $ many topDeclContext <* emptyLines

parseTopDecl :: String -> Except UTopDecl
parseTopDecl s = parseit s topDecl

parseit :: String -> Parser a -> Except a
parseit s p = case parse (p <* (optional eol >> eof)) "" s of
                Left e -> throw ParseErr (errorBundlePretty e)
                Right x -> return x

topDeclContext :: Parser (String, UTopDecl)
topDeclContext = do
  ans <- withSource (emptyLines >> topDecl <* emptyLines)
  blankLines
  outputLines
  blankLines
  return ans

topDecl :: Parser UTopDecl
topDecl =   explicitCommand
        <|> liftM TopDecl decl
        <|> liftM (EvalCmd . Command (EvalExpr Printed)) expr
        <?> "top-level declaration"

explicitCommand :: Parser UTopDecl
explicitCommand = do
  symbol ":"
  cmdName <- identifier
  cmd <- case cmdName of
           "p"       -> return $ EvalExpr Printed
           "t"       -> return GetType
           "passes"  -> return Passes
           "llvm"    -> return LLVM
           "asm"     -> return Asm
           "time"    -> return TimeIt
           "plot"    -> return $ EvalExpr Scatter
           "plotmat" -> return $ EvalExpr Heatmap
           "flops"   -> return Flops
           _   -> fail $ "unrecognized command: " ++ show cmdName
  e <- expr
  return $ EvalCmd (Command cmd e)

-- === Parsing decls ===

decl :: Parser UDecl
decl = typeAlias <|> typedLet <|> unpack <|> letDecl

declSep :: Parser ()
declSep = void $ ((eol >> sc) <|> void (symbol ";"))

typeAlias :: Parser UDecl
typeAlias = do
  symbol "type"
  v <- capVarName
  symbol "="
  ty <- tauType
  return $ TAlias v ty

typedLet :: Parser UDecl
typedLet = do
  v <- try (varName <* symbol "::")
  ty <- sigmaType
  declSep
  Let p e <- letDecl
  case p of
    RecTree _ -> fail "Can't annotate patterns"
    RecLeaf (v' :> b) ->
     if v' /= v
       then fail "Type declaration variable must match assignment variable."
       else case b of
              Ann _ -> fail "Competing type annotations"
              NoAnn -> return $ Let (RecLeaf (v :> Ann ty)) e

unpack :: Parser UDecl
unpack = do
  (b, tv) <- try $ do b <- binder
                      symbol ","
                      tv <- capVarName
                      symbol "=" >> symbol "unpack"
                      return (b, tv)
  body <- expr
  return $ Unpack b tv body

letDecl :: Parser UDecl
letDecl = do
  (p, wrap) <- try $ do p <- pat
                        wrap <- idxLhsArgs <|> lamLhsArgs
                        symbol "="
                        return (p, wrap)
  body <- expr
  return $ Let p (wrap body)

-- === Parsing expressions ===

expr :: Parser UExpr
expr = makeExprParser (sc >> withSourceAnn term >>= maybeAnnot) ops

term :: Parser UExpr
term =   parenRaw
     <|> liftM Var varName
     <|> liftM Lit literal
     <|> declExpr
     <|> lamExpr
     <|> forExpr
     <|> primOp
     <|> ffiCall
     <|> tabCon
     <?> "term"

declExpr :: Parser UExpr
declExpr = do
  symbol "let"
  decls <- decl `sepEndBy` declSep
  symbol "in"
  body <- expr
  return $ Decls decls body

withSourceAnn :: Parser UExpr -> Parser UExpr
withSourceAnn p = liftM (uncurry SrcAnnot) (withPos p)

maybeAnnot :: UExpr -> Parser UExpr
maybeAnnot e = do
  ann <- typeAnnot
  return $ case ann of
             NoAnn -> e
             Ann ty -> Annot e ty

typeAnnot :: Parser Ann
typeAnnot = do
  ann <- optional $ symbol "::" >> sigmaType
  return $ case ann of
    Nothing -> NoAnn
    Just ty -> Ann ty

parenRaw = do
  elts <- parens $ expr `sepBy` symbol ","
  return $ case elts of
    [expr] -> expr
    elts -> RecCon $ Tup elts

primOp :: Parser UExpr
primOp = do
  s <- try $ symbol "%" >> identifier
  b <- case strToBuiltin s of
    Just b -> return b
    Nothing -> fail $ "Unexpected builtin: " ++ s
  args <- parens $ expr `sepBy` symbol ","
  return $ PrimOp b [] args

ffiCall :: Parser UExpr
ffiCall = do
  symbol "%%"
  s <- identifier
  args <- parens $ expr `sepBy` symbol ","
  return $ PrimOp (FFICall (length args) s) [] args

lamExpr :: Parser UExpr
lamExpr = do
  symbol "lam"
  ps <- pat `sepBy` sc
  symbol "."
  body <- expr
  return $ foldr Lam body ps

forExpr :: Parser UExpr
forExpr = do
  symbol "for"
  vs <- pat `sepBy` sc
  symbol "."
  body <- expr
  return $ foldr For body vs

tabCon :: Parser UExpr
tabCon = do
  xs <- brackets $ expr `sepBy` symbol ","
  return $ TabCon NoAnn xs

idxLhsArgs = do
  symbol "."
  args <- pat `sepBy` symbol "."
  return $ \body -> foldr For body args

lamLhsArgs = do
  args <- pat `sepBy` sc
  return $ \body -> foldr Lam body args

literal :: Parser LitVal
literal = lexeme $  fmap IntLit  (try (int <* notFollowedBy (symbol ".")))
                <|> fmap RealLit real
                <|> fmap StrLit stringLiteral
                <|> (symbol "True"  >> return (BoolLit True))
                <|> (symbol "False" >> return (BoolLit False))

identifier :: Parser String
identifier = lexeme . try $ do
  w <- (:) <$> lowerChar <*> many alphaNumChar
  failIf (w `elem` resNames) $ show w ++ " is a reserved word"
  return w
  where
   resNames = ["for", "lam", "let", "in", "unpack"]

appRule = InfixL (sc *> notFollowedBy (choice . map symbol $ opNames)
                     >> return App)
  where
    opNames = ["+", "*", "/", "-", "^", "$"]

binOpRule opchar builtin = InfixL (symbol opchar >> return binOpApp)
  where binOpApp e1 e2 = PrimOp builtin [] [e1, e2]

getRule = Postfix $ do
  vs  <- many $ symbol "." >> idxExpr
  return $ \body -> foldr (flip Get) body (reverse vs)

ops = [ [getRule, appRule]
      , [binOpRule "^" Pow]
      , [binOpRule "*" FMul, binOpRule "/" FDiv]
      , [binOpRule "+" FAdd, binOpRule "-" FSub]
      , [binOpRule "<" FLT, binOpRule ">" FGT]
      , [InfixR (symbol "$" >> return App)]
      , [InfixL (symbol "@deriv" >> return DerivAnnot)]
       ]

varName :: Parser Name
varName = liftM2 Name identifier intQualifier

idxExpr :: Parser UExpr
idxExpr = withSourceAnn $ liftM Var varName

binder :: Parser UBinder
binder = (symbol "_" >> return (Name "_" 0 :> NoAnn))
     <|> liftM2 (:>) varName typeAnnot

pat :: Parser UPat
pat =   parenPat
    <|> liftM RecLeaf binder

parenPat :: Parser UPat
parenPat = do
  xs <- parens $ pat `sepBy` symbol ","
  return $ case xs of
    [x] -> x
    xs -> RecTree $ Tup xs

intQualifier :: Parser Int
intQualifier = do
  count <- optional $ symbol "_" >> lexeme int
  return $ case count of Nothing -> 0
                         Just n  -> n

-- === Parsing types ===

sigmaType :: Parser Type
sigmaType = do
  ty <- typeExpr
  let vs = filter nameIsLower $ envNames (freeVars ty)
  case vs of
    [] -> return ty
    _ -> case inferKinds vs ty of
      Left e -> fail $ pprint e
      Right kinds -> return $ Forall kinds (abstractTVs vs ty)
  where
    nameIsLower v = isLower (nameTag v !! 0)

tauType :: Parser Type
tauType = do
  ty <- sigmaType
  case ty of
    Forall _ _ -> fail $ "Can't have quantified (lowercase) type variables here"
    _ -> return ty

typeExpr :: Parser Type
typeExpr = makeExprParser (sc >> typeExpr') typeOps
  where
    typeOps = [ [InfixR (symbol "=>" >> return TabType)]
              , [InfixR (symbol "->" >> return ArrType)]]

typeExpr' =   parenTy
          <|> existsType
          <|> typeName
          <|> liftM TypeVar varName
          <?> "type"

existsType :: Parser Type
existsType = do
  try $ symbol "E"
  v <- varName
  symbol "."
  body <- tauType
  return $ Exists (abstractTVs [v] body)

typeName :: Parser Type
typeName = do
  w <- lexeme . try $ (:) <$> upperChar <*> many alphaNumChar
  return $ case M.lookup w baseTypeNames of
             Nothing -> TypeVar (rawName w)
             Just b -> BaseType b

capVarName :: Parser Name
capVarName = liftM2 Name capIdentifier intQualifier

capIdentifier :: Parser String
capIdentifier = lexeme . try $ do
  w <- (:) <$> upperChar <*> many alphaNumChar
  failIf (w `M.member` baseTypeNames) $ show w ++ " is a base type"
  return w

baseTypeNames = M.fromList [ ("Int" , IntType) , ("Real", RealType)
                           , ("Bool", BoolType), ("Str" , StrType)]

parenTy :: Parser Type
parenTy = do
  elts <- parens $ typeExpr `sepBy` symbol ","
  return $ case elts of
    [ty] -> ty
    _ -> RecType $ Tup elts
