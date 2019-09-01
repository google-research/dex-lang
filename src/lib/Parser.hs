module Parser (parseProg, parseTopDecl, Prog) where

import Control.Monad
import Control.Monad.Combinators.Expr
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Data.Map.Strict as M
import Data.Char (isLower)
import Data.Maybe (fromMaybe)

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
declSep = void $ (eol >> sc) <|> symbol ";"

typeAlias :: Parser UDecl
typeAlias = do
  symbol "type"
  v <- capVarName
  symbol "="
  ty <- tauType
  return $ TAlias v ty

typedLet :: Parser UDecl
typedLet = do
  (v, ty) <- try $ do
    v <- varName
    symbol "::"
    ty <- sigmaType
    declSep
    return (v, ty)
  v' <- varName
  if v /= v' then fail $ "Expected: " ++ pprint v else return ()
  wrap <- idxLhsArgs <|> lamLhsArgs
  symbol "="
  body <- expr
  return $ Let (RecLeaf (v :> Ann ty)) (wrap body)

unpack :: Parser UDecl
unpack = do
  (b, tv) <- try $ do b <- binder
                      comma
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
     <|> pack
     <?> "term"

parenRaw :: Parser UExpr
parenRaw = do
  elts <- parens $ expr `sepBy` comma
  return $ case elts of
    [e] -> e
    _ -> RecCon $ Tup elts

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

primOp :: Parser UExpr
primOp = do
  s <- try $ symbol "%" >> identifier
  b <- case strToBuiltin s of
    Just b -> return b
    Nothing -> fail $ "Unexpected builtin: " ++ s
  args <- parens $ expr `sepBy` comma
  return $ PrimOp b [] args

ffiCall :: Parser UExpr
ffiCall = do
  symbol "%%"
  s <- identifier
  args <- parens $ expr `sepBy` comma
  return $ PrimOp (FFICall (length args) s) [] args

lamExpr :: Parser UExpr
lamExpr = do
  symbol "lam"
  ps <- pat `sepBy` sc
  period
  body <- expr
  return $ foldr Lam body ps

forExpr :: Parser UExpr
forExpr = do
  symbol "for"
  vs <- pat `sepBy` sc
  period
  body <- expr
  return $ foldr For body vs

tabCon :: Parser UExpr
tabCon = do
  xs <- brackets $ expr `sepBy` comma
  return $ TabCon NoAnn xs

pack :: Parser UExpr
pack = do
  symbol "pack"
  liftM3 Pack (expr <* comma) (tauType <* comma) existsType

idxLhsArgs :: Parser (UExpr -> UExpr)
idxLhsArgs = do
  period
  args <- pat `sepBy` period
  return $ \body -> foldr For body args

lamLhsArgs :: Parser (UExpr -> UExpr)
lamLhsArgs = do
  args <- pat `sepBy` sc
  return $ \body -> foldr Lam body args

literal :: Parser LitVal
literal = lexeme $  fmap IntLit  (try (int <* notFollowedBy (period)))
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
   resNames = ["for", "lam", "let", "in", "unpack", "pack"]

appRule :: Operator Parser UExpr
appRule = InfixL (sc *> notFollowedBy (choice . map symbol $ opNames)
                     >> return App)
  where
    opNames = ["+", "*", "/", "-", "^", "$", "@"]

postFixRule :: Operator Parser UExpr
postFixRule = Postfix $ do
  trailers <- some $     (period >> liftM Left idxExpr)
                     <|> (symbol "@" >> liftM Right typeExpr)
  return $ \e -> foldl addPostFix e trailers
  where
    addPostFix :: UExpr -> Either UExpr Type -> UExpr
    addPostFix e (Left idx) = Get e idx
    addPostFix (TApp e tys) (Right ty) = TApp e (tys ++ [ty])
    addPostFix e (Right ty) = TApp e [ty]

binOpRule :: String -> Builtin -> Operator Parser UExpr
binOpRule opchar builtin = InfixL (symbol opchar >> return binOpApp)
  where binOpApp e1 e2 = PrimOp builtin [] [e1, e2]

ops :: [[Operator Parser UExpr]]
ops = [ [postFixRule, appRule]
      , [binOpRule "^" Pow]
      , [binOpRule "*" FMul, binOpRule "/" FDiv]
      , [binOpRule "+" FAdd, binOpRule "-" FSub]
      , [binOpRule "<" FLT, binOpRule ">" FGT]
      , [InfixR (symbol "$" >> return App)]
      , [InfixL (symbol "#deriv" >> return DerivAnnot)]
       ]

varName :: Parser Name
varName = liftM2 Name identifier intQualifier

idxExpr :: Parser UExpr
idxExpr = withSourceAnn $ liftM Var varName <|> parenRaw

binder :: Parser UBinder
binder = (symbol "_" >> return (Name "_" 0 :> NoAnn))
     <|> liftM2 (:>) varName typeAnnot

pat :: Parser UPat
pat =   parenPat
    <|> liftM RecLeaf binder

parenPat :: Parser UPat
parenPat = do
  xs <- parens $ pat `sepBy` comma
  return $ case xs of
    [x] -> x
    _   -> RecTree $ Tup xs

intQualifier :: Parser Int
intQualifier = do
  n <- optional $ symbol "_" >> lexeme int
  return $ fromMaybe 0 n

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

typeExpr' :: Parser Type
typeExpr' =   parenTy
          <|> existsType
          <|> typeName
          <|> liftM TypeVar varName
          <?> "type"

existsType :: Parser Type
existsType = do
  try $ symbol "E"
  v <- varName
  period
  body <- typeExpr
  return $ Exists (abstractTVs [v] body)

typeName :: Parser Type
typeName = do
  v <- try $ capVarName
  return $ case M.lookup v baseTypeNames of
             Nothing -> TypeVar v
             Just b -> BaseType b

capVarName :: Parser Name
capVarName = liftM2 Name capIdentifier intQualifier

capIdentifier :: Parser String
capIdentifier = lexeme . try $ (:) <$> upperChar <*> many alphaNumChar

baseTypeNames :: M.Map Name BaseType
baseTypeNames = M.fromList
  [ (rawName "Int" , IntType)
  , (rawName "Real", RealType)
  , (rawName "Bool", BoolType)
  , (rawName "Str" , StrType)]

parenTy :: Parser Type
parenTy = do
  elts <- parens $ typeExpr `sepBy` comma
  return $ case elts of
    [ty] -> ty
    _ -> RecType $ Tup elts

comma :: Parser ()
comma = symbol ","

period :: Parser ()
period = symbol "."
