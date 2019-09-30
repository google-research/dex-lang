module Parser (parseProg, parseTopDeclRepl, parseTopDecl) where

import Control.Monad
import Control.Monad.Combinators.Expr
import Text.Megaparsec
import Text.Megaparsec.Char
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

parseProg :: String -> [SourceBlock]
parseProg s = mustParseit s $ manyTill (sourceBlock <* outputLines) eof

parseTopDeclRepl :: String -> Maybe SourceBlock
parseTopDeclRepl s = mustParseit s (reportEOF sourceBlock)

parseTopDecl :: String -> Except UTopDecl
parseTopDecl s = parseit s topDecl

parseit :: String -> Parser a -> Except a
parseit s p = case parse (p <* (optional eol >> eof)) "" s of
                Left e -> throw ParseErr (errorBundlePretty e)
                Right x -> return x

mustParseit :: String -> Parser a -> a
mustParseit s p  = case parseit s p of
  Right ans -> ans
  Left e -> error $ "This shouldn't happen:\n" ++ pprint e

topDecl :: Parser UTopDecl
topDecl = ( explicitCommand
        <|> liftM TopDecl decl
        <|> liftM (EvalCmd . Command (EvalExpr Printed)) expr
        <?> "top-level declaration" ) <* (void eol <|> eof)

sourceBlock :: Parser SourceBlock
sourceBlock = do
  offset <- getOffset
  pos <- getSourcePos
  (source, block) <- withSource $ withRecovery recover $ sourceBlock'
  return $ SourceBlock (unPos (sourceLine pos)) offset source block

recover :: (Stream s, ShowErrorComponent e) => ParseError s e -> Parser SourceBlock'
recover e = consumeTillBreak >> return (UnParseable (parseErrorPretty e))

consumeTillBreak :: Parser ()
consumeTillBreak = void $ manyTill anySingle $ eof <|> void (try (eol >> eol))

sourceBlock' :: Parser SourceBlock'
sourceBlock' =
      (char '\'' >> liftM (ProseBlock . fst) (withSource consumeTillBreak))
  <|> (some eol >> return EmptyLines)
  <|> (sc >> eol >> return CommentLine)
  <|> (liftM UTopDecl topDecl)

explicitCommand :: Parser UTopDecl
explicitCommand = do
  cmdName <- char ':' >> identifier
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

reportEOF :: Parser a -> Parser (Maybe a)
reportEOF p = withRecovery (const (eof >> return Nothing)) (liftM Just p)

-- === Parsing decls ===

decl :: Parser UDecl
decl = typeAlias <|> letPoly <|> unpack <|> letMono

declSep :: Parser ()
declSep = void $ (eol >> sc) <|> symbol ";"

typeAlias :: Parser UDecl
typeAlias = do
  symbol "type"
  v <- upperName
  symbol "="
  ty <- tauType
  return $ TAlias v ty

letPoly :: Parser UDecl
letPoly = do
  (v, (tvs, kinds, ty)) <- try $ do
    v <- lowerName
    symbol "::"
    sTy <- sigmaType
    declSep
    return (v, sTy)
  symbol (pprint v)
  wrap <- idxLhsArgs <|> lamLhsArgs
  symbol "="
  rhs <- liftM wrap expr
  return $ case tvs of
    [] -> LetMono p rhs
     where p = RecLeaf $ v :> Ann ty
    _  -> LetPoly (v:>sTy) (TLam tbs rhs)
     where sTy = Forall kinds (abstractTVs tvs ty)
           tbs = zipWith (:>) tvs kinds

unpack :: Parser UDecl
unpack = do
  (b, tv) <- try $ do b <- binder
                      comma
                      tv <- upperName
                      symbol "=" >> symbol "unpack"
                      return (b, tv)
  body <- expr
  return $ Unpack b tv body

letMono :: Parser UDecl
letMono = do
  (p, wrap) <- try $ do p <- pat
                        wrap <- idxLhsArgs <|> lamLhsArgs
                        symbol "="
                        return (p, wrap)
  body <- expr
  return $ LetMono p (wrap body)

-- === Parsing expressions ===

expr :: Parser UExpr
expr = makeExprParser (sc >> withSourceAnn term >>= maybeAnnot) ops

term :: Parser UExpr
term =   parenRaw
     <|> var
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

var :: Parser UExpr
var = liftM2 Var lowerName $ many (symbol "@" >> tauTypeAtomic)

declExpr :: Parser UExpr
declExpr = do
  symbol "let"
  decls <- decl `sepEndBy` declSep
  symbol "in"
  body <- expr
  return $ wrapDecls decls body

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
  ann <- optional $ symbol "::" >> tauType
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
literal = lexeme $  fmap IntLit  (try (int <* notFollowedBy period))
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
  trailers <- some (period >> idxExpr)
  return $ \e -> foldl Get e trailers

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

idxExpr :: Parser UExpr
idxExpr = withSourceAnn $ rawVar <|> parenRaw

rawVar :: Parser UExpr
rawVar = liftM (flip Var []) lowerName

binder :: Parser UBinder
binder = (symbol "_" >> return (Name "_" 0 :> NoAnn))
     <|> liftM2 (:>) lowerName typeAnnot

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

lowerName :: Parser Name
lowerName = name identifier

upperName :: Parser Name
upperName = name $ lexeme . try $ (:) <$> upperChar <*> many alphaNumChar

name :: Parser String -> Parser Name
name p = liftM2 Name p intQualifier

-- === Parsing types ===

sigmaType :: Parser ([Name], [Kind], Type)
sigmaType = do
  maybeVs <- optional $ do
    try $ symbol "A"
    vs <- many typeVar
    period
    return [v | TypeVar v <- vs]
  ty <- tauType
  let vs' = case maybeVs of
              Nothing -> filter nameIsLower $
                           envNames (freeVars ty)  -- TODO: lexcial order!
              Just vs -> vs
  case inferKinds vs' ty of
    Left e -> fail $ pprint e
    Right kinds -> return (vs', kinds, ty)
  where
    nameIsLower v = isLower (nameTag v !! 0)

tauTypeAtomic :: Parser Type
tauTypeAtomic =   typeName
              <|> typeVar
              <|> parenTy

tauType :: Parser Type
tauType = makeExprParser (sc >> tauType') typeOps
  where
    typeOps = [ [InfixR (symbol "=>" >> return TabType)]
              , [InfixR (symbol "->" >> return ArrType)]]

tauType' :: Parser Type
tauType' =   parenTy
         <|> existsType
         <|> typeName
         <|> typeVar
         <|> idxSetLit
         <?> "type"

typeVar :: Parser Type
typeVar = liftM TypeVar (upperName <|> lowerName)

idxSetLit :: Parser Type
idxSetLit = liftM IdxSetLit $ int

parenTy :: Parser Type
parenTy = do
  elts <- parens $ tauType `sepBy` comma
  return $ case elts of
    [ty] -> ty
    _ -> RecType $ Tup elts

existsType :: Parser Type
existsType = do
  try $ symbol "E"
  ~(TypeVar v) <- typeVar
  period
  body <- tauType
  return $ Exists (abstractTVs [v] body)

typeName :: Parser Type
typeName = liftM BaseType $
       (symbol "Int"  >> return IntType)
   <|> (symbol "Real" >> return RealType)
   <|> (symbol "Bool" >> return BoolType)
   <|> (symbol "Str"  >> return StrType)

comma :: Parser ()
comma = symbol ","

period :: Parser ()
period = symbol "."
