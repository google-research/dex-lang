-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module Parser (Parser, parseit, parseProg, runTheParser,
               parseTopDeclRepl, uint, withSource, tauType,
               emptyLines, brackets, symbol) where

import Control.Monad
import Control.Monad.Combinators.Expr
import Control.Monad.Reader
import Text.Megaparsec hiding (Label, State)
import Text.Megaparsec.Char hiding (space)
import Data.Functor
import Data.List.NonEmpty (NonEmpty (..))
import Data.Void
import qualified Text.Megaparsec.Char.Lexer as L

import Env
import Record
import Syntax
import PPrint

data ParseCtx = ParseCtx { curIndent :: Int
                         , canBreak  :: Bool }
type Parser = ReaderT ParseCtx (Parsec Void String)

parseProg :: String -> [SourceBlock]
parseProg s = mustParseit s $ manyTill (sourceBlock <* outputLines) eof

parseTopDeclRepl :: String -> Maybe SourceBlock
parseTopDeclRepl s = case sbContents b of
  UnParseable True _ -> Nothing
  _ -> Just b
  where b = mustParseit s sourceBlock

parseit :: String -> Parser a -> Except a
parseit s p = case runTheParser s (p <* (optional eol >> eof)) of
  Left e -> throw ParseErr (errorBundlePretty e)
  Right x -> return x

mustParseit :: String -> Parser a -> a
mustParseit s p  = case parseit s p of
  Right ans -> ans
  Left e -> error $ "This shouldn't happen:\n" ++ pprint e

includeSourceFile :: Parser String
includeSourceFile = symbol "include" >> stringLiteral <* eol

sourceBlock :: Parser SourceBlock
sourceBlock = do
  offset <- getOffset
  pos <- getSourcePos
  (src, b) <- withSource $ withRecovery recover $ sourceBlock'
  return $ SourceBlock (unPos (sourceLine pos)) offset src b Nothing

recover :: ParseError String Void -> Parser SourceBlock'
recover e = do
  pos <- liftM statePosState getParserState
  reachedEOF <-  try (mayBreak sc >> eof >> return True)
             <|> return False
  consumeTillBreak
  return $ UnParseable reachedEOF $
    errorBundlePretty (ParseErrorBundle (e :| []) pos)

consumeTillBreak :: Parser ()
consumeTillBreak = void $ manyTill anySingle $ eof <|> void (try (eol >> eol))

sourceBlock' :: Parser SourceBlock'
sourceBlock' =
      (char '\'' >> liftM (ProseBlock . fst) (withSource consumeTillBreak))
  <|> (some eol >> return EmptyLines)
  <|> (sc >> eol >> return CommentLine)
  <|> (liftM IncludeSourceFile includeSourceFile)
  <|> loadData
  <|> dumpData
  <|> explicitCommand
  <|> (liftM (RunModule . declAsModule) (uDecl <* eol))

loadData :: Parser SourceBlock'
loadData = do
  symbol "load"
  fmt <- dataFormat
  s <- stringLiteral
  symbol "as"
  b <- uLetBinder
  void eol
  return $ LoadData (RecLeaf b) fmt s

dataFormat :: Parser DataFormat
dataFormat = do
  s <- nameString
  case s of
    "dxo"  -> return DexObject
    "dxbo" -> return DexBinaryObject
    _      -> fail $ show s ++ " not a recognized data format (one of dxo|dxbo)"

dumpData :: Parser SourceBlock'
dumpData = do
  symbol "dump"
  fmt <- dataFormat
  s <- stringLiteral
  e <- blockOrExpr
  void eol
  return $ Command (Dump fmt s) (exprAsModule e)

explicitCommand :: Parser SourceBlock'
explicitCommand = do
  cmdName <- char ':' >> nameString
  cmd <- case cmdName of
    "p"       -> return $ EvalExpr Printed
    "t"       -> return $ GetType
    "plot"    -> return $ EvalExpr Scatter
    "plotmat" -> return $ EvalExpr Heatmap
    "time"    -> return $ TimeIt
    "passes"  -> return $ ShowPasses
    _ -> case parsePassName cmdName of
      Just p -> return $ ShowPass p
      _ -> fail $ "unrecognized command: " ++ show cmdName
  e <- blockOrExpr <*eol
  return $ Command cmd (exprAsModule e)

declAsModule :: UDecl -> UModule
declAsModule decl = UModule imports exports [decl]
 where
   imports = envNames $ freeVars decl
   exports = envNames $ uDeclBoundVars decl

exprAsModule :: UExpr -> (Name, UModule)
exprAsModule e = (v, UModule imports [v] body)
  where
    v = "*ans*"
    body = [ULet (RecLeaf (v:>Nothing)) e]
    imports = envNames $ freeVars e

tauType :: Parser Type
tauType = undefined

-- === uexpr ===

uExpr :: Parser UExpr
uExpr = makeExprParser uExpr' uops
  where
    uExpr' :: Parser UExpr
    uExpr' =   uArrow
           <|> uImplicitArrow
           <|> leafUExpr
           <|> uLamExpr
           <|> uForExpr
           <|> uPrim
           <?> "expression"

leafUExpr :: Parser UExpr
leafUExpr =   parens uExpr
          <|> uvar
          <|> withSrc (liftM (UPrimExpr . ConExpr . Lit) uLit)
  where
    uLit :: Parser LitVal
    uLit =   (IntLit  <$> intLit)
         <|> (RealLit <$> doubleLit)

    uvar :: Parser UExpr
    uvar = withSrc $ (UVar . (:>())) <$> uName

uDecl :: Parser UDecl
uDecl = do
  lhs <- simpleLet <|> funDefLet
  rhs <- sym "=" >> blockOrExpr
  return $ lhs rhs
  where
    simpleLet :: Parser (UExpr -> UDecl)
    simpleLet = do
      b <- uLetBinder
      return $ ULet (RecLeaf b)

    funDefLet :: Parser (UExpr -> UDecl)
    funDefLet = label "function definition" $ do
      keyWord DefKW
      v <- uName
      lam <- buildLam <$> many uLamBinder <*> optional (annot uExpr)
      return $ \body -> ULet (RecLeaf (v:>Nothing)) (lam body)

uLetBinder :: Parser UBinder
uLetBinder = do
  v <- try $ uName <* lookAhead (sym ":" <|> sym "=")
  ann <- optional $ annot uExpr
  return $ v:>ann

uLamExpr :: Parser UExpr
uLamExpr = do
  sym "\\"
  buildLam <$> some uLamBinder
           <*> (return Nothing)
           <*> (argTerm >> blockOrExpr)

buildLam :: [(UBinder, ArrowHead)]
         -> Maybe UExpr -> UExpr -> UExpr
buildLam binders ann body@(UPos pos _) = case binders of
  [] -> case ann of
    Nothing -> body
    Just ty -> UPos pos $ UAnnot body ty
  (b,ah):bs -> UPos pos $  -- TODO: join with source position of binders too
    ULam ah $ ULamExpr (RecLeaf b) $ buildLam bs ann body

buildFor :: Direction -> [UBinder] -> UExpr -> UExpr
buildFor dir binders body@(UPos pos _) = case binders of
  [] -> body
  b:bs -> UPos pos $ UFor dir $ ULamExpr (RecLeaf b) $ buildFor dir bs body

uForBinder :: Parser UBinder
uForBinder = rawLamBinder <|> parenLamBinder

uForExpr :: Parser UExpr
uForExpr =
  buildFor <$> (     (keyWord ForKW $> Fwd)
                 <|> (keyWord RofKW $> Rev))
           <*> (some uForBinder <* argTerm)
           <*> blockOrExpr

blockOrExpr :: Parser UExpr
blockOrExpr =  block <|> uExpr

type UStatement = (Either UDecl UExpr, SrcPos)

block :: Parser UExpr
block = do
  nextLine
  indent <- liftM length $ some (char ' ')
  withIndent indent $ do
    statements <- mayNotBreak $ uStatement `sepBy1` (semicolon <|> try nextLine)
    case last statements of
      (Left _, _) -> fail "Last statement in a block must be an expression."
      _           -> return $ wrapUStatements statements

wrapUStatements :: [UStatement] -> UExpr
wrapUStatements statements = case statements of
  [(Right e, _)] -> e
  (s, pos):rest -> UPos pos $ case s of
    Left  d -> UDecl d $ wrapUStatements rest
    Right e -> UDecl d $ wrapUStatements rest
      where d = ULet (RecLeaf (NoName:>Nothing)) e
  [] -> error "Shouldn't be reachable"

uStatement :: Parser UStatement
uStatement = withPos $   liftM Left  uDecl
                     <|> liftM Right uExpr

uArrow :: Parser UExpr
uArrow = withSrc $ do
  (v, ah) <- try $ (,) <$> (rawPiBinder <|> parenPiBinder) <*> arrowHead
  resultTy <- uExpr
  return $ UArrow ah (UPi v resultTy)

uImplicitArrow :: Parser UExpr
uImplicitArrow = withSrc $ do
  v <- try $ implicitPiBinder <* sym "->"
  resultTy <- uExpr
  return $ UArrow ImplicitArrow (UPi v resultTy)

arrowHead :: Parser ArrowHead
arrowHead = (sym "->" $> PlainArrow) <|> (sym "=>" $> TabArrow)

uName :: Parser Name
uName = textName <|> symName

annot :: Parser a -> Parser a
annot p = sym ":" >> p

uLamBinder :: Parser (UBinder, ArrowHead)
uLamBinder =   liftM (,PlainArrow   ) rawLamBinder
           <|> liftM (,PlainArrow   ) parenLamBinder
           <|> liftM (,ImplicitArrow) implicitLamBinder

rawLamBinder :: Parser UBinder
rawLamBinder = (:>) <$> uName <*> (optional $ annot leafUExpr)

parenLamBinder :: Parser UBinder
parenLamBinder = parens $ (:>) <$> uName <*> (optional $ annot uExpr)

implicitLamBinder :: Parser UBinder
implicitLamBinder = braces $ (:>) <$> uName <*> (optional $ annot uExpr)

rawPiBinder :: Parser (VarP UType)
rawPiBinder = (:>) <$> uName <*> annot leafUExpr

parenPiBinder :: Parser (VarP UType)
parenPiBinder = parens $ (:>) <$> uName <*> annot uExpr

implicitPiBinder :: Parser (VarP UType)
implicitPiBinder = braces $ (:>) <$> uName <*> annot uExpr

uPrim :: Parser UExpr
uPrim = withSrc $ do
  s <- primName
  Just prim <- return $ strToName s
  UPrimExpr <$> traverseExpr prim primArg primArg primArg
  where primArg = const textName

-- literal symbols here must only use chars from `symChars`
uops :: [[Operator Parser UExpr]]
uops =
  [ [InfixL $ sym "." $> mkGenApp TabArrow]
  , [InfixL $ sc $> mkApp]
  , [symOp "^"]
  , [symOp "*", symOp "/" ]
  , [symOp "+", symOp "-"]
  , [InfixR $ sym "=>" $> mkArrow TabArrow]
  , [symOp "==", symOp "<=", symOp ">=", symOp "<", symOp ">"]
  , [symOp "&&", symOp "||"]
  , [InfixL $ opWithSrc $ backquoteName >>= (return . binApp)]
  , [InfixL $ sym "$" $> mkApp]
  , [symOp "+=", symOp ":="]
  , [InfixR $ sym "->" $> mkArrow PlainArrow]]

opWithSrc :: Parser (SrcPos -> UExpr -> UExpr -> UExpr)
          -> Parser (UExpr -> UExpr -> UExpr)
opWithSrc p = do
  (f, pos) <- withPos p
  return $ f pos

symOp :: String -> Operator Parser UExpr
symOp s = InfixL $ opWithSrc $ do
  label "infix operator" (sym s)
  return $ binApp f
  where f = rawName SourceName $ "(" <> s <> ")"

binApp :: Name -> SrcPos -> UExpr -> UExpr -> UExpr
binApp f pos x y = (f' `mkApp` x) `mkApp` y
  where f' = UPos pos $ UVar (f:>())

mkGenApp :: ArrowHead -> UExpr -> UExpr -> UExpr
mkGenApp ah f x = UPos (joinPos f x) $ UApp ah f x

mkApp :: UExpr -> UExpr -> UExpr
mkApp = mkGenApp PlainArrow

mkArrow :: ArrowHead -> UExpr -> UExpr -> UExpr
mkArrow ah a b = UPos (joinPos a b) $ UArrow ah $ UPi (NoName:>a) b

withSrc :: Parser UExpr' -> Parser UExpr
withSrc p = do
  (e, pos) <- withPos p
  return $ UPos pos e

joinPos :: UExpr -> UExpr -> SrcPos
joinPos (UPos (l, h) _) (UPos (l', h') _) = (min l l', max h h')

_appPreludeName :: SrcPos -> String -> UExpr -> UExpr
_appPreludeName fPos f x = mkApp f' x
  where f' = UPos fPos $ UVar $ rawName SourceName f :> ()

-- === lexemes ===

-- These `Lexer` actions must be non-overlapping and never consume input on failure
type Lexer = Parser

data KeyWord = DefKW | ForKW | RofKW | CaseKW

textName :: Lexer Name
textName = liftM (rawName SourceName) $ lexeme $ try $ do
  w <- (:) <$> letterChar <*> many nameTailChar
  failIf (w `elem` keyWordStrs) $ show w ++ " is a reserved word"
  return w
  where
    keyWordStrs :: [String]
    keyWordStrs = ["def", "for", "rof", "case", "llam"]

keyWord :: KeyWord -> Lexer ()
keyWord kw = lexeme $ try $ string s >> notFollowedBy nameTailChar
  where
    s = case kw of
      DefKW  -> "def"
      ForKW  -> "for"
      RofKW  -> "rof"
      CaseKW -> "case"

primName :: Lexer String
primName = lexeme $ try $ char '%' >> some letterChar

intLit :: Lexer Int
intLit = lexeme $ try $ L.decimal <* notFollowedBy (char '.')

doubleLit :: Lexer Double
doubleLit = lexeme $
      try L.float
  <|> try (fromIntegral <$> ((L.decimal :: Parser Int) <* char '.'))

-- string must only contain characters from the list `symChars`
sym :: String -> Lexer ()
sym s = lexeme $ try $ string s >> notFollowedBy symChar

symName :: Lexer Name
symName = lexeme $ try $ do
  s <- between (char '(') (char ')') $ some symChar
  return $ rawName SourceName $ "(" <> s <> ")"

backquoteName :: Lexer Name
backquoteName = label "backquoted name" $
  lexeme $ try $ between (char '`') (char '`') textName

-- brackets and punctuation
-- (can't treat as sym because e.g. `((` is two separate lexemes)
lParen, rParen, lBracket, rBracket, lBrace, rBrace, comma, semicolon :: Lexer ()

lParen    = notFollowedBy symName >> charLexeme '('
rParen    = charLexeme ')'
lBracket  = charLexeme '['
rBracket  = charLexeme ']'
lBrace    = charLexeme '{'
rBrace    = charLexeme '}'
comma     = charLexeme ','
semicolon = charLexeme ';'

charLexeme :: Char -> Parser ()
charLexeme c = void $ lexeme $ char c

nameTailChar :: Parser Char
nameTailChar = alphaNumChar <|> char '\'' <|> char '_'

symChar :: Parser Char
symChar = choice $ map char symChars

symChars :: [Char]
symChars = ".!$^&*:-~+/=<>|?\\"

-- === Util ===

runTheParser :: String -> Parser a -> Either (ParseErrorBundle String Void) a
runTheParser s p =  parse (runReaderT p (ParseCtx 0 False)) "" s

sc :: Parser ()
sc = L.space space lineComment empty

lineComment :: Parser ()
lineComment = do
  try $ string "--" >> notFollowedBy (void (char 'o'))
  void (takeWhileP (Just "char") (/= '\n'))

emptyLines :: Parser ()
emptyLines = void $ many (sc >> eol)

outputLines :: Parser ()
outputLines = void $ many (symbol ">" >> takeWhileP Nothing (/= '\n') >> eol)

stringLiteral :: Parser String
stringLiteral = char '"' >> manyTill L.charLiteral (char '"') <* sc

space :: Parser ()
space = do
  consumeNewLines <- asks canBreak
  if consumeNewLines
    then space1
    else void $ takeWhile1P (Just "white space") (`elem` (" \t" :: String))

mayBreak :: Parser a -> Parser a
mayBreak p = local (\ctx -> ctx { canBreak = True }) p

mayNotBreak :: Parser a -> Parser a
mayNotBreak p = local (\ctx -> ctx { canBreak = False }) p

nameString :: Parser String
nameString = lexeme . try $ (:) <$> lowerChar <*> many alphaNumChar

uint :: Parser Int
uint = L.decimal <* sc

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: String -> Parser ()
symbol s = void $ L.symbol sc s

argTerm :: Parser ()
argTerm = mayNotBreak $ sym "."

bracketed :: Parser () -> Parser () -> Parser a -> Parser a
bracketed left right p = between left right $ mayBreak p

parens :: Parser a -> Parser a
parens p = bracketed lParen rParen p

brackets :: Parser a -> Parser a
brackets p = bracketed lBracket rBracket p

braces :: Parser a -> Parser a
braces p = bracketed lBrace rBrace p

withPos :: Parser a -> Parser (a, SrcPos)
withPos p = do
  n <- getOffset
  x <- p
  n' <- getOffset
  return $ (x, (n, n'))

nextLine :: Parser ()
nextLine = do
  void eol
  n <- asks curIndent
  void $ mayNotBreak $ many $ try (sc >> eol)
  void $ replicateM n (char ' ')

withSource :: Parser a -> Parser (String, a)
withSource p = do
  s <- getInput
  (x, (start, end)) <- withPos p
  return (take (end - start) s, x)

withIndent :: Int -> Parser a -> Parser a
withIndent n p = local (\ctx -> ctx { curIndent = curIndent ctx + n }) $ p

failIf :: Bool -> String -> Parser ()
failIf True s = fail s
failIf False _ = return ()
