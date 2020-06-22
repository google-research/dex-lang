-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module Parser (Parser, parseit, parseProg, runTheParser, parseData,
               parseTopDeclRepl, uint, withSource, tauType,
               emptyLines, brackets, symbol, symChar, keyWordStrs) where

import Control.Monad
import Control.Monad.Combinators.Expr
import Control.Monad.Reader
import Text.Megaparsec hiding (Label, State)
import Text.Megaparsec.Char hiding (space)
import Data.Char (isLower)
import Data.Functor
import Data.List.NonEmpty (NonEmpty (..))
import Data.Void
import Data.String (fromString)
import qualified Text.Megaparsec.Char.Lexer as L

import Env
import Syntax
import PPrint

data ParseCtx = ParseCtx { curIndent :: Int
                         , canPair   :: Bool
                         , canBreak  :: Bool }
type Parser = ReaderT ParseCtx (Parsec Void String)

parseProg :: String -> [SourceBlock]
parseProg s = mustParseit s $ manyTill (sourceBlock <* outputLines) eof

parseData :: String -> Except UExpr
parseData s = parseit s $ expr <* (optional eol >> eof)

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
      proseBlock
  <|> topLevelCommand
  <|> liftM (RunModule . declAsModule) (uTopDecl <* eol)
  <|> liftM (Command (EvalExpr Printed) . exprAsModule) (expr <* eol)
  <|> hidden (some eol >> return EmptyLines)
  <|> hidden (sc >> eol >> return CommentLine)

proseBlock :: Parser SourceBlock'
proseBlock = label "prose block" $ char '\'' >> liftM (ProseBlock . fst) (withSource consumeTillBreak)

loadData :: Parser SourceBlock'
loadData = do
  symbol "load"
  fmt <- dataFormat
  s <- stringLiteral
  symbol "as"
  b <- uBinder
  void eol
  return $ LoadData b fmt s

topLevelCommand :: Parser SourceBlock'
topLevelCommand =
      (liftM IncludeSourceFile includeSourceFile)
  <|> loadData
  <|> dumpData
  <|> explicitCommand
  <?> "top-level command"

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
  return $ case (e, cmd) of
    (WithSrc _ (UVar (v:>())), GetType) -> GetNameType v
    _ -> Command cmd (exprAsModule e)

declAsModule :: UDecl -> UModule
declAsModule dec@(ULet (WithSrc _ pat,_) _) = UModule imports exports [dec]
 where
   imports = envNames $ freeUVars dec
   exports = envNames $ foldMap (@>()) pat

exprAsModule :: UExpr -> (Name, UModule)
exprAsModule e = (v, UModule imports [v] body)
  where
    v = "_ans_"
    body = [ULet (WithSrc (srcPos e) (namePat v), Nothing) e]
    imports = envNames $ freeUVars e

tauType :: Parser Type
tauType = undefined

-- === uexpr ===

expr :: Parser UExpr
expr = mayNotPair $ makeExprParser leafExpr ops

-- expression without exposed infix operators
leafExpr :: Parser UExpr
leafExpr =   parens (mayPair $ makeExprParser leafExpr ops)
         <|> uTabCon
         <|> uVar
         <|> uHole
         <|> uLit
         <|> uPiType
         <|> uLamExpr
         <|> uForExpr
         <|> uCaseExpr
         <|> uPrim
         <|> unitCon
         <?> "expression"

containedExpr :: Parser UExpr
containedExpr =   parens (mayPair $ makeExprParser leafExpr ops)
              <|> uVar
              <?> "contained expression"

uType :: Parser UType
uType = expr

uLit :: Parser UExpr
uLit = withSrc $ liftM (UPrimExpr . ConExpr . Lit) litVal

litVal :: Parser LitVal
litVal =   (IntLit  <$> intLit)
       <|> (RealLit <$> doubleLit)
       <?> "literal"

uVar :: Parser UExpr
uVar = withSrc $ try $ (UVar . (:>())) <$> (uName <* notFollowedBy (sym ":"))

uHole :: Parser UExpr
uHole = withSrc $ underscore $> UHole

uTopDecl :: Parser UDecl
uTopDecl = do
  ~(ULet (p, ann) rhs, pos) <- withPos decl
  let ann' = fmap (addImplicitImplicitArgs pos) ann
  return $ ULet (p, ann') rhs
  where
    addImplicitImplicitArgs :: SrcPos -> UType -> UType
    addImplicitImplicitArgs pos ty = foldr (addImplicitArg pos) ty implicitVars
      where
        implicitVars = filter isLowerCaseName $ envNames $ freeUVars ty
        isLowerCaseName :: Name -> Bool
        isLowerCaseName (Name _ tag _) = isLower $ head $ tagToStr tag
        isLowerCaseName _ = False

    addImplicitArg :: SrcPos -> Name -> UType -> UType
    addImplicitArg pos v ty =
      WithSrc pos $ UPi (v:>uTyKind) ImplicitArrow ty
      where
        k = if v == rawName SourceName "eff" then EffectRowKind else TypeKind
        uTyKind = WithSrc pos $ UPrimExpr $ TCExpr k

decl :: Parser UDecl
decl = do
  lhs <- simpleLet <|> funDefLet
  rhs <- sym "=" >> blockOrExpr
  return $ lhs rhs

simpleLet :: Parser (UExpr -> UDecl)
simpleLet = label "let binding" $ do
  pat <- try $ uPat <* lookAhead (sym "=" <|> sym ":")
  ann <- optional $ annot uType
  return $ ULet (pat, ann)

funDefLet :: Parser (UExpr -> UDecl)
funDefLet = label "function definition" $ mayBreak $ do
  keyWord DefKW
  v <- withSrc $ namePat <$> uName
  bs <- some arg
  (eff, ty) <- label "result type annotation" $ annot effectiveType
  let piBinders = flip map bs $ \(p, ann, arr) -> (patName p:>ann, arr)
  let funTy = buildPiType piBinders eff ty
  let letBinder = (v, Just funTy)
  let lamBinders = flip map bs $ \(p,_, arr) -> ((p,Nothing), arr)
  return $ \body -> ULet letBinder (buildLam lamBinders body)
  where
    arg :: Parser (UPat, UType, UArrow)
    arg = label "def arg" $ do
      (p, ty) <-(            ((,) <$> uVarPat <*> annot containedExpr)
                  <|> parens ((,) <$> uPat    <*> annot uType))
      arr <- arrow (return ()) <|> return (PlainArrow ())
      return (p, ty, arr)

patName :: UPat -> Name
patName (WithSrc _ (PatBind (v:>()))) = v
patName _ = NoName

buildPiType :: [(UPiBinder, UArrow)] -> EffectRow -> UType -> UType
buildPiType [] _ _ = error "shouldn't be possible"
buildPiType ((b,arr):bs) eff ty = WithSrc pos $ case bs of
  [] -> UPi b (fmap (const eff ) arr) ty
  _  -> UPi b (fmap (const Pure) arr) $ buildPiType bs eff ty
  where WithSrc pos _ = varAnn b

effectiveType :: Parser (EffectRow, UType)
effectiveType = (,) <$> effects <*> uType

effects :: Parser EffectRow
effects = braces someEffects <|> return Pure
  where
    someEffects = do
      effs <- liftM2 (,) effectName uName `sepBy` sym ","
      v <- optional $ symbol "|" >> uName
      return $ EffectRow effs v

effectName :: Parser EffectName
effectName =     (keyWord WriteKW $> Writer)
             <|> (keyWord ReadKW  $> Reader)
             <|> (keyWord StateKW $> State)
             <?> "effect name (Accum|Read|State)"

uLamExpr :: Parser UExpr
uLamExpr = do
  sym "\\"
  bs <- some uBinder
  body <- argTerm >> blockOrExpr
  return $ buildLam (map (,PlainArrow ()) bs) body

buildLam :: [(UBinder, UArrow)] -> UExpr -> UExpr
buildLam binders body@(WithSrc pos _) = case binders of
  [] -> body
  -- TODO: join with source position of binders too
  (b,arr):bs -> WithSrc (joinPos pos' pos) $ ULam b arr $ buildLam bs body
     where (WithSrc pos' _, _) = b

buildFor :: SrcPos -> Direction -> [UBinder] -> UExpr -> UExpr
buildFor pos dir binders body = case binders of
  [] -> body
  b:bs -> WithSrc pos $ UFor dir b $ buildFor pos dir bs body

uForExpr :: Parser UExpr
uForExpr = do
  (dir, pos) <- withPos $   (keyWord ForKW $> Fwd)
                        <|> (keyWord RofKW $> Rev)
  buildFor pos dir <$> (some uBinder <* argTerm) <*> blockOrExpr

blockOrExpr :: Parser UExpr
blockOrExpr =  block <|> expr

unitCon :: Parser UExpr
unitCon = withSrc $ symbol "()" $> (UPrimExpr $ ConExpr $ UnitCon)

uTabCon :: Parser UExpr
uTabCon = withSrc $ do
  xs <- brackets $ expr `sepBy` sym ","
  ty <- optional (annot uType)
  return $ UTabCon xs ty

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
  (s, pos):rest -> WithSrc pos $ case s of
    Left  d -> UDecl d $ wrapUStatements rest
    Right e -> UDecl d $ wrapUStatements rest
      where d = ULet (WithSrc pos (namePat NoName), Nothing) e
  [] -> error "Shouldn't be reachable"

uStatement :: Parser UStatement
uStatement = withPos $   liftM Left  decl
                     <|> liftM Right expr

-- TODO: put the `try` only around the `x:` not the annotation itself
uPiType :: Parser UExpr
uPiType = withSrc $ UPi <$> uPiBinder <*> arrow effects <*> uType
  where
    uPiBinder :: Parser UPiBinder
    uPiBinder = label "pi binder" $ do
      v <- try $ uBinderName <* sym ":"
      ty <- containedExpr
      return (v:>ty)

arrow :: Parser eff -> Parser (ArrowP eff)
arrow p =   (sym "->"  >> liftM PlainArrow p)
        <|> (sym "=>"  $> TabArrow)
        <|> (sym "--o" $> LinArrow)
        <|> (sym "?->"  $> ImplicitArrow)
        <?> "arrow"

uCaseExpr :: Parser UExpr
uCaseExpr = do
  ((), pos) <- withPos $ keyWord CaseKW
  e <- expr
  nextLine
  indent <- liftM length $ some $ char ' '
  withIndent indent $ do
    l <- lexeme (string "Left") >> caseLam
    nextLine
    r <- lexeme (string "Right") >> caseLam
    return $ applyNamed pos "caseAnalysis" [e, l, r]

caseLam :: Parser UExpr
caseLam = do
  p <- uPat
  sym "->"
  body <- blockOrExpr
  return $ WithSrc (srcPos body) $ ULam (p, Nothing) (PlainArrow ()) body

applyNamed :: SrcPos -> String -> [UExpr] -> UExpr
applyNamed pos name args = foldl mkApp f args
  where f = WithSrc pos $ UVar (Name SourceName (fromString name) 0:>())

uBinderName :: Parser Name
uBinderName = uName <|> (underscore >> return NoName)

uName :: Parser Name
uName = textName <|> symName

annot :: Parser a -> Parser a
annot p = label "type annotation" $ sym ":" >> p

uPat :: Parser UPat
uPat =   uVarPat
     <|> withSrc (symbol "()" $> PatUnit)
     <|> parens uPat'
     <?> "pattern"

uPat' :: Parser UPat
uPat' = do
  p1 <- uPat
  (   (do sym ","
          p2 <- uPat'
          return $ joinSrc p1 p2 $ PatPair p1 p2)
   <|> return p1)

uVarPat :: Parser UPat
uVarPat = withSrc $ namePat <$> uBinderName

uBinder :: Parser UBinder
uBinder =  label "binder" $ (,) <$> uPat <*> optional (annot containedExpr)

uPrim :: Parser UExpr
uPrim = withSrc $ do
  s <- primName
  case s of
    "ffi" -> do
      f <- lexeme $ some nameTailChar
      retTy <- baseType
      args <- some textName
      return $ UPrimExpr $ OpExpr $ FFICall f retTy args
    _ -> case strToName s of
      Just prim -> UPrimExpr <$> traverse (const textName) prim
      Nothing -> fail $ "Unrecognized primitive: " ++ s

baseType :: Parser BaseType
baseType =   (symbol "Int"  $> IntType)
         <|> (symbol "Real" $> RealType)
         <|> (symbol "Bool" $> BoolType)

-- === infix ops ===

-- literal symbols here must only use chars from `symChars`
ops :: [[Operator Parser UExpr]]
ops =
  [ [InfixL $ sym "." $> mkGenApp TabArrow, symOp "!"]
  , [InfixL $ sc $> mkApp]
  , [symOp "@"]
  , [symOp "^"]
  , [symOp "*", symOp "/" ]
  , [symOp "+", prefixNegOp, symOp "-"]
  , [InfixR $ sym "=>" $> mkArrow TabArrow]
  , [symOp "==", symOp "<=", symOp ">=", symOp "<", symOp ">"]
  , [symOp "&&", symOp "||"]
  , [InfixL $ opWithSrc $ backquoteName >>= (return . binApp)]
  , [InfixR $ mayBreak (sym "$") $> mkApp]
  , [symOp "+=", symOp ":=", symOp "|"]
  , [InfixR infixEffArrow, InfixR infixLinArrow]
  , [InfixR $ symOpP "&", pairOp]
  , indexRangeOps
  ]

opWithSrc :: Parser (SrcPos -> UExpr -> UExpr -> UExpr)
          -> Parser (UExpr -> UExpr -> UExpr)
opWithSrc p = do
  (f, pos) <- withPos p
  return $ f pos

pairOp :: Operator Parser UExpr
pairOp = InfixR $ opWithSrc $ do
  allowed <- asks canPair
  if allowed
    then sym "," >> return (binApp f)
    else fail "Unexpected comma"
  where f = rawName SourceName $ "(,)"

symOp :: String -> Operator Parser UExpr
symOp s = InfixL $ symOpP s

symOpP :: String -> Parser (UExpr -> UExpr -> UExpr)
symOpP s = opWithSrc $ do
  label "infix operator" (sym s)
  return $ binApp f
  where f = rawName SourceName $ "(" <> s <> ")"

prefixNegOp :: Operator Parser UExpr
prefixNegOp = Prefix $ label "negation" $ do
  ((), pos) <- withPos $ sym "-"
  let f = WithSrc pos $ UVar $ rawName SourceName "neg" :> ()
  return $ \case
    -- Special case: negate literals directly
    WithSrc litpos (IntLitExpr i)
      -> WithSrc (joinPos pos litpos) (IntLitExpr (-i))
    WithSrc litpos (RealLitExpr i)
      -> WithSrc (joinPos pos litpos) (RealLitExpr (-i))
    x -> mkApp f x

binApp :: Name -> SrcPos -> UExpr -> UExpr -> UExpr
binApp f pos x y = (f' `mkApp` x) `mkApp` y
  where f' = WithSrc pos $ UVar (f:>())

mkGenApp :: UArrow -> UExpr -> UExpr -> UExpr
mkGenApp arr f x = joinSrc f x $ UApp arr f x

mkApp :: UExpr -> UExpr -> UExpr
mkApp f x = joinSrc f x $ UApp (PlainArrow ()) f x

infixLinArrow :: Parser (UType -> UType -> UType)
infixLinArrow = do
  ((), pos) <- withPos $ sym "--o"
  return $ \a b -> WithSrc pos $ UPi (NoName:>a) LinArrow b

infixEffArrow :: Parser (UType -> UType -> UType)
infixEffArrow = do
  ((), pos) <- withPos $ sym "->"
  eff <- effects
  return $ \a b -> WithSrc pos $ UPi (NoName:>a) (PlainArrow eff) b

mkArrow :: Arrow -> UExpr -> UExpr -> UExpr
mkArrow arr a b = joinSrc a b $ UPi (NoName:>a) arr b

namePat :: Name -> UPat'
namePat v = PatBind (v:>())

withSrc :: Parser a -> Parser (WithSrc a)
withSrc p = do
  (x, pos) <- withPos p
  return $ WithSrc pos x

joinSrc :: WithSrc a -> WithSrc b -> c -> WithSrc c
joinSrc (WithSrc p1 _) (WithSrc p2 _) x = WithSrc (joinPos p1 p2) x

joinPos :: SrcPos -> SrcPos -> SrcPos
joinPos (l, h) (l', h') =(min l l', max h h')

indexRangeOps :: [Operator Parser UExpr]
indexRangeOps =
  [ Prefix    $ symPos ".."   <&> \pos h   -> range pos  Unlimited       (InclusiveLim h)
  , inpostfix $ symPos ".."   <&> \pos l h -> range pos (InclusiveLim l) (limFromMaybe h)
  , inpostfix $ symPos "<.."  <&> \pos l h -> range pos (ExclusiveLim l) (limFromMaybe h)
  , Prefix    $ symPos "..<"  <&> \pos h   -> range pos  Unlimited       (ExclusiveLim h)
  , InfixL    $ symPos "..<"  <&> \pos l h -> range pos (InclusiveLim l) (ExclusiveLim h)
  , InfixL    $ symPos "<..<" <&> \pos l h -> range pos (ExclusiveLim l) (ExclusiveLim h) ]
  where
    range pos l h = WithSrc pos $ UIndexRange l h
    symPos s = snd <$> withPos (sym s)

limFromMaybe :: Maybe a -> Limit a
limFromMaybe Nothing = Unlimited
limFromMaybe (Just x) = InclusiveLim x

inpostfix :: Parser (UExpr -> Maybe UExpr -> UExpr) -> Operator Parser UExpr
inpostfix = inpostfix' expr

inpostfix' :: Parser a -> Parser (a -> Maybe a -> a) -> Operator Parser a
inpostfix' p op = Postfix $ do
  f <- op
  rest <- optional p
  return $ \x -> f x rest

-- === lexemes ===

-- These `Lexer` actions must be non-overlapping and never consume input on failure
type Lexer = Parser

data KeyWord = DefKW | ForKW | RofKW | CaseKW | ReadKW | WriteKW | StateKW

textName :: Lexer Name
textName = liftM (rawName SourceName) $ label "identifier" $ lexeme $ try $ do
  w <- (:) <$> letterChar <*> many nameTailChar
  failIf (w `elem` keyWordStrs) $ show w ++ " is a reserved word"
  return w

keyWord :: KeyWord -> Lexer ()
keyWord kw = lexeme $ try $ string s >> notFollowedBy nameTailChar
  where
    s = case kw of
      DefKW  -> "def"
      ForKW  -> "for"
      RofKW  -> "rof"
      CaseKW -> "case"
      ReadKW  -> "Read"
      WriteKW -> "Accum"
      StateKW -> "State"

keyWordStrs :: [String]
keyWordStrs = ["def", "for", "rof", "case", "llam", "Read", "Write", "Accum"]

primName :: Lexer String
primName = lexeme $ try $ char '%' >> some letterChar

intLit :: Lexer Int
intLit = lexeme $ try $ L.decimal <* notFollowedBy (char '.')

doubleLit :: Lexer Double
doubleLit = lexeme $
      try L.float
  <|> try (fromIntegral <$> (L.decimal :: Parser Int) <* char '.')

-- string must only contain characters from the list `symChars`
sym :: String -> Lexer ()
sym s = lexeme $ try $ string s >> notFollowedBy symChar

symName :: Lexer Name
symName = label "symbol name" $ lexeme $ try $ do
  s <- between (char '(') (char ')') $ some symChar
  return $ rawName SourceName $ "(" <> s <> ")"

backquoteName :: Lexer Name
backquoteName = label "backquoted name" $
  lexeme $ try $ between (char '`') (char '`') textName

-- brackets and punctuation
-- (can't treat as sym because e.g. `((` is two separate lexemes)
lParen, rParen, lBracket, rBracket, lBrace, rBrace, semicolon, underscore :: Lexer ()

lParen    = notFollowedBy symName >> notFollowedBy unitCon >> charLexeme '('
rParen    = charLexeme ')'
lBracket  = charLexeme '['
rBracket  = charLexeme ']'
lBrace    = charLexeme '{'
rBrace    = charLexeme '}'
semicolon = charLexeme ';'
underscore = charLexeme '_'

charLexeme :: Char -> Parser ()
charLexeme c = void $ lexeme $ char c

nameTailChar :: Parser Char
nameTailChar = alphaNumChar <|> char '\'' <|> char '_'

symChar :: Parser Char
symChar = choice $ map char symChars

symChars :: [Char]
symChars = ".,!$^&*:-~+/=<>|?\\@"

-- === Util ===

runTheParser :: String -> Parser a -> Either (ParseErrorBundle String Void) a
runTheParser s p = parse (runReaderT p (ParseCtx 0 False False)) "" s

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

mayPair :: Parser a -> Parser a
mayPair p = local (\ctx -> ctx { canPair = True }) p

mayNotPair :: Parser a -> Parser a
mayNotPair p = local (\ctx -> ctx { canPair = False }) p

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
