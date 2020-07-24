-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module Parser (Parser, parseit, parseProg, runTheParser, parseData,
               parseTopDeclRepl, uint, withSource,
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
  (src, (level, b)) <- withSource $ withRecovery recover $ do
    level <- logLevel <|> logTime <|> return LogNothing
    b <- sourceBlock'
    return (level, b)
  return $ SourceBlock (unPos (sourceLine pos)) offset level src b Nothing

recover :: ParseError String Void -> Parser (LogLevel, SourceBlock')
recover e = do
  pos <- liftM statePosState getParserState
  reachedEOF <-  try (mayBreak sc >> eof >> return True)
             <|> return False
  consumeTillBreak
  let errmsg = errorBundlePretty (ParseErrorBundle (e :| []) pos)
  return (LogNothing, UnParseable reachedEOF errmsg)

consumeTillBreak :: Parser ()
consumeTillBreak = void $ manyTill anySingle $ eof <|> void (try (eol >> eol))

logLevel :: Parser LogLevel
logLevel = do
  void $ try $ lexeme $ char '%' >> string "passes"
  passes <- many passName
  void eol
  case passes of
    [] -> return $ LogAll
    _ -> return $ LogPasses passes

logTime :: Parser LogLevel
logTime = do
  void $ try $ lexeme $ char '%' >> string "time"
  void eol
  return PrintEvalTime

passName :: Parser PassName
passName = choice [thisNameString s $> x | (s, x) <- passNames]

passNames :: [(String, PassName)]
passNames = [(show x, x) | x <- [minBound..maxBound]]

sourceBlock' :: Parser SourceBlock'
sourceBlock' =
      proseBlock
  <|> topLevelCommand
  <|> liftM (\d -> RunModule $ UModule [d]) (topDecl <* eolf)
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
  b <- patAnn
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
    _ -> fail $ "unrecognized command: " ++ show cmdName
  e <- blockOrExpr <* eolf
  return $ case (e, cmd) of
    (WithSrc _ (UVar (v:>())), GetType) -> GetNameType (asGlobal v)
    _ -> Command cmd (exprAsModule e)

exprAsModule :: UExpr -> (Name, UModule)
exprAsModule e = (asGlobal v, UModule [d])
  where
    v = mkName "_ans_"
    d = ULet PlainLet (WithSrc (srcPos e) (UPatBinder (Bind (v:>()))), Nothing) e

-- === uexpr ===

expr :: Parser UExpr
expr = mayNotPair $ makeExprParser leafExpr ops

-- expression without exposed infix operators
leafExpr :: Parser UExpr
leafExpr =   parens (mayPair $ makeExprParser leafExpr ops)
         <|> uTabCon
         <|> uVarOcc
         <|> uHole
         <|> uLit
         <|> uPiType
         <|> uLamExpr
         <|> uForExpr
         <|> caseExpr
         <|> uCaseExpr
         <|> uPrim
         <|> unitCon
         <?> "expression"

containedExpr :: Parser UExpr
containedExpr =   parens (mayPair $ makeExprParser leafExpr ops)
              <|> uVarOcc
              <?> "contained expression"

uType :: Parser UType
uType = expr

uLit :: Parser UExpr
uLit = withSrc $ liftM (UPrimExpr . ConExpr . Lit) litVal

litVal :: Parser LitVal
litVal =   (IntLit  <$> intLit)
       <|> (RealLit <$> doubleLit)
       <?> "literal"

uVarOcc :: Parser UExpr
uVarOcc = withSrc $ try $ (UVar . (:>())) <$> (occName <* notFollowedBy (sym ":"))
  where occName = upperName <|> lowerName <|> symName

uHole :: Parser UExpr
uHole = withSrc $ underscore $> UHole

letAnnStr :: Parser LetAnn
letAnnStr =   (string "instance"   $> InstanceLet)
          <|> (string "superclass" $> SuperclassLet)

topDecl :: Parser UDecl
topDecl = dataDef <|> topLet

topLet :: Parser UDecl
topLet = do
  lAnn <- (char '@' >> letAnnStr <* (void eol <|> sc)) <|> return PlainLet
  ~(ULet _ (p, ann) rhs, pos) <- withPos decl
  let ann' = fmap (addImplicitImplicitArgs pos) ann
  return $ ULet lAnn (p, ann') rhs
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
      WithSrc pos $ UPi (Bind (v:>uTyKind)) ImplicitArrow ty
      where
        k = if v == mkName "eff" then EffectRowKind else TypeKind
        uTyKind = WithSrc pos $ UPrimExpr $ TCExpr k

dataDef :: Parser UDecl
dataDef = do
  keyWord DataKW
  tyCon <- tyConDef
  sym "="
  dataCons <- onePerLine dataConDef
  return $ UData tyCon dataCons

-- TODO: default to `Type` if unannoted
tyConDef :: Parser UConDef
tyConDef = UConDef <$> upperName <*> many annBinder

-- TODO: dependent types
dataConDef :: Parser UConDef
dataConDef = UConDef <$> upperName <*> many dataConDefBinder

dataConDefBinder :: Parser UAnnBinder
dataConDefBinder = annBinder <|> (Ignore <$> containedExpr)

decl :: Parser UDecl
decl = do
  lhs <- simpleLet <|> funDefLet
  rhs <- sym "=" >> blockOrExpr
  return $ lhs rhs

simpleLet :: Parser (UExpr -> UDecl)
simpleLet = label "let binding" $ do
  p <- try $ (letPat <|> parens pat) <* lookAhead (sym "=" <|> sym ":")
  ann <- optional $ annot uType
  return $ ULet PlainLet (p, ann)

letPat :: Parser UPat
letPat = nameAsPat $ upperName <|> lowerName <|> symName

funDefLet :: Parser (UExpr -> UDecl)
funDefLet = label "function definition" $ mayBreak $ do
  keyWord DefKW
  v <- letPat
  bs <- some arg
  (eff, ty) <- label "result type annotation" $ annot effectiveType
  let piBinders = flip map bs $ \(p, ann, arr) -> (patAsBinder p ann, arr)
  let funTy = buildPiType piBinders eff ty
  let letBinder = (v, Just funTy)
  let lamBinders = flip map bs $ \(p,_, arr) -> ((p,Nothing), arr)
  return $ \body -> ULet PlainLet letBinder (buildLam lamBinders body)
  where
    arg :: Parser (UPat, UType, UArrow)
    arg = label "def arg" $ do
      (p, ty) <-parens ((,) <$> pat <*> annot uType)
      arr <- arrow (return ()) <|> return (PlainArrow ())
      return (p, ty, arr)

patAsBinder :: UPat -> UType -> UAnnBinder
patAsBinder (WithSrc _ (UPatBinder (Bind (v:>())))) ty = Bind $ v:>ty
patAsBinder _ ty = Ignore ty

nameAsPat :: Parser Name -> Parser UPat
nameAsPat p = withSrc $ (UPatBinder . Bind . (:>())) <$> p

buildPiType :: [(UAnnBinder, UArrow)] -> EffectRow -> UType -> UType
buildPiType [] _ _ = error "shouldn't be possible"
buildPiType ((b,arr):bs) eff ty = WithSrc pos $ case bs of
  [] -> UPi b (fmap (const eff ) arr) ty
  _  -> UPi b (fmap (const Pure) arr) $ buildPiType bs eff ty
  where WithSrc pos _ = binderAnn b

effectiveType :: Parser (EffectRow, UType)
effectiveType = (,) <$> effects <*> uType

effects :: Parser EffectRow
effects = braces someEffects <|> return Pure
  where
    someEffects = do
      effs <- liftM2 (,) effectName lowerName `sepBy` sym ","
      v <- optional $ symbol "|" >> lowerName
      return $ EffectRow effs v

effectName :: Parser EffectName
effectName =     (keyWord WriteKW $> Writer)
             <|> (keyWord ReadKW  $> Reader)
             <|> (keyWord StateKW $> State)
             <?> "effect name (Accum|Read|State)"

uLamExpr :: Parser UExpr
uLamExpr = do
  sym "\\"
  bs <- some patAnn
  body <- argTerm >> blockOrExpr
  return $ buildLam (map (,PlainArrow ()) bs) body

buildLam :: [(UPatAnn, UArrow)] -> UExpr -> UExpr
buildLam binders body@(WithSrc pos _) = case binders of
  [] -> body
  -- TODO: join with source position of binders too
  (b,arr):bs -> WithSrc (joinPos pos' pos) $ ULam b arr $ buildLam bs body
     where (WithSrc pos' _, _) = b

buildFor :: SrcPos -> Direction -> [UPatAnn] -> UExpr -> UExpr
buildFor pos dir binders body = case binders of
  [] -> body
  b:bs -> WithSrc pos $ UFor dir b $ buildFor pos dir bs body

uForExpr :: Parser UExpr
uForExpr = do
  (dir, pos) <- withPos $   (keyWord ForKW $> Fwd)
                        <|> (keyWord RofKW $> Rev)
  buildFor pos dir <$> (some patAnn <* argTerm) <*> blockOrExpr

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
block = withIndent $ do
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
      where d = ULet PlainLet (WithSrc pos (UPatBinder (Ignore ())), Nothing) e
  [] -> error "Shouldn't be reachable"

uStatement :: Parser UStatement
uStatement = withPos $   liftM Left  decl
                     <|> liftM Right expr

-- TODO: put the `try` only around the `x:` not the annotation itself
uPiType :: Parser UExpr
uPiType = withSrc $ UPi <$> annBinder <*> arrow effects <*> uType

annBinder :: Parser UAnnBinder
annBinder = label "annoted binder" $ do
  v <- try $ ((Just <$> lowerName) <|> (underscore $> Nothing)) <* sym ":"
  ty <- containedExpr
  return $ case v of
    Just v' -> Bind (v':>ty)
    Nothing -> Ignore ty

arrow :: Parser eff -> Parser (ArrowP eff)
arrow p =   (sym "->"  >> liftM PlainArrow p)
        <|> (sym "=>"  $> TabArrow)
        <|> (sym "--o" $> LinArrow)
        <|> (sym "?->" $> ImplicitArrow)
        <|> (sym "?=>" $> ClassArrow)
        <?> "arrow"

caseExpr :: Parser UExpr
caseExpr = withSrc $ do
  keyWord CaseKW
  e <- expr
  keyWord OfKW
  alts <- onePerLine $ UAlt <$> pat <*> (sym "->" *> blockOrExpr)
  return $ UCase e alts

onePerLine :: Parser a -> Parser [a]
onePerLine p =   liftM (:[]) p
             <|> (withIndent $ mayNotBreak $ p `sepBy1` try nextLine)

pat :: Parser UPat
pat = makeExprParser leafPat patOps

leafPat :: Parser UPat
leafPat =
      (withSrc (symbol "()" $> UPatUnit))
  <|> parens pat <|> (withSrc $
          (UPatBinder <$>  (   (Bind <$> (:>()) <$> lowerName)
                           <|> (underscore $> Ignore ())))
      <|> (UPatLit    <$> litVal)
      <|> (UPatCon    <$> upperName <*> many pat))

-- TODO: add user-defined patterns
patOps :: [[Operator Parser UPat]]
patOps = [[InfixR $ sym "," $> \x y -> joinSrc x y $ UPatPair x y]]

uCaseExpr :: Parser UExpr
uCaseExpr = do
  ((), pos) <- withPos $ keyWord OldCaseKW
  e <- expr
  withIndent $ do
    l <- lexeme (string "Left") >> caseLam
    nextLine
    r <- lexeme (string "Right") >> caseLam
    return $ applyNamed pos "caseAnalysis" [e, l, r]

caseLam :: Parser UExpr
caseLam = do
  p <- pat
  sym "->"
  body <- blockOrExpr
  return $ WithSrc (srcPos body) $ ULam (p, Nothing) (PlainArrow ()) body

applyNamed :: SrcPos -> String -> [UExpr] -> UExpr
applyNamed pos name args = foldl mkApp f args
  where f = WithSrc pos $ UVar (Name SourceName (fromString name) 0:>())

annot :: Parser a -> Parser a
annot p = label "type annotation" $ sym ":" >> p

patAnn :: Parser UPatAnn
patAnn = label "pattern" $ (,) <$> pat <*> optional (annot containedExpr)

uPrim :: Parser UExpr
uPrim = withSrc $ do
  s <- primName
  case s of
    "ffi" -> do
      f <- lexeme $ some nameTailChar
      retTy <- baseType
      args <- some lowerName
      return $ UPrimExpr $ OpExpr $ FFICall f retTy args
    _ -> case strToName s of
      Just prim -> UPrimExpr <$> traverse (const lowerName) prim
      Nothing -> fail $ "Unrecognized primitive: " ++ s

baseType :: Parser BaseType
baseType =   (symbol "Int"  $> Scalar IntType)
         <|> (symbol "Real" $> Scalar RealType)
         <|> (symbol "Bool" $> Scalar BoolType)

-- === infix ops ===

-- literal symbols here must only use chars from `symChars`
ops :: [[Operator Parser UExpr]]
ops =
  [ [InfixL $ sym "." $> mkGenApp TabArrow, symOp "!"]
  , [InfixL $ sc $> mkApp]
  , [prefixNegOp]
  , [anySymOp] -- other ops with default fixity
  , [symOp "+", symOp "-", symOp "||", symOp "&&",
     InfixR $ sym "=>" $> mkArrow TabArrow,
     InfixL $ opWithSrc $ backquoteName >>= (return . binApp)]
  , [InfixR $ mayBreak (infixSym "$") $> mkApp]
  , [symOp "+=", symOp ":=", symOp "|", InfixR infixArrow]
  , [InfixR $ symOpP "&", pairOp]
  , indexRangeOps
  ]

opWithSrc :: Parser (SrcPos -> a -> a -> a)
          -> Parser (a -> a -> a)
opWithSrc p = do
  (f, pos) <- withPos p
  return $ f pos

pairOp :: Operator Parser UExpr
pairOp = InfixR $ opWithSrc $ do
  allowed <- asks canPair
  if allowed
    then infixSym "," >> return (binApp f)
    else fail "Unexpected comma"
  where f = mkName $ "(,)"

anySymOp :: Operator Parser UExpr
anySymOp = InfixL $ opWithSrc $ do
  s <- label "infix operator" (mayBreak anySym)
  return $ binApp $ mkSymName s

infixSym :: String -> Parser ()
infixSym s = mayBreak $ sym s

symOp :: String -> Operator Parser UExpr
symOp s = InfixL $ symOpP s

symOpP :: String -> Parser (UExpr -> UExpr -> UExpr)
symOpP s = opWithSrc $ do
  label "infix operator" (infixSym s)
  return $ binApp $ mkSymName s

mkSymName :: String -> Name
mkSymName s = mkName $ "(" <> s <> ")"

prefixNegOp :: Operator Parser UExpr
prefixNegOp = Prefix $ label "negation" $ do
  ((), pos) <- withPos $ sym "-"
  let f = WithSrc pos $ UVar $ mkName "neg" :> ()
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

infixArrow :: Parser (UType -> UType -> UType)
infixArrow = do
  notFollowedBy (sym "=>")  -- table arrows have special fixity
  (arr, pos) <- withPos $ arrow effects
  return $ \a b -> WithSrc pos $ UPi (Ignore a) arr b

mkArrow :: Arrow -> UExpr -> UExpr -> UExpr
mkArrow arr a b = joinSrc a b $ UPi (Ignore a) arr b

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

mkName :: String -> Name
mkName s = Name SourceName (fromString s) 0

-- === lexemes ===

-- These `Lexer` actions must be non-overlapping and never consume input on failure
type Lexer = Parser

data KeyWord = DefKW | ForKW | RofKW | CaseKW | OfKW
             | ReadKW | WriteKW | StateKW | OldCaseKW | DataKW | WhereKW

upperName :: Lexer Name
upperName = liftM mkName $ label "upper-case name" $ lexeme $
  checkNotKeyword $ (:) <$> upperChar <*> many nameTailChar

lowerName  :: Lexer Name
lowerName = liftM mkName $ label "lower-case name" $ lexeme $
  checkNotKeyword $ (:) <$> lowerChar <*> many nameTailChar

checkNotKeyword :: Parser String -> Parser String
checkNotKeyword p = try $ do
  s <- p
  failIf (s `elem` keyWordStrs) $ show s ++ " is a reserved word"
  return s

keyWord :: KeyWord -> Lexer ()
keyWord kw = lexeme $ try $ string s >> notFollowedBy nameTailChar
  where
    s = case kw of
      DefKW  -> "def"
      ForKW  -> "for"
      RofKW  -> "rof"
      CaseKW -> "case"
      OfKW   -> "of"
      ReadKW  -> "Read"
      WriteKW -> "Accum"
      StateKW -> "State"
      DataKW -> "data"
      WhereKW -> "where"
      OldCaseKW -> "oldcase"

keyWordStrs :: [String]
keyWordStrs = ["def", "for", "rof", "case", "of", "llam",
               "Read", "Write", "Accum", "oldcase", "data", "where"]

primName :: Lexer String
primName = lexeme $ try $ char '%' >> some alphaNumChar

intLit :: Lexer Int
intLit = lexeme $ try $ L.decimal <* notFollowedBy (char '.')

doubleLit :: Lexer Double
doubleLit = lexeme $
      try L.float
  <|> try (fromIntegral <$> (L.decimal :: Parser Int) <* char '.')

knownSymStrs :: [String]
knownSymStrs = [".", ":", "!", "=", "-", "+", "||", "&&", "$", "&", ",", "+=", ":=",
                "->", "=>", "?->", "?=>", "--o", "--",
                "..", "<..", "..<", "..<", "<..<"]

-- string must be in `knownSymStrs`
sym :: String -> Lexer ()
sym s = lexeme $ try $ string s >> notFollowedBy symChar

anySym :: Lexer String
anySym = lexeme $ try $ do
  s <- some symChar
  -- TODO: consider something faster than linear search here
  failIf (s `elem` knownSymStrs) ""
  return s

symName :: Lexer Name
symName = label "symbol name" $ lexeme $ try $ do
  s <- between (char '(') (char ')') $ some symChar
  return $ mkName $ "(" <> s <> ")"

backquoteName :: Lexer Name
backquoteName = label "backquoted name" $
  lexeme $ try $ between (char '`') (char '`') (upperName <|> lowerName)

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
outputLines = void $ many (symbol ">" >> takeWhileP Nothing (/= '\n') >> ((eol >> return ()) <|> eof))

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

thisNameString :: String -> Parser ()
thisNameString s = lexeme $ try $ string s >> notFollowedBy alphaNumChar

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

withIndent :: Parser a -> Parser a
withIndent p = do
  nextLine
  indent <- liftM length $ some (char ' ')
  local (\ctx -> ctx { curIndent = curIndent ctx + indent }) $ p

eolf :: Parser ()
eolf = void eol <|> eof

failIf :: Bool -> String -> Parser ()
failIf True s = fail s
failIf False _ = return ()
