-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE OverloadedStrings #-}

module Parser (Parser, parseit, parseProg, parseData, runTheParser,
               parseTopDeclRepl, parseTopDecl, uint, withSource,
               emptyLines, brackets, tauType, symbol) where

import Control.Monad
import Control.Monad.Combinators.Expr
import Control.Monad.Reader
import Text.Megaparsec hiding (Label, State)
import Text.Megaparsec.Char hiding (space)
import Data.Functor
import Data.Foldable (fold)
import Data.List.NonEmpty (NonEmpty (..))
import Data.Void
import qualified Text.Megaparsec.Char.Lexer as L

import Env
import Record
import Syntax
import PPrint
import Type

data ParseCtx = ParseCtx { curIndent :: Int
                         , canBreak  :: Bool }
type Parser = ReaderT ParseCtx (Parsec Void String)

parseProg :: String -> [SourceBlock]
parseProg s = mustParseit s $ manyTill (sourceBlock <* outputLines) eof

parseData :: String -> Except FExpr
parseData s = parseit s literalData

parseTopDeclRepl :: String -> Maybe SourceBlock
parseTopDeclRepl s = case sbContents b of
  UnParseable True _ -> Nothing
  _ -> Just b
  where b = mustParseit s sourceBlock

parseTopDecl :: String -> Except FDecl
parseTopDecl s = parseit s topDecl

parseit :: String -> Parser a -> Except a
parseit s p = case runTheParser s (p <* (optional eol >> eof)) of
  Left e -> throw ParseErr (errorBundlePretty e)
  Right x -> return x

mustParseit :: String -> Parser a -> a
mustParseit s p  = case parseit s p of
  Right ans -> ans
  Left e -> error $ "This shouldn't happen:\n" ++ pprint e

topDecl :: Parser FDecl
topDecl = ( ruleDef
        <|> typeDef
        <|> letMono
        <|> letPoly
        <?> "top-level declaration" ) <* (void eol <|> eof)

includeSourceFile :: Parser String
includeSourceFile = symbol "include" >> stringLiteral <* eol

sourceBlock :: Parser SourceBlock
sourceBlock = do
  offset <- getOffset
  pos <- getSourcePos
  (src, b) <- withSource $ withRecovery recover $ sourceBlock'
  return $ SourceBlock (unPos (sourceLine pos)) offset src b

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
  <|> (liftM (RunModule . declAsModule) topDecl)
  <|> liftM (Command (EvalExpr Printed) . exprAsModule) (expr <* eol)

loadData :: Parser SourceBlock'
loadData = do
  symbol "load"
  fmt <- dataFormat
  s <- stringLiteral
  symbol "as"
  p <- pat
  void eol
  return $ LoadData p fmt s

dataFormat :: Parser DataFormat
dataFormat = do
  s <- identifier
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
  cmdName <- char ':' >> identifier
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
  return $ case (cmd, e) of
    (GetType, SrcAnnot (FVar v) _) -> GetNameType v
    _ -> Command cmd (exprAsModule e)

ruleDef :: Parser FDecl
ruleDef = do
  v <- try $ lowerName <* symbol "#"
  symbol s
  symbol ":"
  (ty, tlam) <- letPolyTail $ pprint v ++ "#" ++ s
  return $ FRuleDef (LinearizationDef v) ty tlam
  where s = "lin"

typeDef :: Parser FDecl
typeDef = do
  symbol "type"
  v <- typeVar
  tvs <- many localTypeVar
  equalSign
  ty <- tauType
  let ty' = case tvs of
              [] -> ty
              _  -> TypeAlias tvs ty
  return $ TyDef v ty'

-- === Parsing decls ===

letPoly :: Parser FDecl
letPoly = do
  v <- try $ lowerName <* symbol ":"
  (ty, tlam) <- letPolyTail (pprint v)
  return $ letPolyToMono (LetPoly (v:>ty) tlam)

letPolyTail :: String -> Parser (Type, FTLam)
letPolyTail s = do
  ~(Forall tbs qs ty) <- mayNotBreak $ sigmaType
  nextLine
  symbol s
  wrap <- idxLhsArgs <|> lamLhsArgs
  equalSign
  rhs <- liftM wrap blockOrExpr
  return (Forall tbs qs ty, FTLam tbs qs rhs)

letPolyToMono :: FDecl -> FDecl
letPolyToMono d = case d of
  LetPoly (v:> Forall [] _ ty) (FTLam [] _ rhs) -> LetMono (RecLeaf $ v:> ty) rhs
  _ -> d

letMono :: Parser FDecl
letMono = do
  (p, wrap) <- try $ do p <- pat
                        wrap <- idxLhsArgs <|> lamLhsArgs
                        equalSign
                        return (p, wrap)
  body <- blockOrExpr
  return $ LetMono p (wrap body)

-- === Parsing expressions ===

type Statement = Either FDecl FExpr

blockOrExpr :: Parser FExpr
blockOrExpr = block <|> expr

block :: Parser FExpr
block = do
  nextLine
  indent <- liftM length $ some (char ' ')
  withIndent indent $ do
    statements <- mayNotBreak $ statement `sepBy1` (symbol ";" <|> try nextLine)
    case last statements of
      Left _ -> fail "Last statement in a block must be an expression."
      _      -> return $ wrapStatements statements

wrapStatements :: [Statement] -> FExpr
wrapStatements statements = case statements of
  [Right e] -> e
  s:rest -> FDecl s' (wrapStatements rest)
    where s' = case s of
                 Left  d -> d
                 Right e -> LetMono (RecLeaf (NoName:>NoAnn)) e
  [] -> error "Shouldn't be reachable"

statement :: Parser Statement
statement =   liftM Left (letMono <|> letPoly)
          <|> liftM Right expr
          <?> "decl or expr"

expr :: Parser FExpr
expr = makeExprParser (withSourceAnn expr') ops

expr' :: Parser FExpr
expr' =   parenExpr
      <|> var
      <|> liftM fPrimCon idxLit
      <|> liftM (fPrimCon . Lit) literal
      <|> lamExpr
      <|> forExpr
      <|> primExpr
      <|> ffiCall
      <|> tabCon
      <?> "expr"

parenExpr :: Parser FExpr
parenExpr = do
  e <- parens $ block <|> productCon
  ann <- typeAnnot
  return $ case ann of NoAnn -> e
                       ty    -> Annot e ty

productCon :: Parser FExpr
productCon = do
  ans <- prod expr
  return $ case ans of
    Left x -> x
    Right xs -> fPrimCon $ RecCon (Tup xs)

prod :: Parser a -> Parser (Either a [a])
prod p = prod1 p <|> return (Right [])

prod1 :: Parser a -> Parser (Either a [a])
prod1 p = do
  x <- p
  sep <- optional comma
  case sep of
    Nothing -> return $ Left x
    Just () -> do
      xs <- p `sepEndBy` comma
      return $ Right (x:xs)

var :: Parser FExpr
var = do
  v <- lowerName
  tyArgs <- many tyArg
  return $ case tyArgs of
    [] -> FVar (v:>NoAnn)
    _  -> FPrimExpr $ OpExpr $ TApp (FVar (v:>NoAnn)) tyArgs

tyArg :: Parser Type
tyArg = symbol "@" >> tauTypeAtomic

withSourceAnn :: Parser FExpr -> Parser FExpr
withSourceAnn p = liftM (uncurry SrcAnnot) (withPos p)

typeAnnot :: Parser Type
typeAnnot = do
  ann <- optional $ symbol ":" >> tauTypeAtomic
  return $ case ann of
    Nothing -> NoAnn
    Just ty -> ty

primExpr :: Parser FExpr
primExpr = do
  s <- try $ symbol "%" >> identifier
  prim <- case strToName s of
    Just prim -> return prim
    Nothing -> fail $ "Unexpected builtin: " ++ s
  liftM FPrimExpr $ parens $ traverseExpr prim
      (const $ (tyArg <|> return NoAnn) <* optional comma)
      (const $ expr       <* optional comma)
      (const $ rawLamExpr <* optional comma)

ffiCall :: Parser FExpr
ffiCall = do
  symbol "%%"
  s <- identifier
  args <- parens $ expr `sepBy` comma
  return $ fPrimOp $ FFICall s (map (const NoAnn) args) NoAnn args

rawLamExpr :: Parser FLamExpr
rawLamExpr = do
  symbol "\\"
  p <- pat
  argTerm
  body <- blockOrExpr
  return $ FLamExpr p body

-- TODO: combine lamExpr/linlamExpr/forExpr
lamExpr :: Parser FExpr
lamExpr = do
  ann <-    NoAnn <$ symbol "\\"
        <|> Lin   <$ symbol "llam"
  ps <- pat `sepBy` sc
  argTerm
  body <- blockOrExpr
  return $ foldr (fLam ann) body ps

forExpr :: Parser FExpr
forExpr = do
  symbol "for"
  vs <- pat `sepBy` sc
  argTerm
  body <- blockOrExpr
  return $ foldr fFor body vs

tabCon :: Parser FExpr
tabCon = do
  xs <- brackets $ (expr `sepEndBy` comma)
  n <- tyArg <|> return (FixedIntRange 0 (length xs))
  return $ fPrimOp $ TabCon n NoAnn xs

idxLhsArgs :: Parser (FExpr -> FExpr)
idxLhsArgs = do
  period
  args <- pat `sepBy` period
  return $ \body -> foldr fFor body args

lamLhsArgs :: Parser (FExpr -> FExpr)
lamLhsArgs = do
  args <- pat `sepBy` sc
  return $ \body -> foldr (fLam NoAnn) body args

idxLit :: Parser (PrimCon Type FExpr FLamExpr)
idxLit = do
  i <- try $ uint <* symbol "@"
  n <- uint
  failIf (i < 0 || i >= n) $ "Index out of bounds: "
                                ++ pprint i ++ " of " ++ pprint n
  return $ AsIdx (FixedIntRange 0 n)
                 (FPrimExpr $ ConExpr $ Lit $ IntLit i)

literal :: Parser LitVal
literal =     numLit
          <|> liftM StrLit stringLiteral
          <|> (symbol "True"  >> return (BoolLit True))
          <|> (symbol "False" >> return (BoolLit False))

numLit :: Parser LitVal
numLit = do
  x <- num
  return $ case x of Left  r -> RealLit r
                     Right i -> IntLit  i

identifier :: Parser String
identifier = lexeme . try $ do
  w <- (:) <$> lowerChar <*> many (alphaNumChar <|> char '\'')
  failIf (w `elem` resNames) $ show w ++ " is a reserved word"
  return w
  where resNames = ["for", "llam"]

appRule :: Operator Parser FExpr
appRule = InfixL (sc *> notFollowedBy (choice . map symbol $ opNames)
                     >> return (\x y -> fPrimOp $ App NoAnn x y))
  where
    opNames = [ ".", "+", "*", "/", "- ", "^", "$", "@"
              , "<", ">", "<=", ">=", "&&", "||", "=="]

scalarBinOpRule :: String -> ScalarBinOp -> Operator Parser FExpr
scalarBinOpRule opchar op = binOpRule opchar f
  where f x y = FPrimExpr $ OpExpr $ ScalarBinOp op x y

cmpRule :: String -> CmpOp -> Operator Parser FExpr
cmpRule opchar op = binOpRule opchar f
  where f x y = FPrimExpr $ OpExpr $ Cmp op NoAnn x y

binOpRule :: String -> (FExpr -> FExpr -> FExpr) -> Operator Parser FExpr
binOpRule opchar f = InfixL $ do
  ((), pos) <- (withPos $ mayBreak $ symbol opchar) <* (optional eol >> sc)
  return $ \e1 e2 -> SrcAnnot (f e1 e2) pos

backtickRule :: Operator Parser FExpr
backtickRule = InfixL $ do
  void $ char '`'
  v <- rawVar
  char '`' >> sc
  return $ \x y -> (v `app` x) `app ` y

ops :: [[Operator Parser FExpr]]
ops = [ [binOpRule "." (\x i -> FPrimExpr $ OpExpr $ TabGet x i)]
      , [appRule]
      , [scalarBinOpRule "^" Pow]
      , [scalarBinOpRule "*" FMul, scalarBinOpRule "/" FDiv]
      -- trailing space after "-" to distinguish from negation
      , [scalarBinOpRule "+" FAdd, scalarBinOpRule "- " FSub]
      , [cmpRule "==" Equal, cmpRule "<=" LessEqual, cmpRule ">=" GreaterEqual,
         cmpRule "<" Less, cmpRule ">" Greater]
      , [scalarBinOpRule "&&" And, scalarBinOpRule "||" Or]
      , [backtickRule]
      , [InfixR (mayBreak (symbol "$") >> return (\x y -> app x y))]
       ]

rawVar :: Parser FExpr
rawVar = do
  v <- lowerName
  return $ FVar (v:>NoAnn)

binder :: Parser Var
binder = (symbol "_" >> return (NoName :> NoAnn))
     <|> liftM2 (:>) lowerName typeAnnot

pat :: Parser Pat
pat =   parenPat
    <|> liftM RecLeaf binder

parenPat :: Parser Pat
parenPat = do
  ans <- parens $ prod pat
  return $ case ans of
    Left  x  -> x
    Right xs -> RecTree $ Tup xs

lowerName :: Parser Name
lowerName = name SourceName identifier

upperStr :: Parser String
upperStr = lexeme . try $ (:) <$> upperChar <*> many alphaNumChar

name :: NameSpace -> Parser String -> Parser Name
name ns p = liftM (rawName ns) p

equalSign :: Parser ()
equalSign = try $ symbol "=" >> notFollowedBy (symbol ">" <|> symbol "=")

argTerm :: Parser ()
argTerm = mayNotBreak $ symbol "."

fLam :: Type -> Pat -> FExpr -> FExpr
fLam l p body = fPrimCon $ Lam l NoAnn $ FLamExpr p body

fFor :: Pat -> FExpr -> FExpr
fFor p body = fPrimOp $ For $ FLamExpr p body

fPrimCon :: PrimCon Type FExpr FLamExpr -> FExpr
fPrimCon con = FPrimExpr $ ConExpr con

fPrimOp :: PrimOp Type FExpr FLamExpr -> FExpr
fPrimOp op = FPrimExpr $ OpExpr op

app :: FExpr -> FExpr -> FExpr
app f x = fPrimOp $ App NoAnn f x

-- === Parsing types ===

sigmaType :: Parser Type
sigmaType = explicitSigmaType <|> implicitSigmaType

explicitSigmaType :: Parser Type
explicitSigmaType = do
  symbol "A"
  tbs <- many typeBinder
  qs <- (symbol "|" >> qual `sepBy` comma) <|> return []
  mayBreak period
  ty <- tauType
  return $ Forall tbs qs ty

implicitSigmaType :: Parser Type
implicitSigmaType = do
  ty <- tauType
  let tbs =  [v:>NoKindAnn | v <- envNames (freeVars ty)
                           , nameSpace v == LocalTVName]
  return $ Forall tbs [] ty

typeBinder :: Parser TVar
typeBinder = do
  (v:>_) <- typeVar <|> localTypeVar
  k <-  (symbol ":" >> kindName)
    <|> return NoKindAnn
  return $ v :> k

kindName :: Parser Kind
kindName =   (symbol "Ty"     >> return TyKind)
         <|> (symbol "Mult"   >> return MultKind)
         <|> (symbol "Effect" >> return EffectKind)
         <?> "kind"

qual :: Parser TyQual
qual = do
  c <- className
  v <- typeVar <|> localTypeVar
  return $ TyQual v c

className :: Parser ClassName
className = do
  s <- upperStr
  case s of
    "Data" -> return Data
    "VS"   -> return VSpace
    "Ix"   -> return IdxSet
    _ -> fail $ "Unrecognized class constraint: " ++ s

-- addClassVars :: ClassName -> [Name] -> TVar -> TVar
-- addClassVars c vs ~b@(v:>(TyKind cs))
--   | v `elem` vs && not (c `elem` cs) = v:>(TyKind (c:cs))
--   | otherwise = b

tauTypeAtomic :: Parser Type
tauTypeAtomic =   parenTy
              <|> liftM (ArrowType NonLin) piType
              <|> liftM Ref (symbol "Ref" >> tauTypeAtomic)
              <|> typeName
              <|> intRangeType
              <|> indexRangeType
              <|> liftM TypeVar typeVar
              <|> liftM TypeVar localTypeVar
              <|> idxSetLit
              <?> "type"

tauType :: Parser Type
tauType = makeExprParser (sc >> tauTypeAtomic) typeOps
  where
    typeOps = [ [tyAppRule]
              , [InfixR (TabType <$ symbol "=>")]
              , [InfixR arrowType] ]

intRangeType :: Parser Type
intRangeType = do
  low <- try $ do
    low <- atom
    symbol "...<"
    return low
  high <- atom
  return $ IntRange low high

indexRangeType :: Parser Type
indexRangeType = do
  -- TODO: We need `try` because `.` is overloaded.
  --       Consider requiring parens or using `->` in for/lambda.
  low  <- try $ lowerLim <* char '.'
  high <- upperLim
  sc
  when ((low, high) == (Unlimited, Unlimited)) $
    fail "Index range must be provided with at least one bound"
  return $ IndexRange NoAnn low high

lowerLim :: Parser (Limit Atom)
lowerLim =   (                      char '.' $> Unlimited)
         <|> (atom >>= \lim -> (   (char '.' $> InclusiveLim lim)
                               <|> (char '<' $> ExclusiveLim lim)))

upperLim :: Parser (Limit Atom)
upperLim =   (char '.' >> (   liftM  InclusiveLim atom
                          <|> return Unlimited))
         <|> (char '<' >>     liftM  ExclusiveLim atom)

atom :: Parser Atom
atom = do
  e <- expr'
  case fromAtomicFExpr e of
    Nothing -> fail "Expected a fully-reduced expression"
    Just x -> return x

arrowType :: Parser (Type -> Type -> Type)
arrowType = do
  lin <-  NonLin <$ symbol "->"
      <|> Lin    <$ symbol "--o"
  eff <- effectType <|> return noEffect
  return $ \a b -> ArrowType lin $ Pi a (eff, b)

piType :: Parser PiType
piType = do
  v <- try $ lowerName <* symbol ":"
  a <- tauTypeAtomic
  symbol "->"
  eff <- effectType <|> return noEffect
  b <- tauType
  return $ makePi (v:>a) (eff, b)

effectRow :: Parser (EffectRow Type)
effectRow = do
  e <- effectName
  v <- lowerName
  return $ (v:>()) @> (e, NoAnn)

effectName :: Parser EffectName
effectName =
      (symbol "Reader" >> return Reader)
  <|> (symbol "Writer" >> return Writer)
  <|> (symbol "State"  >> return State )

-- TODO: linearity
effectType :: Parser Effect
effectType =  bracketed "{" "}" $ do
  effects <- effectRow `sepBy` comma
  tailVar <- optional $ do
               symbol "|"
               localTypeVar
  return $ Effect (fold effects) (fmap TypeVar tailVar)

tyAppRule :: Operator Parser Type
tyAppRule = InfixL (sc *> notFollowedBy (choice . map symbol $ tyOpNames)
                    >> return applyType)
  where tyOpNames = ["=>", "->", "--o"]

applyType :: Type -> Type -> Type
applyType (TypeApp ty args) arg = TypeApp ty (args ++ [arg])
applyType ty arg = TypeApp ty [arg]

typeVar :: Parser TVar
typeVar = do
  v <- name SourceTypeName upperStr
  return (v:> NoKindAnn)

localTypeVar :: Parser TVar
localTypeVar = do
  v <- name LocalTVName identifier
  return (v:> NoKindAnn)

idxSetLit :: Parser Type
idxSetLit = do
  n <- uint
  return $ FixedIntRange 0 n

parenTy :: Parser Type
parenTy = do
  ans <- parens $ prod tauType
  return $ case ans of
    Left ty  -> ty
    Right xs -> RecType $ Tup xs

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

-- === Parsing literal data ===

-- TODO: parse directly to an atom instead

literalData :: Parser FExpr
literalData =   liftM (FPrimExpr . ConExpr) idxLit
            <|> liftM (FPrimExpr . ConExpr . Lit) literal
            <|> tupleData
            <|> tableData

tupleData :: Parser FExpr
tupleData = do
  xs <- parens $ literalData `sepEndBy` comma
  return $ FPrimExpr $ ConExpr $ RecCon $ Tup xs

tableData :: Parser FExpr
tableData = do
  xs <- brackets $ literalData `sepEndBy` comma
  n <- tyArg <|> return (FixedIntRange 0 (length xs))
  return $ FPrimExpr $ OpExpr $ TabCon n NoAnn xs

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

num :: Parser (Either Double Int)
num =    liftM Left (try (L.signed (return ()) L.float) <* sc)
     <|> (do x <- L.signed (return ()) L.decimal
             trailingPeriod <- optional $ try $ char '.' >> notFollowedBy (char '.')
             sc
             return $ case trailingPeriod of
               Just _  -> Left (fromIntegral x)
               Nothing -> Right x)

uint :: Parser Int
uint = L.decimal <* sc

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: String -> Parser ()
symbol s = void $ L.symbol sc s

bracketed :: String -> String -> Parser a -> Parser a
bracketed left right p = between (symbol left) (symbol right) $ mayBreak p

parens :: Parser a -> Parser a
parens p = bracketed "(" ")" p

brackets :: Parser a -> Parser a
brackets p = bracketed "[" "]" p

withPos :: Parser a -> Parser (a, (Int, Int))
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
