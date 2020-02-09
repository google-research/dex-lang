-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE OverloadedStrings #-}

module Parser (parseit, parseProg, parseData, parseTopDeclRepl, parseTopDecl,
              tauType) where

import Control.Monad
import Control.Monad.Combinators.Expr
import Data.String
import Text.Megaparsec
import Text.Megaparsec.Char
import Data.Char (isLower)
import Data.Maybe (fromMaybe)
import Data.List.NonEmpty (NonEmpty (..))
import Data.Void

import Env
import Record
import ParseUtil
import Syntax
import Fresh
import Type
import PPrint

parseProg :: String -> [SourceBlock]
parseProg s = mustParseit s $ manyTill (sourceBlock <* outputLines) eof

parseData :: String -> Except FExpr
parseData s = parseit s literalData

parseTopDeclRepl :: String -> Maybe SourceBlock
parseTopDeclRepl s = case sbContents block of
  UnParseable True _ -> Nothing
  _ -> Just block
  where block = mustParseit s sourceBlock

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
        <|> (topDeclAnn >> decl)  -- TODO: bring back annotation
        <?> "top-level declaration" ) <* (void eol <|> eof)

includeSourceFile :: Parser String
includeSourceFile = symbol "include" >> stringLiteral <* eol

sourceBlock :: Parser SourceBlock
sourceBlock = do
  offset <- getOffset
  pos <- getSourcePos
  (source, block) <- withSource $ withRecovery recover $ sourceBlock'
  return $ SourceBlock (unPos (sourceLine pos)) offset source block

recover :: ParseError String Void -> Parser SourceBlock'
recover e = do
  pos <- liftM statePosState getParserState
  reachedEOF <- (eof >> return True) <|> return False
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
  e <- declOrExpr
  void eol
  return $ Command (Dump fmt s) (exprAsModule e)

explicitCommand :: Parser SourceBlock'
explicitCommand = do
  cmdName <- char ':' >> identifier <* (optional eol >> sc)
  cmd <- case cmdName of
    "p"       -> return $ EvalExpr Printed
    "t"       -> return $ GetType
    "plot"    -> return $ EvalExpr Scatter
    "plotmat" -> return $ EvalExpr Heatmap
    "time"    -> return $ TimeIt
    "flops"   -> return $ Flops
    "passes"  -> return $ ShowPasses
    "pass"    -> liftM ShowPass $ identifier <* (optional eol >> sc)
    _ -> fail $ "unrecognized command: " ++ show cmdName
  e <- declOrExpr <*eol
  return $ Command cmd (exprAsModule e)

topDeclAnn :: Parser DeclAnn
topDeclAnn =   (symbol "@primitive" >> declSep >> return ADPrimitive)
           <|> return PlainDecl

ruleDef :: Parser FDecl
ruleDef = do
  v <- try $ lowerName <* symbol "#"
  symbol s
  symbol "::"
  (ty, tlam) <- letPolyTail $ pprint v ++ "#" ++ s
  return $ FRuleDef (LinearizationDef v) ty tlam
  where s = "lin"

typeDef :: Parser FDecl
typeDef = do
  symbol "type"
  v <- upperName
  bs <- many lowerName
  equalSign
  ty <- tauType
  let ty' = case bs of
              [] -> ty
              _  -> TypeAlias (map varAnn tvs) (abstractTVs tvs ty)
                      where tvs = map asTVar bs
  return $ TyDef (asTVar v) ty'

-- === Parsing decls ===

decl :: Parser FDecl
decl = letMono <|> letPoly

declSep :: Parser ()
declSep = void $ some $ (eol >> sc) <|> symbol ";"

asTVar :: Name -> TVar
asTVar v = v :> Kind []

letPoly :: Parser FDecl
letPoly = do
  v <- try $ lowerName <* symbol "::"
  (ty, tlam) <- letPolyTail (pprint v)
  return $ letPolyToMono (LetPoly (v:>ty) tlam)

letPolyTail :: String -> Parser (Type, FTLam)
letPolyTail s = do
  (tbs, ty) <- mayNotBreak $ sigmaType
  declSep
  symbol s
  wrap <- idxLhsArgs <|> lamLhsArgs
  equalSign
  rhs <- liftM wrap declOrExpr
  return (Forall (map varAnn tbs) (abstractTVs tbs ty), FTLam tbs rhs)

letPolyToMono :: FDecl -> FDecl
letPolyToMono d = case d of
  LetPoly (v:> Forall [] ty) (FTLam [] rhs) -> LetMono (RecLeaf $ v:> ty) rhs
  _ -> d

letMono :: Parser FDecl
letMono = do
  (p, wrap) <- try $ do p <- pat
                        wrap <- idxLhsArgs <|> lamLhsArgs
                        equalSign
                        return (p, wrap)
  body <- declOrExpr
  return $ LetMono p (wrap body)

-- === Parsing expressions ===

expr :: Parser FExpr
expr = makeExprParser (withSourceAnn term) ops

term :: Parser FExpr
term =   parenExpr
     <|> var
     <|> liftM fPrimCon idxLit
     <|> liftM (fPrimCon . Lit) literal
     <|> lamExpr
     <|> forExpr
     <|> primExpr
     <|> ffiCall
     <|> tabCon
     <?> "term"

declOrExpr :: Parser FExpr
declOrExpr =   declExpr
           <|> doExpr
           <|> expr <?> "decl or expr"

parenExpr :: Parser FExpr
parenExpr = do
  e <- parens $ declExpr <|> productCon
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
  return $ FVar (v:>NoAnn) tyArgs

tyArg :: Parser Type
tyArg = symbol "@" >> tauTypeAtomic

declExpr :: Parser FExpr
declExpr = liftM2 FDecl (mayNotBreak decl <* declSep) declOrExpr

doExpr :: Parser FExpr
doExpr = do
  (p, bound) <- mayNotBreak doBind <* declSep
  body <- declOrExpr
  return $ fPrimCon $ Bind bound (FLamExpr p body)

doBind :: Parser (Pat, FExpr)
doBind = do
  p <- try $ pat <* symbol "<-"
  body <- expr
  return (p, body)

withSourceAnn :: Parser FExpr -> Parser FExpr
withSourceAnn p = liftM (uncurry SrcAnnot) (withPos p)

typeAnnot :: Parser Type
typeAnnot = do
  ann <- optional $ symbol "::" >> tauTypeAtomic
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
  symbol "lam"
  p <- pat
  argTerm
  body <- declOrExpr
  return $ FLamExpr p body

-- TODO: combine lamExpr/linlamExpr/forExpr
lamExpr :: Parser FExpr
lamExpr = do
  symbol "lam"
  ps <- pat `sepBy` sc
  argTerm
  body <- declOrExpr
  return $ foldr fLam body ps

forExpr :: Parser FExpr
forExpr = do
  symbol "for"
  vs <- pat `sepBy` sc
  argTerm
  body <- declOrExpr
  return $ foldr fFor body vs

tabCon :: Parser FExpr
tabCon = do
  xs <- brackets $ (expr `sepEndBy` comma)
  return $ fPrimOp $ TabCon NoAnn NoAnn xs

idxLhsArgs :: Parser (FExpr -> FExpr)
idxLhsArgs = do
  period
  args <- pat `sepBy` period
  return $ \body -> foldr fFor body args

lamLhsArgs :: Parser (FExpr -> FExpr)
lamLhsArgs = do
  args <- pat `sepBy` sc
  return $ \body -> foldr fLam body args

idxLit :: Parser (PrimCon Type FExpr FLamExpr)
idxLit = do
  i <- try $ uint <* symbol "@"
  n <- uint
  failIf (i < 0 || i >= n) $ "Index out of bounds: "
                                ++ pprint i ++ " of " ++ pprint n
  return $ AsIdx n (FPrimExpr $ PrimConExpr $ Lit $ IntLit i)

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
  where resNames = ["for", "lam"]

appRule :: Operator Parser FExpr
appRule = InfixL (sc *> notFollowedBy (choice . map symbol $ opNames)
                     >> return (\x y -> fPrimOp $ App x y))
  where
    opNames = ["+", "*", "/", "- ", "^", "$", "@", "<", ">", "<=", ">=", "&&", "||", "=="]

postFixRule :: Operator Parser FExpr
postFixRule = Postfix $ do
  trailers <- some (period >> idxExpr)
  return $ \e -> foldl (\x i -> fPrimCon $ TabGet x i) e trailers

scalarBinOpRule :: String -> ScalarBinOp -> Operator Parser FExpr
scalarBinOpRule opchar op = binOpRule opchar f
  where f x y = FPrimExpr $ PrimOpExpr $ ScalarBinOp op x y

cmpRule :: String -> CmpOp -> Operator Parser FExpr
cmpRule opchar op = binOpRule opchar f
  where f x y = FPrimExpr $ PrimOpExpr $ Cmp op NoAnn x y

binOpRule :: String -> (FExpr -> FExpr -> FExpr) -> Operator Parser FExpr
binOpRule opchar f = InfixL $ do
  ((), pos) <- (withPos $ symbol opchar) <* (optional eol >> sc)
  return $ \e1 e2 -> SrcAnnot (f e1 e2) pos

backtickRule :: Operator Parser FExpr
backtickRule = InfixL $ do
  void $ char '`'
  v <- rawVar
  char '`' >> sc
  return $ \x y -> (v `app` x) `app ` y

ops :: [[Operator Parser FExpr]]
ops = [ [postFixRule, appRule]
      , [scalarBinOpRule "^" Pow]
      , [scalarBinOpRule "*" FMul, scalarBinOpRule "/" FDiv]
      -- -- trailing space after "-" to distinguish from negation
      , [scalarBinOpRule "+" FAdd, scalarBinOpRule "- " FSub]
      , [cmpRule "==" Equal, cmpRule "<=" LessEqual, cmpRule ">=" GreaterEqual,
         -- These "<" and ">" must come after "<=" and ">=" or parser will see ("<","=")
         cmpRule "<" Less, cmpRule ">" Greater
        ]
      , [scalarBinOpRule "&&" And, scalarBinOpRule "||" Or]
      , [backtickRule]
      , [InfixR (symbol "$" >> optional eol >> sc >> return (\x y -> app x y))]
       ]

idxExpr :: Parser FExpr
idxExpr = withSourceAnn $ rawVar <|> parens productCon

rawVar :: Parser FExpr
rawVar = do
  v <- lowerName
  return $ FVar (v:>NoAnn) []

binder :: Parser Var
binder = (symbol "_" >> return ("_" :> NoAnn))
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

intQualifier :: Parser Int
intQualifier = do
  n <- optional $ symbol "_" >> uint
  return $ fromMaybe 0 n

lowerName :: Parser Name
lowerName = name identifier

upperName :: Parser Name
upperName = name upperStr

upperStr :: Parser String
upperStr = lexeme . try $ (:) <$> upperChar <*> many alphaNumChar

name :: Parser String -> Parser Name
name p = do
  s <- p
  n <- intQualifier
  return $ Name (fromString s) n

equalSign :: Parser ()
equalSign = do
  try $ symbol "=" >> notFollowedBy (symbol ">" <|> symbol "=")
  optional eol >> sc

argTerm :: Parser ()
argTerm = symbol "." >> optional eol >> sc

fLam :: Pat -> FExpr -> FExpr
fLam p body = fPrimCon $ Lam NoAnn $ FLamExpr p body

fFor :: Pat -> FExpr -> FExpr
fFor p body = fPrimOp $ For $ FLamExpr p body

fPrimCon :: PrimCon Type FExpr FLamExpr -> FExpr
fPrimCon con = FPrimExpr $ PrimConExpr con

fPrimOp :: PrimOp Type FExpr FLamExpr -> FExpr
fPrimOp op = FPrimExpr $ PrimOpExpr op

app :: FExpr -> FExpr -> FExpr
app f x = fPrimOp $ App f x

-- === Parsing types ===

sigmaType :: Parser ([TVar], Type)
sigmaType = do
  maybeTbs <- optional $ do
    symbol "A"
    tBs <- many typeBinder
    period
    return tBs
  ty <- tauType
  let tbs = case maybeTbs of
              Nothing -> map (:> Kind []) vs
                -- TODO: lexcial order!
                where vs = filter nameIsLower $ envNames (freeVars ty)
              Just tbs' -> tbs'
  let tbs' = map (  addClassVars Data   (dataVars   ty)
                  . addClassVars IdxSet (idxSetVars ty)) tbs
  return (tbs', ty)
  where
    nameIsLower v = isLower (tagToStr (nameTag v) !! 0)

typeBinder :: Parser TVar
typeBinder = do
  ~(TypeVar (v:>_)) <- typeVar
  cs <-   (symbol "::" >> (    liftM (:[]) className
                           <|> parens (className `sepBy` comma)))
      <|> return []
  return (v:>Kind cs)

className :: Parser ClassName
className = do
  s <- upperStr
  case s of
    "Data" -> return Data
    "VS"   -> return VSpace
    "Ix"   -> return IdxSet
    _ -> fail $ "Unrecognized class constraint: " ++ s

addClassVars :: ClassName -> [Name] -> TVar -> TVar
addClassVars c vs b@(v:>(Kind cs))
  | v `elem` vs && not (c `elem` cs) = v:>(Kind (c:cs))
  | otherwise = b

idxSetVars :: Type -> [Name]
idxSetVars ty = case ty of
  ArrType _ a b -> recur a <> recur b
  TabType a b   -> envNames (freeVars a) <> recur b
  RecType r     -> foldMap recur r
  _             -> []
  where recur = idxSetVars

dataVars :: Type -> [Name]
dataVars ty = case ty of
  ArrType _ a b -> recur a <> recur b
  TabType _ b   -> envNames (freeVars b)
  RecType r     -> foldMap recur r
  _             -> []
  where recur = dataVars

tauTypeAtomic :: Parser Type
tauTypeAtomic =   typeName
              <|> typeVar
              <|> idxSetLit
              <|> parenTy

tauType :: Parser Type
tauType = makeExprParser (sc >> tauType') typeOps
  where
    typeOps = [ [tyAppRule]
              , [InfixR (symbol "=>" >> return TabType)]
              , [InfixR (symbol "->"  >> return (ArrType (Mult NonLin))),
                 InfixR (symbol "--o" >> return (ArrType (Mult Lin)))]]

tyAppRule :: Operator Parser Type
tyAppRule = InfixL (sc *> notFollowedBy (choice . map symbol $ tyOpNames)
                    >> return applyType)
  where tyOpNames = ["=>", "->", "--o"]

applyType :: Type -> Type -> Type
applyType (TypeApp ty args) arg = TypeApp ty (args ++ [arg])
applyType ty arg = TypeApp ty [arg]

tauType' :: Parser Type
tauType' =   parenTy
         <|> monadType
         <|> lensType
         <|> typeName
         <|> typeVar
         <|> idxSetLit
         <?> "type"

typeVar :: Parser Type
typeVar = do
  v <- upperName <|> lowerName
  return $ TypeVar (v:> Kind [])

monadType :: Parser Type
monadType = do
  symbol "Monad"
  r <- tauTypeAtomic
  w <- tauTypeAtomic
  s <- tauTypeAtomic
  a <- tauTypeAtomic
  return $ Monad (Effect r w s) a

lensType :: Parser Type
lensType = do
  symbol "Lens"
  a <- tauTypeAtomic
  b <- tauTypeAtomic
  return $ Lens a b

idxSetLit :: Parser Type
idxSetLit = liftM IdxSetLit uint

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
literalData =   liftM (FPrimExpr . PrimConExpr) idxLit
            <|> liftM (FPrimExpr . PrimConExpr . Lit) literal
            <|> tupleData
            <|> tableData

tupleData :: Parser FExpr
tupleData = do
  xs <- parens $ literalData `sepEndBy` comma
  return $ FPrimExpr $ PrimConExpr $ RecCon $ Tup xs

tableData :: Parser FExpr
tableData = do
  xs <- brackets $ literalData `sepEndBy` comma
  return $ FPrimExpr $ PrimOpExpr $ TabCon NoAnn NoAnn xs
