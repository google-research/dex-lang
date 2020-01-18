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
import qualified Data.Map.Strict as M

import Env
import Record
import ParseUtil
import Syntax
import Fresh
import Type
import PPrint

parseProg :: String -> [SourceBlock]
parseProg s = mustParseit s $ manyTill (sourceBlock <* outputLines) eof

parseData :: String -> Except Expr
parseData s = parseit s literalData

parseTopDeclRepl :: String -> Maybe SourceBlock
parseTopDeclRepl s = case sbContents block of
  UnParseable True _ -> Nothing
  _ -> Just block
  where block = mustParseit s sourceBlock

parseTopDecl :: String -> Except TopDecl
parseTopDecl s = parseit s topDecl

parseit :: String -> Parser a -> Except a
parseit s p = case runTheParser s (p <* (optional eol >> eof)) of
  Left e -> throw ParseErr (errorBundlePretty e)
  Right x -> return x

mustParseit :: String -> Parser a -> a
mustParseit s p  = case parseit s p of
  Right ans -> ans
  Left e -> error $ "This shouldn't happen:\n" ++ pprint e

topDecl :: Parser TopDecl
topDecl = ( explicitCommand
        <|> ruleDef
        <|> liftM2 TopDecl topDeclAnn decl
        <|> liftM (EvalCmd . Command (EvalExpr Printed)) expr
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
  <|> (liftM UTopDecl topDecl)

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
  return $ UTopDecl $ EvalCmd (Command (Dump fmt s) e)

explicitCommand :: Parser TopDecl
explicitCommand = do
  cmdName <- char ':' >> identifier <* (optional eol >> sc)
  cmd <- case M.lookup cmdName commandNames of
    Just cmd -> return cmd
    Nothing -> fail $ "unrecognized command: " ++ show cmdName
  e <- declOrExpr
  return $ EvalCmd (Command cmd e)

topDeclAnn :: Parser DeclAnn
topDeclAnn =   (symbol "@primitive" >> declSep >> return ADPrimitive)
           <|> return PlainDecl

ruleDef :: Parser TopDecl
ruleDef = do
  v <- try $ lowerName <* symbol "#"
  symbol s
  symbol "::"
  (ty, tlam) <- letPolyTail $ pprint v ++ "#" ++ s
  return $ RuleDef (LinearizationDef v) ty tlam
  where s = "lin"

-- === Parsing decls ===

decl :: Parser Decl
decl = typeDef <|> unpack <|> doBind <|> letMono <|> letPoly

declSep :: Parser ()
declSep = void $ some $ (eol >> sc) <|> symbol ";"

typeDef :: Parser Decl
typeDef = do
  defType <-     (symbol "type"    >> return TyAlias)
             <|> (symbol "newtype" >> return NewType)
  v <- upperName
  bs <- many lowerName
  equalSign
  ty <- tauType
  return $ TyDef defType v (map (:>()) bs) ty

letPoly :: Parser Decl
letPoly = do
  v <- try $ lowerName <* symbol "::"
  (ty, tlam) <- letPolyTail (pprint v)
  return $ letPolyToMono (LetPoly (v:>ty) tlam)

letPolyTail :: String -> Parser (SigmaType, TLam)
letPolyTail s = do
  (tbs, ty) <- mayNotBreak $ sigmaType
  declSep
  symbol s
  wrap <- idxLhsArgs <|> lamLhsArgs
  equalSign
  rhs <- liftM wrap declOrExpr
  let (tvs, kinds) = unzip [(tv,k) | tv:>k <- tbs]
  let sTy = Forall kinds (abstractTVs tvs ty)
  return (sTy, TLam tbs rhs)

letPolyToMono :: Decl -> Decl
letPolyToMono d = case d of
  LetPoly (v:> Forall [] ty) (TLam [] rhs) -> LetMono (RecLeaf $ v:> ty) rhs
  _ -> d

doBind :: Parser Decl
doBind = do
  p <- try $ pat <* symbol "<-"
  body <- expr
  return $ DoBind p body

unpack :: Parser Decl
unpack = do
  (b, tv) <- try $ do b <- binder
                      comma
                      tv <- upperName
                      symbol "=" >> symbol "unpack"
                      return (b, tv)
  body <- expr
  return $ Unpack b tv body

letMono :: Parser Decl
letMono = do
  (p, wrap) <- try $ do p <- pat
                        wrap <- idxLhsArgs <|> lamLhsArgs
                        equalSign
                        return (p, wrap)
  body <- declOrExpr
  return $ LetMono p (wrap body)

-- === Parsing expressions ===

expr :: Parser Expr
expr = makeExprParser (withSourceAnn term) ops

term :: Parser Expr
term =   parenExpr
     <|> var
     <|> idxLit
     <|> liftM Lit literal
     <|> lamExpr
     <|> forExpr
     <|> primOp
     <|> ffiCall
     <|> tabCon
     <|> pack
     <?> "term"

declOrExpr :: Parser Expr
declOrExpr = declExpr <|> expr <?> "decl or expr"

parenExpr :: Parser Expr
parenExpr = do
  e <- parens $ declExpr <|> productCon
  ann <- typeAnnot
  return $ case ann of NoAnn -> e
                       ty    -> Annot e ty

productCon :: Parser Expr
productCon = do
  ans <- prod expr
  return $ case ans of
    Left x -> x
    Right (k, xs) -> RecCon k (Tup xs)

prod :: Parser a -> Parser (Either a (ProdKind, [a]))
prod p = prod1 p <|> return (Right (Cart, []))

prod1 :: Parser a -> Parser (Either a (ProdKind, [a]))
prod1 p = do
  x <- p
  sep <- optional $     (comma >> return Cart)
                    <|> (colon >> return Tens)
  case sep of
    Nothing -> return $ Left x
    Just k -> do
      xs <- p `sepEndBy` sep'
      return $ Right (k, x:xs)
      where sep' = case k of Cart -> comma
                             Tens -> colon

var :: Parser Expr
var = do
  v <- lowerName
  tyArgs <- many tyArg
  return $ Var v NoAnn tyArgs

tyArg :: Parser Type
tyArg = symbol "@" >> tauTypeAtomic

declExpr :: Parser Expr
declExpr = liftM2 Decl (mayNotBreak decl <* declSep) declOrExpr

withSourceAnn :: Parser Expr -> Parser Expr
withSourceAnn p = liftM (uncurry SrcAnnot) (withPos p)

typeAnnot :: Parser Type
typeAnnot = do
  ann <- optional $ symbol "::" >> tauTypeAtomic
  return $ case ann of
    Nothing -> NoAnn
    Just ty -> ty

primOp :: Parser Expr
primOp = do
  s <- try $ symbol "%" >> identifier
  b <- case M.lookup s builtinNames of
    Just b -> return b
    Nothing -> fail $ "Unexpected builtin: " ++ s
  symbol "("
  tyArgs <- tyArg `sepBy` comma
  args   <- expr  `sepBy` comma
  symbol ")"
  return $ PrimOp b tyArgs args

ffiCall :: Parser Expr
ffiCall = do
  symbol "%%"
  s <- identifier
  args <- parens $ expr `sepBy` comma
  return $ PrimOp (FFICall (length args) s) [] args

-- TODO: combine lamExpr/linlamExpr/forExpr
lamExpr :: Parser Expr
lamExpr = do
  multAnn <-    (symbol "lam"  >> return NoAnn)
            <|> (symbol "llam" >> return (Mult Lin))
  ps <- pat `sepBy` sc
  argTerm
  body <- declOrExpr
  return $ foldr (Lam multAnn) body ps

forExpr :: Parser Expr
forExpr = do
  symbol "for"
  vs <- pat `sepBy` sc
  argTerm
  body <- declOrExpr
  return $ foldr For body vs

tabCon :: Parser Expr
tabCon = do
  xs <- brackets $ (expr `sepEndBy` comma)
  return $ TabCon NoAnn xs

pack :: Parser Expr
pack = do
  symbol "pack"
  liftM3 Pack (expr <* comma) (tauType <* comma) existsType

idxLhsArgs :: Parser (Expr -> Expr)
idxLhsArgs = do
  period
  args <- pat `sepBy` period
  return $ \body -> foldr For body args

lamLhsArgs :: Parser (Expr -> Expr)
lamLhsArgs = do
  args <- pat `sepBy` sc
  return $ \body -> foldr (Lam NoAnn) body args

idxLit :: Parser Expr
idxLit = liftM2 (flip IdxLit) (try $ uint <* symbol "@") uint

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
  where
   resNames = ["for", "lam", "llam", "unpack", "pack"]

appRule :: Operator Parser Expr
appRule = InfixL (sc *> notFollowedBy (choice . map symbol $ opNames)
                     >> return App)
  where
    opNames = ["+", "*", "/", "- ", "^", "$", "@", "<", ">", "<=", ">=", "&&", "||", "=="]

postFixRule :: Operator Parser Expr
postFixRule = Postfix $ do
  trailers <- some (period >> idxExpr)
  return $ \e -> foldl Get e trailers

binOpRule :: String -> Builtin -> Operator Parser Expr
binOpRule opchar builtin = InfixL $ do
  ((), pos) <- (withPos $ symbol opchar) <* (optional eol >> sc)
  return $ \e1 e2 -> SrcAnnot (PrimOp builtin [] [e1, e2]) pos

backtickRule :: Operator Parser Expr
backtickRule = InfixL $ do
  void $ char '`'
  v <- rawVar
  char '`' >> sc
  return $ \x y -> (v `App` x) `App` y

ops :: [[Operator Parser Expr]]
ops = [ [postFixRule, appRule]
      , [binOpRule "^" Pow]
      , [binOpRule "*" FMul, binOpRule "/" FDiv]
      -- trailing space after "-" to distinguish from negation
      , [binOpRule "+" FAdd, binOpRule "- " FSub]
      , [binOpRule "==" (Cmp Equal),
         binOpRule "<=" (Cmp LessEqual),
         binOpRule ">=" (Cmp GreaterEqual),
         -- These "<" and ">" must come after "<=" and ">=" or parser will see ("<","=")
         binOpRule "<" (Cmp Less), binOpRule ">" (Cmp Greater)
        ]
      , [binOpRule "&&" And, binOpRule "||" Or]
      , [backtickRule]
      , [InfixR (symbol "$" >> optional eol >> sc >> return App)]
       ]

idxExpr :: Parser Expr
idxExpr = withSourceAnn $ rawVar <|> parens productCon

rawVar :: Parser Expr
rawVar = do
  v <- lowerName
  return $ Var v NoAnn []

binder :: Parser Binder
binder = (symbol "_" >> return ("_" :> NoAnn))
     <|> liftM2 (:>) lowerName typeAnnot

pat :: Parser Pat
pat =   parenPat
    <|> liftM RecLeaf binder

parenPat :: Parser Pat
parenPat = do
  ans <- parens $ prod pat
  return $ case ans of
    Left x -> x
    Right (_, xs) -> RecTree $ Tup xs

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

-- === Parsing types ===

sigmaType :: Parser ([TBinder], Type)
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
  let tbs' = map (addIdxSetVars (idxSetVars ty)) tbs
  return (tbs', ty)
  where
    nameIsLower v = isLower (tagToStr (nameTag v) !! 0)

typeBinder :: Parser TBinder
typeBinder = do
  ~(TypeVar v) <- typeVar
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

addIdxSetVars :: [Name] -> TBinder -> TBinder
addIdxSetVars vs b@(v:>(Kind cs))
  | v `elem` vs && not (IdxSet `elem` cs) = v:>(Kind (IdxSet:cs))
  | otherwise = b

idxSetVars :: Type -> [Name]
idxSetVars ty = case ty of
  ArrType _ a b  -> recur a <> recur b
  TabType a b    -> envNames (freeVars a) <> recur b
  RecType Cart r -> foldMap recur r
  Exists body    -> recur body
  _ -> []
  where recur = idxSetVars

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
         <|> existsType
         <|> typeName
         <|> typeVar
         <|> idxSetLit
         <?> "type"

typeVar :: Parser Type
typeVar = liftM TypeVar (upperName <|> lowerName)

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
    Left ty -> ty
    Right (k, xs) -> RecType k $ Tup xs

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

colon :: Parser ()
colon = symbol ":"

-- === Parsing literal data ===

literalData :: Parser Expr
literalData =   idxLit
            <|> liftM Lit literal
            <|> tupleData
            <|> tableData

tupleData :: Parser Expr
tupleData = do
  xs <- parens $ literalData `sepEndBy` comma
  return $ RecCon Cart $ Tup xs

tableData :: Parser Expr
tableData = do
  xs <- brackets $ literalData `sepEndBy` comma
  return $ TabCon NoAnn xs
