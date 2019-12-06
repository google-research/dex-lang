-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE OverloadedStrings #-}

module Parser (parseProg, parseTopDeclRepl, parseTopDecl) where

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

parseTopDeclRepl :: String -> Maybe SourceBlock
parseTopDeclRepl s = case sbContents block of
  UnParseable True _ -> Nothing
  _ -> Just block
  where block = mustParseit s sourceBlock

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
        <|> ruleDef
        <|> liftM2 TopDecl topDeclAnn decl
        <|> liftM (EvalCmd . Command (EvalExpr Printed)) expr
        <?> "top-level declaration" ) <* (void eol <|> eof)

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
  <|> (liftM UTopDecl topDecl)

explicitCommand :: Parser UTopDecl
explicitCommand = do
  cmdName <- char ':' >> identifier
  cmd <- case M.lookup cmdName commandNames of
    Just cmd -> return cmd
    Nothing -> fail $ "unrecognized command: " ++ show cmdName
  e <- declOrExpr
  return $ EvalCmd (Command cmd e)

topDeclAnn :: Parser DeclAnn
topDeclAnn =   (symbol "@primitive" >> declSep >> return ADPrimitive)
           <|> return PlainDecl

ruleDef :: Parser UTopDecl
ruleDef = do
  v <- try $ lowerName <* symbol "#"
  symbol s
  symbol "::"
  (ty, tlam) <- letPolyTail $ pprint v ++ "#" ++ s
  return $ RuleDef (LinearizationDef v) ty tlam
  where s = "lin"

-- === Parsing decls ===

decl :: Parser UDecl
decl = typeDef <|> unpack <|> letMono <|> letPoly

declSep :: Parser ()
declSep = void $ (eol >> sc) <|> symbol ";"

typeDef :: Parser UDecl
typeDef = do
  defType <-     (symbol "type"    >> return TyAlias)
             <|> (symbol "newtype" >> return NewType)
  v <- upperName
  equalSign
  ty <- tauType
  return $ TyDef defType v ty

letPoly :: Parser UDecl
letPoly = do
  v <- try $ lowerName <* symbol "::"
  (ty, tlam) <- letPolyTail (pprint v)
  return $ letPolyToMono (LetPoly (v:>ty) tlam)

letPolyTail :: String -> Parser (SigmaType, UTLam)
letPolyTail s = do
  (tbs, ty) <- sigmaType
  declSep
  symbol s
  wrap <- idxLhsArgs <|> lamLhsArgs (linearities ty)
  equalSign
  rhs <- liftM wrap declOrExpr
  let (tvs, kinds) = unzip [(tv,k) | tv:>k <- tbs]
  let sTy = Forall kinds (abstractTVs tvs ty)
  return (sTy, TLam tbs rhs)

letPolyToMono :: UDecl -> UDecl
letPolyToMono d = case d of
  LetPoly (v:> Forall [] ty) (TLam [] rhs) -> LetMono (RecLeaf $ v:> Ann ty) rhs
  _ -> d

linearities :: Type -> [Lin]
linearities (ArrType l _ b) = l:linearities b
linearities _ = []

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
                        wrap <- idxLhsArgs <|> lamLhsArgs []
                        equalSign
                        return (p, wrap)
  body <- declOrExpr
  return $ LetMono p (wrap body)

-- === Parsing expressions ===

expr :: Parser UExpr
expr = makeExprParser (withSourceAnn term) ops

term :: Parser UExpr
term =   parenExpr
     <|> var
     <|> liftM Lit literal
     <|> lamExpr
     <|> linlamExpr
     <|> forExpr
     <|> primOp
     <|> ffiCall
     <|> tabCon
     <|> pack
     <?> "term"

declOrExpr :: Parser UExpr
declOrExpr = declExpr <|> expr <?> "decl or expr"

parenExpr :: Parser UExpr
parenExpr = do
  e <- parens $ declExpr <|> productCon
  ann <- typeAnnot
  return $ case ann of NoAnn  -> e
                       Ann ty -> Annot e ty

productCon :: Parser UExpr
productCon = do
  (k, xs) <- prod expr
  return $ case xs of
    []  -> unitCon
    [x] -> x
    _   -> RecCon k (Tup xs)

prod :: Parser a -> Parser (ProdKind, [a])
prod p = prod1 p <|> return (Cart, [])

prod1 :: Parser a -> Parser (ProdKind, [a])
prod1 p = do
  x <- p
  sep <- optional $     (comma >> return Cart)
                    <|> (colon >> return Tens)
  case sep of
    Nothing -> return (Cart, [x])
    Just k -> do
      xs <- p `sepBy` sep'
      return (k, x:xs)
      where sep' = case k of Cart -> comma
                             Tens -> colon

var :: Parser UExpr
var = liftM2 Var lowerName $ many (symbol "@" >> tauTypeAtomic)

declExpr :: Parser UExpr
declExpr = liftM2 Decl (decl <* declSep) declOrExpr

withSourceAnn :: Parser UExpr -> Parser UExpr
withSourceAnn p = liftM (uncurry SrcAnnot) (withPos p)

typeAnnot :: Parser Ann
typeAnnot = do
  ann <- optional $ symbol "::" >> tauTypeAtomic
  return $ case ann of
    Nothing -> NoAnn
    Just ty -> Ann ty

primOp :: Parser UExpr
primOp = do
  s <- try $ symbol "%" >> identifier
  b <- case M.lookup s builtinNames of
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

-- TODO: combine lamExpr/linlamExpr/forExpr
lamExpr :: Parser UExpr
lamExpr = do
  symbol "lam"
  ps <- pat `sepBy` sc
  argTerm
  body <- declOrExpr
  return $ foldr (Lam NonLin) body ps

linlamExpr :: Parser UExpr
linlamExpr = do
  symbol "llam"
  ps <- pat `sepBy` sc
  argTerm
  body <- declOrExpr
  return $ foldr (Lam Lin) body ps

forExpr :: Parser UExpr
forExpr = do
  symbol "for"
  vs <- pat `sepBy` sc
  argTerm
  body <- declOrExpr
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

lamLhsArgs :: [Lin] -> Parser (UExpr -> UExpr)
lamLhsArgs lin = do
  args <- pat `sepBy` sc
  return $ \body -> foldr (uncurry Lam) body (zip (lin ++ repeat NonLin) args)

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

appRule :: Operator Parser UExpr
appRule = InfixL (sc *> notFollowedBy (choice . map symbol $ opNames)
                     >> return App)
  where
    opNames = ["+", "*", "/", "- ", "^", "$", "@", "<", ">", "&&", "||"]

postFixRule :: Operator Parser UExpr
postFixRule = Postfix $ do
  trailers <- some (period >> idxExpr)
  return $ \e -> foldl Get e trailers

binOpRule :: String -> Builtin -> Operator Parser UExpr
binOpRule opchar builtin = InfixL $ do
  ((), pos) <- withPos $ symbol opchar
  return $ \e1 e2 -> SrcAnnot (PrimOp builtin [] [e1, e2]) pos

ops :: [[Operator Parser UExpr]]
ops = [ [postFixRule, appRule]
      , [binOpRule "^" Pow]
      , [binOpRule "*" FMul, binOpRule "/" FDiv]
      -- trailing space after "-" to distinguish from negation
      , [binOpRule "+" FAdd, binOpRule "- " FSub]
      , [binOpRule "<" FLT, binOpRule ">" FGT]
      , [binOpRule "&&" And, binOpRule "||" Or]
      , [InfixR (symbol "$" >> return App)]
       ]

idxExpr :: Parser UExpr
idxExpr = withSourceAnn $ rawVar <|> parens productCon

rawVar :: Parser UExpr
rawVar = liftM (flip Var []) lowerName

binder :: Parser UBinder
binder = (symbol "_" >> return ("_" :> NoAnn))
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
  try $ symbol "=" >> notFollowedBy (symbol ">")
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
    typeOps = [ [InfixR (symbol "=>" >> return TabType)]
              , [InfixR (symbol "->"  >> return (ArrType NonLin)),
                 InfixR (symbol "--o" >> return (ArrType Lin))]]

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
idxSetLit = liftM IdxSetLit uint

parenTy :: Parser Type
parenTy = do
  (k, xs) <- parens $ prod tauType
  return $ case xs of
    [ty] -> ty
    _ -> RecType k $ Tup xs

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
