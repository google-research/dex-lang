module Parser (parseProg, parseTopDecl, Prog) where

import Control.Monad
import Control.Monad.Combinators.Expr
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Parsec as P
import Data.List (isPrefixOf, nub)
import Data.Char (isLower)
import Data.Either (isRight)

import Env
import Record
import ParseUtil
import Syntax
import Fresh
import Inference
import PPrint

type Prog = [(String, Except UTopDecl)]

parseProg :: String -> Prog
parseProg source = map (\s -> (s, parseTopDecl s)) (splitDecls source)

parseTopDecl :: String -> Except UTopDecl
parseTopDecl = parseit (emptyLines >> topDeclInstr <* emptyLines)

parseit :: Parser a -> String -> Except a
parseit p s = case parse (p <* eof) "" s of
                Left e -> throw ParseErr (errorBundlePretty e)
                Right x -> return x

topDeclInstr :: Parser UTopDecl
topDeclInstr =   explicitCommand
             <|> liftM UTopDecl ( typeAlias
                              <|> typedTopLet
                              <|> topUnpack
                              <|> topLet )
             <|> liftM (UEvalCmd . Command EvalExpr) expr
             <?> "top-level declaration"

explicitCommand :: Parser UTopDecl
explicitCommand = do
  symbol ":"
  cmdName <- identifier
  cmd <- case cmdName of
           "p"       -> return EvalExpr
           "t"       -> return GetType
           "passes"  -> return Passes
           "llvm"    -> return LLVM
           "asm"     -> return Asm
           "time"    -> return TimeIt
           "plot"    -> return Plot
           "plotmat" -> return PlotMat
           _   -> fail $ "unrecognized command: " ++ show cmdName
  e <- expr
  return $ UEvalCmd (Command cmd e)

typedTopLet :: Parser UDecl
typedTopLet = do
  v <- try (varName <* symbol "::")
  ty <- sigmaType <* eol
  ULet p e <- topLet
  case p of
    RecTree _ -> fail "Can't annotate top-level pattern-match"
    RecLeaf (UBind (v' :> b)) ->
     if v' /= v
       then fail "Type declaration variable must match assignment variable."
       else case b of
              Just _ -> fail "Conflicting type annotations"
              Nothing -> return $ ULet (RecLeaf (UBind (v :> Just ty))) e

topUnpack :: Parser UDecl
topUnpack = do
  (b, tv) <- try unpackBinder
  body <- expr
  return $ UUnpack b tv body

unpackBinder :: Parser (UBinder, Var)
unpackBinder = do
  b <- binder
  symbol ","
  tv <- capVarName
  symbol "=" >> symbol "unpack"
  return (b, tv)

topLet :: Parser UDecl
topLet = do
  (p, wrap) <- try $ do p <- pat
                        wrap <- idxLhsArgs <|> lamLhsArgs
                        symbol "="
                        return (p, wrap)
  body <- expr
  return $ ULet p (wrap body)

expr :: Parser UExpr
expr = makeExprParser (sc >> withSource term >>= maybeAnnot) ops

withSource :: Parser UExpr -> Parser UExpr
withSource p = do
  n <- getOffset
  t <- p
  n' <- getOffset
  return $ USrcAnnot t (n, n')

term :: Parser UExpr
term =   parenRaw
     <|> varExpr
     <|> liftM ULit literal
     <|> declExpr
     <|> lamExpr
     <|> forExpr
     <|> primOp
     <|> tabCon
     <?> "term"

maybeAnnot :: UExpr -> Parser UExpr
maybeAnnot e = do
  t <- optional typeAnnot
  return $ case t of
             Nothing -> e
             Just t -> UAnnot e t

typeAnnot :: Parser Type
typeAnnot = symbol "::" >> sigmaType

parenRaw = do
  elts <- parens $ expr `sepBy` symbol ","
  return $ case elts of
    [expr] -> expr
    elts -> URecCon $ Tup elts

-- maybeNamed :: Parser a -> Parser (Maybe String, a)
-- maybeNamed p = do
--   v <- optional $ try $
--     do v <- identifier
--        symbol "="
--        return v
--   x <- p
--   return (v, x)

varExpr :: Parser UExpr
varExpr = liftM (UVar . rawName) identifier

primOp :: Parser UExpr
primOp = do
  symbol "%"
  s <- identifier
  case strToBuiltin s of
    Just b -> do
      args <- parens $ expr `sepBy` symbol ","
      return $ UPrimOp b args
    Nothing -> fail $ "Unexpected builtin: " ++ s

declExpr :: Parser UExpr
declExpr = do
  symbol "let"
  decls <- (typeAlias <|> unpackDecl
             <|> typedLocalLet <|> localLet) `sepBy` symbol ";"
  symbol "in"
  body <- expr
  return $ UDecls decls body

lamExpr :: Parser UExpr
lamExpr = do
  symbol "lam"
  ps <- pat `sepBy` sc
  symbol "."
  body <- expr
  return $ foldr ULam body ps

forExpr :: Parser UExpr
forExpr = do
  symbol "for"
  vs <- some idxPat -- `sepBy` sc
  symbol "."
  body <- expr
  return $ foldr UFor body vs

typeAlias :: Parser UDecl
typeAlias = do
  symbol "type"
  v <- capVarName
  symbol "="
  ty <- tauType
  return $ UTAlias v ty

unpackDecl :: Parser UDecl
unpackDecl = do
  (b, tv) <- try unpackBinder
  body <- expr
  return $ UUnpack b tv body

typedLocalLet :: Parser UDecl
typedLocalLet = do
  v <- try (varName <* symbol "::")
  ty <- sigmaType <* symbol ";"
  v' <- varName
  if v' /= v
    then fail "Type declaration variable must match assignment variable."
    else return ()
  wrap <- idxLhsArgs <|> lamLhsArgs
  symbol "="
  body <- expr
  return $ ULet (RecLeaf (UBind (v :> Just ty))) (wrap body)

localLet :: Parser UDecl
localLet = do
  p <- pat
  wrap <- idxLhsArgs <|> lamLhsArgs
  symbol "="
  body <- expr
  return $ ULet p (wrap body)

tabCon :: Parser UExpr
tabCon = do
  xs <- brackets $ expr `sepBy` symbol ","
  return $ UTabCon xs

idxLhsArgs = do
  symbol "."
  args <- idxPat `sepBy` symbol "."
  return $ \body -> foldr UFor body args

lamLhsArgs = do
  args <- pat `sepBy` sc
  return $ \body -> foldr ULam body args

literal :: Parser LitVal
literal = lexeme $  fmap IntLit  (try (int <* notFollowedBy (symbol ".")))
                <|> fmap RealLit real
                <|> fmap StrLit stringLiteral

identifier :: Parser String
identifier = lexeme . try $ do
  w <- (:) <$> lowerChar <*> many alphaNumChar
  if w `elem` resNames
    then fail $ show w ++ " is a reserved word"
    else return w
 where
   resNames = ["for", "lam", "let", "in", "unpack"]

capIdentifier :: Parser String
capIdentifier = lexeme . try $ do
  w <- (:) <$> upperChar <*> many alphaNumChar
  if w `elem` resNames
    then fail $ show w ++ " is a reserved word"
    else return w
  where
    resNames = ["Int", "Real", "Bool", "Str", "A", "E"]

appRule = InfixL (sc *> notFollowedBy (choice . map symbol $ opNames)
                     >> return UApp)
  where
    opNames = ["+", "*", "/", "-", "^"]

binOpRule opchar builtin = InfixL (symbol opchar >> return binOpApp)
  where binOpApp e1 e2 = UPrimOp builtin [e1, e2]

getRule = Postfix $ do
  vs  <- many $ symbol "." >> idxExpr
  return $ \body -> foldr (flip UGet) body (reverse vs)

ops = [ [getRule, appRule]
      , [binOpRule "^" Pow]
      , [binOpRule "*" FMul]  -- binOpRule "/" Div]
      , [binOpRule "+" FAdd, binOpRule "-" FSub]
      ]

varName :: Parser Name
varName = liftM rawName identifier

capVarName :: Parser Name
capVarName = liftM rawName capIdentifier

idxExpr :: Parser UExpr
idxExpr = withSource $ liftM UVar varName

binder :: Parser UBinder
binder =     (symbol "_" >> return IgnoreBind)
         <|> (liftM UBind $ liftM2 (:>) varName (optional typeAnnot))

idxPat = binder

pat :: Parser Pat
pat =   parenPat
    <|> liftM RecLeaf binder

parenPat :: Parser Pat
parenPat = do
  xs <- parens $ pat `sepBy` symbol ","
  return $ case xs of
    [x] -> x
    xs -> RecTree $ Tup xs

sigmaType :: Parser Type
sigmaType = do
  ty <- typeExpr
  let vs = nub $ filter nameIsLower (freeTyVars ty)
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
          <|> liftM BaseType baseType
          <|> liftM TypeVar capVarName
          <|> liftM TypeVar varName
          <|> existsType
          <?> "type"

existsType :: Parser Type
existsType = do
  try $ symbol "E"
  v <- varName
  symbol "."
  body <- tauType
  return $ Exists (abstractTVs [v] body)

baseType :: Parser BaseType
baseType = (symbol "Int"  >> return IntType)
       <|> (symbol "Real" >> return RealType)
       <|> (symbol "Bool" >> return BoolType)
       <|> (symbol "Str"  >> return StrType)
       <?> "base type"

parenTy :: Parser Type
parenTy = do
  elts <- parens $ typeExpr `sepBy` symbol ","
  return $ case elts of
    [ty] -> ty
    _ -> RecType $ Tup elts

type LineParser = P.Parsec [String] ()

splitDecls :: String -> [String]
splitDecls s = parsecParse (   blanks
                            >> P.many (P.try topDeclString)
                            <* commentsOrBlanks) $ lines s

parsecParse :: LineParser a -> [String] -> a
parsecParse p s = case P.parse (p <* P.eof) "" s of
                    Left e -> error (show e)
                    Right x -> x

lineMatch :: (String -> Bool) -> LineParser String
lineMatch test = P.tokenPrim show nextPos toMaybe
  where nextPos pos _ _ = P.incSourceColumn pos 1
        toMaybe x = if test x then Just x
                              else Nothing

topDeclString :: LineParser String
topDeclString = do comments <- P.many (commentLine <* blanks)
                   annLines <- P.many annotLine
                   fstLine  <- lineMatch (const True)
                   rest     <- P.many continuedLine <* blanks
                   return $ unlines $ comments ++ annLines ++ (fstLine : rest)
  where
    annotLine = lineMatch $ isRight . parse (identifier >> symbol "::") ""
    continuedLine = lineMatch (" "  `isPrefixOf`)

commentLine :: LineParser String
commentLine = lineMatch ("--" `isPrefixOf`)

commentsOrBlanks :: LineParser ()
commentsOrBlanks = void $ P.many (void commentLine <|> blankLine)

blankLine :: LineParser ()
blankLine = void $ lineMatch (\line -> null line || ">" `isPrefixOf` line)

blanks :: LineParser ()
blanks = void $ P.many blankLine
