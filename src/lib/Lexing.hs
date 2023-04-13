-- Copyright 2022 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module Lexing where

import Control.Monad.State.Strict
import Data.Char
import Data.HashSet qualified as HS
import qualified Data.Scientific as Scientific
import Data.String (fromString)
import Data.Text (Text)
import Data.Text          qualified as T
import Data.Void
import Data.Word

import Text.Megaparsec hiding (Label, State)
import Text.Megaparsec.Char hiding (space, eol)
import qualified Text.Megaparsec.Char as MC
import qualified Text.Megaparsec.Char.Lexer as L
import Text.Megaparsec.Debug

import Err
import Types.Primitives

data ParseCtx = ParseCtx
  { curIndent      :: Int  -- used Reader-style (i.e. ask/local)
  , canBreak       :: Bool -- used Reader-style (i.e. ask/local)
  , prevWhitespace :: Bool -- tracks whether we just consumed whitespace
  }

initParseCtx :: ParseCtx
initParseCtx = ParseCtx 0 False False

type Parser = StateT ParseCtx (Parsec Void Text)

parseit :: Text -> Parser a -> Except a
parseit s p = case parse (fst <$> runStateT p initParseCtx) "" s of
  Left e  -> throw ParseErr $ errorBundlePretty e
  Right x -> return x

mustParseit :: Text -> Parser a -> a
mustParseit s p  = case parseit s p of
  Success x -> x
  Failure e -> error $ "This shouldn't happen:\n" ++ pprint e

debug :: (Show a) => String -> Parser a -> Parser a
debug lbl action = do
  ctx <- get
  lift $ dbg lbl $ fst <$> runStateT action ctx

-- === Lexemes ===

type Lexer = Parser

nextChar :: Lexer Char
nextChar = do
  i <- getInput
  guard $ not $ T.null i
  return $ T.head i
{-# INLINE nextChar #-}

anyCaseName  :: Lexer SourceName
anyCaseName = label "name" $ lexeme $
  checkNotKeyword $ (:) <$> satisfy (\c -> isLower c || isUpper c) <*>
    (T.unpack <$> takeWhileP Nothing (\c -> isAlphaNum c || c == '\'' || c == '_'))

anyName :: Lexer SourceName
anyName = anyCaseName <|> symName

checkNotKeyword :: Parser String -> Parser String
checkNotKeyword p = try $ do
  s <- p
  failIf (s `HS.member` keyWordSet) $ show s ++ " is a reserved word"
  return s
{-# INLINE checkNotKeyword #-}

data KeyWord = DefKW | ForKW | For_KW | RofKW | Rof_KW | CaseKW | OfKW
             | DataKW | StructKW | InterfaceKW
             | InstanceKW | GivenKW | WithKW | SatisfyingKW
             | IfKW | ThenKW | ElseKW | DoKW
             | ImportKW | ForeignKW | NamedInstanceKW
             | EffectKW | HandlerKW | JmpKW | CtlKW | ReturnKW | ResumeKW
             | CustomLinearizationKW | CustomLinearizationSymbolicKW | PassKW
  deriving (Enum)

keyWordToken :: KeyWord -> String
keyWordToken = \case
  DefKW           -> "def"
  ForKW           -> "for"
  RofKW           -> "rof"
  For_KW          -> "for_"
  Rof_KW          -> "rof_"
  CaseKW          -> "case"
  IfKW            -> "if"
  ThenKW          -> "then"
  ElseKW          -> "else"
  OfKW            -> "of"
  DataKW          -> "data"
  StructKW        -> "struct"
  InterfaceKW     -> "interface"
  InstanceKW      -> "instance"
  NamedInstanceKW -> "named-instance"
  GivenKW         -> "given"
  WithKW          -> "with"
  SatisfyingKW    -> "satisfying"
  DoKW            -> "do"
  ImportKW        -> "import"
  ForeignKW       -> "foreign"
  EffectKW        -> "effect"
  HandlerKW       -> "handler"
  JmpKW           -> "jmp"
  CtlKW           -> "ctl"
  ReturnKW        -> "return"
  ResumeKW        -> "resume"
  CustomLinearizationKW -> "custom-linearization"
  CustomLinearizationSymbolicKW -> "custom-linearization-symbolic"
  PassKW          -> "pass"

keyWord :: KeyWord -> Lexer ()
keyWord kw = lexeme $ try $ string (fromString $ keyWordToken kw)
  >> notFollowedBy nameTailChar

keyWordSet :: HS.HashSet String
keyWordSet = HS.fromList keyWordStrs

keyWordStrs :: [String]
keyWordStrs = map keyWordToken [DefKW .. PassKW]

primName :: Lexer String
primName = lexeme $ try $ char '%' >> some alphaNumChar

charLit :: Lexer Char
charLit = lexeme $ char '\'' >> L.charLiteral <* char '\''

strLit :: Lexer String
strLit = lexeme $ char '"' >> manyTill L.charLiteral (char '"')

natLit :: Lexer Word64
natLit = lexeme $ try $ L.decimal <* notFollowedBy (char '.')

doubleLit :: Lexer Double
doubleLit = lexeme $
      try L.float
  <|> try (fromIntegral <$> (L.decimal :: Parser Int) <* char '.')
  <|> try do
    s <- L.scientific
    case Scientific.toBoundedRealFloat s of
      Right f -> return f
      Left  _ -> fail "Non-representable floating point literal"

knownSymStrs :: HS.HashSet String
knownSymStrs = HS.fromList
  [ ".", ":", "::", "!", "=", "-", "+", "||", "&&"
  , "$", "&>", "|", ",", ",>", "<-", "+=", ":="
  , "->", "->>", "=>", "?->", "?=>", "--o", "--", "<<<", ">>>"
  , "..", "<..", "..<", "..<", "<..<", "?", "#", "##", "#?", "#&", "#|", "@"]

-- string must be in `knownSymStrs`
sym :: Text -> Lexer ()
sym s = lexeme $ try $ string s >> notFollowedBy symChar

anySym :: Lexer String
anySym = lexeme $ try $ do
  s <- some symChar
  failIf (s `HS.member` knownSymStrs) ""
  return s

symName :: Lexer SourceName
symName = label "symbol name" $ lexeme $ try $ do
  s <- between (char '(') (char ')') $ some symChar
  return $ "(" <> s <> ")"

backquoteName :: Lexer SourceName
backquoteName = label "backquoted name" $
  lexeme $ try $ between (char '`') (char '`') anyCaseName

-- brackets and punctuation
-- (can't treat as sym because e.g. `((` is two separate lexemes)
lParen, rParen, lBracket, rBracket, lBrace, rBrace, semicolon, underscore :: Lexer ()

lParen    = charLexeme '('
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
symChar = token (\c -> if HS.member c symChars then Just c else Nothing) mempty

symChars :: HS.HashSet Char
symChars = HS.fromList ".,!$^&*:-~+/=<>|?\\@#"

-- === Util ===

sc :: Parser ()
sc = (skipSome s >> recordWhitespace) <|> return ()
  where s = hidden space <|> hidden lineComment

lineComment :: Parser ()
lineComment = do
  try $ string "--" >> notFollowedBy (void (char 'o'))
  void (takeWhileP (Just "char") (/= '\n'))

outputLines :: Parser ()
outputLines = void $ many (symbol ">" >> takeWhileP Nothing (/= '\n') >> ((eol >> return ()) <|> eof))

space :: Parser ()
space = gets canBreak >>= \case
  True  -> space1
  False -> void $ takeWhile1P (Just "white space") (`elem` (" \t" :: String))

mayBreak :: Parser a -> Parser a
mayBreak p = pLocal (\ctx -> ctx { canBreak = True }) p
{-# INLINE mayBreak #-}

mayNotBreak :: Parser a -> Parser a
mayNotBreak p = pLocal (\ctx -> ctx { canBreak = False }) p
{-# INLINE mayNotBreak #-}

precededByWhitespace :: Parser Bool
precededByWhitespace = gets prevWhitespace
{-# INLINE precededByWhitespace #-}

recordWhitespace :: Parser ()
recordWhitespace = modify \ctx -> ctx { prevWhitespace = True }
{-# INLINE recordWhitespace #-}

recordNonWhitespace :: Parser ()
recordNonWhitespace = modify \ctx -> ctx { prevWhitespace = False }
{-# INLINE recordNonWhitespace #-}

nameString :: Parser String
nameString = lexeme . try $ (:) <$> lowerChar <*> many alphaNumChar

thisNameString :: Text -> Parser ()
thisNameString s = lexeme $ try $ string s >> notFollowedBy alphaNumChar

bracketed :: Parser () -> Parser () -> Parser a -> Parser a
bracketed left right p = between left right $ mayBreak $ sc >> p
{-# INLINE bracketed #-}

parens :: Parser a -> Parser a
parens p = bracketed lParen rParen p
{-# INLINE parens #-}

brackets :: Parser a -> Parser a
brackets p = bracketed lBracket rBracket p
{-# INLINE brackets #-}

braces :: Parser a -> Parser a
braces p = bracketed lBrace rBrace p
{-# INLINE braces #-}

withPos :: Parser a -> Parser (a, SrcPos)
withPos p = do
  n <- getOffset
  x <- p
  n' <- getOffset
  return $ (x, (n, n'))
{-# INLINE withPos #-}

nextLine :: Parser ()
nextLine = do
  eol
  n <- curIndent <$> get
  void $ mayNotBreak $ many $ try (sc >> eol)
  void $ replicateM n (char ' ')

withSource :: Parser a -> Parser (Text, a)
withSource p = do
  s <- getInput
  (x, (start, end)) <- withPos p
  return (T.take (end - start) s, x)
{-# INLINE withSource #-}

withIndent :: Parser a -> Parser a
withIndent p = do
  nextLine
  indent <- T.length <$> takeWhileP (Just "space") (==' ')
  when (indent <= 0) empty
  pLocal (\ctx -> ctx { curIndent = curIndent ctx + indent }) $ mayNotBreak p
{-# INLINE withIndent #-}

pLocal :: (ParseCtx -> ParseCtx) -> Parser a -> Parser a
pLocal f p = do
  s <- get
  put (f s) >> p <* put s
{-# INLINE pLocal #-}

eol :: Parser ()
eol = void MC.eol

eolf :: Parser ()
eolf = eol <|> eof

failIf :: Bool -> String -> Parser ()
failIf True s = fail s
failIf False _ = return ()

lexeme :: Parser a -> Parser a
lexeme p = L.lexeme sc (p <* recordNonWhitespace)
{-# INLINE lexeme #-}

symbol :: Text -> Parser ()
symbol s = void $ L.symbol sc s

