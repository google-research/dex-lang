-- Copyright 2022 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module Lexing where

import Control.Monad
import Control.Monad.State.Strict
import Data.ByteString.Internal (c2w)
import Data.HashSet qualified as HS
import qualified Data.Scientific as Scientific
import qualified Data.ByteString as BS
import Data.String (fromString)
import Data.Void
import Data.Word
import Data.Word8 (isLower, isUpper, isAlphaNum)
import qualified Data.Map.Strict as M

import Text.Megaparsec hiding (Label, State)
import Text.Megaparsec.Byte hiding (space, eol)
import qualified Text.Megaparsec.Byte as MC
import qualified Text.Megaparsec.Byte.Lexer as L
import Text.Megaparsec.Debug

import Err
import PPrint
import Types.Primitives
import Types.Source
import Util (BString, bs2str, toSnocList, errorbs)

data ParseCtx = ParseCtx
  { curIndent      :: Int  -- used Reader-style (i.e. ask/local)
  , canBreak       :: Bool -- used Reader-style (i.e. ask/local)
  , prevWhitespace :: Bool -- tracks whether we just consumed whitespace
  , sourceIdCounter :: Int  -- starts at 1 (0 is reserved for the root)
  , curAtomicLexemes :: [SrcId]
  , curLexemeInfo    :: LexemeInfo } -- append to, writer-style

initParseCtx :: ParseCtx
initParseCtx = ParseCtx 0 False False 1 mempty mempty

type Parser = StateT ParseCtx (Parsec Void BString)

parseit :: BString -> Parser a -> Except a
parseit s p = case parse (fst <$> runStateT p initParseCtx) "" s of
  Left e  -> throwErr $ ParseErr $ MiscParseErr $ fromString $ errorBundlePretty e
  Right x -> return x

mustParseit :: BString -> Parser a -> a
mustParseit s p  = case parseit s p of
  Success x -> x
  Failure e -> errorbs $ "This shouldn't happen:\n" <> pprint e

-- === Lexemes ===

type Lexer = Parser

nextChar :: Lexer Word8
nextChar = do
  i <- getInput
  guard $ not $ BS.null i
  return $ BS.head i
{-# INLINE nextChar #-}

anyCaseName  :: Lexer (WithSrc SourceName)
anyCaseName = label "name" $ lexeme LowerName anyCaseName' -- TODO: distinguish lowercase/uppercase

anyCaseName' :: Lexer SourceName
anyCaseName' = liftM MkSourceName $ checkNotKeyword do
  c <- satisfy (\c -> isLower c || isUpper c)
  cs <- takeWhileP Nothing (\c -> isAlphaNum c || c == c2w '\'' || c == c2w '_')
  return $ BS.pack [c] <> cs

anyName :: Lexer (WithSrc SourceName)
anyName = anyCaseName <|> symName

checkNotKeyword :: Parser BString -> Parser BString
checkNotKeyword p = try $ do
  s <- p
  when (s `HS.member` keyWordSet) $ fail $ show s ++ " is a reserved word"
  return s
{-# INLINE checkNotKeyword #-}

data KeyWord = DefKW | ForKW | For_KW | RofKW | Rof_KW | CaseKW | OfKW
             | DataKW | StructKW | InterfaceKW
             | InstanceKW | GivenKW | WithKW | SatisfyingKW
             | IfKW | ThenKW | ElseKW | DoKW
             | ImportKW | ForeignKW | NamedInstanceKW
             | CustomLinearizationKW | CustomLinearizationSymbolicKW | PassKW
  deriving (Enum)

keyWordToken :: KeyWord -> BString
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
  DataKW          -> "enum"
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
  CustomLinearizationKW -> "custom-linearization"
  CustomLinearizationSymbolicKW -> "custom-linearization-symbolic"
  PassKW          -> "pass"

keyWord :: KeyWord -> Lexer ()
keyWord kw = atomicLexeme Keyword $ try $
  string (keyWordToken kw) >> notFollowedBy nameTailChar
  where
    nameTailChar :: Parser Word8
    nameTailChar = alphaNumChar <|> cchar '\'' <|> cchar '_'

keyWordSet :: HS.HashSet BString
keyWordSet = HS.fromList keyWordStrs

keyWordStrs :: [BString]
keyWordStrs = map keyWordToken [DefKW .. PassKW]

primName :: Lexer (WithSrc BString)
primName = lexeme MiscLexeme $ try $ cchar '%' >> (BS.pack <$> some alphaNumChar)

charLit :: Lexer (WithSrc Char)
charLit = undefined -- lexeme MiscLexeme $ cchar '\'' >> L.charLiteral <* cchar '\''

strLit :: Lexer (WithSrc BString)
strLit = undefined -- lexeme StringLiteralLexeme $ cchar '"' >> manyTill L.charLiteral (cchar '"')

natLit :: Lexer (WithSrc Word64)
natLit = lexeme LiteralLexeme $ try $ L.decimal <* notFollowedBy (cchar '.')

doubleLit :: Lexer (WithSrc Double)
doubleLit = lexeme LiteralLexeme $
      try L.float
  <|> try (fromIntegral <$> (L.decimal :: Parser Int) <* cchar '.')
  <|> try do
    s <- L.scientific
    case Scientific.toBoundedRealFloat s of
      Right f -> return f
      Left  _ -> fail "Non-representable floating point literal"

knownSymStrs :: HS.HashSet BString
knownSymStrs = HS.fromList
  [ ".", ":", "::", "!", "=", "-", "+", "||", "&&"
  , "$", "&>", "|", ",", ",>", "<-", "+=", ":="
  , "->", "->>", "=>", "?->", "?=>", "<<<", ">>>"
  , "..", "<..", "..<", "..<", "<..<", "?", "#", "##", "#?", "#&", "#|", "@"]

sym :: BString -> Lexer ()
sym s = atomicLexeme Symbol $ sym' s

symWithId :: BString -> Lexer SrcId
symWithId s = liftM srcPos $ lexeme Symbol $ sym' s

cchar :: Char -> Lexer Word8
cchar c = char (c2w c)

-- string must be in `knownSymStrs`
sym' :: BString -> Lexer ()
sym' s = void $ try $ string s >> notFollowedBy symChar

anySym :: Lexer (WithSrc BString)
anySym = lexeme Symbol $ try $ do
  s <- BS.pack <$> some symChar
  when (s `HS.member` knownSymStrs) $ fail ""
  return s

symName :: Lexer (WithSrc SourceName)
symName = label "symbol name" $ lexeme Symbol $ try $ do
  s <- BS.pack <$> between (cchar '(') (cchar ')') (some symChar)
  return $ MkSourceName $ "(" <> s <> ")"

backquoteName :: Lexer (WithSrc SourceName)
backquoteName = label "backquoted name" $
  lexeme Symbol $ try $ between (cchar '`') (cchar '`') anyCaseName'

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
charLexeme c = atomicLexeme Symbol $ void $ cchar c

symChar :: Parser Word8
symChar = token (\c -> if HS.member c symChars then Just c else Nothing) mempty

symChars :: HS.HashSet Word8
symChars = HS.fromList $ map c2w ".,!$^&*:-~+/=<>|?\\@#"

-- XXX: unlike other lexemes, this doesn't consume trailing whitespace
dot :: Parser ()
dot = do
  WithSrc sid () <- lexeme' (return ()) Symbol (void $ cchar '.')
  emitAtomicLexeme sid

-- === Util ===

sc :: Parser ()
sc = (skipSome s >> recordWhitespace) <|> return ()
  where s = hidden space <|> hidden lineComment

lineComment :: Parser ()
lineComment = string "#" >> void (takeWhileP (Just "char") (/= c2w '\n'))

outputLines :: Parser ()
outputLines = void $ many (symbol ">" >> takeWhileP Nothing (/= c2w '\n') >> ((eol >> return ()) <|> eof))

space :: Parser ()
space = gets canBreak >>= \case
  True  -> space1
  False -> void $ takeWhile1P (Just "white space") (`elem` ([c2w ' ', c2w '\t']))

setCanBreakLocally :: Bool -> Parser a -> Parser a
setCanBreakLocally brLocal p = do
  brPrev <- gets canBreak
  modify \ctx -> ctx {canBreak = brLocal}
  ans <- p
  modify \ctx -> ctx {canBreak = brPrev}
  return ans
{-# INLINE setCanBreakLocally #-}

mayBreak :: Parser a -> Parser a
mayBreak p = setCanBreakLocally True p
{-# INLINE mayBreak #-}

mayNotBreak :: Parser a -> Parser a
mayNotBreak p = setCanBreakLocally False p
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

nameString :: Parser BString
nameString = lexemeIgnoreSrcId LowerName $ try do
  BS.pack <$> ((:) <$> lowerChar <*> many alphaNumChar)

thisNameString :: BString -> Parser ()
thisNameString s = lexemeIgnoreSrcId MiscLexeme $ try $ string s >> notFollowedBy alphaNumChar

bracketed :: Parser () -> Parser () -> Parser a -> Parser a
bracketed left right p = do
  left
  ans <- mayBreak $ sc >> p
  right
  return ans
{-# INLINE bracketed #-}

braces :: Parser a -> Parser a
braces p = bracketed lBrace rBrace p
{-# INLINE braces #-}

nextLine :: Parser ()
nextLine = do
  eol
  n <- curIndent <$> get
  void $ mayNotBreak $ many $ try (sc >> eol)
  void $ replicateM n (cchar ' ')

withSource :: Parser a -> Parser (BString, a)
withSource p = do
  s <- getInput
  start <- getOffset
  x <- p
  end <- getOffset
  return (BS.take (end - start) s, x)
{-# INLINE withSource #-}

withIndent :: Parser a -> Parser a
withIndent p = do
  nextLine
  indent <- BS.length <$> takeWhileP (Just "space") (== c2w ' ')
  when (indent <= 0) empty
  locallyExtendCurIndent indent $ mayNotBreak p
{-# INLINE withIndent #-}

locallyExtendCurIndent :: Int -> Parser a -> Parser a
locallyExtendCurIndent n p = do
  indentPrev <- gets curIndent
  modify \ctx -> ctx { curIndent = indentPrev + n }
  ans <- p
  modify \ctx -> ctx { curIndent = indentPrev }
  return ans

eol :: Parser ()
eol = void MC.eol

eolf :: Parser ()
eolf = eol <|> eof

freshSrcId :: Parser SrcId
freshSrcId = do
  c <- gets sourceIdCounter
  modify \ctx -> ctx { sourceIdCounter = c + 1 }
  return $ SrcId c

withLexemeInfo :: Parser a -> Parser (LexemeInfo, a)
withLexemeInfo cont = do
  smPrev <- gets curLexemeInfo
  modify \ctx -> ctx { curLexemeInfo = mempty }
  result <- cont
  sm <- gets curLexemeInfo
  modify \ctx -> ctx { curLexemeInfo = smPrev }
  return (sm, result)

emitLexemeInfo :: LexemeInfo -> Parser ()
emitLexemeInfo m = modify \ctx -> ctx { curLexemeInfo = curLexemeInfo ctx <> m }

lexemeIgnoreSrcId :: LexemeType -> Parser a -> Parser a
lexemeIgnoreSrcId lexemeType p = withoutSrc <$> lexeme lexemeType p

symbol :: BString -> Parser ()
symbol s = void $ L.symbol sc s

lexeme :: LexemeType -> Parser a -> Parser (WithSrc a)
lexeme lexemeType p = lexeme' sc lexemeType p
{-# INLINE lexeme #-}

lexeme' :: Parser () -> LexemeType -> Parser a -> Parser (WithSrc a)
lexeme' sc' lexemeType p = do
  start <- getOffset
  ans <- p
  end <- getOffset
  recordNonWhitespace
  sc'
  sid <- freshSrcId
  emitLexemeInfo $ mempty
    { lexemeList = toSnocList [sid]
    , lexemeInfo = M.singleton sid (lexemeType, (start, end)) }
  return $ WithSrc sid ans
{-# INLINE lexeme' #-}

atomicLexeme :: LexemeType -> Parser () -> Parser ()
atomicLexeme lexemeType p = do
  WithSrc sid () <- lexeme lexemeType p
  emitAtomicLexeme sid
{-# INLINE atomicLexeme #-}

emitAtomicLexeme :: LexemeId -> Parser ()
emitAtomicLexeme sid = modify \ctx ->
  ctx { curAtomicLexemes = curAtomicLexemes ctx ++ [sid] }

collectAtomicLexemeIds :: Parser a -> Parser ([SrcId], a)
collectAtomicLexemeIds p = do
  prevAtomicLexemes <- gets curAtomicLexemes
  modify \ctx -> ctx { curAtomicLexemes = [] }
  ans <- p
  localLexemes <- gets curAtomicLexemes
  modify \ctx -> ctx { curAtomicLexemes = prevAtomicLexemes }
  return (localLexemes, ans)
