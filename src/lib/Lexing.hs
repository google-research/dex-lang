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
import qualified Data.Map.Strict as M

import Text.Megaparsec hiding (Label, State)
import Text.Megaparsec.Char hiding (space, eol)
import qualified Text.Megaparsec.Char as MC
import qualified Text.Megaparsec.Char.Lexer as L
import Text.Megaparsec.Debug

import Err
import PPrint
import Types.Primitives
import Types.Source
import Util (toSnocList)

data ParseCtx = ParseCtx
  { curIndent      :: Int  -- used Reader-style (i.e. ask/local)
  , canBreak       :: Bool -- used Reader-style (i.e. ask/local)
  , prevWhitespace :: Bool -- tracks whether we just consumed whitespace
  , sourceIdCounter :: Int  -- starts at 1 (0 is reserved for the root)
  , curAtomicLexemes :: [SrcId]
  , curLexemeInfo    :: LexemeInfo } -- append to, writer-style

initParseCtx :: ParseCtx
initParseCtx = ParseCtx 0 False False 1 mempty mempty

type Parser = StateT ParseCtx (Parsec Void Text)

parseit :: Text -> Parser a -> Except a
parseit s p = case parse (fst <$> runStateT p initParseCtx) "" s of
  Left e  -> throwErr $ ParseErr $ MiscParseErr $ errorBundlePretty e
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

anyCaseName  :: Lexer (WithSrc SourceName)
anyCaseName = label "name" $ lexeme LowerName anyCaseName' -- TODO: distinguish lowercase/uppercase

anyCaseName' :: Lexer SourceName
anyCaseName' =
  liftM MkSourceName $ checkNotKeyword $ (:) <$> satisfy (\c -> isLower c || isUpper c) <*>
    (T.unpack <$> takeWhileP Nothing (\c -> isAlphaNum c || c == '\'' || c == '_'))

anyName :: Lexer (WithSrc SourceName)
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
keyWord kw = atomicLexeme Keyword $ try $
  string (fromString $ keyWordToken kw) >> notFollowedBy nameTailChar
  where
    nameTailChar :: Parser Char
    nameTailChar = alphaNumChar <|> char '\'' <|> char '_'

keyWordSet :: HS.HashSet String
keyWordSet = HS.fromList keyWordStrs

keyWordStrs :: [String]
keyWordStrs = map keyWordToken [DefKW .. PassKW]

primName :: Lexer (WithSrc String)
primName = lexeme MiscLexeme $ try $ char '%' >> some alphaNumChar

charLit :: Lexer (WithSrc Char)
charLit = lexeme MiscLexeme $ char '\'' >> L.charLiteral <* char '\''

strLit :: Lexer (WithSrc String)
strLit = lexeme StringLiteralLexeme $ char '"' >> manyTill L.charLiteral (char '"')

natLit :: Lexer (WithSrc Word64)
natLit = lexeme LiteralLexeme $ try $ L.decimal <* notFollowedBy (char '.')

doubleLit :: Lexer (WithSrc Double)
doubleLit = lexeme LiteralLexeme $
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
  , "->", "->>", "=>", "?->", "?=>", "<<<", ">>>"
  , "..", "<..", "..<", "..<", "<..<", "?", "#", "##", "#?", "#&", "#|", "@"]

sym :: Text -> Lexer ()
sym s = atomicLexeme Symbol $ sym' s

symWithId :: Text -> Lexer SrcId
symWithId s = liftM srcPos $ lexeme Symbol $ sym' s

-- string must be in `knownSymStrs`
sym' :: Text -> Lexer ()
sym' s = void $ try $ string s >> notFollowedBy symChar

anySym :: Lexer (WithSrc String)
anySym = lexeme Symbol $ try $ do
  s <- some symChar
  failIf (s `HS.member` knownSymStrs) ""
  return s

symName :: Lexer (WithSrc SourceName)
symName = label "symbol name" $ lexeme Symbol $ try $ do
  s <- between (char '(') (char ')') $ some symChar
  return $ MkSourceName $ "(" <> s <> ")"

backquoteName :: Lexer (WithSrc SourceName)
backquoteName = label "backquoted name" $
  lexeme Symbol $ try $ between (char '`') (char '`') anyCaseName'

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
charLexeme c = atomicLexeme Symbol $ void $ char c

symChar :: Parser Char
symChar = token (\c -> if HS.member c symChars then Just c else Nothing) mempty

symChars :: HS.HashSet Char
symChars = HS.fromList ".,!$^&*:-~+/=<>|?\\@#"

-- XXX: unlike other lexemes, this doesn't consume trailing whitespace
dot :: Parser ()
dot = do
  WithSrc sid () <- lexeme' (return ()) Symbol (void $ char '.')
  emitAtomicLexeme sid

-- === Util ===

sc :: Parser ()
sc = (skipSome s >> recordWhitespace) <|> return ()
  where s = hidden space <|> hidden lineComment

lineComment :: Parser ()
lineComment = string "#" >> void (takeWhileP (Just "char") (/= '\n'))

outputLines :: Parser ()
outputLines = void $ many (symbol ">" >> takeWhileP Nothing (/= '\n') >> ((eol >> return ()) <|> eof))

space :: Parser ()
space = gets canBreak >>= \case
  True  -> space1
  False -> void $ takeWhile1P (Just "white space") (`elem` (" \t" :: String))

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

nameString :: Parser String
nameString = lexemeIgnoreSrcId LowerName . try $ (:) <$> lowerChar <*> many alphaNumChar

thisNameString :: Text -> Parser ()
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
  void $ replicateM n (char ' ')

withSource :: Parser a -> Parser (Text, a)
withSource p = do
  s <- getInput
  start <- getOffset
  x <- p
  end <- getOffset
  return (T.take (end - start) s, x)
{-# INLINE withSource #-}

withIndent :: Parser a -> Parser a
withIndent p = do
  nextLine
  indent <- T.length <$> takeWhileP (Just "space") (==' ')
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

failIf :: Bool -> String -> Parser ()
failIf True s = fail s
failIf False _ = return ()

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

symbol :: Text -> Parser ()
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
