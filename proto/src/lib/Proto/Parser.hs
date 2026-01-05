-- Copyright 2025 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module Proto.Parser where

import Control.Monad
import Data.ByteString.Short (ShortByteString)
import Data.Word
import qualified Data.ByteString as BS
import qualified Data.ByteString.Short as SBS
import System.Environment

import Proto.Util
import Proto.Doc
import Proto.Monad

-- === parse tree data structure ===

type ParseTreePath = [Int]

type ParseTreeAnn = ParseTree ParseTreePath
data ParseTree ann = ParseTree {
  val :: ParseTree' ann,
  ann :: ann}

-- Whitespace because ParseTree needs to be printable to the exact original text
data ParseTree' ann =
   InfixOp (ParseTree ann) Whitespace Token Whitespace (ParseTree ann)
 | Parens Token Whitespace (ParseTree ann) Whitespace Token
 | Leaf Token
 | ParseError ParseError (ParseTree ann) Whitespace Token Remainder

data ParseError = Expected Token | ExpectedEOL
type Remainder = (Whitespace, [WTS Token])

-- === token data structure ===

-- String should only contain ' ' and '\t'. May be empty.
data Whitespace = Whitespace ShortByteString
data Token =
   Identifier ShortByteString
 | IntLit Int
 | LParen | RParen
 | Symbol ShortByteString
   deriving (Eq)

-- with trailing whitespace
data WTS a = WTS
  { val :: a
  , ws  :: Whitespace }  deriving Functor

instance Show Token where
  show = \case
    LParen -> "("
    RParen -> ")"
    IntLit n -> show n
    Symbol c-> show c
    Identifier s -> show s

-- === top-level interface ===

runParser :: BS.ByteString -> ProtoM r ParseTreeAnn
runParser s = do
  tokens <- lexit s
  tree <- parseit tokens
  return $ addPaths tree

-- === key paths ===

addPaths :: ParseTree () -> ParseTreeAnn
addPaths treeTop = go [] treeTop where
  go :: [Int] -> ParseTree () -> ParseTreeAnn
  go pathRev t = flip ParseTree (reverse pathRev) $ case t.val of
   InfixOp l lw op rw r -> InfixOp (go (0:pathRev) l) lw op rw (go (1:pathRev) r)
   Parens l lw t rw r -> Parens l lw (go pathRev t) rw r
   Leaf x -> Leaf x
   ParseError e tree w t rem -> ParseError e (go pathRev tree) w t rem

-- === main parser ===

type Precedence = Int  -- higher binds tighter

data ParseCtx = ParseCtx {
  tokens :: Ref [WTS Token],
  precedence :: LocalRef Precedence }

type ParserM = ProtoM ParseCtx

parseit :: [WTS Token] -> ProtoM r (ParseTree ())
parseit ts = do
  ctx <- ParseCtx <$> newRef ts <*> newLocalRef 0
  liftProtoM (const ctx) do
    parseExpr >>= checkEOL

pt :: ParseTree' () -> ParseTree ()
pt t = ParseTree t ()

parseExpr :: ParserM (WTS (ParseTree ()))
parseExpr = do
  t1 <- nextToken
  e <- case t1.val of
    LParen -> do
      c <- getCtx
      e <- setLocal c.precedence 0 parseExpr
      t2 <- nextToken
      when (t2.val /= RParen) (error "parse error")
      return $ WTS (pt $ Parens t1.val t1.ws e.val e.ws t2.val) t2.ws
    Symbol _ -> undefined
    Identifier _ -> return $ (pt . Leaf) <$> t1
    IntLit     _ -> return $ (pt . Leaf) <$> t1
  considerInfix e

considerInfix :: WTS (ParseTree ()) -> ParserM (WTS (ParseTree ()))
considerInfix lhs = peekToken >>= \case
  Nothing -> return lhs
  Just t2 -> do
    symPrecedence t2 >>= \case
      Nothing -> return lhs  -- not an infix operator
      Just t2Prec -> do
        c <- getCtx
        prec <- get c.precedence
        if t2Prec <= prec
          then return lhs
          else do
            t2' <- nextToken
            rhs <- setLocal c.precedence (t2Prec + 1) parseExpr
            let tree = InfixOp lhs.val lhs.ws t2'.val t2'.ws rhs.val
            considerInfix $ WTS (pt tree) rhs.ws

symPrecedence :: Token -> ParserM (Maybe Precedence)
symPrecedence = \case
  Symbol s | s == "*" -> return $ Just 20
           | s == "+" -> return $ Just 10
  _ -> return Nothing

peekToken :: ParserM (Maybe Token)
peekToken = do
  c <- getCtx
  get c.tokens >>= \case
    [] -> return Nothing
    t:_ -> return $ Just t.val

getRemainder :: Whitespace -> ParserM Remainder
getRemainder ws = do
  rem <- whileJust peekToken \_ -> nextToken
  return (ws, rem)

nextToken :: ParserM (WTS Token)
nextToken = do
  c <- getCtx
  get c.tokens >>= \case
    [] -> error "oops"
    t:ts -> do
      set c.tokens ts
      return t

checkEOL :: WTS (ParseTree ()) -> ParserM (ParseTree ())
checkEOL tree = do
  peekToken >>= \case
    Nothing -> return tree.val
    Just _ -> do
      t <- nextToken
      remainder <- getRemainder t.ws
      return $ pt $ ParseError ExpectedEOL tree.val tree.ws t.val remainder

-- === lexer ===

data ScannerCtx = ScannerCtx {
  source :: BS.ByteString,
  tokens :: AppendRef (WTS Token),
  pos    :: Ref Int }

type ScannerM = ProtoM ScannerCtx

lexit :: BS.ByteString -> ProtoM r [WTS Token]
lexit source = do
  ctx <- ScannerCtx source <$> newAppendRef <*> newRef 0
  liftProtoM (const ctx) do
    whileJust nextChar \c -> do
      t <- lexChar c
      ws <- Whitespace . SBS.pack <$> takeMany isWhitespace
      return $ WTS t ws

lexChar :: Word8 -> ScannerM Token
lexChar = \case
  c | isLeadingIdentifierChar c -> do
        cs <- takeMany isNonFirstIdentifierChar
        return $ Identifier $ SBS.pack $ c:cs
    | isDigit c -> do
        cs <- takeMany isDigit  -- TODO: -1, 1.2, 1e2
        return $ IntLit $ read (map w2c (c:cs))
    | isSymbol c -> do
        cs <- takeMany isSymbol
        return $ Symbol $ SBS.pack $ c:cs
    | c == c2w ')' -> return RParen
    | c == c2w '(' -> return LParen
    | otherwise -> error $ "Unrecognized:\n" <> show (fromEnum c)

nextChar :: ScannerM (Maybe Word8)
nextChar = do
  c <- getCtx
  i <- get c.pos
  set c.pos $ i + 1
  return $ BS.indexMaybe c.source i

emit :: WTS Token -> ScannerM ()
emit t = do
  c <- getCtx
  append c.tokens t

peekChar :: ScannerM (Maybe Word8)
peekChar = do
  c <- getCtx
  i <- get c.pos
  return $ BS.indexMaybe c.source i

takeMany :: (Word8 -> Bool) -> ScannerM [Word8]
takeMany isGood = do
  peekChar >>= \case
    Just c | isGood c -> do
      _ <- nextChar
      (c:) <$> takeMany isGood
    _ -> return []

toChar :: Word8 -> Char
toChar x = toEnum $ fromIntegral x

-- ~!@$%^&*-=+/?|
isSymbol :: Word8 -> Bool
isSymbol c = c `elem` map c2w "!@$%^&*-=+/?|"

isWhitespace :: Word8 -> Bool
isWhitespace c = c `elem` [c2w ' ', c2w '\n']

isDigit :: Word8 -> Bool
isDigit c = c2w '0' <= c && c <= c2w '9'

isLower :: Word8 -> Bool
isLower c = c2w 'a' <= c && c <= c2w 'z'

isUpper :: Word8 -> Bool
isUpper c = c2w 'A' <= c && c <= c2w 'Z'


isLeadingIdentifierChar :: Word8 -> Bool
isLeadingIdentifierChar c = isLower c || isUpper c -- TODO: underscore  || w2c c == '_'

isNonFirstIdentifierChar :: Word8 -> Bool
isNonFirstIdentifierChar c = isLeadingIdentifierChar c || isDigit c

-- === applicative command-line argument parser ===

parseArgsIO :: ArgParser a -> ProtoM r a
parseArgsIO p = do
  args <- liftIO getArgs
  ctx <- ArgParserCtx <$> newRef args <*> pure (getHelpText p)
  liftProtoM (const ctx) do
    parseArgsM p
    -- TODO: check for unrecognized arguments

data ArgParserCtx = ArgParserCtx {
  args :: Ref [String],
  helpText :: Doc }

type ArgParserM = ProtoM ArgParserCtx

data ArgParser a =
   SubCommands [(String, ArgParser a)]
 | PositionalArg (OptionPayload a)
 | Option String a (OptionPayload a)
 | ApplicativeJazz (FA ArgParser a)
  deriving (Functor, Applicative) via (FreeApplicative ArgParser)

instance FromFA ArgParser where
  fromFA = ApplicativeJazz

data OptionPayload a where
  IntOption :: OptionPayload Int
  StringOption :: OptionPayload String
  EnumOption :: [(String, a)] -> OptionPayload a
  -- Comma-separated list. These shouldn't be nested.
  ListOption :: OptionPayload a -> OptionPayload [a]

parseArgsM :: ArgParser a -> ArgParserM a
parseArgsM p = case p of
  SubCommands commands -> do
    cmd <- nextArg
    case lookup cmd commands of
      Nothing -> throwWithHelp $
        oneLiner $ "unrecognized command: " <> cmd
      Just parser -> parseArgsM parser
  PositionalArg option -> do
    cmd <- nextArg
    parseOptionPayload option cmd
  Option _ _ _ -> undefined
  ApplicativeJazz app -> runFA parseArgsM app

nextArg :: ArgParserM String
nextArg = do
  ctx <- getCtx
  args <- get ctx.args
  case args of
    [] -> throwWithHelp $ oneLiner "Expected an argument"
    arg:rest -> set ctx.args rest  >> return arg

parseOptionPayload :: OptionPayload a -> String -> ArgParserM a
parseOptionPayload p arg = case p of
  StringOption -> return arg
  _ -> error "todo"

throwWithHelp :: Doc -> ArgParserM a
throwWithHelp errorMsg = do
  ctx <- getCtx
  throw do
    errorMsg
    oneLiner "Usage:"
    indented ctx.helpText

-- TODO: also tab-completion
getHelpText :: ArgParser a -> Doc
getHelpText = \case
  SubCommands cmds -> forM_ cmds \(cmd, p) -> do
    oneLiner cmd
    indented $ getHelpText p
  PositionalArg _ -> oneLiner "<positional command>"
  Option _ _ _ -> undefined
  ApplicativeJazz fa -> case fa of
    Pure _ -> return ()
    FMap _ p -> getHelpText p
    LiftA2 _ p1 p2 -> getHelpText p1 >> getHelpText p2
