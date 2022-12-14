-- Copyright 2022 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module ConcreteSyntax (
  mustParseit, sourceBlocks, sourceBlock, joinPos, jointPos,
  keyWordStrs, showPrimName,
  binOptL, binOptR, nary,
  WithSrc (..), CSourceBlock, CSourceBlock' (..),
  CTopDecl, CTopDecl' (..), CBlock (..), CDecl, CDecl' (..),
  NameAndArgs, Group, Group'(..),
  Bin, Bin' (..), Bracket (..), LabelPrefix (..), ForKind (..),
  pattern ExprDecl, pattern ExprBlock, pattern Bracketed,
  pattern Binary, pattern Prefix, pattern Postfix, pattern Identifier) where

import Control.Monad.Combinators.Expr qualified as Expr
import Control.Monad.Reader
import Data.Char
import Data.Functor
import Data.List.NonEmpty (NonEmpty (..))
import Data.Map qualified as M
import Data.Maybe (fromMaybe)
import Data.String (fromString)
import Data.Text (Text)
import Data.Text          qualified as T
import Data.Tuple
import Data.Void
import Data.Word
import GHC.Generics (Generic (..))
import Text.Megaparsec hiding (Label, State)
import Text.Megaparsec.Char hiding (space, eol)
import qualified Unsafe.Coerce as TrulyUnsafe

import Err
import Lexing
import Name
import IRVariants
import Types.Primitives hiding (Equal)
import Types.Primitives qualified as P
import Types.Source

sourceBlocks :: Parser [CSourceBlock]
sourceBlocks = manyTill (sourceBlock <* outputLines) eof

-- === Parsing target ADT ===

data WithSrc a = WithSrc SrcPosCtx a
  deriving (Show, Functor)

type CSourceBlock = SourceBlockP CSourceBlock'

data CSourceBlock'
  = CTopDecl CTopDecl
  | CCommand CmdName CBlock
  | CDeclareForeign SourceName SourceName Group
  | CDeclareCustomLinearization SourceName SymbolicZeros Group
  | CMisc SourceBlockMisc
  | CUnParseable ReachedEOF String
  deriving (Show, Generic)

type CTopDecl = WithSrc CTopDecl'
data CTopDecl'
  = CDecl LetAnn CDecl
  | CData SourceName -- Type constructor name
      [Group] -- Arguments, including class constraints
      [NameAndArgs] -- Constructor names and argument sets
  | CInterface [Group] -- Superclasses
      NameAndArgs -- Class name and arguments
      -- Method declarations: name, arguments, type.  TODO: Allow operators?
      [(Group, Group)]
  | CEffectDecl SourceName [(SourceName, UResumePolicy, Group)]
  | CHandlerDecl SourceName -- Handler name
      SourceName -- Effect name
      SourceName -- Body type parameter
      Group -- Handler arguments
      Group -- Handler type annotation
      [(SourceName, Maybe UResumePolicy, CBlock)] -- Handler methods
  deriving (Show, Generic)

type NameAndArgs = (SourceName, [Group])

type CDecl = WithSrc CDecl'
data CDecl'
  = CLet Group CBlock
  -- Arrow binder <-
  | CBind Group CBlock
  -- name, args, type, body.  The header should contain the parameters,
  -- optional effects, and return type
  | CDef SourceName Group (Maybe Group) CBlock
  -- header, givens (may be empty), methods, optional name.  The header should contain
  -- the prerequisites, class name, and class arguments.
  | CInstance Group Group
      [(SourceName, CBlock)] -- Method definitions
      (Maybe SourceName) -- Optional name of instance
  | CExpr Group
  deriving (Show, Generic)

type Group = WithSrc Group'
data Group'
  = CEmpty
  | CIdentifier SourceName
  | CPrim PrimName [Group]
  | CNat Word64
  | CInt Int
  | CString String
  | CChar Char
  | CFloat Double
  | CHole
  | CLabel LabelPrefix String
  | CParens CBlock
  | CBracket Bracket Group
  -- Encode various separators of lists (like commas) as infix
  -- operators in their own right (with defined precedence!) at this
  -- level.  We will enforce correct structure in the translation to
  -- abstract syntax.
  | CBin Bin Group Group
  | CPrefix SourceName Group -- covers unary - and unary + among others
  | CPostfix SourceName Group
  | CLambda [Group] CBlock  -- The arguments do not have Juxtapose at the top level
  | CFor ForKind [Group] CBlock -- also for_, rof, rof_, view
  | CCase Group [(Group, CBlock)] -- scrutinee, alternatives
  | CIf Group CBlock (Maybe CBlock)
  | CDo CBlock
  deriving (Show, Generic)

type Bin = WithSrc Bin'
data Bin'
  = Juxtapose
  | EvalBinOp String
  | Ampersand
  | DepAmpersand
  | IndexingDot
  | Comma
  | DepComma
  | Colon
  | DoubleColon
  | Dollar
  | Arrow Arrow
  | FatArrow  -- =>
  | Question
  | Pipe
  | Equal
  deriving (Eq, Ord, Show, Generic)

interp_operator :: String -> Bin'
interp_operator = \case
  "&"   -> Ampersand
  "&>"  -> DepAmpersand
  "."   -> IndexingDot
  ","   -> Comma
  ",>"  -> DepComma
  ":"   -> Colon
  "::"  -> DoubleColon
  "$"   -> Dollar
  "->"  -> Arrow PlainArrow
  "?->" -> Arrow ImplicitArrow
  "?=>" -> Arrow ClassArrow
  "--o" -> Arrow LinArrow
  "=>"  -> FatArrow
  "?"   -> Question
  "|"   -> Pipe
  "="   -> Equal
  " "   -> Juxtapose  -- The parser in the precedence table canonicalizes already
  name  -> EvalBinOp $ "(" <> name <> ")"

-- We can add others, like @{ or [| or whatever
data Bracket = Square | Curly | CurlyPipe
  deriving (Show, Generic)

data LabelPrefix
  = PlainLabel
  | RecordIsoLabel
  | VariantIsoLabel
  | RecordZipIsoLabel
  | VariantZipIsoLabel
  deriving (Show, Generic)

data ForKind
  = KFor
  | KFor_
  | KRof
  | KRof_
  | KView
  deriving (Show, Generic)

data CBlock = CBlock [CDecl] -- last decl should be a CExpr
  deriving (Show, Generic)

pattern DeclTopDecl :: LetAnn -> CDecl -> CTopDecl
pattern DeclTopDecl ann d <- WithSrc _ (CDecl ann d) where
  DeclTopDecl ann d@(WithSrc src _) = WithSrc src (CDecl ann d)

pattern ExprDecl :: Group -> CDecl
pattern ExprDecl g <- WithSrc _ (CExpr g) where
  ExprDecl g@(WithSrc src _) = WithSrc src (CExpr g)

pattern ExprBlock :: Group -> CBlock
pattern ExprBlock g <- (CBlock [ExprDecl g]) where
  ExprBlock g = CBlock [ExprDecl g]

pattern Bracketed :: Bracket -> Group -> Group
pattern Bracketed b g <- (WithSrc _ (CBracket b g)) where
  Bracketed b g = WithSrc Nothing $ CBracket b g

pattern Binary :: Bin' -> Group -> Group -> Group
pattern Binary op lhs rhs <- (WithSrc _ (CBin (WithSrc _ op) lhs rhs)) where
  Binary op lhs rhs = joinSrc lhs rhs $ CBin (WithSrc Nothing op) lhs rhs

pattern Prefix :: SourceName -> Group -> Group
pattern Prefix op g <- (WithSrc _ (CPrefix op g)) where
  Prefix op g = WithSrc Nothing $ CPrefix op g

pattern Postfix :: SourceName -> Group -> Group
pattern Postfix op g <- (WithSrc _ (CPostfix op g)) where
  Postfix op g = WithSrc Nothing $ CPostfix op g

pattern Identifier :: SourceName -> Group
pattern Identifier name <- (WithSrc _ (CIdentifier name)) where
  Identifier name = WithSrc Nothing $ CIdentifier name

binOptL :: Bin' -> Group -> (Maybe Group, Maybe Group)
binOptL tag = \case
  (WithSrc _ (CParens (ExprBlock content))) -> binOptL tag content
  (Binary tag' lhs rhs) | tag == tag' -> (Just lhs, Just rhs)
  rhs -> (Nothing, Just rhs)

binOptR :: Bin' -> Group -> (Maybe Group, Maybe Group)
binOptR tag = \case
  (WithSrc _ (CParens (ExprBlock content))) -> binOptR tag content
  (Binary tag' lhs rhs) | tag == tag' -> (Just lhs, Just rhs)
  lhs -> (Just lhs, Nothing)

-- Unroll a nest of binary applications of the given Bin' into a flat
-- list.  If the top group is not such a binary application, return it
-- as a singleton.
nary :: Bin' -> Group -> [Group]
nary op g = go g [] where
  go (Binary binOp lhs rhs) rest | op == binOp = go lhs $ go rhs rest
  go (WithSrc _ CEmpty) rest = rest
  go grp rest = grp:rest

-- Roll up a list of groups as binary applications, associating to the left.
nary' :: Bin' -> [Group] -> Group
nary' _ [] = WithSrc Nothing CEmpty
nary' _ (lst:[]) = lst
nary' op (g1:(g2:rest)) = go (Binary op g1 g2) rest where
  go lhs [] = lhs
  go lhs (g:gs) = go (Binary op lhs g) gs

-- === Parser (top-level structure) ===

sourceBlock :: Parser CSourceBlock
sourceBlock = do
  offset <- getOffset
  pos <- getSourcePos
  (src, (level, b)) <- withSource $ withRecovery recover $ do
    level <- logLevel <|> logTime <|> logBench <|> return LogNothing
    b <- sourceBlock'
    return (level, b)
  return $ SourceBlockP (unPos (sourceLine pos)) offset level src b

recover :: ParseError Text Void -> Parser (LogLevel, CSourceBlock')
recover e = do
  pos <- liftM statePosState getParserState
  reachedEOF <-  try (mayBreak sc >> eof >> return True)
             <|> return False
  consumeTillBreak
  let errmsg = errorBundlePretty (ParseErrorBundle (e :| []) pos)
  return (LogNothing, CUnParseable reachedEOF errmsg)

importModule :: Parser CSourceBlock'
importModule = CMisc . ImportModule . OrdinaryModule <$> do
  keyWord ImportKW
  s <- anyCaseName
  eol
  return s

declareForeign :: Parser CSourceBlock'
declareForeign = do
  keyWord ForeignKW
  foreignName <- strLit
  b <- lowerName
  void $ label "type annotation" $ sym ":"
  ty <- cGroup
  eol
  return $ CDeclareForeign foreignName b ty

declareCustomLinearization :: Parser CSourceBlock'
declareCustomLinearization = do
  zeros <- (keyWord CustomLinearizationSymbolicKW $> SymbolicZeros)
       <|> (keyWord CustomLinearizationKW $> InstantiateZeros)
  fun <- anyCaseName
  linearization <- cGroup
  eol
  return $ CDeclareCustomLinearization fun zeros linearization

consumeTillBreak :: Parser ()
consumeTillBreak = void $ manyTill anySingle $ eof <|> void (try (eol >> eol))

logLevel :: Parser LogLevel
logLevel = do
  void $ try $ lexeme $ char '%' >> string "passes"
  passes <- many passName
  eol
  case passes of
    [] -> return LogAll
    _ -> return $ LogPasses passes

logTime :: Parser LogLevel
logTime = do
  void $ try $ lexeme $ char '%' >> string "time"
  eol
  return PrintEvalTime

logBench :: Parser LogLevel
logBench = do
  void $ try $ lexeme $ char '%' >> string "bench"
  benchName <- strLit
  eol
  return $ PrintBench benchName

passName :: Parser PassName
passName = choice [thisNameString s $> x | (s, x) <- passNames]

passNames :: [(Text, PassName)]
passNames = [(T.pack $ show x, x) | x <- [minBound..maxBound]]

sourceBlock' :: Parser CSourceBlock'
sourceBlock' =
      proseBlock
  <|> topLevelCommand
  <|> liftM CTopDecl (dataDef <* eolf)
  <|> liftM CTopDecl (DeclTopDecl PlainLet <$> instanceDef True  <* eolf)
  <|> liftM CTopDecl (DeclTopDecl PlainLet <$> instanceDef False <* eolf)
  <|> liftM CTopDecl (interfaceDef <* eolf)
  <|> liftM CTopDecl (effectDef <* eolf)
  <|> liftM CTopDecl (handlerDef <* eolf)
  <|> liftM CTopDecl (topLet <* eolf)
  <|> hidden (some eol >> return (CMisc EmptyLines))
  <|> hidden (sc >> eol >> return (CMisc CommentLine))

proseBlock :: Parser CSourceBlock'
proseBlock = label "prose block" $ char '\'' >> fmap (CMisc . ProseBlock . fst) (withSource consumeTillBreak)

topLevelCommand :: Parser CSourceBlock'
topLevelCommand =
      importModule
  <|> declareForeign
  <|> declareCustomLinearization
  <|> (CMisc . QueryEnv <$> envQuery)
  <|> explicitCommand
  <?> "top-level command"

envQuery :: Parser EnvQuery
envQuery = string ":debug" >> sc >> (
      (DumpSubst        <$  (string "env"   >> sc))
  <|> (InternalNameInfo <$> (string "iname" >> sc >> rawName))
  <|> (SourceNameInfo   <$> (string "sname" >> sc >> anyName)))
       <* eol
  where
    rawName :: Parser RawName
    rawName = undefined -- RawName <$> (fromString <$> anyName) <*> intLit

explicitCommand :: Parser CSourceBlock'
explicitCommand = do
  cmdName <- char ':' >> nameString
  cmd <- case cmdName of
    "p"       -> return $ EvalExpr Printed
    "t"       -> return $ GetType
    "html"    -> return $ EvalExpr RenderHtml
    "export"  -> ExportFun <$> nameString
    _ -> fail $ "unrecognized command: " ++ show cmdName
  e <- cBlock <* eolf
  return $ case (e, cmd) of
    (ExprBlock (WithSrc _ (CIdentifier v)), GetType) -> CMisc $ GetNameType v
    _ -> CCommand cmd e

dataDef :: Parser CTopDecl
dataDef = withSrc do
  keyWord DataKW
  tyName <- anyName
  args <- many cGroupNoJuxtEqual
  sym "="
  dataCons <- onePerLine nameAndArgs
  return $ CData tyName args dataCons

interfaceDef :: Parser CTopDecl
interfaceDef = withSrc do
  keyWord InterfaceKW
  superclasses <- superclassConstraints
  className <- nameAndArgs
  methodDecls <- onePerLine do
    methodName <- cNames
    void $ label "type annotation" $ sym ":"
    ty <- cGroup
    return (methodName, ty)
  return $ CInterface superclasses className methodDecls

superclassConstraints :: Parser [Group]
superclassConstraints = optionalMonoid $ brackets $ cNames `sepBy` sym ","

effectDef :: Parser CTopDecl
effectDef = withSrc do
  keyWord EffectKW
  effName <- anyName
  sigs <- opSigList
  return $ CEffectDecl (fromString effName) sigs

opSigList :: Parser [(SourceName, UResumePolicy, Group)]
opSigList = onePerLine do
  policy <- resumePolicy
  v <- anyName
  void $ sym ":"
  ty <- cGroup
  return (fromString v, policy, ty)

resumePolicy :: Parser UResumePolicy
resumePolicy =  (keyWord JmpKW $> UNoResume)
            <|> (keyWord DefKW $> ULinearResume)
            <|> (keyWord CtlKW $> UAnyResume)

handlerDef :: Parser CTopDecl
handlerDef = withSrc do
  keyWord HandlerKW
  handlerName <- anyName
  keyWord OfKW
  effectName <- anyName
  bodyTyArg <- anyName
  args <- cGroupNoColon <|> pure (WithSrc Nothing CEmpty)
  void $ sym ":"
  retTy <- cGroupNoEqual
  methods <- onePerLine effectOpDef
  return $ CHandlerDecl (fromString handlerName) (fromString effectName)
    (fromString bodyTyArg) args retTy methods

effectOpDef :: Parser (SourceName, Maybe UResumePolicy, CBlock)
effectOpDef = do
  (rp, v) <- (keyWord ReturnKW $> (Nothing, "return"))
         <|> ((,) <$> (Just <$> resumePolicy) <*> anyName)
  sym "="
  rhs <- cBlock
  return ((fromString v), rp, rhs)

nameAndArgs :: Parser NameAndArgs
nameAndArgs = do
  n <- anyName
  args <- many cGroupNoBrackets
  return (n, args)

topLet :: Parser CTopDecl
topLet = withSrc do
  lAnn <- (char '@' >> letAnnStr <* (eol <|> sc)) <|> return PlainLet
  decl <- cDecl
  return $ CDecl lAnn decl
  where
    letAnnStr :: Parser LetAnn
    letAnnStr = (string "noinline"   $> NoInlineLet)

onePerLine :: Parser a -> Parser [a]
onePerLine p =   liftM (:[]) p
             <|> (withIndent $ mayNotBreak $ p `sepBy1` try nextLine)
{-# INLINE onePerLine #-}

-- === Groups ===

-- Parse a block, which could also just be a group
cBlock :: Parser CBlock
cBlock = cBlock' >>= \case
  Left blk -> return blk
  Right ex -> return $ ExprBlock ex

-- Parse a block or a group but tell me which (i.e., whether it was indented or not)
cBlock' :: Parser (Either CBlock Group)
cBlock' = Left <$> realBlock <|> Right <$> cGroupNoSeparators where
  realBlock = withIndent $
    CBlock <$> (mayNotBreak $ cDecl `sepBy1` (semicolon <|> try nextLine))

cDecl :: Parser CDecl
cDecl = instanceDef True <|> (do
  lhs <- funDefLet <|> (try simpleLet)
  rhs <- cBlock
  return $ lhs rhs) <|> (ExprDecl <$> cGroup)

instanceDef :: Bool -> Parser CDecl
instanceDef isNamed = withSrc $ do
  name <- case isNamed of
    False -> keyWord InstanceKW $> Nothing
    True  -> keyWord NamedInstanceKW *> (Just . fromString <$> anyName) <* sym ":"
  header <- cGroup
  givens <- optional (keyWord GivenKW >> cGroup)
  methods <- onePerLine instanceMethod
  return $ CInstance header (fromMaybe (WithSrc Nothing CEmpty) givens) methods name

instanceMethod :: Parser (SourceName, CBlock)
instanceMethod = do
  v <- anyName
  mayNotBreak $ sym "="
  rhs <- cBlock
  return (fromString v, rhs)

simpleLet :: Parser (CBlock -> CDecl)
simpleLet = withSrc1 $ do
  binder <- cGroupNoEqual
  next <- nextChar
  case next of
    '=' -> sym  "=" >> return (CLet  binder)
    '<' -> sym "<-" >> return (CBind binder)
    _   -> fail ""

funDefLet :: Parser (CBlock -> CDecl)
funDefLet = label "function definition" (mayBreak $ withSrc1 do
  keyWord DefKW
  name <- anyName
  args <- cGroupNoColon <|> pure (WithSrc Nothing CEmpty)
  typeAnn <- optional (sym ":" >> cGroupNoEqual)
  return (CDef name args typeAnn)) <* sym "="

cGroup :: Parser Group
cGroup = makeExprParser (withSrc leafGroup) ops

-- Like cGroup but does not allow juxtaposition or . at the top level
cGroupNoJuxtDot :: Parser Group
cGroupNoJuxtDot = makeExprParser (withSrc leafGroup) $
  withoutOp "space" $ withoutOp "." ops

-- Like cGroup but does not allow juxtaposition or = at the top level
cGroupNoJuxtEqual :: Parser Group
cGroupNoJuxtEqual = makeExprParser (withSrc leafGroup) $
  withoutOp "space" $ withoutOp "=" ops

-- Like cGroup but does not allow square brackets `[]`, juxtaposition,
-- or `=` at the top level
cGroupNoBrackets :: Parser Group
cGroupNoBrackets = makeExprParser (withSrc leafGroupNoBrackets) $
  withoutOp "space" $ withoutOp "=" ops

-- Like cGroup but does not allow : or =
cGroupNoColon :: Parser Group
cGroupNoColon = makeExprParser (withSrc leafGroup) $
  withoutOp ":" $ withoutOp "=" ops

-- Like cGroup but does not allow =
cGroupNoEqual :: Parser Group
cGroupNoEqual = makeExprParser (withSrc leafGroup) $
  withoutOp "=" ops

cGroupNoArrow :: Parser Group
cGroupNoArrow = makeExprParser (withSrc leafGroup) $
  withoutOp "->" ops

cGroupNoSeparators :: Parser Group
cGroupNoSeparators = makeExprParser (withSrc leafGroup) $
  withoutOp "?" $ withoutOp "," $ withoutOp "&" $ withoutOp "|" ops

cGroupInBraces :: Parser Group
cGroupInBraces = optional separator >>= \case
  Just sep -> afterSep sep
  Nothing -> contents
  where
    afterSep sep = Binary sep (WithSrc Nothing CEmpty) <$> contents
                   <|> pure (Binary sep (WithSrc Nothing CEmpty) (WithSrc Nothing CEmpty))
    separator =     sym "&" $> Ampersand
                <|> sym "|" $> Pipe
                <|> sym "?" $> Question
                <|> sym "," $> Comma
    contents = makeExprParser (withSrc leafGroupTrailingEmpty)
      $ replaceOp "@" (Expr.Prefix $ unOp CPrefix "@")
      $ replaceOp "space" noTrailingJuxt $ ops
    noTrailingJuxt = Expr.InfixL $ opWithSrc $ (sc >> notFollowedBy rBrace) $> (binApp Juxtapose)

cLam :: Parser Group'
cLam = do
  sym "\\"
  bs <- many cGroupNoJuxtDot
  mayNotBreak $ sym "."
  body <- cBlock
  return $ CLambda bs body

cFor :: Parser Group'
cFor = do
  kw <- forKW
  indices <- many cGroupNoJuxtDot
  mayNotBreak $ sym "."
  body <- cBlock
  return $ CFor kw indices body
  where forKW =     keyWord ForKW  $> KFor
                <|> keyWord For_KW $> KFor_
                <|> keyWord RofKW  $> KRof
                <|> keyWord Rof_KW $> KRof_
                <|> keyWord ViewKW $> KView

cCase :: Parser Group'
cCase = do
  keyWord CaseKW
  scrut <- cGroup
  keyWord OfKW
  alts <- onePerLine $ (,) <$> cGroupNoArrow <*> (sym "->" *> cBlock)
  return $ CCase scrut alts

-- We support the following syntaxes for `if`:
-- - 1-armed then-newline
--     if predicate
--       then consequent
--     if predicate
--       then
--         consequent1
--         consequent2
-- - 2-armed then-newline else-newline
--     if predicate
--       then consequent
--       else alternate
--   and the three other versions where the consequent or the
--   alternate are themselves blocks
-- - 1-armed then-inline
--     if predicate then consequent
--     if predicate then
--       consequent1
--       consequent2
-- - 2-armed then-inline else-inline
--     if predicate then consequent else alternate
--     if predicate then consequent else
--       alternate1
--       alternate2
-- - Notably, an imagined 2-armed then-inline else-newline
--     if predicate then
--       consequent1
--       consequent2
--     else alternate
--   is not an option, because the indentation lines up badly.  To wit,
--   one would want the `else` to be indented relative to the `if`,
--   but outdented relative to the consequent block, and if the `then` is
--   inline there is no indentation level that does that.
-- - Last candiate is
--      if predicate
--        then consequent else alternate
--      if predicate
--        then consequent else
--          alternate1
--          alternate2
cIf :: Parser Group'
cIf = mayNotBreak do
  keyWord IfKW
  predicate <- cGroup
  (cons, alt) <- thenSameLine <|> thenNewLine
  return $ CIf predicate cons alt

thenSameLine :: Parser (CBlock, Maybe CBlock)
thenSameLine = do
  keyWord ThenKW
  cBlock' >>= \case
    (Left blk) -> do
      let msg = ("No `else` may follow same-line `then` and indented consequent"
                  ++ "; indent and align both `then` and `else`, or write the "
                  ++ "whole `if` on one line.")
      mayBreak $ noElse msg
      return (blk, Nothing)
    (Right ex) -> do
      alt <- optional
        $ (keyWord ElseKW >> cBlock)
          <|> (lookAhead (try $ withIndent (mayNotBreak $ keyWord ElseKW))
               >> withIndent (mayNotBreak $ keyWord ElseKW >> cBlock))
      return (ExprBlock ex, alt)

thenNewLine :: Parser (CBlock, Maybe CBlock)
thenNewLine = withIndent $ mayNotBreak $ do
  keyWord ThenKW
  cBlock' >>= \case
    (Left blk) -> do
      alt <- do
        -- With `mayNotBreak`, this just forbids inline else
        noElse ("Same-line `else` may not follow indented consequent;"
                ++ " put the `else` on the next line.")
        optional $ do
          try $ nextLine >> keyWord ElseKW
          cBlock
      return (blk, alt)
    (Right ex) -> do
      void $ optional $ try nextLine
      alt <- optional $ keyWord ElseKW >> cBlock
      return (ExprBlock ex, alt)

noElse :: String -> Parser ()
noElse msg = (optional $ try $ sc >> keyWord ElseKW) >>= \case
  Just () -> fail msg
  Nothing -> return ()

leafGroupTrailingEmpty :: Parser Group'
leafGroupTrailingEmpty = do
  next <- nextChar
  case next of
    '}' -> return CEmpty
    ']' -> return CEmpty
    ')' -> return CEmpty
    _   -> leafGroup

leafGroup :: Parser Group'
leafGroup = do
  next <- nextChar
  case next of
    '[' -> CBracket Square <$> (emptyBrackets <|> brackets cGroup)
    _   -> leafGroupNoBrackets
  where emptyBrackets = withSrc $ symbol "[]" $> CEmpty

leafGroupNoBrackets :: Parser Group'
leafGroupNoBrackets = do
  next <- nextChar
  case next of
    '_'  -> underscore $> CHole
    '('  -> (symbol "()" $> (CParens $ ExprBlock $ WithSrc Nothing CEmpty))
            <|> CIdentifier <$> symName
            <|> parens (CParens . ExprBlock <$> cGroupNoEqual)
    '{'  -> curlyBraced
    '\"' -> CString <$> strLit
    '\'' -> CChar <$> charLit
    '%'  -> do
      name <- primName
      case strToPrimName name of
        Just prim -> CPrim prim <$> many cGroupNoJuxtDot
        Nothing   -> fail $ "Unrecognized primitive: " ++ name
    '#'  -> liftM2 CLabel labelPrefix fieldLabel
    _ | isDigit next -> (    CNat   <$> natLit
                         <|> CFloat <$> doubleLit)
    '\\' -> cLam
    -- For exprs include view, for, rof, for_, rof_
    'v'  -> cFor  <|> CIdentifier <$> anyName
    'f'  -> cFor  <|> CIdentifier <$> anyName
    'r'  -> cFor  <|> CIdentifier <$> (anyName <|> (keyWord ResumeKW >> return "resume"))
    'c'  -> cCase <|> CIdentifier <$> anyName
    'i'  -> cIf   <|> CIdentifier <$> anyName
    'd'  -> (CDo <$> (mayNotBreak $ keyWord DoKW >> cBlock)) <|> CIdentifier <$> anyName
    _    -> CIdentifier <$> anyName

-- What does an open curly brace actually mean in Dex?  It could be
-- - A variant, which is defined by being bracketed with {| and |}
-- - A fieldful thing, which is syntactically weird because
--   - The separator (one of &, |, ?, and comma) may appear immediately after
--     the open brace, to disambiguate a single-element fieldful thing
--     - However, comma usually doesn't, because {field} defaults to
--       a normal record, which is what {,field} would mean
--   - The separator may be the only contents of the braces, to disambiguate
--     a zero-element fieldful thing
--   - The separator is also permitted to dangle at the end, supporting
--     diff-friendly lists
--   - The @ becomes a prefix operator at the top level, meaning dynamic fields
--     (normally it's syntactic sugar for `from_ordinal`)
-- - An effect row, which may (and often does) have a leading |
--   - This just looks like a unary fieldful thing delimited by |
--
-- Observe that there is a local ambiguity between variant data and a
-- singleton variant type, both of which start with "{|"
curlyBraced :: Parser Group'
curlyBraced = try (bracketed (symbol "{|") (symbol "|}") $ CBracket CurlyPipe <$> cGroup)
              <|> CBracket Curly <$> (withSrc $ symbol "{}" $> CEmpty)
              <|> braces (CBracket Curly <$> cGroupInBraces)

-- A `PrecTable` is enough information to (i) remove or replace
-- operators for special contexts, and (ii) build the input structure
-- for Expr.makeExprParser.
type PrecTable a = [[(SourceName, Expr.Operator Parser a)]]

makeExprParser :: Parser a -> PrecTable a -> Parser a
makeExprParser p tbl = Expr.makeExprParser p tbl' where
  tbl' = map (map snd) tbl

withoutOp :: SourceName -> PrecTable a -> PrecTable a
withoutOp op tbl = map (filter ((/= op) . fst)) tbl

replaceOp :: SourceName -> Expr.Operator Parser a -> PrecTable a -> PrecTable a
replaceOp name op tbl = map (map replace) tbl where
  replace (name', op') | name' == name = (name, op)
                       | otherwise = (name', op')

ops :: PrecTable Group
ops =
  [ [symOpL   ".", symOpL   "!"]
  , [juxtaposition]
  , [unOpPre  "-", unOpPre  "+"]
  , [backquote]
  -- Other ops with default fixity
  , [other]
  , [symOpL   "*", symOpL   "/"]
  , [symOpL  ".*", symOpL  "*."]
  , [symOpL ".**", symOpL "**."]
  , [symOpL  "**"]
  , [symOpL   "+", symOpL   "-"]
  , [symOpL  "-|"]
  , [symOpL "+>>"]
  , [symOpL  "<>"]
  , [symOpN  "~~"]
  , [symOpN   "<", symOpN  "<=", symOpN ">", symOpN ">="]
  , [symOpN  "==", symOpN  "!="]
  , [symOpL  "&&"]
  , [symOpL  "||"]
  , [unOpPre "..", unOpPre "..<", unOpPost "..", unOpPost "<.."]
  , [symOpR  "=>"]
  , [symOpR  "->", symOpR "--o", symOpR "?->", symOpR "?=>"]
  , [symOpL ">>>"]
  , [symOpL "<<<"]
  , [symOpL "&>>"]
  , [symOpL "<<&"]
  , [symOpL   "@"]
  , [unOpPre  "@"]
  , [unOpPre "@..."]
  , [unOpPre "..."]
  , [symOpN  "::"]
  , [symOpL  "|>"]
  , [symOpR   "$"]
  , [symOpN  "+=", symOpN  ":="]
  -- Associate right so the mistaken utterance foo : i:Fin 4 => (..i)
  -- groups as a bad pi type rather than a bad binder
  , [symOpR   ":"]
  , [symOpL   "="]
  -- Single-expression bodies for if, lambda, for, case, and do
  -- notionally have this precedence.
  -- This means that, for example,
  --   \x y. foo bar baz, stuff
  -- will group as
  --   (\x y. foo bar baz), stuff
  -- not
  --   \x y. (foo bar baz, stuff)
  -- We do this so that lambdas may be written inside pairs and records.
  -- This is achieved by cBlock invoking cGroupNoSeparators rather than cGroup.
  , [symOpL   "?"]
  -- Weak decision to associate `,` and `&` to the right because n-ary
  -- tuples are internally represented curried, so this puts the new
  -- element in front.
  , [symOpR   ","]
  , [symOpR  ",>"]
  , [symOpR   "&"]
  , [symOpR  "&>"]
  , [symOpL   "|"]
  ] where
  juxtaposition = ("space", Expr.InfixL $ opWithSrc $ sc $> (binApp Juxtapose))
  other = ("other", anySymOp)
  backquote = ("backquote", Expr.InfixL $ opWithSrc $ backquoteName >>= (return . binApp . EvalBinOp))

labelPrefix :: Parser LabelPrefix
labelPrefix = sym "#" $> RecordIsoLabel
  <|> sym "##" $> PlainLabel
  <|> sym "#?" $> VariantIsoLabel
  <|> sym "#&" $> RecordZipIsoLabel
  <|> sym "#|" $> VariantZipIsoLabel

opWithSrc :: Parser (SrcPos -> a -> a -> a)
          -> Parser (a -> a -> a)
opWithSrc p = do
  (f, pos) <- withPos p
  return $ f pos
{-# INLINE opWithSrc #-}

anySymOp :: Expr.Operator Parser Group
anySymOp = Expr.InfixL $ opWithSrc $ do
  s <- label "infix operator" (mayBreak anySym)
  return $ binApp $ interp_operator s

infixSym :: SourceName -> Parser ()
infixSym s = mayBreak $ sym $ T.pack s

symOpN :: SourceName -> (SourceName, Expr.Operator Parser Group)
symOpN s = (s, Expr.InfixN $ symOp s)

symOpL :: SourceName -> (SourceName, Expr.Operator Parser Group)
symOpL s = (s, Expr.InfixL $ symOp s)

symOpR :: SourceName -> (SourceName, Expr.Operator Parser Group)
symOpR s = (s, Expr.InfixR $ symOp s)

symOp :: SourceName -> Parser (Group -> Group -> Group)
symOp s = opWithSrc $ do
  label "infix operator" (infixSym s)
  return $ binApp $ interp_operator s

unOpPre :: SourceName -> (SourceName, Expr.Operator Parser Group)
unOpPre s = (s, Expr.Prefix $ unOp CPrefix s)

unOpPost :: SourceName -> (SourceName, Expr.Operator Parser Group)
unOpPost s = (s, Expr.Postfix $ unOp CPostfix s)

unOp :: (SourceName -> Group -> Group') -> SourceName -> Parser (Group -> Group)
unOp f s = do
  ((), pos) <- withPos $ sym $ fromString s
  return \g@(WithSrc grpPos _) -> WithSrc (joinPos (Just pos) grpPos) $ f s g

binApp :: Bin' -> SrcPos -> Group -> Group -> Group
binApp f pos x y = joinSrc3 f' x y $ CBin f' x y
  where f' = WithSrc (Just pos) f

cNames :: Parser Group
cNames = nary' Juxtapose <$> map (fmap CIdentifier) <$> many (withSrc anyName)

withSrc :: Parser a -> Parser (WithSrc a)
withSrc p = do
  (x, pos) <- withPos p
  return $ WithSrc (Just pos) x

withSrc1 :: Parser (a -> b) -> Parser (a -> WithSrc b)
withSrc1 p = do
  (f, pos) <- withPos p
  return $ WithSrc (Just pos) . f

joinSrc :: WithSrc a1 -> WithSrc a2 -> a3 -> WithSrc a3
joinSrc (WithSrc p1 _) (WithSrc p2 _) x = WithSrc (joinPos p1 p2) x

joinSrc3 :: WithSrc a1 -> WithSrc a2 -> WithSrc a3 -> a4 -> WithSrc a4
joinSrc3 (WithSrc p1 _) (WithSrc p2 _) (WithSrc p3 _) x =
  WithSrc (concatPos [p1, p2, p3]) x

joinPos :: Maybe SrcPos -> Maybe SrcPos -> Maybe SrcPos
joinPos Nothing p = p
joinPos p Nothing = p
joinPos (Just (l, h)) (Just (l', h')) = Just (min l l', max h h')

jointPos :: WithSrc a1 -> WithSrc a2 -> Maybe SrcPos
jointPos (WithSrc p1 _) (WithSrc p2 _) = joinPos p1 p2

concatPos :: [Maybe SrcPos] -> Maybe SrcPos
concatPos [] = Nothing
concatPos (pos:rest) = foldl joinPos pos rest

-- === primitive constructors and operators ===

strToPrimName :: String -> Maybe PrimName
strToPrimName s = M.lookup s primNames

primNameToStr :: PrimName -> String
primNameToStr prim = case lookup prim $ map swap $ M.toList primNames of
  Just s  -> s
  Nothing -> show prim

showPrimName :: PrimName -> String
showPrimName prim = primNameToStr prim
{-# NOINLINE showPrimName #-}

primNames :: M.Map String PrimName
primNames = M.fromList
  [ ("ask"      , UMAsk), ("mextend", UMExtend)
  , ("get"      , UMGet), ("put"    , UMPut)
  , ("while"    , UWhile)
  , ("linearize", ULinearize), ("linearTranspose", UTranspose)
  , ("runReader", URunReader), ("runWriter"      , URunWriter), ("runState", URunState)
  , ("runIO"    , URunIO    ), ("catchException" , UCatchException) ]

-- -- TODO: Can we derive these generically? Or use Show/Read?
-- --       (These prelude-only names don't have to be pretty.)
-- primExprNames :: M.Map String (PrimExpr CoreIR ())
-- primExprNames = M.fromList []
-- primExprNames = M.fromList
--   [ ("iadd" , binary IAdd),  ("isub"  , binary ISub)
--   , ("imul" , binary IMul),  ("fdiv"  , binary FDiv)
--   , ("fadd" , binary FAdd),  ("fsub"  , binary FSub)
--   , ("fmul" , binary FMul),  ("idiv"  , binary IDiv)
--   , ("irem" , binary IRem)
--   , ("fpow" , binary FPow)
--   , ("and"  , binary BAnd),  ("or"    , binary BOr )
--   , ("not"  , unary  BNot),  ("xor"   , binary BXor)
--   , ("shl"  , binary BShL),  ("shr"   , binary BShR)
--   , ("ieq"  , binary (ICmp P.Equal)), ("feq", binary (FCmp P.Equal))
--   , ("igt"  , binary (ICmp Greater)), ("fgt", binary (FCmp Greater))
--   , ("ilt"  , binary (ICmp Less)),    ("flt", binary (FCmp Less))
--   , ("fneg" , unary  FNeg)
--   , ("exp"  , unary  Exp),   ("exp2"  , unary Exp2)
--   , ("log"  , unary  Log),   ("log2"  , unary Log2), ("log10" , unary Log10)
--   , ("sin"  , unary  Sin),   ("cos"   , unary Cos)
--   , ("tan"  , unary  Tan),   ("sqrt"  , unary Sqrt)
--   , ("floor", unary  Floor), ("ceil"  , unary Ceil), ("round", unary Round)
--   , ("log1p", unary  Log1p), ("lgamma", unary LGamma)
--   , ("erf", unary Erf),      ("erfc", unary Erfc)
--   , ("sumToVariant"   , OpExpr $ SumToVariant ())
--   , ("throwError"     , OpExpr $ ThrowError ())
--   , ("throwException" , OpExpr $ ThrowException ())
--   , ("indexRef"   , OpExpr $ IndexRef () ())
--   , ("select"     , OpExpr $ Select () () ())
--   , ("TyKind"    , TCExpr $ TypeKind)
--   , ("Float64"   , TCExpr $ BaseType $ Scalar Float64Type)
--   , ("Float32"   , TCExpr $ BaseType $ Scalar Float32Type)
--   , ("Int64"     , TCExpr $ BaseType $ Scalar Int64Type)
--   , ("Int32"     , TCExpr $ BaseType $ Scalar Int32Type)
--   , ("Word8"     , TCExpr $ BaseType $ Scalar Word8Type)
--   , ("Word32"    , TCExpr $ BaseType $ Scalar Word32Type)
--   , ("Word64"    , TCExpr $ BaseType $ Scalar Word64Type)
--   , ("Int32Ptr"  , TCExpr $ BaseType $ ptrTy $ Scalar Int32Type)
--   , ("Word8Ptr"  , TCExpr $ BaseType $ ptrTy $ Scalar Word8Type)
--   , ("Word32Ptr" , TCExpr $ BaseType $ ptrTy $ Scalar Word32Type)
--   , ("Word64Ptr" , TCExpr $ BaseType $ ptrTy $ Scalar Word64Type)
--   , ("Float32Ptr", TCExpr $ BaseType $ ptrTy $ Scalar Float32Type)
--   , ("PtrPtr"    , TCExpr $ BaseType $ ptrTy $ ptrTy $ Scalar Word8Type)
--   , ("Nat"       , TCExpr $ Nat)
--   , ("Fin"       , TCExpr $ Fin ())
--   , ("Label"     , TCExpr $ LabelType)
--   , ("Ref"       , TCExpr $ RefType (Just ()) ())
--   , ("PairType"  , TCExpr $ ProdType [(), ()])
--   , ("UnitType"  , TCExpr $ ProdType [])
--   , ("EffKind"   , TCExpr $ EffectRowKind)
--   , ("LabeledRowKind", TCExpr $ LabeledRowKindTC)
--   , ("pair", ConExpr $ ProdCon [(), ()])
--   , ("fstRef", OpExpr $ ProjRef 0 ())
--   , ("sndRef", OpExpr $ ProjRef 1 ())
--   , ("cast", OpExpr  $ CastOp () ())
--   , ("bitcast", OpExpr $ BitcastOp () ())
--   , ("alloc", OpExpr $ IOAlloc (Scalar Word8Type) ())
--   , ("free" , OpExpr $ IOFree ())
--   , ("ptrOffset", OpExpr $ PtrOffset () ())
--   , ("ptrLoad"  , OpExpr $ PtrLoad ())
--   , ("ptrStore" , OpExpr $ PtrStore () ())
--   , ("dataConTag", OpExpr $ SumTag ())
--   , ("toEnum"    , OpExpr $ ToEnum () ())
--   , ("outputStream", OpExpr $ OutputStream)
--   , ("newtype"    , ConExpr $ Newtype () ())
--   , ("projNewtype", OpExpr $ ProjBaseNewtype ())
--   , ("projMethod0", OpExpr $ ProjMethod () 0)
--   , ("projMethod1", OpExpr $ ProjMethod () 1)
--   , ("projMethod2", OpExpr $ ProjMethod () 2)
--   , ("explicitDict", ConExpr $ ExplicitDict () ())
--   , ("explicitApply", OpExpr $ ExplicitApply () ())
--   , ("monoLit", OpExpr $ MonoLiteral ())
--   ]
--   where
--     binary op = OpExpr $ BinOp op () ()
--     unary  op = OpExpr $ UnOp  op ()
--     ptrTy  ty = PtrType (CPU, ty)
