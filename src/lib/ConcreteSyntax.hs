-- Copyright 2022 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module ConcreteSyntax (
  mustParseit, sourceBlocks, sourceBlock, joinPos,
  keyWordStrs, showPrimName,
  binOptL, binOptR, nary,
  WithSrc (..), CSourceBlock, CSourceBlock' (..),
  CTopDecl (..), CBlock (..), CDecl (..), Group, Group'(..),
  Bin, Bin' (..), Bracket (..), LabelPrefix (..), ForKind (..),
  pattern ExprBlock, pattern Bracketed,
  pattern Binary, pattern Unary, pattern Identifier) where

import Control.Monad.Combinators.Expr qualified as Expr
import Control.Monad.Reader
import Data.Char
import Data.Functor
import Data.HashSet qualified as HS
import Data.List.NonEmpty (NonEmpty (..))
import Data.Map qualified as M
import qualified Data.Scientific as Scientific
import Data.String (fromString)
import Data.Text (Text)
import Data.Text          qualified as T
import Data.Tuple
import Data.Void
import Data.Word
import GHC.Generics (Generic (..))
import Text.Megaparsec hiding (Label, State)
import Text.Megaparsec.Char hiding (space, eol)
import qualified Text.Megaparsec.Char as MC
import qualified Text.Megaparsec.Char.Lexer as L
import Debug.Trace qualified as Tr

import Err
import LabeledItems
import Name
import Types.Primitives hiding (Equal)
import Types.Primitives qualified as P
import Types.Source

parseit :: Text -> Parser a -> Except a
parseit s p = case parse (runReaderT p (ParseCtx 0 False)) "" s of
  Left e  -> throw ParseErr $ errorBundlePretty e
  Right x -> return x

mustParseit :: Text -> Parser a -> a
mustParseit s p  = case parseit s p of
  Success x -> x
  Failure e -> error $ "This shouldn't happen:\n" ++ pprint e

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
  | CMisc SourceBlockMisc
  | CUnParseable ReachedEOF String
  deriving (Show, Generic)

data CTopDecl
  = CDecl LetAnn CDecl
  | CData Group -- Type constructor name and arguments
      (Maybe Group) -- Optional class constraints
      [Group] -- Constructor names and argument sets
  | CInterface [Group] -- Superclasses
      Group -- Class name and arguments
      -- Method declarations: name, arguments, type.  TODO: Allow operators?
      [(Group, Group)]
  deriving (Show, Generic)

data CDecl
  = CLet Group CBlock
  -- name, header, body.  The header should contain the parameters,
  -- optional effects, and return type
  | CDef SourceName Group CBlock
  -- header, methods, optional name.  The header should contain
  -- the prerequisites, class name, and class arguments.
  | CInstance Group
      [(SourceName, CBlock)] -- Method definitions
      (Maybe SourceName) -- Optional name of instance
  | CExpr Group
  deriving (Show, Generic)

type Group = WithSrc Group'
data Group'
  -- TODO(axch): Be able to parse empty groups where allowed, e.g. {}
  -- for an empty record or record pattern, or () for the nullary pair
  -- constructor (if I want to do that with an empty group)
  = CEmpty
  | CIdentifier SourceName
  | CPrim (PrimExpr Group)
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
  | CBin Bin Group Group -- could encode whitespace-as-application here or add another constructor for it
  | CUn SourceName Group -- covers unary - and unary + among others
  -- The dot `.` wants loose precedence as a delimiter between lambda
  -- arguments and the body, but tight precedence as indexing.
  | CLambda [Group] CBlock
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
  | IndexingDot
  | Comma
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
  "."   -> IndexingDot
  ","   -> Comma
  ":"   -> Colon
  "::"  -> DoubleColon
  "$"   -> Dollar
  "->"  -> Arrow PlainArrow
  "?->" -> Arrow ImplicitArrow
  "?=>" -> Arrow ClassArrow
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

pattern ExprBlock :: Group -> CBlock
pattern ExprBlock g <- (CBlock [CExpr g]) where
  ExprBlock g = CBlock [CExpr g]

pattern Bracketed :: Bracket -> Group -> Group
pattern Bracketed b g <- (WithSrc _ (CBracket b g)) where
  Bracketed b g = WithSrc Nothing $ CBracket b g

pattern Binary :: Bin' -> Group -> Group -> Group
pattern Binary op lhs rhs <- (WithSrc _ (CBin (WithSrc _ op) lhs rhs)) where
  Binary op lhs rhs = joinSrc lhs rhs $ CBin (WithSrc Nothing op) lhs rhs

pattern Unary :: SourceName -> Group -> Group
pattern Unary op g <- (WithSrc _ (CUn op g)) where
  Unary op g = WithSrc Nothing $ CUn op g

pattern Identifier :: SourceName -> Group
pattern Identifier name <- (WithSrc _ (CIdentifier name)) where
  Identifier name = WithSrc Nothing $ CIdentifier name

binOptL :: Bin' -> Group -> (Maybe Group, Maybe Group)
binOptL tag = \case
  (Binary tag' lhs rhs) | tag == tag' -> (Just lhs, Just rhs)
  rhs -> (Nothing, Just rhs)

binOptR :: Bin' -> Group -> (Maybe Group, Maybe Group)
binOptR tag = \case
  (Binary tag' lhs rhs) | tag == tag' -> (Just lhs, Just rhs)
  lhs -> (Just lhs, Nothing)

-- Unroll a nest of binary applications of the given Bin' into a flat
-- list.  If the top group is not such a binary application, return it
-- as a singleton.
nary :: Bin' -> Group -> [Group]
nary op g = go g [] where
  go (Binary binOp lhs rhs) rest | op == binOp = go lhs $ go rhs rest
  go grp rest = grp:rest

-- Roll up a list of groups as binary applications.
nary' :: Bin' -> [Group] -> Group
nary' _ [] = WithSrc Nothing CEmpty
nary' _ (lst:[]) = lst
nary' op (g:rest) = Binary op g $ nary' op rest

data ParseCtx = ParseCtx { curIndent :: Int
                         , canBreak  :: Bool }
type Parser = ReaderT ParseCtx (Parsec Void Text)

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
  <|> liftM CTopDecl (CDecl PlainLet <$> instanceDef True  <* eolf)
  <|> liftM CTopDecl (CDecl PlainLet <$> instanceDef False <* eolf)
  <|> liftM CTopDecl (interfaceDef <* eolf)
  <|> liftM CTopDecl (topLet <* eolf)
  <|> liftM (CCommand (EvalExpr Printed)) (SingletonBlock <$> cGroup <* eolf)
  <|> hidden (some eol >> return (CMisc EmptyLines))
  <|> hidden (sc >> eol >> return (CMisc CommentLine))

proseBlock :: Parser CSourceBlock'
proseBlock = label "prose block" $ char '\'' >> fmap (CMisc . ProseBlock . fst) (withSource consumeTillBreak)

topLevelCommand :: Parser CSourceBlock'
topLevelCommand =
      importModule
  <|> declareForeign
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
    (SingletonBlock (WithSrc _ (CIdentifier v)), GetType) -> CMisc $ GetNameType v
    _ -> CCommand cmd e

dataDef :: Parser CTopDecl
dataDef = do
  keyWord DataKW
  tyCon <- cGroupNoBrackets
  ifaces <- (lookAhead lBracket >> (Just <$> cGroup)) <|> pure Nothing
  sym "="
  dataCons <- onePerLine cGroup
  return $ CData tyCon ifaces dataCons

interfaceDef :: Parser CTopDecl
interfaceDef = do
  keyWord InterfaceKW
  superclasses <- superclassConstraints
  className <- cNames  -- TODO(axch) Insist on a non-empty list of names?
  methodDecls <- onePerLine do
    methodName <- cNames
    void $ label "type annotation" $ sym ":"
    ty <- cGroup
    return (methodName, ty)
  return $ CInterface superclasses className methodDecls

superclassConstraints :: Parser [Group]
superclassConstraints = optionalMonoid $ brackets $ cNames `sepBy` sym ","

topLet :: Parser CTopDecl
topLet = do
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

pattern SingletonBlock :: Group -> CBlock
pattern SingletonBlock g = CBlock [CExpr g]

-- === Groups ===

cBlock :: Parser CBlock
cBlock = realBlock <|> ExprBlock <$> cGroup where
  realBlock = withIndent $
    CBlock <$> (mayNotBreak $ cDecl `sepBy1` (semicolon <|> try nextLine))

cDecl :: Parser CDecl
cDecl = instanceDef True <|> (do
  lhs <- funDefLet <|> (try $ simpleLet <* lookAhead (sym "="))
  rhs <- sym "=" >> cBlock
  return $ lhs rhs) <|> (CExpr <$> cGroup)

instanceDef :: Bool -> Parser CDecl
instanceDef isNamed = do
  name <- case isNamed of
    False -> keyWord InstanceKW $> Nothing
    True  -> keyWord NamedInstanceKW *> (Just . fromString <$> anyName) <* sym ":"
  header <- cGroup
  methods <- onePerLine instanceMethod
  return $ CInstance header methods name

instanceMethod :: Parser (SourceName, CBlock)
instanceMethod = do
  v <- anyName
  sym "="
  rhs <- cBlock
  return (fromString v, rhs)

simpleLet :: Parser (CBlock -> CDecl)
simpleLet = do
  binder <- cGroupNoEqual
  return $ CLet binder

funDefLet :: Parser (CBlock -> CDecl)
funDefLet = label "function definition" $ mayBreak $ do
  keyWord DefKW
  name <- anyName
  header <- cGroupNoEqual
  return (CDef name header)

cGroup :: Parser Group
cGroup = makeExprParser (withSrc leafGroup) ops

-- Like cGroup but does not allow juxtaposition or . at the top level
cGroupNoJuxt :: Parser Group
cGroupNoJuxt = makeExprParser (withSrc leafGroup) $
  withoutOp "space" $ withoutOp "." ops

-- Like cGroup but does not allow square brackets `[]` or `=` at the top level
cGroupNoBrackets :: Parser Group
cGroupNoBrackets = makeExprParser (withSrc leafGroupNoBrackets) $
  withoutOp "=" ops

-- Like cGroup but does not allow =
cGroupNoEqual :: Parser Group
cGroupNoEqual = makeExprParser (withSrc leafGroup) $
  withoutOp "=" ops

cGroupNoArrow :: Parser Group
cGroupNoArrow = makeExprParser (withSrc leafGroup) $
  withoutOp "->" ops

cGroupPrefixAt :: Parser Group
cGroupPrefixAt = makeExprParser (withSrc leafGroup) $
  replaceOp "@" (Expr.Prefix $ unOp "@") ops

cLam :: Parser Group'
cLam = do
  sym "\\"
  bs <- many cGroupNoJuxt
  sym "."
  body <- cBlock
  return $ CLambda bs body

cFor :: Parser Group'
cFor = do
  kw <- forKW
  indices <- many cGroupNoJuxt
  sym "."
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

cIf :: Parser Group'
cIf = do
  keyWord IfKW
  predicate <- cGroup
  keyWord ThenKW
  cons <- cBlock
  alt  <- optional $ keyWord ElseKW >> cBlock
  return $ CIf predicate cons alt

leafGroup :: Parser Group'
leafGroup = do
  next <- nextChar
  case next of
    '[' -> brackets $ CBracket Square <$> cGroup
    _ -> leafGroupNoBrackets

leafGroupNoBrackets :: Parser Group'
leafGroupNoBrackets = do
  next <- nextChar
  case next of
    '_'  -> underscore $> CHole
    '('  -> (symbol "()" $> (CParens $ ExprBlock $ WithSrc Nothing CEmpty))
            <|> parens (CParens . ExprBlock <$> cGroupNoEqual)
    '{'  -> do next2 <- nextChar
               case next2 of
                 '|' -> bracketed (symbol "{|") (symbol "|}") $ CBracket CurlyPipe <$> cGroup
                 _   -> braces $ CBracket Curly <$> cGroupPrefixAt
    '\"' -> CString <$> strLit
    '\'' -> CChar <$> charLit
    '%'  -> do
      name <- primName
      case strToPrimName name of
        Just prim -> CPrim <$> traverse (const cGroupNoJuxt) prim
        Nothing   -> fail $ "Unrecognized primitive: " ++ name
    '#'  -> liftM2 CLabel labelPrefix fieldLabel
    _ | isDigit next -> (    CNat   <$> natLit
                         <|> CFloat <$> doubleLit)
    '\\' -> cLam
    -- For exprs include view, for, rof, for_, rof_
    'v'  -> cFor  <|> CIdentifier <$> anyName
    'f'  -> cFor  <|> CIdentifier <$> anyName
    'r'  -> cFor  <|> CIdentifier <$> anyName
    'c'  -> cCase <|> CIdentifier <$> anyName
    'i'  -> cIf   <|> CIdentifier <$> anyName
    'd'  -> (CDo <$> (keyWord DoKW >> cBlock)) <|> CIdentifier <$> anyName
    _    -> CIdentifier <$> anyName

-- Rationales for precedence order

-- We have several groups of operators with relevant precedence
-- interactions.
--
-- - Numeric and Boolean arithmetic.  The conventional order is
--   - Exponentiation is tightest
--   - Then unary arithmetic (+, -)
--     - But we may want to make it tighter, because these are often
--       part of numeric literals
--   - Then multiplication and division (including .* and *. for vectors)
--     - Probably also includes ** **. and .** for matmul and matvec
--   - Then addition and subtraction (-| is a subtraction operator)
--   - Then comparison (including ~~ for almost equal)
--   - Then equality and inequality (looser than comparison because == makes
--     sense on booleans but > doesn't)
--   - Then Boolean operations
--     - && is tighter than || because or-of-ands form
--       is easier to understand; analogous to sum-of-products form
--
-- - Type-level operators
--   - Maybe .. and friends should be pretty tight (tighter than
--     arrow and colon), so they can appear without parens in `for`
--     binder annotations and in function types?  Maybe even tighter
--     than => so they can appear in array types?
--   - The <..< operator doesn't exist
--   - Array arrow wants to be tighter than function arrow because we
--     often want arrays in function types (not so much vice versa)
--     - However, that's not as common these days, so could go for
--       uniformity (for example, by making them adjacent in the
--       precedence)
--   - Making type arithmetic looser than array arrow would encourage
--     SoA form; the other way would encourage AoS form
--     - Status quo is that type arithmetic is looser than =>
--   - Varied function arrows (->, --o, ?->, ?=>) want to be same
--     precedence so they associate jointly
--   - Should colon be tighter or looser than arrow?  Tighter
--     makes it easier to write pi types with simply-typed arguments.
--     Looser makes it easier to annotate let binders with function types.
--     Same consideration applies again to array types.
--     - Argument: make it loose so that def is uniform without
--       special treatment (e.g., no cGroupNoColon at all); bite the
--       cost to pi types, on the grounds that they are written rarely
--     - Code hack: very tight would also make the code for cGroupNoColon
--       a little cleaner, I think.
--   - Type arithmetic (&, |)
--     - One might argue that these should be tighter
--       than function arrows because we want to return or consume
--       tuples or pairs more than we want to form pairs of functions.
--     - & should be tighter than | for the same reason as && and ||
--     - However, they are also used as separators for record and
--       variant types, where they want to be looser than : because :
--       is used as a sub-separator separating the field name from its
--       type.  Also, records and variants are already grouped by curlies,
--       so there is no pressure to make their separators tight.
--     - We choose that the latter use dominates, with the down side
--       that pairs and Either types must always be enclosed in
--       parens.  But that's fine; the parens serve as a pun reminding
--       the user that a pair is just a binary record with anonymous
--       fields.
--
-- - Universals that interact with everything
--   - Juxtaposition as function application is tighter than all the above
--     because functions can compute arguments to those operators
--   - However, we make array indexing and reference slicing tighter than
--     function composition because they make function arguments very often,
--     and we like punning x.i as a name (in this case, for the array element)
--   - Dollar as function application is looser than all the above because
--     the above can compute arguments to functions
--   - Reverse function application |> should probably be just one level tighter
--     than dollar, because
--       value |> unary |> unary |> binary $ value
--     sort of makes sense, and the left pipe should compute the first,
--     not second, argument to the binary function
--   - := and += are statement-like (in that they return unit, so
--     cannot be usefully nested), so should be even looser than
--     dollar, so that dollar can be used to compute the RHS.
--   - Atsign @ is sugar for from_ordinal taking the number on the left
--     and the type on the right, and producing an index.
--     - If we make it looser than indexing, then it will have to be
--       parenthesized as a direct argument to indexing anyway, and we
--       might as well make it very loose so it doesn't force parens
--       on any type and arithmetic computations
--     - However, it feels weird to have @ be looser than number
--       arithmetic because it seems to want to change the
--       interpretation of one thing, rather than a computation for
--       things
--     - On the other hand, maybe it is reasonable for it to be looser
--       than type arithmetic, so we can write 4 @ Fin 2 & Fin 3
--     - An alternative would be to make @ tighter than indexing, so
--       that xs.5@_ works.  However, because indexing is tighter than
--       application, there's no way for xs.5@Fin 7 to work without parens
--       somewhere.  What do we think of xs.5@(Fin 7) vs xs.(5@Fin 7)?
--     - If we make @ loose, we should probably write it with surrounding
--       spaces.
--     - Dougal says: Forget @, let's not worry about it too much
--   - Atsign @ is also used in the curly brace syntaxes as a prefix
--     to a field label that makes that field name evaluated instead
--     of taken literally.  In this capacity, the only requirement is
--     that it bind tighter than the separator between the label and
--     the value, namely, `:` or `=`.
--   - At-ellipsis @... is used in such syntaxes as a prefix to
--     denote that the field label refers to multiple fields.
--
-- - Special snowflakes that interact with almost nothing
--   - Function composition >>> and <<< are logically the same
--     precedence, but I assume we'd rather they didn't chain, b/c
--     that's just confusing.  They should probably be tighter than
--     $ and |> but don't interact with anything else?
--   - Ditto the iso versions <<& and &>>, though who knows what their
--     relative precedence should be to the function versions.
--     - Maybe doesn't matter because they shouldn't meet.
--   - Monoid combine <>.  Technically this can act like *, +, &&, ||,
--     >>>, or <<< depending on the monoid, but in practice it presumably
--     only interacts with data types that have default monoids, so is
--     independent?
--   - Pointer offset +>> should probably be looser than arithmetic,
--     since the latter can compute the offset
--
-- - "Operators" whose groups are not expressions
--   - Equals = is used to separate the binder from the body in a let
--     or a def, and as the label separator for record and variant data.
--     In the latter capacity, it's reasonable to make it an operator
--     that's looser than all the above (notably including $ and |>)
--   - Colon serves as a label separator for record and variant types,
--     so we can also make it very loose.  But should be tighter than
--     =, to be usable for type annotations of fields in the future.
--   - & and | separate fields of record and variant types, respectively.
--     They should be looser than :.
--   - , and | separate fields of records and variant data, respectively.
--     For this use case, they should be looser than =.
--   - , is also used to separate fields in tuple constructors, def
--     class argument lists, and in effect rows.  In all three cases,
--     it's already externally grouped, so can be very low precedence.
--   - | should be looser than , because | is used to separate the
--     remainder of an effect row.
--   - ? separates fields in labeled rows.  Let it be looser than :, but
--     tighter than , and |
--   - Ellipsis ... marks remainder groups in almost all of the above.
--     We can make it a unary prefix operator that's tighter than the
--     separators comma, & and |, but looser than expressions.

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
  [ [symOpL ".", symOpL "!"]
  , [("space", Expr.InfixL $ opWithSrc $ sc $> (binApp Juxtapose))]
  , [unOpPre "-", unOpPre "+"]
  , [("other", anySymOp)] -- other ops with default fixity
  , [symOpL "+", symOpL "-", symOpL "||", symOpL "&&",
     symOpR "=>",
     ("backquote", Expr.InfixL $ opWithSrc $ backquoteName >>= (return . binApp . EvalBinOp)),
     symOpL "<<<", symOpL ">>>", symOpL "<<&", symOpL "&>>"]
  , [unOpPre "..", unOpPre "..<",
     unOpPost "..", unOpPost "<.."]
  , [symOpR "->", symOpR "--o", symOpR "?->", symOpR "?=>"]
  , [symOpL "@"]
  , [unOpPre "@..."]
  , [unOpPre "..."]
  , [symOpL "::"]
  , [symOpR "$"]
  , [symOpL "+=", symOpL ":="]
  , [symOpL ":"]
  , [symOpL "="]
  , [symOpL "?"]
  -- Weak decision to associate `,` and `&` to the right because n-ary
  -- tuples are internally represented curried, so this puts the new
  -- element in front.
  , [symOpR ","]
  , [symOpR "&"]
  , [symOpL "|"]
  ]

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

symOpL :: SourceName -> (SourceName, Expr.Operator Parser Group)
symOpL s = (s, Expr.InfixL $ symOp s)

symOpR :: SourceName -> (SourceName, Expr.Operator Parser Group)
symOpR s = (s, Expr.InfixR $ symOp s)

symOp :: SourceName -> Parser (Group -> Group -> Group)
symOp s = opWithSrc $ do
  label "infix operator" (infixSym s)
  return $ binApp $ interp_operator s

unOpPre :: SourceName -> (SourceName, Expr.Operator Parser Group)
unOpPre s = (s, Expr.Prefix $ unOp s)

unOpPost :: SourceName -> (SourceName, Expr.Operator Parser Group)
unOpPost s = (s, Expr.Postfix $ unOp s)

unOp :: SourceName -> Parser (Group -> Group)
unOp s = do
  ((), pos) <- withPos $ sym "-"
  return \g@(WithSrc grpPos _) -> WithSrc (joinPos (Just pos) grpPos) $ CUn s g

binApp :: Bin' -> SrcPos -> Group -> Group -> Group
binApp f pos x y = joinSrc3 f' x y $ CBin f' x y
  where f' = WithSrc (Just pos) f

cNames :: Parser Group
cNames = nary' Juxtapose <$> map (fmap CIdentifier) <$> many (withSrc anyName)

withSrc :: Parser a -> Parser (WithSrc a)
withSrc p = do
  (x, pos) <- withPos p
  return $ WithSrc (Just pos) x

joinSrc :: WithSrc a1 -> WithSrc a2 -> a3 -> WithSrc a3
joinSrc (WithSrc p1 _) (WithSrc p2 _) x = WithSrc (joinPos p1 p2) x

joinSrc3 :: WithSrc a1 -> WithSrc a2 -> WithSrc a3 -> a4 -> WithSrc a4
joinSrc3 (WithSrc p1 _) (WithSrc p2 _) (WithSrc p3 _) x =
  WithSrc (concatPos [p1, p2, p3]) x

joinPos :: Maybe SrcPos -> Maybe SrcPos -> Maybe SrcPos
joinPos Nothing p = p
joinPos p Nothing = p
joinPos (Just (l, h)) (Just (l', h')) = Just (min l l', max h h')

concatPos :: [Maybe SrcPos] -> Maybe SrcPos
concatPos [] = Nothing
concatPos (pos:rest) = foldl joinPos pos rest

-- === Lexemes ===

type Lexer = Parser

data KeyWord = DefKW | ForKW | For_KW | RofKW | Rof_KW | CaseKW | OfKW
             | ReadKW | WriteKW | StateKW | DataKW | InterfaceKW
             | InstanceKW | WhereKW | IfKW | ThenKW | ElseKW | DoKW
             | ExceptKW | IOKW | ViewKW | ImportKW | ForeignKW | NamedInstanceKW

nextChar :: Lexer Char
nextChar = do
  i <- getInput
  guard $ not $ T.null i
  return $ T.head i
{-# INLINE nextChar #-}

upperName :: Lexer SourceName
upperName = label "upper-case name" $ lexeme $
  checkNotKeyword $ (:) <$> upperChar <*> many nameTailChar

lowerName  :: Lexer SourceName
lowerName = label "lower-case name" $ lexeme $
  checkNotKeyword $ (:) <$> lowerChar <*> many nameTailChar

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

keyWord :: KeyWord -> Lexer ()
keyWord kw = lexeme $ try $ string s >> notFollowedBy nameTailChar
  where
    s = case kw of
      DefKW  -> "def"
      ForKW  -> "for"
      RofKW  -> "rof"
      For_KW  -> "for_"
      Rof_KW  -> "rof_"
      CaseKW -> "case"
      IfKW   -> "if"
      ThenKW -> "then"
      ElseKW -> "else"
      OfKW   -> "of"
      ReadKW  -> "Read"
      WriteKW -> "Accum"
      StateKW -> "State"
      ExceptKW -> "Except"
      IOKW     -> "IO"
      DataKW -> "data"
      InterfaceKW -> "interface"
      InstanceKW -> "instance"
      NamedInstanceKW -> "named-instance"
      WhereKW -> "where"
      DoKW   -> "do"
      ViewKW -> "view"
      ImportKW -> "import"
      ForeignKW -> "foreign"

keyWordSet :: HS.HashSet String
keyWordSet = HS.fromList keyWordStrs

keyWordStrs :: [String]
keyWordStrs = ["def", "for", "for_", "rof", "rof_", "case", "of", "llam",
               "Read", "Write", "Accum", "Except", "IO", "data", "interface",
               "instance", "named-instance", "where", "if", "then", "else",
               "do", "view", "import", "foreign"]

fieldLabel :: Lexer Label
fieldLabel = label "field label" $ lexeme $
  checkNotKeyword $ (:) <$> (lowerChar <|> upperChar) <*> many nameTailChar

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
  [".", ":", "::", "!", "=", "-", "+", "||", "&&", "$", "&", "|", ",", "+=", ":="
  , "->", "=>", "?->", "?=>", "--o", "--", "<<<", ">>>", "<<&", "&>>"
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
symChars = HS.fromList ".,!$^&*:-~+/=<>|?\\@"

-- === Util ===

sc :: Parser ()
sc = skipMany $ hidden space <|> hidden lineComment

lineComment :: Parser ()
lineComment = do
  try $ string "--" >> notFollowedBy (void (char 'o'))
  void (takeWhileP (Just "char") (/= '\n'))

outputLines :: Parser ()
outputLines = void $ many (symbol ">" >> takeWhileP Nothing (/= '\n') >> ((eol >> return ()) <|> eof))

space :: Parser ()
space = do
  consumeNewLines <- asks canBreak
  if consumeNewLines
    then space1
    else void $ takeWhile1P (Just "white space") (`elem` (" \t" :: String))

mayBreak :: Parser a -> Parser a
mayBreak p = local (\ctx -> ctx { canBreak = True }) p
{-# INLINE mayBreak #-}

mayNotBreak :: Parser a -> Parser a
mayNotBreak p = local (\ctx -> ctx { canBreak = False }) p
{-# INLINE mayNotBreak #-}

optionalMonoid :: Monoid a => Parser a -> Parser a
optionalMonoid p = p <|> return mempty
{-# INLINE optionalMonoid #-}

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
  n <- asks curIndent
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
  local (\ctx -> ctx { curIndent = curIndent ctx + indent }) $ p
{-# INLINE withIndent #-}

eol :: Parser ()
eol = void MC.eol

eolf :: Parser ()
eolf = eol <|> eof

failIf :: Bool -> String -> Parser ()
failIf True s = fail s
failIf False _ = return ()

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc
{-# INLINE lexeme #-}

symbol :: Text -> Parser ()
symbol s = void $ L.symbol sc s

-- === primitive constructors and operators ===

type PrimName = PrimExpr ()

strToPrimName :: String -> Maybe PrimName
strToPrimName s = M.lookup s builtinNames

primNameToStr :: PrimName -> String
primNameToStr prim = case lookup prim $ map swap $ M.toList builtinNames of
  Just s  -> s
  Nothing -> show prim

showPrimName :: PrimExpr e -> String
showPrimName prim = primNameToStr $ fmap (const ()) prim
{-# NOINLINE showPrimName #-}

-- TODO: Can we derive these generically? Or use Show/Read?
--       (These prelude-only names don't have to be pretty.)
builtinNames :: M.Map String PrimName
builtinNames = M.fromList
  [ ("iadd", binOp IAdd), ("isub", binOp ISub)
  , ("imul", binOp IMul), ("fdiv", binOp FDiv)
  , ("fadd", binOp FAdd), ("fsub", binOp FSub)
  , ("fmul", binOp FMul), ("idiv", binOp IDiv)
  , ("irem", binOp IRem)
  , ("fpow", binOp FPow)
  , ("and" , binOp BAnd), ("or"  , binOp BOr ), ("not" , unOp BNot), ("xor", binOp BXor)
  , ("shl" , binOp BShL), ("shr" , binOp BShR)
  , ("ieq" , binOp (ICmp P.Equal)), ("feq", binOp (FCmp P.Equal))
  , ("igt" , binOp (ICmp Greater)), ("fgt", binOp (FCmp Greater))
  , ("ilt" , binOp (ICmp Less)),    ("flt", binOp (FCmp Less))
  , ("fneg", unOp  FNeg)
  , ("exp" , unOp  Exp), ("exp2"  , unOp  Exp2)
  , ("log" , unOp Log), ("log2" , unOp Log2 ), ("log10" , unOp Log10)
  , ("sin" , unOp  Sin), ("cos" , unOp Cos)
  , ("tan" , unOp  Tan), ("sqrt", unOp Sqrt)
  , ("floor", unOp Floor), ("ceil", unOp Ceil), ("round", unOp Round)
  , ("log1p", unOp Log1p), ("lgamma", unOp LGamma)
  , ("sumToVariant"   , OpExpr $ SumToVariant ())
  , ("throwError"     , OpExpr $ ThrowError ())
  , ("throwException" , OpExpr $ ThrowException ())
  , ("ask"        , OpExpr $ PrimEffect () $ MAsk)
  , ("mextend"    , OpExpr $ PrimEffect () $ MExtend (BaseMonoid () ()) ())
  , ("get"        , OpExpr $ PrimEffect () $ MGet)
  , ("put"        , OpExpr $ PrimEffect () $ MPut  ())
  , ("indexRef"   , OpExpr $ IndexRef () ())
  , ("select"     , OpExpr $ Select () () ())
  , ("while"           , HofExpr $ While ())
  , ("linearize"       , HofExpr $ Linearize ())
  , ("linearTranspose" , HofExpr $ Transpose ())
  , ("runReader"       , HofExpr $ RunReader () ())
  , ("runWriter"       , HofExpr $ RunWriter (BaseMonoid () ()) ())
  , ("runState"        , HofExpr $ RunState  () ())
  , ("runIO"           , HofExpr $ RunIO ())
  , ("catchException"  , HofExpr $ CatchException ())
  , ("TyKind"    , TCExpr $ TypeKind)
  , ("Float64"   , TCExpr $ BaseType $ Scalar Float64Type)
  , ("Float32"   , TCExpr $ BaseType $ Scalar Float32Type)
  , ("Int64"     , TCExpr $ BaseType $ Scalar Int64Type)
  , ("Int32"     , TCExpr $ BaseType $ Scalar Int32Type)
  , ("Word8"     , TCExpr $ BaseType $ Scalar Word8Type)
  , ("Word32"    , TCExpr $ BaseType $ Scalar Word32Type)
  , ("Word64"    , TCExpr $ BaseType $ Scalar Word64Type)
  , ("Int32Ptr"  , TCExpr $ BaseType $ ptrTy $ Scalar Int32Type)
  , ("Word8Ptr"  , TCExpr $ BaseType $ ptrTy $ Scalar Word8Type)
  , ("Word32Ptr" , TCExpr $ BaseType $ ptrTy $ Scalar Word32Type)
  , ("Word64Ptr" , TCExpr $ BaseType $ ptrTy $ Scalar Word64Type)
  , ("Float32Ptr", TCExpr $ BaseType $ ptrTy $ Scalar Float32Type)
  , ("PtrPtr"    , TCExpr $ BaseType $ ptrTy $ ptrTy $ Scalar Word8Type)
  , ("Fin"       , TCExpr $ Fin ())
  , ("Label"     , TCExpr $ LabelType)
  , ("Ref"       , TCExpr $ RefType (Just ()) ())
  , ("PairType"  , TCExpr $ ProdType [(), ()])
  , ("UnitType"  , TCExpr $ ProdType [])
  , ("EffKind"   , TCExpr $ EffectRowKind)
  , ("LabeledRowKind", TCExpr $ LabeledRowKindTC)
  , ("pair", ConExpr $ ProdCon [(), ()])
  , ("fstRef", OpExpr $ ProjRef 0 ())
  , ("sndRef", OpExpr $ ProjRef 1 ())
  , ("cast", OpExpr  $ CastOp () ())
  , ("alloc", OpExpr $ IOAlloc (Scalar Word8Type) ())
  , ("free" , OpExpr $ IOFree ())
  , ("ptrOffset", OpExpr $ PtrOffset () ())
  , ("ptrLoad"  , OpExpr $ PtrLoad ())
  , ("ptrStore" , OpExpr $ PtrStore () ())
  , ("dataConTag", OpExpr $ DataConTag ())
  , ("toEnum"    , OpExpr $ ToEnum () ())
  , ("outputStreamPtr", OpExpr $ OutputStreamPtr)
  , ("projMethod0", OpExpr $ ProjMethod () 0)
  , ("projMethod1", OpExpr $ ProjMethod () 1)
  , ("projMethod2", OpExpr $ ProjMethod () 2)
  , ("explicitDict", ConExpr $ ExplicitDict () ())
  , ("explicitApply", OpExpr $ ExplicitApply () ())
  , ("monoLit", OpExpr $ MonoLiteral ())
  ]
  where
    binOp  op = OpExpr $ BinOp op () ()
    unOp   op = OpExpr $ UnOp  op ()
    ptrTy  ty = PtrType (Heap CPU, ty)
