-- Copyright 2022 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module ConcreteSyntax (
  mustParseit, sourceBlocks, sourceBlock,
  keyWordStrs, showPrimName,
  parseUModule, parseUModuleDeps,
  finishUModuleParse, preludeImportBlock, mustParseSourceBlock,
  pattern Identifier) where

import Control.Monad.Combinators.Expr qualified as Expr
import Control.Monad.Reader
import Data.Char
import Data.Either
import Data.Functor
import Data.List.NonEmpty (NonEmpty (..))
import Data.String (fromString)
import Data.Text (Text)
import Data.Text          qualified as T
import Data.Text.Encoding qualified as T
import Data.Void
import Text.Megaparsec hiding (Label, State)
import Text.Megaparsec.Char hiding (space, eol)

import Err
import Lexing
import Types.Core
import Types.Source
import Types.Primitives
import Util

-- TODO: implement this more efficiently rather than just parsing the whole
-- thing and then extracting the deps.
parseUModuleDeps :: ModuleSourceName -> File -> [ModuleSourceName]
parseUModuleDeps name file = deps
  where UModule _ deps _ = parseUModule name $ T.decodeUtf8 $ fContents file
{-# SCC parseUModuleDeps #-}

finishUModuleParse :: UModulePartialParse -> UModule
finishUModuleParse (UModulePartialParse name _ file) =
  parseUModule name (T.decodeUtf8 $ fContents file)

parseUModule :: ModuleSourceName -> Text -> UModule
parseUModule name s = do
  let blocks = mustParseit s sourceBlocks
  let preamble = case name of
        Prelude -> []
        _ -> [preludeImportBlock]
  let blocks' = preamble ++ blocks
  let imports = flip foldMap blocks' \b -> case sbContents b of
                  Misc (ImportModule moduleName) -> [moduleName]
                  _ -> []
  UModule name imports blocks'
{-# SCC parseUModule #-}

preludeImportBlock :: SourceBlock
preludeImportBlock = SourceBlock 0 0 "" mempty (Misc $ ImportModule Prelude)

sourceBlocks :: Parser [SourceBlock]
sourceBlocks = manyTill (sourceBlock <* outputLines) eof
{-# SCC sourceBlocks #-}

mustParseSourceBlock :: Text -> SourceBlock
mustParseSourceBlock s = mustParseit s sourceBlock

-- === helpers for target ADT ===

interpOperator :: SrcId -> String -> ([SrcId], Bin)
interpOperator sid = \case
  "&>"  -> atomic DepAmpersand
  "."   -> atomic Dot
  ",>"  -> atomic DepComma
  ":"   -> atomic Colon
  "|"   -> atomic Pipe
  "::"  -> atomic DoubleColon
  "$"   -> atomic Dollar
  "->>" -> atomic ImplicitArrow
  "=>"  -> atomic FatArrow
  "="   -> atomic CSEqual
  name  -> ([], EvalBinOp $ WithSrc sid $ fromString $ "(" <> name <> ")")
  where
    atomic :: Bin -> ([SrcId], Bin)
    atomic b = ([sid], b)

pattern Identifier :: SourceName -> GroupW
pattern Identifier name <- (WithSrcs _ _ (CLeaf (CIdentifier name)))

-- === Parser (top-level structure) ===

sourceBlock :: Parser SourceBlock
sourceBlock = do
  offset <- getOffset
  pos <- getSourcePos
  (src, (lexInfo, b)) <- withSource $ withLexemeInfo $ withRecovery recover $ sourceBlock'
  let lexInfo' = lexInfo { lexemeInfo = lexemeInfo lexInfo <&> \(t, (l, r)) -> (t, (l-offset, r-offset))}
  return $ SourceBlock (unPos (sourceLine pos)) offset src lexInfo' b

recover :: ParseError Text Void -> Parser SourceBlock'
recover e = do
  pos <- liftM statePosState getParserState
  reachedEOF <-  try (mayBreak sc >> eof >> return True)
             <|> return False
  consumeTillBreak
  let errmsg = errorBundlePretty (ParseErrorBundle (e :| []) pos)
  return $ UnParseable reachedEOF errmsg

importModule :: Parser SourceBlock'
importModule = Misc . ImportModule . OrdinaryModule <$> do
  keyWord ImportKW
  WithSrc _ s <- anyCaseName
  eol
  return s

declareForeign :: Parser SourceBlock'
declareForeign = do
  keyWord ForeignKW
  foreignName <- strLit
  b <- anyName
  void $ label "type annotation" $ sym ":"
  ty <- cGroup
  eol
  return $ DeclareForeign (fmap fromString foreignName) b ty

declareCustomLinearization :: Parser SourceBlock'
declareCustomLinearization = do
  zeros <- (keyWord CustomLinearizationSymbolicKW $> SymbolicZeros)
       <|> (keyWord CustomLinearizationKW $> InstantiateZeros)
  fun <- anyCaseName
  linearization <- cGroup
  eol
  return $ DeclareCustomLinearization fun zeros linearization

consumeTillBreak :: Parser ()
consumeTillBreak = void $ manyTill anySingle $ eof <|> void (try (eol >> eol))

sourceBlock' :: Parser SourceBlock'
sourceBlock' =
      proseBlock
  <|> topLevelCommand
  <|> liftM TopDecl topDecl
  <|> topLetOrExpr <* eolf
  <|> hidden (some eol >> return (Misc EmptyLines))
  <|> hidden (sc >> eol >> return (Misc CommentLine))

topDecl :: Parser CTopDeclW
topDecl = withSrcs topDecl' <* eolf

topDecl' :: Parser CTopDecl
topDecl' =
      dataDef
  <|> structDef
  <|> interfaceDef
  <|> (CInstanceDecl <$> instanceDef True)
  <|> (CInstanceDecl <$> instanceDef False)

proseBlock :: Parser SourceBlock'
proseBlock = label "prose block" $
  char '\'' >> fmap (Misc . ProseBlock . fst) (withSource consumeTillBreak)

topLevelCommand :: Parser SourceBlock'
topLevelCommand =
      importModule
  <|> declareForeign
  <|> declareCustomLinearization
  -- <|> (Misc . QueryEnv <$> envQuery)
  <|> explicitCommand
  <?> "top-level command"

_envQuery :: Parser EnvQuery
_envQuery = error "not implemented"
-- string ":debug" >> sc >> (
--       (DumpSubst        <$  (string "env"   >> sc))
--   <|> (InternalNameInfo <$> (string "iname" >> sc >> rawName))
--   <|> (SourceNameInfo   <$> (string "sname" >> sc >> anyName)))
--        <* eol
--   where
--     rawName :: Parser RawName
--     rawName = RawName <$> (fromString <$> anyName) <*> intLit

explicitCommand :: Parser SourceBlock'
explicitCommand = do
  cmdName <- char ':' >> nameString
  cmd <- case cmdName of
    "p"       -> return $ EvalExpr (Printed Nothing)
    "pp"      -> return $ EvalExpr (Printed (Just PrintHaskell))
    "pcodegen"-> return $ EvalExpr (Printed (Just PrintCodegen))
    "t"       -> return $ GetType
    "html"    -> return $ EvalExpr RenderHtml
    "export"  -> ExportFun <$> nameString
    _ -> fail $ "unrecognized command: " ++ show cmdName
  b <- cBlock <* eolf
  e <- case b of
    ExprBlock e -> return e
    IndentedBlock sid decls -> withSrcs $ return $ CDo $ IndentedBlock sid decls
  return $ case (e, cmd) of
    (WithSrcs sid _ (CLeaf (CIdentifier v)), GetType) -> Misc $ GetNameType (WithSrc sid v)
    _ -> Command cmd e

type CDefBody = ([(SourceNameW, GroupW)], [(LetAnn, CDef)])
structDef :: Parser CTopDecl
structDef = do
  keyWord StructKW
  tyName <- anyName
  (params, givens) <- typeParams
  (fields, defs) <- oneLiner <|> multiLiner
  return $ CStruct tyName params givens fields defs
  where
    oneLiner :: Parser CDefBody
    oneLiner = do
      field <- nameAndType
      return ([field], [])

    multiLiner :: Parser CDefBody
    multiLiner = partitionEithers <$> onePerLine do
      (    (Left  <$> nameAndType)
       <|> (Right <$> funDefLetWithAnn))

funDefLetWithAnn :: Parser (LetAnn, CDef)
funDefLetWithAnn = do
  ann <- topLetAnn <|> return PlainLet
  def <- funDefLet
  return (ann, def)

dataDef :: Parser CTopDecl
dataDef = do
  keyWord DataKW
  tyName <- anyName
  (params, givens) <- typeParams
  dataCons <- onePerLine do
    dataConName <- anyName
    dataConArgs <- optional explicitParams
    return (dataConName, dataConArgs)
  return $ CData tyName params givens dataCons

interfaceDef :: Parser CTopDecl
interfaceDef = do
  keyWord InterfaceKW
  className <- anyName
  params <- explicitParams
  methodDecls <- try (withIndent (keyWord PassKW) >> return [])
    <|> onePerLine do
      methodName <- anyName
      void $ label "type annotation" $ sym ":"
      ty <- cGroup
      return (methodName, ty)
  return $ CInterface className params methodDecls

nameAndType :: Parser (SourceNameW, GroupW)
nameAndType = do
  n <- anyName
  sym ":"
  arg <- cGroup
  return (n, arg)

topLetOrExpr :: Parser SourceBlock'
topLetOrExpr = topLet >>= \case
  WithSrcs _ _ (CSDecl ann (CExpr e)) -> do
    when (ann /= PlainLet) $ fail "Cannot annotate expressions"
    return $ Command (EvalExpr (Printed Nothing)) e
  d -> return $ TopDecl d

topLet :: Parser CTopDeclW
topLet = withSrcs do
  lAnn <- topLetAnn <|> return PlainLet
  decl <- cDecl
  return $ CSDecl lAnn decl

topLetAnn :: Parser LetAnn
topLetAnn = do
  void $ char '@'
  ann <-  (string "inline"   $> InlineLet)
      <|> (string "noinline" $> NoInlineLet)
  nextLine
  return ann

onePerLine :: Parser a -> Parser [a]
onePerLine p =   liftM (:[]) p
             <|> (withIndent $ p `sepBy1` try nextLine)
{-# INLINE onePerLine #-}

-- === Groups ===

cBlock :: Parser CSBlock
cBlock = indentedBlock <|> ExprBlock <$> cGroup

indentedBlock :: Parser CSBlock
indentedBlock = withIndent do
  WithSrcs sid _ decls <- withSrcs $ withSrcs cDecl `sepBy1` (void semicolon <|> try nextLine)
  return $ IndentedBlock sid decls

cDecl :: Parser CSDecl
cDecl =   (CDefDecl <$> funDefLet)
      <|> simpleLet
      <|> (keyWord PassKW >> return CPass)

simpleLet :: Parser CSDecl
simpleLet = do
  lhs <- cGroupNoEqual
  next <- nextChar
  case next of
    '=' -> sym  "=" >> CLet  lhs <$> cBlock
    '<' -> sym "<-" >> CBind lhs <$> cBlock
    _   -> return $ CExpr lhs

instanceDef :: Bool -> Parser CInstanceDef
instanceDef isNamed = do
  optNameAndArgs <- case isNamed of
    False -> keyWord InstanceKW $> Nothing
    True  -> keyWord NamedInstanceKW >> do
      name <- anyName
      args <-  (sym ":" >> return Nothing)
           <|> ((Just <$> parenList cParenGroup) <* sym "->")
      return $ Just (name, args)
  className <- anyName
  args <- argList
  givens <- optional givenClause
  methods <- withIndent $ (withSrcs cDecl) `sepBy1` try nextLine
  return $ CInstanceDef className args givens methods optNameAndArgs

funDefLet :: Parser CDef
funDefLet = label "function definition" do
  keyWord DefKW
  mayBreak do
    name   <- anyName
    params <- explicitParams
    rhs    <- optional do
      expl     <- explicitness
      effs     <- optional cEffs
      resultTy <- cGroupNoEqual
      return (expl, effs, resultTy)
    givens <- optional givenClause
    mayNotBreak do
      sym "="
      body <- cBlock
      return $ CDef name params rhs givens body

explicitness :: Parser AppExplicitness
explicitness =   (sym "->"  $> ExplicitApp)
             <|> (sym "->>" $> ImplicitApp)

-- Intended for occurrences, like `foo(x, y, z)` (cf. defParamsList).
argList :: Parser [GroupW]
argList = do
  WithSrcs _ _ gs <- withSrcs $ bracketedGroup immediateLParen rParen cParenGroup
  return gs

immediateLParen :: Parser ()
immediateLParen = label "'(' (without preceding whitespace)" do
  nextChar >>= \case
    '(' -> precededByWhitespace >>= \case
      True -> empty
      False -> lParen
    _ -> empty

-- Putting `sym =` inside the cases gives better errors.
typeParams :: Parser (Maybe ExplicitParams, Maybe GivenClause)
typeParams =
      (explicitParamsAndGivens <* sym "=")
  <|> (return (Nothing, Nothing)    <* sym "=")

explicitParamsAndGivens :: Parser (Maybe ExplicitParams, Maybe GivenClause)
explicitParamsAndGivens = (,) <$> (Just <$> explicitParams) <*> optional givenClause

explicitParams :: Parser ExplicitParams
explicitParams = label "parameter list in parentheses (without preceding whitespace)" $
  withSrcs $ bracketedGroup immediateLParen rParen cParenGroup

parenList :: Parser GroupW -> Parser BracketedGroup
parenList p = withSrcs $ bracketedGroup lParen rParen p

bracketedGroup :: Parser () -> Parser () -> Parser GroupW -> Parser [GroupW]
bracketedGroup l r p = bracketed l r $ commaSep p

noGap :: Parser ()
noGap = precededByWhitespace >>= \case
  True -> fail "Unexpected whitespace"
  False -> return ()

givenClause :: Parser GivenClause
givenClause = do
  keyWord GivenKW
  (,) <$> parenList cGroup <*> optional (parenList cGroup)

withClause :: Parser WithClause
withClause = keyWord WithKW >> parenList cGroup

cEffs :: Parser CEffs
cEffs = withSrcs $ braces do
  effs <- commaSep cGroupNoPipe
  effTail <- optional $ sym "|" >> cGroup
  return (effs, effTail)

commaSep :: Parser a -> Parser [a]
commaSep p = sepBy p (sym ",")

cParenGroup :: Parser GroupW
cParenGroup = (withSrcs (CGivens <$> givenClause)) <|> cGroup

cGroup :: Parser GroupW
cGroup = makeExprParser leafGroup ops

cGroupNoJuxt :: Parser GroupW
cGroupNoJuxt = makeExprParser leafGroup $
  withoutOp "space" $ withoutOp "." ops

cGroupNoEqual :: Parser GroupW
cGroupNoEqual = makeExprParser leafGroup $
  withoutOp "=" ops

cGroupNoPipe :: Parser GroupW
cGroupNoPipe = makeExprParser leafGroup $
  withoutOp "|" ops

cGroupNoArrow :: Parser GroupW
cGroupNoArrow = makeExprParser leafGroup $
  withoutOp "->" ops

cNullaryLam :: Parser Group
cNullaryLam = do
  void $ sym "\\."
  body <- cBlock
  return $ CLambda [] body

cLam :: Parser Group
cLam = do
  void $ sym "\\"
  bs <- many cGroupNoJuxt
  void $ mayNotBreak $ sym "."
  body <- cBlock
  return $ CLambda bs body

cFor :: Parser Group
cFor = do
  kw <- forKW
  indices <- many cGroupNoJuxt
  void $ mayNotBreak $ sym "."
  body <- cBlock
  return $ CFor kw indices body
  where forKW =     keyWord ForKW  $> KFor
                <|> keyWord For_KW $> KFor_
                <|> keyWord RofKW  $> KRof
                <|> keyWord Rof_KW $> KRof_

cDo :: Parser Group
cDo = do
  keyWord DoKW
  CDo <$> cBlock

cCase :: Parser Group
cCase = do
  keyWord CaseKW
  scrut <- cGroup
  keyWord OfKW
  alts <- onePerLine cAlt
  return $ CCase scrut alts

cAlt :: Parser CaseAlt
cAlt = do
  pat <- cGroupNoArrow
  sym "->"
  body <- cBlock
  return (pat, body)

-- see [Note if-syntax]
cIf :: Parser Group
cIf = mayNotBreak do
  keyWord IfKW
  predicate <- cGroup
  (cons, alt) <- thenSameLine <|> thenNewLine
  return $ CIf predicate cons alt

thenSameLine :: Parser (CSBlock, Maybe CSBlock)
thenSameLine = do
  void $ keyWord ThenKW
  cBlock >>= \case
    IndentedBlock sid blk -> do
      let msg = ("No `else` may follow same-line `then` and indented consequent"
                  ++ "; indent and align both `then` and `else`, or write the "
                  ++ "whole `if` on one line.")
      mayBreak $ noElse msg
      return (IndentedBlock sid blk, Nothing)
    ExprBlock ex -> do
      alt <- optional
        $ (keyWord ElseKW >> cBlock)
          <|> (lookAhead (try $ withIndent (keyWord ElseKW))
               >> withIndent (keyWord ElseKW >> cBlock))
      return (ExprBlock ex, alt)

thenNewLine :: Parser (CSBlock, Maybe CSBlock)
thenNewLine = withIndent $ do
  void $ keyWord ThenKW
  cBlock >>= \case
    IndentedBlock sid blk -> do
      alt <- do
        -- With `mayNotBreak`, this just forbids inline else
        noElse ("Same-line `else` may not follow indented consequent;"
                ++ " put the `else` on the next line.")
        optional $ do
          void $ try $ nextLine >> keyWord ElseKW
          cBlock
      return (IndentedBlock sid blk, alt)
    ExprBlock ex -> do
      void $ optional $ try nextLine
      alt <- optional $ keyWord ElseKW >> cBlock
      return (ExprBlock ex, alt)

noElse :: String -> Parser ()
noElse msg = (optional $ try $ sc >> keyWord ElseKW) >>= \case
  Just _ -> fail msg
  Nothing -> return ()

leafGroup :: Parser GroupW
leafGroup = leafGroup' >>= appendPostfixGroups
 where
  leafGroup' :: Parser GroupW
  leafGroup' = do
    next <- nextChar
    case next of
      '_'  ->  withSrcs $ CLeaf <$> (underscore >> pure CHole)
      '('  ->  toCLeaf CIdentifier <$> symName
           <|> cParens
      '['  -> cBrackets
      '\"' -> toCLeaf CString <$> strLit
      '\'' -> toCLeaf CChar   <$> charLit
      '%'  -> do
        WithSrc sid name <- primName
        case strToPrimName name of
          Just prim -> WithSrcs sid [] <$> CPrim prim <$> argList
          Nothing   -> fail $ "Unrecognized primitive: " ++ name
      _ | isDigit next -> (    toCLeaf CNat   <$> natLit
                           <|> toCLeaf CFloat <$> doubleLit)
      '\\' -> withSrcs (cNullaryLam <|> cLam)
      -- For exprs include for, rof, for_, rof_
      'f'  -> (withSrcs cFor)  <|> cIdentifier
      'd'  -> (withSrcs cDo)   <|> cIdentifier
      'r'  -> (withSrcs cFor)  <|> cIdentifier
      'c'  -> (withSrcs cCase) <|> cIdentifier
      'i'  -> (withSrcs cIf)   <|> cIdentifier
      _    -> cIdentifier

  appendPostfixGroups :: GroupW -> Parser GroupW
  appendPostfixGroups g =
        (noGap >> appendPostfixGroup g >>= appendPostfixGroups)
    <|> return g

  appendPostfixGroup :: GroupW -> Parser GroupW
  appendPostfixGroup g = withSrcs $
        (CJuxtapose False g <$> cParens)
    <|> (CJuxtapose False g <$> cBrackets)
    <|> appendFieldAccess g

  appendFieldAccess :: GroupW -> Parser Group
  appendFieldAccess g = try do
    dot
    field <- cFieldName
    return $ CBin Dot g field

cFieldName :: Parser GroupW
cFieldName = cIdentifier <|> (toCLeaf CNat <$> natLit)

cIdentifier :: Parser GroupW
cIdentifier = toCLeaf CIdentifier <$> anyName

toCLeaf :: (a -> CLeaf) -> WithSrc a -> GroupW
toCLeaf toLeaf (WithSrc sid leaf) = WithSrcs sid [] $ CLeaf $ toLeaf leaf

cParens :: Parser GroupW
cParens = withSrcs $ CParens <$> bracketedGroup lParen rParen cParenGroup

cBrackets :: Parser GroupW
cBrackets = withSrcs $ CBrackets <$> bracketedGroup lBracket rBracket cGroup

-- A `PrecTable` is enough information to (i) remove or replace
-- operators for special contexts, and (ii) build the input structure
-- for Expr.makeExprParser.
type PrecTable a = [[(SourceName, Expr.Operator Parser a)]]

makeExprParser :: Parser a -> PrecTable a -> Parser a
makeExprParser p tbl = Expr.makeExprParser p tbl' where
  tbl' = map (map snd) tbl

withoutOp :: SourceName -> PrecTable a -> PrecTable a
withoutOp op tbl = map (filter ((/= op) . fst)) tbl

ops :: PrecTable GroupW
ops =
  [ [symOpL   "!"]
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
  , [symOpR  "=>"]
  , [arrow, symOpR "->>"]
  , [symOpL ">>>"]
  , [symOpL "<<<"]
  , [symOpL   "@"]
  , [symOpN  "::"]
  , [symOpR   "$"]
  , [symOpN  "+=", symOpN  ":="]
  -- Associate right so the mistaken utterance foo : i:Fin 4 => (..i)
  -- groups as a bad pi type rather than a bad binder
  , [symOpR   ":"]
  , [symOpL   "|"]
  , [symOpR  ",>"]
  , [symOpR  "&>"]
  , [withClausePostfix]
  , [symOpL   "="]
  ] where
  other = ("other", anySymOp)
  backquote = ("backquote", Expr.InfixL backquoteOp)
  juxtaposition  = ("space", Expr.InfixL $ sc >> addSrcIdToBinOp (return \x y -> ([], CJuxtapose True x y)))
  withClausePostfix = ("with", Expr.Postfix withClausePostfixOp)
  arrow = ("->", Expr.InfixR arrowOp)

addSrcIdToBinOp :: Parser (GroupW -> GroupW -> ([SrcId], Group)) -> Parser (GroupW -> GroupW -> GroupW)
addSrcIdToBinOp op = do
  f <- op
  sid <- freshSrcId
  return \x y -> do
    let (atomicSids, g) = f x y
    WithSrcs sid atomicSids g
{-# INLINE addSrcIdToBinOp #-}

addSrcIdToUnOp :: Parser (GroupW -> Group) -> Parser (GroupW -> GroupW)
addSrcIdToUnOp op = do
  f <- op
  sid <- freshSrcId
  return \x -> WithSrcs sid [] $ f x
{-# INLINE addSrcIdToUnOp #-}

backquoteOp :: Parser (GroupW -> GroupW -> GroupW)
backquoteOp = binApp do
  fname <- backquoteName
  return ([], EvalBinOp fname)

anySymOp :: Expr.Operator Parser GroupW
anySymOp = Expr.InfixL $ binApp do
  WithSrc sid s <- label "infix operator" (mayBreak anySym)
  return $ interpOperator sid s

symOpN :: String -> (SourceName, Expr.Operator Parser GroupW)
symOpN s = (fromString s, Expr.InfixN $ symOp s)

symOpL :: String -> (SourceName, Expr.Operator Parser GroupW)
symOpL s = (fromString s, Expr.InfixL $ symOp s)

symOpR :: String -> (SourceName, Expr.Operator Parser GroupW)
symOpR s = (fromString s, Expr.InfixR $ symOp s)

symOp :: String -> Parser (GroupW -> GroupW -> GroupW)
symOp s = binApp do
  sid <- label "infix operator" (mayBreak $ symWithId $ T.pack s)
  return $ interpOperator sid s

arrowOp :: Parser (GroupW -> GroupW -> GroupW)
arrowOp = addSrcIdToBinOp do
  sid <- symWithId "->"
  optEffs <- optional cEffs
  return \lhs rhs -> ([sid], CArrow lhs optEffs rhs)

unOpPre :: String -> (SourceName, Expr.Operator Parser GroupW)
unOpPre s = (fromString s, Expr.Prefix $ prefixOp s)

prefixOp :: String -> Parser (GroupW -> GroupW)
prefixOp s = addSrcIdToUnOp do
  symId <- symWithId (fromString s)
  return $ CPrefix (WithSrc symId $ fromString s)

binApp :: Parser ([SrcId], Bin) -> Parser (GroupW -> GroupW -> GroupW)
binApp f = addSrcIdToBinOp do
  (sids, op) <- f
  return \x y -> (sids, CBin op x y)

withClausePostfixOp :: Parser (GroupW -> GroupW)
withClausePostfixOp = addSrcIdToUnOp do
  rhs <- withClause
  return \lhs -> CWith lhs rhs

withSrcs :: Parser a -> Parser (WithSrcs a)
withSrcs p = do
  sid <- freshSrcId
  (sids, result) <- collectAtomicLexemeIds p
  return $ WithSrcs sid sids result

-- === notes ===

-- note [if-syntax]
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
