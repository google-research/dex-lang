-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module Parser (Parser, parseit, parseProg, runTheParser, parseData,
               parseTopDeclRepl, uint, withSource, parseExpr, exprAsModule,
               emptyLines, brackets, symbol, symChar, keyWordStrs) where

import Control.Monad
import Control.Monad.Combinators.Expr
import Control.Monad.Reader
import Text.Megaparsec hiding (Label, State)
import Text.Megaparsec.Char hiding (space)
import Data.Char (isLower)
import Data.Functor
import Data.List.NonEmpty (NonEmpty (..))
import qualified Data.Map.Strict as M
import Data.Void
import Data.String (fromString)
import qualified Text.Megaparsec.Char.Lexer as L
import qualified Text.Megaparsec.Debug

import Env
import Syntax
import PPrint

-- canPair is used for the ops (,) (|) (&) which should only appear inside
-- parentheses (to avoid conflicts with records and other syntax)
data ParseCtx = ParseCtx { curIndent :: Int
                         , canPair   :: Bool
                         , canBreak  :: Bool }
type Parser = ReaderT ParseCtx (Parsec Void String)

parseProg :: String -> [SourceBlock]
parseProg s = mustParseit s $ manyTill (sourceBlock <* outputLines) eof

parseData :: String -> Except UExpr
parseData s = parseit s $ expr <* (optional eol >> eof)

parseTopDeclRepl :: String -> Maybe SourceBlock
parseTopDeclRepl s = case sbContents b of
  UnParseable True _ -> Nothing
  _ -> Just b
  where b = mustParseit s sourceBlock

parseExpr :: String -> Maybe UExpr
parseExpr s = case parseit s (expr <* eof) of
  Right ans -> Just ans
  Left  e   -> Nothing

parseit :: String -> Parser a -> Except a
parseit s p = case runTheParser s (p <* (optional eol >> eof)) of
  Left e -> throw ParseErr (errorBundlePretty e)
  Right x -> return x

mustParseit :: String -> Parser a -> a
mustParseit s p  = case parseit s p of
  Right ans -> ans
  Left e -> error $ "This shouldn't happen:\n" ++ pprint e

includeSourceFile :: Parser String
includeSourceFile = symbol "include" >> stringLiteral <* eol

sourceBlock :: Parser SourceBlock
sourceBlock = do
  offset <- getOffset
  pos <- getSourcePos
  (src, (level, b)) <- withSource $ withRecovery recover $ do
    level <- logLevel <|> logTime <|> logBench <|> return LogNothing
    b <- sourceBlock'
    return (level, b)
  return $ SourceBlock (unPos (sourceLine pos)) offset level src b Nothing

recover :: ParseError String Void -> Parser (LogLevel, SourceBlock')
recover e = do
  pos <- liftM statePosState getParserState
  reachedEOF <-  try (mayBreak sc >> eof >> return True)
             <|> return False
  consumeTillBreak
  let errmsg = errorBundlePretty (ParseErrorBundle (e :| []) pos)
  return (LogNothing, UnParseable reachedEOF errmsg)

consumeTillBreak :: Parser ()
consumeTillBreak = void $ manyTill anySingle $ eof <|> void (try (eol >> eol))

logLevel :: Parser LogLevel
logLevel = do
  void $ try $ lexeme $ char '%' >> string "passes"
  passes <- many passName
  void eol
  case passes of
    [] -> return $ LogAll
    _ -> return $ LogPasses passes

logTime :: Parser LogLevel
logTime = do
  void $ try $ lexeme $ char '%' >> string "time"
  void eol
  return PrintEvalTime

logBench :: Parser LogLevel
logBench = do
  void $ try $ lexeme $ char '%' >> string "bench"
  benchName <- stringLiteral
  void eol
  return $ PrintBench benchName

passName :: Parser PassName
passName = choice [thisNameString s $> x | (s, x) <- passNames]

passNames :: [(String, PassName)]
passNames = [(show x, x) | x <- [minBound..maxBound]]

sourceBlock' :: Parser SourceBlock'
sourceBlock' =
      proseBlock
  <|> topLevelCommand
  <|> liftM (declsToModule . (:[])) (topDecl <* eolf)
  <|> liftM (declsToModule . (:[])) (interfaceInstance <* eolf)
  <|> liftM declsToModule (interfaceDef <* eolf)
  <|> liftM (Command (EvalExpr Printed) . exprAsModule) (expr <* eol)
  <|> hidden (some eol >> return EmptyLines)
  <|> hidden (sc >> eol >> return CommentLine)
  where declsToModule = RunModule . UModule . toNest

proseBlock :: Parser SourceBlock'
proseBlock = label "prose block" $ char '\'' >> liftM (ProseBlock . fst) (withSource consumeTillBreak)

loadData :: Parser SourceBlock'
loadData = do
  symbol "load"
  fmt <- dataFormat
  s <- stringLiteral
  symbol "as"
  b <- patAnn
  void eol
  return $ LoadData b fmt s

topLevelCommand :: Parser SourceBlock'
topLevelCommand =
      (liftM IncludeSourceFile includeSourceFile)
  <|> loadData
  <|> dumpData
  <|> explicitCommand
  <?> "top-level command"

dataFormat :: Parser DataFormat
dataFormat = do
  s <- nameString
  case s of
    "dxo"  -> return DexObject
    "dxbo" -> return DexBinaryObject
    _      -> fail $ show s ++ " not a recognized data format (one of dxo|dxbo)"

dumpData :: Parser SourceBlock'
dumpData = do
  symbol "dump"
  fmt <- dataFormat
  s <- stringLiteral
  e <- blockOrExpr
  void eol
  return $ Command (Dump fmt s) (exprAsModule e)

explicitCommand :: Parser SourceBlock'
explicitCommand = do
  cmdName <- char ':' >> nameString
  cmd <- case cmdName of
    "p"       -> return $ EvalExpr Printed
    "t"       -> return $ GetType
    "html"    -> return $ EvalExpr RenderHtml
    "export"  -> ExportFun <$> nameString
    "plot"    -> return $ EvalExpr Scatter
    "plotmat"      -> return $ EvalExpr (Heatmap False)
    "plotmatcolor" -> return $ EvalExpr (Heatmap True)
    _ -> fail $ "unrecognized command: " ++ show cmdName
  e <- blockOrExpr <* eolf
  return $ case (e, cmd) of
    (WithSrc _ (UVar (v:>())), GetType) -> GetNameType (asGlobal v)
    _ -> Command cmd (exprAsModule e)

exprAsModule :: UExpr -> (Name, UModule)
exprAsModule e = (asGlobal v, UModule (toNest [d]))
  where
    v = mkName "_ans_"
    d = ULet PlainLet (WithSrc (srcPos e) (UPatBinder (Bind (v:>()))), Nothing) e

-- === uexpr ===

expr :: Parser UExpr
expr = mayNotPair $ makeExprParser leafExpr ops

-- expression without exposed infix operators
leafExpr :: Parser UExpr
leafExpr = parens (mayPair $ makeExprParser leafExpr ops)
         <|> uTabCon
         <|> uVarOcc
         <|> uHole
         <|> uString
         <|> uLit
         <|> uPiType
         <|> uLamExpr
         <|> uForExpr
         <|> caseExpr
         <|> uPrim
         <|> unitCon
         <|> (uLabeledExprs `fallBackTo` uVariantExpr)
         <|> uIsoSugar
         <?> "expression"

containedExpr :: Parser UExpr
containedExpr =   parens (mayPair $ makeExprParser leafExpr ops)
              <|> uVarOcc
              <|> uLabeledExprs
              <?> "contained expression"

uType :: Parser UType
uType = expr

uString :: Lexer UExpr
uString = do
  (s, pos) <- withPos $ strLit
  let cs = map (WithSrc (Just pos) . UCharLit) s
  return $ WithSrc (Just pos) $ UTabCon cs

uLit :: Parser UExpr
uLit = withSrc $ uLitParser
  where uLitParser = UCharLit <$> charLit
                 <|> UIntLit  <$> intLit
                 <|> UFloatLit <$> doubleLit
                 <?> "literal"

uVarOcc :: Parser UExpr
uVarOcc = withSrc $ try $ (UVar . (:>())) <$> (occName <* notFollowedBy (sym ":"))
  where occName = upperName <|> lowerName <|> symName

uHole :: Parser UExpr
uHole = withSrc $ underscore $> UHole

letAnnStr :: Parser LetAnn
letAnnStr =   (string "instance"   $> InstanceLet)
          <|> (string "superclass" $> SuperclassLet)

topDecl :: Parser UDecl
topDecl = dataDef <|> topLet

topLet :: Parser UDecl
topLet = do
  lAnn <- (char '@' >> letAnnStr <* (void eol <|> sc)) <|> return PlainLet
  ~(ULet _ (p, ann) rhs, pos) <- withPos decl
  let (ann', rhs') = addImplicitImplicitArgs pos ann rhs
  return $ ULet lAnn (p, ann') rhs'

addImplicitImplicitArgs :: SrcPos -> Maybe UType -> UExpr -> (Maybe UType, UExpr)
addImplicitImplicitArgs _ Nothing e = (Nothing, e)
addImplicitImplicitArgs sourcePos (Just typ) ex =
  let (ty', e') = foldr (addImplicitArg sourcePos) (typ, ex) implicitVars
  in (Just ty', e')
  where
    implicitVars = filter isLowerCaseName $ envNames $ freeUVars typ
    isLowerCaseName :: Name -> Bool
    isLowerCaseName (Name _ tag _) = isLower $ head $ tagToStr tag
    isLowerCaseName _ = False

    addImplicitArg :: SrcPos -> Name -> (UType, UExpr) -> (UType, UExpr)
    addImplicitArg pos v (ty, e) =
      ( WithSrc (Just pos) $ UPi  (Bind (v:>uTyKind)) ImplicitArrow ty
      , WithSrc (Just pos) $ ULam (WithSrc (Just pos) (UPatBinder (Bind (v:>()))), Just uTyKind) ImplicitArrow e)
      where
        k = if v == mkName "eff" then EffectRowKind else TypeKind
        uTyKind = WithSrc (Just pos) $ UPrimExpr $ TCExpr k

interfaceDef :: Parser [UDecl]
interfaceDef = do
  keyWord InterfaceKW
  (tyCon, pos) <- withPos tyConDef
  keyWord WhereKW
  recordFieldsWithSrc <- withSrc $ interfaceRecordFields ":"
  let (UConDef interfaceName uAnnBinderNest) = tyCon
      record = (URecordTy . NoExt) <$> recordFieldsWithSrc
      consName = mkInterfaceConsName interfaceName
      varNames = fmap (\(Bind v) -> varName v) uAnnBinderNest
      (WithSrc _ recordFields) = recordFieldsWithSrc
      funDefs = mkFunDefs (pos, varNames, interfaceName) recordFields
  return $ (UData tyCon [UConDef consName (toNest [Ignore record])]) : funDefs
  where
    -- From an interface
    --   interface I a:Type b:Type where
    --     f : a -> b
    -- mkFunDefs generates the equivalent of the following function definition:
    --   def f (instance# : I a b) ?=> : a -> b =
    --     (I# {f=f,...}) = instance#
    --     f
    -- where I# is an automatically generated constructor of I.
    mkFunDefs
      :: (SrcPos, Nest Name, Name) -> LabeledItems UExpr -> [UDecl]
    mkFunDefs meta (LabeledItems items) =
        fmap (\(name, ty :| []) -> mkOneFunDef meta (name, ty)) $ M.toList items
    mkOneFunDef :: (SrcPos, Nest Name, Name) -> (Label, UExpr) -> UDecl
    mkOneFunDef (pos, typeVarNames, interfaceName) (fLabel, fType) =
      ULet PlainLet (p, ann') rhs'
      where
        uAnnBinder = Bind $
          instanceName :> (foldl mkUApp (var interfaceName) typeVarNames)
        p = patb fLabel
        ann = Just $ ns $ UPi uAnnBinder ClassArrow fType

        mkUApp func typeVarName =
          ns $ UApp (PlainArrow ()) func (var typeVarName)
        recordStr = "recordVar"
        recordPat = ns $ UPatRecord $ Ext (labeledSingleton fLabel (patb
          fLabel)) $ Just (ns (UPatBinder (Ignore ())))
        conPat = ns $ UPatCon (mkInterfaceConsName interfaceName)
          $ toNest [patb recordStr]

        let1 = ULet PlainLet (conPat, Nothing) $ var instanceName
        let2 = ULet PlainLet (recordPat, Nothing) $ var $ mkName recordStr
        body = ns $ UDecl let1 (ns $ UDecl let2 (var (mkName fLabel)))
        rhs = ns $ ULam (patb instanceStr, Nothing) ClassArrow body
        (ann', rhs') = addImplicitImplicitArgs pos ann rhs

        ns = WithSrc Nothing
        patb s = ns $ UPatBinder $ Bind $ mkName s :> ()
        instanceStr = mkNoShadowingStr "instance"
        instanceName = mkName instanceStr
        var name = ns $ UVar $ name :> ()

dataDef :: Parser UDecl
dataDef = do
  keyWord DataKW
  tyCon <- tyConDef
  sym "="
  dataCons <- onePerLine dataConDef
  return $ UData tyCon dataCons

-- TODO: default to `Type` if unannoted
tyConDef :: Parser UConDef
tyConDef = UConDef <$> (upperName <|> symName) <*> manyNested namedBinder

-- TODO: dependent types
dataConDef :: Parser UConDef
dataConDef = UConDef <$> upperName <*> manyNested dataConDefBinder

dataConDefBinder :: Parser UAnnBinder
dataConDefBinder = annBinder <|> (Ignore <$> containedExpr)

decl :: Parser UDecl
decl = do
  lhs <- simpleLet <|> funDefLet
  rhs <- sym "=" >> blockOrExpr
  return $ lhs rhs

interfaceInstance :: Parser UDecl
interfaceInstance = do
  keyWord InstanceKW
  (p, pos) <- withPos letPat
  ann <- annot uType
  case mkConstructorNameVar ann of
    Left err              -> fail err
    Right constructorNameVar -> do
      keyWord WhereKW
      record <- withSrc $ (URecord . NoExt) <$> interfaceRecordFields "="
      let constructorCall = constructorNameVar `mkApp` record
          (ann', rhs') = addImplicitImplicitArgs pos (Just ann) constructorCall
      return $ ULet InstanceLet (p, ann') rhs'
  where
    -- Here, we are traversing the type annotation to retrieve the name of
    -- the interface and generate its corresponding constructor. A valid type
    -- annotation for an instance is composed of:
    -- 1) implicit/class arguments
    -- 2) a function whose name is the name of the interface applied to 0 or
    --    more arguments
    mkConstructorNameVar ann =
      stripArrows ann >>= stripAppliedArgs >>= buildConstructor

    stripArrows (WithSrc _ (UPi _ arr typ))
      | arr `elem` [ClassArrow, ImplicitArrow] = stripArrows typ
      | otherwise = Left ("Met invalid arrow '" ++ pprint arr ++ "' in type " ++
                          "annotation of instance. Only class arrows and " ++
                          "implicit arrows are allowed.")
    stripArrows ann = Right ann

    stripAppliedArgs ann
      | (WithSrc _ (UApp _ func _)) <- ann = stripAppliedArgs func
      | otherwise = Right ann

    buildConstructor (WithSrc _ (UVar v)) =
      Right $ (var . nameToStr . mkInterfaceConsName . varName) v
    buildConstructor _ = Left ("Could not extract interface name from type " ++
                               "annotation.")
    var s = WithSrc Nothing $ UVar $ mkName s :> ()

interfaceRecordFields :: String -> Parser (LabeledItems UExpr)
interfaceRecordFields bindwith =
  fuse <$> onePerLine (do l <- fieldLabel
                          e <- symbol bindwith *> expr
                          return $ labeledSingleton l e)
  where fuse = foldr (<>) NoLabeledItems

simpleLet :: Parser (UExpr -> UDecl)
simpleLet = label "let binding" $ do
  p <- try $ (letPat <|> leafPat) <* lookAhead (sym "=" <|> sym ":")
  ann <- optional $ annot uType
  return $ ULet PlainLet (p, ann)

letPat :: Parser UPat
letPat = nameAsPat $ upperName <|> lowerName <|> symName

funDefLet :: Parser (UExpr -> UDecl)
funDefLet = label "function definition" $ mayBreak $ do
  keyWord DefKW
  v <- letPat
  bs <- some arg
  (eff, ty) <- label "result type annotation" $ annot effectiveType
  let piBinders = flip map bs $ \(p, ann, arr) -> (patAsBinder p ann, arr)
  let funTy = buildPiType piBinders eff ty
  let letBinder = (v, Just funTy)
  let lamBinders = flip map bs $ \(p,_, arr) -> ((p,Nothing), arr)
  return $ \body -> ULet PlainLet letBinder (buildLam lamBinders body)
  where
    arg :: Parser (UPat, UType, UArrow)
    arg = label "def arg" $ do
      (p, ty) <-parens ((,) <$> pat <*> annot uType)
      arr <- arrow (return ()) <|> return (PlainArrow ())
      return (p, ty, arr)

patAsBinder :: UPat -> UType -> UAnnBinder
patAsBinder (WithSrc _ (UPatBinder (Bind (v:>())))) ty = Bind $ v:>ty
patAsBinder _ ty = Ignore ty

nameAsPat :: Parser Name -> Parser UPat
nameAsPat p = withSrc $ (UPatBinder . Bind . (:>())) <$> p

buildPiType :: [(UAnnBinder, UArrow)] -> EffectRow -> UType -> UType
buildPiType [] _ _ = error "shouldn't be possible"
buildPiType ((b,arr):bs) eff ty = WithSrc pos $ case bs of
  [] -> UPi b (fmap (const eff ) arr) ty
  _  -> UPi b (fmap (const Pure) arr) $ buildPiType bs eff ty
  where WithSrc pos _ = binderAnn b

effectiveType :: Parser (EffectRow, UType)
effectiveType = (,) <$> effects <*> uType

effects :: Parser EffectRow
effects = braces someEffects <|> return Pure
  where
    someEffects = do
      effs <- liftM2 (,) effectName lowerName `sepBy` sym ","
      v <- optional $ symbol "|" >> lowerName
      return $ EffectRow effs v

effectName :: Parser EffectName
effectName =     (keyWord WriteKW $> Writer)
             <|> (keyWord ReadKW  $> Reader)
             <|> (keyWord StateKW $> State)
             <?> "effect name (Accum|Read|State)"

uLamExpr :: Parser UExpr
uLamExpr = do
  sym "\\"
  bs <- some patAnn
  arrowType <-
    (argTerm >> return (PlainArrow ()))
    <|> (arrow (return ()) >>= \case
          PlainArrow _ -> fail
            "To construct an explicit lambda function, use '.' instead of '->'\n"
          TabArrow -> fail
            "To construct a table, use 'for i. body' instead of '\\i => body'\n"
          arr -> return arr)
  body <- blockOrExpr
  return $ buildLam (map (,arrowType) bs) body

buildLam :: [(UPatAnn, UArrow)] -> UExpr -> UExpr
buildLam binders body@(WithSrc pos _) = case binders of
  [] -> body
  -- TODO: join with source position of binders too
  (b,arr):bs -> WithSrc (joinPos pos' pos) $ ULam b arr $ buildLam bs body
     where (WithSrc pos' _, _) = b

buildFor :: SrcPos -> Direction -> [UPatAnn] -> UExpr -> UExpr
buildFor pos dir binders body = case binders of
  [] -> body
  b:bs -> WithSrc (Just pos) $ UFor dir b $ buildFor pos dir bs body

uForExpr :: Parser UExpr
uForExpr = do
  (dir, pos) <- withPos $   (keyWord ForKW $> Fwd)
                        <|> (keyWord RofKW $> Rev)
  buildFor pos dir <$> (some patAnn <* argTerm) <*> blockOrExpr

blockOrExpr :: Parser UExpr
blockOrExpr =  block <|> expr

unitCon :: Parser UExpr
unitCon = withSrc $ symbol "()" $> (UPrimExpr $ ConExpr $ UnitCon)

uTabCon :: Parser UExpr
uTabCon = withSrc $ do
  xs <- brackets $ expr `sepBy` sym ","
  return $ UTabCon xs

type UStatement = (Either UDecl UExpr, SrcPos)

block :: Parser UExpr
block = withIndent $ do
  statements <- mayNotBreak $ uStatement `sepBy1` (semicolon <|> try nextLine)
  case last statements of
    (Left _, _) -> fail "Last statement in a block must be an expression."
    _           -> return $ wrapUStatements statements

wrapUStatements :: [UStatement] -> UExpr
wrapUStatements statements = case statements of
  [(Right e, _)] -> e
  (s, pos):rest -> WithSrc (Just pos) $ case s of
    Left  d -> UDecl d $ wrapUStatements rest
    Right e -> UDecl d $ wrapUStatements rest
      where d = ULet PlainLet (WithSrc (Just pos) (UPatBinder (Ignore ())), Nothing) e
  [] -> error "Shouldn't be reachable"

uStatement :: Parser UStatement
uStatement = withPos $   liftM Left  decl
                     <|> liftM Right expr

-- TODO: put the `try` only around the `x:` not the annotation itself
uPiType :: Parser UExpr
uPiType = withSrc $ UPi <$> annBinder <*> arrow effects <*> uType

annBinder :: Parser UAnnBinder
annBinder = try $ namedBinder <|> anonBinder

namedBinder :: Parser UAnnBinder
namedBinder = label "named annoted binder" $ lowerName
                                           >>= \v  -> sym ":" >> containedExpr
                                           >>= \ty -> return $ Bind (v:>ty)

anonBinder :: Parser UAnnBinder
anonBinder =
  label "anonymous annoted binder" $ Ignore <$> (underscore >> sym ":"
                                                            >> containedExpr)

arrow :: Parser eff -> Parser (ArrowP eff)
arrow p =   (sym "->"  >> liftM PlainArrow p)
        <|> (sym "=>"  $> TabArrow)
        <|> (sym "--o" $> LinArrow)
        <|> (sym "?->" $> ImplicitArrow)
        <|> (sym "?=>" $> ClassArrow)
        <?> "arrow"

caseExpr :: Parser UExpr
caseExpr = withSrc $ do
  keyWord CaseKW
  e <- expr
  keyWord OfKW
  alts <- onePerLine $ UAlt <$> pat <*> (sym "->" *> blockOrExpr)
  return $ UCase e alts

onePerLine :: Parser a -> Parser [a]
onePerLine p =   liftM (:[]) p
             <|> (withIndent $ mayNotBreak $ p `sepBy1` try nextLine)

pat :: Parser UPat
pat = makeExprParser leafPat patOps

leafPat :: Parser UPat
leafPat =
      (withSrc (symbol "()" $> UPatUnit))
  <|> parens pat
  <|> (withSrc $
          (UPatBinder <$>  (   (Bind <$> (:>()) <$> lowerName)
                           <|> (underscore $> Ignore ())))
      <|> (UPatCon    <$> upperName <*> manyNested pat)
      <|> (variantPat `fallBackTo` recordPat)
      <|> brackets (UPatTable <$> leafPat `sepBy` sym ",")
  )
  where pun pos l = WithSrc (Just pos) $ UPatBinder $ Bind (mkName l:>())
        def pos = WithSrc (Just pos) $ UPatBinder $ Ignore ()
        variantPat = parseVariant leafPat UPatVariant UPatVariantLift
        recordPat = UPatRecord <$> parseLabeledItems "," "=" leafPat
                                                     (Just pun) (Just def)

-- TODO: add user-defined patterns
patOps :: [[Operator Parser UPat]]
patOps = [[InfixR $ sym "," $> \x y -> joinSrc x y $ UPatPair x y]]

annot :: Parser a -> Parser a
annot p = label "type annotation" $ sym ":" >> p

patAnn :: Parser UPatAnn
patAnn = label "pattern" $ (,) <$> pat <*> optional (annot containedExpr)

uPrim :: Parser UExpr
uPrim = withSrc $ do
  s <- primName
  case s of
    "ffi" -> do
      f <- lexeme $ some nameTailChar
      retTy <- leafExpr
      args <- some leafExpr
      return $ UPrimExpr $ OpExpr $ FFICall f retTy args
    _ -> case strToPrimName s of
      Just prim -> UPrimExpr <$> traverse (const leafExpr) prim
      Nothing -> fail $ "Unrecognized primitive: " ++ s

uVariantExpr :: Parser UExpr
uVariantExpr = withSrc $ parseVariant expr UVariant UVariantLift

parseVariant :: Parser a -> (LabeledItems () -> Label -> a -> b) -> (LabeledItems () -> a -> b) -> Parser b
parseVariant subparser buildLabeled buildExt =
  bracketed (symbol "{|") (symbol "|}") $ do
    let parseInactive = try $ fieldLabel <* notFollowedBy (symbol "=")
    inactiveLabels <- parseInactive `endBy1` (symbol "|") <|> pure []
    let inactiveItems = foldr (<>) NoLabeledItems $ map (flip labeledSingleton ()) inactiveLabels
    let parseLabeled = do l <- fieldLabel
                          symbol "="
                          buildLabeled inactiveItems l <$> subparser
    let parseExt = do symbol "..."
                      buildExt inactiveItems <$> subparser
    parseLabeled <|> parseExt

uLabeledExprs :: Parser UExpr
uLabeledExprs = withSrc $
    (URecord <$> build "," "=" (Just varPun) Nothing)
    `fallBackTo` (URecordTy <$> build "&" ":" Nothing Nothing)
    `fallBackTo` (UVariantTy <$> build "|" ":" Nothing Nothing)
  where build sep bindwith = parseLabeledItems sep bindwith expr

varPun :: SrcPos -> Label -> UExpr
varPun pos str = WithSrc (Just pos) $ UVar (mkName str :> ())

uIsoSugar :: Parser UExpr
uIsoSugar = withSrc (char '#' *> options) where
  options = (recordFieldIso <$> fieldLabel)
            <|> char '?' *> (variantFieldIso <$> fieldLabel)
            <|> char '&' *> (recordZipIso <$> fieldLabel)
            <|> char '|' *> (variantZipIso <$> fieldLabel)
  ns = WithSrc Nothing
  var s = ns $ UVar $ mkName s :> ()
  patb s = ns $ UPatBinder $ Bind $ mkName s :> ()
  plain = PlainArrow ()
  lam p b = ns $ ULam (p, Nothing) plain b
  recordFieldIso field =
    UApp plain (var "MkIso") $
      ns $ URecord $ NoExt $
        labeledSingleton "fwd" (lam
          (ns $ UPatRecord $ Ext (labeledSingleton field (patb "x"))
                                       (Just $ patb "r"))
          $ (var "(,)") `mkApp` (var "x") `mkApp` (var "r")
        )
        <> labeledSingleton "bwd" (lam
          (ns $ UPatPair (patb "x") (patb "r"))
          $ ns $ URecord $ Ext (labeledSingleton field $ var "x")
                               $ Just $ var "r"
        )
  variantFieldIso field =
    UApp plain (var "MkIso") $
      ns $ URecord $ NoExt $
        labeledSingleton "fwd" (lam (patb "v") $ ns $ UCase (var "v")
            [ UAlt (ns $ UPatVariant NoLabeledItems field (patb "x"))
                $ var "Left" `mkApp` var "x"
            , UAlt (ns $ UPatVariantLift (labeledSingleton field ()) (patb "r"))
                $ var "Right" `mkApp` var "r"
            ]
        )
        <> labeledSingleton "bwd" (lam (patb "v") $ ns $ UCase (var "v")
            [ UAlt (ns $ UPatCon (mkName "Left") (toNest [patb "x"]))
                $ ns $ UVariant NoLabeledItems field $ var "x"
            , UAlt (ns $ UPatCon (mkName "Right") (toNest [patb "r"]))
                $ ns $ UVariantLift (labeledSingleton field ()) $ var "r"
            ]
        )
  recordZipIso field =
    UApp plain (var "MkIso") $
      ns $ URecord $ NoExt $
        labeledSingleton "fwd" (lam
          (ns $ UPatPair
            (ns $ UPatRecord $ Ext NoLabeledItems $ Just $ patb "l")
            (ns $ UPatRecord $ Ext (labeledSingleton field $ patb "x")
                                   $ Just $ patb "r"))
          $ (var "(,)")
            `mkApp` (ns $ URecord $ Ext (labeledSingleton field $ var "x")
                                        $ Just $ var "l")
            `mkApp` (ns $ URecord $ Ext NoLabeledItems $ Just $ var "r")
        )
        <> labeledSingleton "bwd" (lam
          (ns $ UPatPair
            (ns $ UPatRecord $ Ext (labeledSingleton field $ patb "x")
                                   $ Just $ patb "l")
            (ns $ UPatRecord $ Ext NoLabeledItems $ Just $ patb "r"))
          $ (var "(,)")
            `mkApp` (ns $ URecord $ Ext NoLabeledItems $ Just $ var "l")
            `mkApp` (ns $ URecord $ Ext (labeledSingleton field $ var "x")
                                        $ Just $ var "r")
        )
  variantZipIso field =
    UApp plain (var "MkIso") $
      ns $ URecord $ NoExt $
        labeledSingleton "fwd" (lam (patb "v") $ ns $ UCase (var "v")
            [ UAlt (ns $ UPatCon (mkName "Left") (toNest [patb "l"]))
                $ var "Left" `mkApp` (ns $
                    UVariantLift (labeledSingleton field ()) $ var "l")
            , UAlt (ns $ UPatCon (mkName "Right") (toNest [patb "w"]))
                $ ns $ UCase (var "w")
                [ UAlt (ns $ UPatVariant NoLabeledItems field (patb "x"))
                    $ var "Left" `mkApp` (ns $
                        UVariant NoLabeledItems field $ var "x")
                , UAlt (ns $ UPatVariantLift (labeledSingleton field ())
                                             (patb "r"))
                    $ var "Right" `mkApp` var "r"
                ]
            ]
        )
        <> labeledSingleton "bwd" (lam (patb "v") $ ns $ UCase (var "v")
            [ UAlt (ns $ UPatCon (mkName "Left") (toNest [patb "w"]))
                $ ns $ UCase (var "w")
                [ UAlt (ns $ UPatVariant NoLabeledItems field (patb "x"))
                    $ var "Right" `mkApp` (ns $
                        UVariant NoLabeledItems field $ var "x")
                , UAlt (ns $ UPatVariantLift (labeledSingleton field ())
                                             (patb "r"))
                    $ var "Left" `mkApp` var "r"
                ]
            , UAlt (ns $ UPatCon (mkName "Right") (toNest [patb "l"]))
                $ var "Right" `mkApp` (ns $
                    UVariantLift (labeledSingleton field ()) $ var "l")
            ]
        )

parseLabeledItems
  :: String -> String -> Parser a
  -> Maybe (SrcPos -> Label -> a) -> Maybe (SrcPos -> a)
  -> Parser (ExtLabeledItems a a)
parseLabeledItems sep bindwith itemparser punner tailDefault =
  bracketed lBrace rBrace $ atBeginning
  where
    atBeginning = someItems
                  <|> (symbol sep >> (stopAndExtend <|> stopWithoutExtend))
                  <|> stopWithoutExtend
    stopWithoutExtend = return $ NoExt NoLabeledItems
    stopAndExtend = do
      ((), pos) <- withPos $ symbol "..."
      rest <- case tailDefault of
        Just def -> itemparser <|> pure (def pos)
        Nothing -> itemparser
      return $ Ext NoLabeledItems (Just rest)
    beforeSep = (symbol sep >> afterSep) <|> stopWithoutExtend
    afterSep = someItems <|> stopAndExtend <|> stopWithoutExtend
    someItems = do
      (l, pos) <- withPos fieldLabel
      let explicitBound = symbol bindwith *> itemparser
      itemVal <- case punner of
        Just punFn -> explicitBound <|> pure (punFn pos l)
        Nothing -> explicitBound
      rest <- beforeSep
      return $ prefixExtLabeledItems (labeledSingleton l itemVal) rest

-- Combine two parsers such that if the first fails, we try the second one.
-- If both fail, consume the same amount of input as the parser that
-- consumed the most input, and use its error message. Useful if you want
-- to parse multiple things, but they share some common starting symbol, and
-- you don't want the first one failing to prevent the second from succeeding.
-- Unlike using `try` and/or (<|>), if both parsers fail and either one consumes
-- input, parsing is aborted. Also, if both parsers consume the same amount of
-- input, we combine the symbols each was expecting.
fallBackTo :: Parser a -> Parser a -> Parser a
fallBackTo optionA optionB = do
  startState <- getParserState
  resA <- observing $ optionA
  case resA of
    Right val -> return val
    Left errA -> do
      stateA <- getParserState
      updateParserState $ const startState
      resB <- observing $ optionB
      case resB of
        Right val -> return val
        Left errB -> case compare (errorOffset errA) (errorOffset errB) of
          LT -> parseError errB
          GT -> updateParserState (const stateA) >> parseError errA
          EQ -> case (errA, errB) of
            -- Combine what each was expecting.
            (TrivialError offset unexpA expA, TrivialError _ unexpB expB)
                -> parseError $ TrivialError offset (unexpA <|> unexpB)
                                                    (expA <> expB)
            _ -> fail $ "Multiple failed parse attempts:\n"
                  <> parseErrorPretty errA <> "\n" <> parseErrorPretty errB

-- === infix ops ===

-- literal symbols here must only use chars from `symChars`
ops :: [[Operator Parser UExpr]]
ops =
  [ [InfixL $ sym "." $> mkGenApp TabArrow, symOp "!"]
  , [InfixL $ sc $> mkApp]
  , [prefixNegOp]
  , [anySymOp] -- other ops with default fixity
  , [symOp "+", symOp "-", symOp "||", symOp "&&",
     InfixR $ sym "=>" $> mkArrow TabArrow,
     InfixL $ opWithSrc $ backquoteName >>= (return . binApp),
     symOp "<<<", symOp ">>>", symOp "<<&", symOp "&>>"]
  , [annotatedExpr]
  , [InfixR $ mayBreak (infixSym "$") $> mkApp]
  , [symOp "+=", symOp ":=", InfixL $ pairingSymOpP "|", InfixR infixArrow]
  , [InfixR $ pairingSymOpP "&", InfixR $ pairingSymOpP ","]
  , indexRangeOps
  ]

opWithSrc :: Parser (SrcPos -> a -> a -> a)
          -> Parser (a -> a -> a)
opWithSrc p = do
  (f, pos) <- withPos p
  return $ f pos

anySymOp :: Operator Parser UExpr
anySymOp = InfixL $ opWithSrc $ do
  s <- label "infix operator" (mayBreak anySym)
  return $ binApp $ mkSymName s

infixSym :: String -> Parser ()
infixSym s = mayBreak $ sym s

symOp :: String -> Operator Parser UExpr
symOp s = InfixL $ symOpP s

symOpP :: String -> Parser (UExpr -> UExpr -> UExpr)
symOpP s = opWithSrc $ do
  label "infix operator" (infixSym s)
  return $ binApp $ mkSymName s

pairingSymOpP :: String -> Parser (UExpr -> UExpr -> UExpr)
pairingSymOpP s = opWithSrc $ do
  allowed <- asks canPair
  if allowed
    then infixSym s >> return (binApp (mkSymName s))
    else fail $ "Unexpected delimiter " <> s

mkSymName :: String -> Name
mkSymName s = mkName $ "(" <> s <> ")"

prefixNegOp :: Operator Parser UExpr
prefixNegOp = Prefix $ label "negation" $ do
  ((), pos) <- withPos $ sym "-"
  let f = WithSrc (Just pos) $ UVar $ mkName "neg" :> ()
  return $ \case
    -- Special case: negate literals directly
    WithSrc litpos (IntLitExpr i)
      -> WithSrc (joinPos (Just pos) litpos) (IntLitExpr (-i))
    WithSrc litpos (FloatLitExpr i)
      -> WithSrc (joinPos (Just pos) litpos) (FloatLitExpr (-i))
    x -> mkApp f x

binApp :: Name -> SrcPos -> UExpr -> UExpr -> UExpr
binApp f pos x y = (f' `mkApp` x) `mkApp` y
  where f' = WithSrc (Just pos) $ UVar (f:>())

mkGenApp :: UArrow -> UExpr -> UExpr -> UExpr
mkGenApp arr f x = joinSrc f x $ UApp arr f x

mkApp :: UExpr -> UExpr -> UExpr
mkApp f x = joinSrc f x $ UApp (PlainArrow ()) f x

infixArrow :: Parser (UType -> UType -> UType)
infixArrow = do
  notFollowedBy (sym "=>")  -- table arrows have special fixity
  (arr, pos) <- withPos $ arrow effects
  return $ \a b -> WithSrc (Just pos) $ UPi (Ignore a) arr b

mkArrow :: Arrow -> UExpr -> UExpr -> UExpr
mkArrow arr a b = joinSrc a b $ UPi (Ignore a) arr b

withSrc :: Parser a -> Parser (WithSrc a)
withSrc p = do
  (x, pos) <- withPos p
  return $ WithSrc (Just pos) x

joinSrc :: WithSrc a -> WithSrc b -> c -> WithSrc c
joinSrc (WithSrc p1 _) (WithSrc p2 _) x = WithSrc (joinPos p1 p2) x

joinPos :: Maybe SrcPos -> Maybe SrcPos -> Maybe SrcPos
joinPos Nothing p = p
joinPos p Nothing = p
joinPos (Just (l, h)) (Just (l', h')) = Just (min l l', max h h')

indexRangeOps :: [Operator Parser UExpr]
indexRangeOps =
  [ Prefix    $ symPos ".."   <&> \pos h   -> range pos  Unlimited       (InclusiveLim h)
  , inpostfix $ symPos ".."   <&> \pos l h -> range pos (InclusiveLim l) (limFromMaybe h)
  , inpostfix $ symPos "<.."  <&> \pos l h -> range pos (ExclusiveLim l) (limFromMaybe h)
  , Prefix    $ symPos "..<"  <&> \pos h   -> range pos  Unlimited       (ExclusiveLim h)
  , InfixL    $ symPos "..<"  <&> \pos l h -> range pos (InclusiveLim l) (ExclusiveLim h)
  , InfixL    $ symPos "<..<" <&> \pos l h -> range pos (ExclusiveLim l) (ExclusiveLim h) ]
  where
    range pos l h = WithSrc (Just pos) $ UIndexRange l h
    symPos s = snd <$> withPos (sym s)

limFromMaybe :: Maybe a -> Limit a
limFromMaybe Nothing = Unlimited
limFromMaybe (Just x) = InclusiveLim x

annotatedExpr :: Operator Parser UExpr
annotatedExpr = InfixL $ opWithSrc $
  sym ":" $> (\pos v ty -> WithSrc (Just pos) $ UTypeAnn v ty)

inpostfix :: Parser (UExpr -> Maybe UExpr -> UExpr) -> Operator Parser UExpr
inpostfix = inpostfix' expr

inpostfix' :: Parser a -> Parser (a -> Maybe a -> a) -> Operator Parser a
inpostfix' p op = Postfix $ do
  f <- op
  rest <- optional p
  return $ \x -> f x rest

mkName :: String -> Name
mkName s = Name SourceName (fromString s) 0

nameToStr :: Name -> String
nameToStr = tagToStr . nameTag

-- This function is used to generate a string that is guaranteed to never shadow
-- any user-defined name, as "#" is an invalid identifier character in normal
-- source code.
mkNoShadowingStr :: String -> String
mkNoShadowingStr = (++ "#")

mkInterfaceConsName :: Name -> Name
mkInterfaceConsName =
  GlobalName . fromString . mkNoShadowingStr . nameToStr

-- === lexemes ===

-- These `Lexer` actions must be non-overlapping and never consume input on failure
type Lexer = Parser

data KeyWord = DefKW | ForKW | RofKW | CaseKW | OfKW
             | ReadKW | WriteKW | StateKW | DataKW | InterfaceKW
             | InstanceKW | WhereKW

upperName :: Lexer Name
upperName = liftM mkName $ label "upper-case name" $ lexeme $
  checkNotKeyword $ (:) <$> upperChar <*> many nameTailChar

lowerName  :: Lexer Name
lowerName = liftM mkName $ label "lower-case name" $ lexeme $
  checkNotKeyword $ (:) <$> lowerChar <*> many nameTailChar

checkNotKeyword :: Parser String -> Parser String
checkNotKeyword p = try $ do
  s <- p
  failIf (s `elem` keyWordStrs) $ show s ++ " is a reserved word"
  return s

keyWord :: KeyWord -> Lexer ()
keyWord kw = lexeme $ try $ string s >> notFollowedBy nameTailChar
  where
    s = case kw of
      DefKW  -> "def"
      ForKW  -> "for"
      RofKW  -> "rof"
      CaseKW -> "case"
      OfKW   -> "of"
      ReadKW  -> "Read"
      WriteKW -> "Accum"
      StateKW -> "State"
      DataKW -> "data"
      InterfaceKW -> "interface"
      InstanceKW -> "instance"
      WhereKW -> "where"

keyWordStrs :: [String]
keyWordStrs = ["def", "for", "rof", "case", "of", "llam",
               "Read", "Write", "Accum", "data", "interface",
               "instance", "where"]

fieldLabel :: Lexer Label
fieldLabel = label "field label" $ lexeme $
  checkNotKeyword $ (:) <$> (lowerChar <|> upperChar) <*> many nameTailChar

primName :: Lexer String
primName = lexeme $ try $ char '%' >> some alphaNumChar

charLit :: Lexer Char
charLit = lexeme $ char '\'' >> L.charLiteral <* char '\''

strLit :: Lexer String
strLit = lexeme $ char '"' >> manyTill L.charLiteral (char '"')

intLit :: Lexer Int
intLit = lexeme $ try $ L.decimal <* notFollowedBy (char '.')

doubleLit :: Lexer Double
doubleLit = lexeme $
      try L.float
  <|> try (fromIntegral <$> (L.decimal :: Parser Int) <* char '.')

knownSymStrs :: [String]
knownSymStrs = [".", ":", "!", "=", "-", "+", "||", "&&", "$", "&", "|", ",", "+=", ":=",
                "->", "=>", "?->", "?=>", "--o", "--", "<<<", ">>>", "<<&", "&>>",
                "..", "<..", "..<", "..<", "<..<"]

-- string must be in `knownSymStrs`
sym :: String -> Lexer ()
sym s = lexeme $ try $ string s >> notFollowedBy symChar

anySym :: Lexer String
anySym = lexeme $ try $ do
  s <- some symChar
  -- TODO: consider something faster than linear search here
  failIf (s `elem` knownSymStrs) ""
  return s

symName :: Lexer Name
symName = label "symbol name" $ lexeme $ try $ do
  s <- between (char '(') (char ')') $ some symChar
  return $ mkName $ "(" <> s <> ")"

backquoteName :: Lexer Name
backquoteName = label "backquoted name" $
  lexeme $ try $ between (char '`') (char '`') (upperName <|> lowerName)

-- brackets and punctuation
-- (can't treat as sym because e.g. `((` is two separate lexemes)
lParen, rParen, lBracket, rBracket, lBrace, rBrace, semicolon, underscore :: Lexer ()

lParen    = notFollowedBy symName >> notFollowedBy unitCon >> charLexeme '('
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
symChar = choice $ map char symChars

symChars :: [Char]
symChars = ".,!$^&*:-~+/=<>|?\\@"

-- === Util ===

runTheParser :: String -> Parser a -> Either (ParseErrorBundle String Void) a
runTheParser s p = parse (runReaderT p (ParseCtx 0 False False)) "" s

sc :: Parser ()
sc = L.space space lineComment empty

lineComment :: Parser ()
lineComment = do
  try $ string "--" >> notFollowedBy (void (char 'o'))
  void (takeWhileP (Just "char") (/= '\n'))

emptyLines :: Parser ()
emptyLines = void $ many (sc >> eol)

outputLines :: Parser ()
outputLines = void $ many (symbol ">" >> takeWhileP Nothing (/= '\n') >> ((eol >> return ()) <|> eof))

stringLiteral :: Parser String
stringLiteral = char '"' >> manyTill L.charLiteral (char '"') <* sc

space :: Parser ()
space = do
  consumeNewLines <- asks canBreak
  if consumeNewLines
    then space1
    else void $ takeWhile1P (Just "white space") (`elem` (" \t" :: String))

mayBreak :: Parser a -> Parser a
mayBreak p = local (\ctx -> ctx { canBreak = True }) p

mayNotBreak :: Parser a -> Parser a
mayNotBreak p = local (\ctx -> ctx { canBreak = False }) p

mayPair :: Parser a -> Parser a
mayPair p = local (\ctx -> ctx { canPair = True }) p

mayNotPair :: Parser a -> Parser a
mayNotPair p = local (\ctx -> ctx { canPair = False }) p

nameString :: Parser String
nameString = lexeme . try $ (:) <$> lowerChar <*> many alphaNumChar

thisNameString :: String -> Parser ()
thisNameString s = lexeme $ try $ string s >> notFollowedBy alphaNumChar

uint :: Parser Int
uint = L.decimal <* sc

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: String -> Parser ()
symbol s = void $ L.symbol sc s

argTerm :: Parser ()
argTerm = mayNotBreak $ sym "."

bracketed :: Parser () -> Parser () -> Parser a -> Parser a
bracketed left right p = between left right $ mayBreak p

parens :: Parser a -> Parser a
parens p = bracketed lParen rParen p

brackets :: Parser a -> Parser a
brackets p = bracketed lBracket rBracket p

braces :: Parser a -> Parser a
braces p = bracketed lBrace rBrace p

manyNested :: Parser a -> Parser (Nest a)
manyNested p = toNest <$> many p

withPos :: Parser a -> Parser (a, SrcPos)
withPos p = do
  n <- getOffset
  x <- p
  n' <- getOffset
  return $ (x, (n, n'))

nextLine :: Parser ()
nextLine = do
  void eol
  n <- asks curIndent
  void $ mayNotBreak $ many $ try (sc >> eol)
  void $ replicateM n (char ' ')

withSource :: Parser a -> Parser (String, a)
withSource p = do
  s <- getInput
  (x, (start, end)) <- withPos p
  return (take (end - start) s, x)

withIndent :: Parser a -> Parser a
withIndent p = do
  nextLine
  indent <- liftM length $ some (char ' ')
  local (\ctx -> ctx { curIndent = curIndent ctx + indent }) $ p

eolf :: Parser ()
eolf = void eol <|> eof

failIf :: Bool -> String -> Parser ()
failIf True s = fail s
failIf False _ = return ()

_debug :: Show a => String -> Parser a -> Parser a
_debug s m = mapReaderT (Text.Megaparsec.Debug.dbg s) m
