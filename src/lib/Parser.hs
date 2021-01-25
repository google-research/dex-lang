-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module Parser (parseProg) where

-- module Parser (
--   Parser, parseit, parseProg, runTheParser, parseData,
--   parseTopDeclRepl, uint, withSource, parseExpr, exprAsModule,
--   emptyLines, brackets, symbol, symChar, keyWordStrs
--   ) where

import Control.Monad
import Control.Monad.Combinators.Expr
import Control.Monad.Reader
import Text.Megaparsec hiding (Label, State)
import Text.Megaparsec.Char hiding (space, eol)
import qualified Text.Megaparsec.Char as MC
import Data.Char (isLower)
import Data.Functor
import Data.List.NonEmpty (NonEmpty (..))
import Data.Void
import qualified Data.Set as S
import Data.String (fromString)
import qualified Text.Megaparsec.Char.Lexer as L
import qualified Text.Megaparsec.Debug

import Err
import Naming
import Syntax
import LabeledItems
import HigherKinded
import Util (pprint)

-- -- canPair is used for the ops (,) (|) (&) which should only appear inside
-- -- parentheses (to avoid conflicts with records and other syntax)
-- data ParseCtx = ParseCtx { curIndent :: Int
--                          , canPair   :: Bool
--                          , canBreak  :: Bool }
-- type Parser = ReaderT ParseCtx (Parsec Void String)

-- type SUType   = UType   SourceNS
-- type SUExpr   = UExpr   SourceNS
-- type SUExpr'  = UExpr'  SourceNS
-- type SUDecl   = UDecl   SourceNS
-- type SUPat    = UPat    SourceNS
-- type SUPat'   = UPat'   SourceNS
-- type SUModule = UModule SourceNS
-- type SUAlt    = UAlt    SourceNS

parseProg :: String -> [SourceBlock]
parseProg = undefined
-- parseProg s = mustParseit s $ manyTill (sourceBlock <* outputLines) eof

-- parseData :: String -> Except SUExpr
-- parseData s = parseit s $ expr <* (optional eol >> eof)

-- parseTopDeclRepl :: String -> Maybe SourceBlock
-- parseTopDeclRepl s = case sbContents b of
--   UnParseable True _ -> Nothing
--   _ -> Just b
--   where b = mustParseit s sourceBlock

-- parseExpr :: String -> Except SUExpr
-- parseExpr s = parseit s (expr <* eof)

-- parseit :: String -> Parser a -> Except a
-- parseit s p = case runTheParser s (p <* (optional eol >> eof)) of
--   Left e -> throw ParseErr (errorBundlePretty e)
--   Right x -> return x

-- mustParseit :: String -> Parser a -> a
-- mustParseit s p  = case parseit s p of
--   Right ans -> ans
--   Left e -> error $ "This shouldn't happen:\n" ++ pprint e

-- importModule :: Parser SourceBlock'
-- importModule = ImportModule <$> do
--   keyWord ImportKW
--   s <- (:) <$> letterChar <*> many alphaNumChar
--   eol
--   return s

-- sourceBlock :: Parser SourceBlock
-- sourceBlock = do
--   offset <- getOffset
--   pos <- getSourcePos
--   (src, (level, b)) <- withSource $ withRecovery recover $ do
--     level <- logLevel <|> logTime <|> logBench <|> return LogNothing
--     b <- sourceBlock'
--     return (level, b)
--   return $ SourceBlock (unPos (sourceLine pos)) offset level src b

-- recover :: ParseError String Void -> Parser (LogLevel, SourceBlock')
-- recover e = do
--   pos <- liftM statePosState getParserState
--   reachedEOF <-  try (mayBreak sc >> eof >> return True)
--              <|> return False
--   consumeTillBreak
--   let errmsg = errorBundlePretty (ParseErrorBundle (e :| []) pos)
--   return (LogNothing, UnParseable reachedEOF errmsg)

-- consumeTillBreak :: Parser ()
-- consumeTillBreak = void $ manyTill anySingle $ eof <|> void (try (eol >> eol))

-- logLevel :: Parser LogLevel
-- logLevel = do
--   void $ try $ lexeme $ char '%' >> string "passes"
--   passes <- many passName
--   eol
--   case passes of
--     [] -> return LogAll
--     _ -> return $ LogPasses passes

-- logTime :: Parser LogLevel
-- logTime = do
--   void $ try $ lexeme $ char '%' >> string "time"
--   eol
--   return PrintEvalTime

-- logBench :: Parser LogLevel
-- logBench = do
--   void $ try $ lexeme $ char '%' >> string "bench"
--   benchName <- stringLiteral
--   eol
--   return $ PrintBench benchName

-- passName :: Parser PassName
-- passName = choice [thisNameString s $> x | (s, x) <- passNames]

-- passNames :: [(String, PassName)]
-- passNames = [(show x, x) | x <- [minBound..maxBound]]

-- sourceBlock' :: Parser SourceBlock'
-- sourceBlock' =
--       proseBlock
--   <|> topLevelCommand
--   -- <|> liftM declToModule (topDecl <* eolf)
--   -- <|> liftM declToModule (instanceDef True  <* eolf)
--   -- <|> liftM declToModule (instanceDef False <* eolf)
--   -- <|> liftM declToModule (interfaceDef <* eolf)
--   <|> liftM (Command (EvalExpr Printed) . exprAsModule) (expr <* eol)
--   <|> hidden (some eol >> return EmptyLines)
--   <|> hidden (sc >> eol >> return CommentLine)
--   -- where
--   --   declsToModule = RunModule . SUModule . toUNest
--   --   declToModule = declsToModule . (:[])

-- proseBlock :: Parser SourceBlock'
-- proseBlock = label "prose block" $ char '\'' >> fmap (ProseBlock . fst) (withSource consumeTillBreak)

-- topLevelCommand :: Parser SourceBlock'
-- topLevelCommand =
--       importModule
--   <|> explicitCommand
--   <?> "top-level command"

-- explicitCommand :: Parser SourceBlock'
-- explicitCommand = do
--   cmdName <- char ':' >> nameString
--   cmd <- case cmdName of
--     "p"       -> return $ EvalExpr Printed
--     "t"       -> return $ GetType
--     "html"    -> return $ EvalExpr RenderHtml
--     "export"  -> ExportFun <$> nameString
--     _ -> fail $ "unrecognized command: " ++ show cmdName
--   e <- blockOrExpr <* eolf
--   return $ case (e, cmd) of
--     (WithSrcH _ (UVar v), GetType) -> GetNameType v
--     _ -> Command cmd (exprAsModule e)

-- exprAsModule :: SUExpr -> (SourceName, SUModule)
-- exprAsModule = undefined
-- -- exprAsModule e = (v, UModule (toUNest [d]))
-- --   where
-- --     v = mkName "_ans_"
-- --     d = ULet PlainLet (WithSrcH (srcPos e) (nameToPat v), Nothing) e

-- -- === uexpr ===

-- expr :: Parser SUExpr
-- expr = mayNotPair $ makeExprParser leafExpr ops

-- -- expression without exposed infix operators
-- leafExpr :: Parser SUExpr
-- leafExpr = parens (mayPair $ makeExprParser leafExpr ops)
--          <|> uTabCon
--          <|> uVarOcc
--          <|> uHole
--          <|> uString
--          <|> uLit
--          <|> uPiType
--          <|> uLamExpr
--          <|> uViewExpr
--          <|> uForExpr
--          <|> caseExpr
--          <|> ifExpr
--          <|> uPrim
--          <|> unitCon
--          <|> (uLabeledExprs `fallBackTo` uVariantExpr)
--          <|> uIsoSugar
--          <|> uDoSugar
--          <?> "expression"

-- containedExpr :: Parser SUExpr
-- containedExpr =   parens (mayPair $ makeExprParser leafExpr ops)
--               <|> uVarOcc
--               <|> uLabeledExprs
--               <?> "contained expression"

-- uType :: Parser SUType
-- uType = expr

-- uString :: Lexer SUExpr
-- uString = do
--   (s, pos) <- withPos $ strLit
--   let addSrc = WithSrcH (Just pos)
--   let cs = map (addSrc . charExpr) s
--   return $ mkApp (ns (UVar "toList")) $ addSrc $ UTabCon cs

-- uLit :: Parser SUExpr
-- uLit = withSrc $ uLitParser
--   where uLitParser = charExpr <$> charLit
--                  <|> UIntLit  <$> intLit
--                  <|> UFloatLit <$> doubleLit
--                  <?> "literal"

-- charExpr :: Char -> SUExpr'
-- charExpr c = UPrimExpr $ ConExpr $ Lit $ Word8Lit $ fromIntegral $ fromEnum c

-- uVarOcc :: Parser SUExpr
-- uVarOcc = withSrc $ try $ UVar <$> (anyName <* notFollowedBy (sym ":"))

-- uHole :: Parser SUExpr
-- uHole = withSrc $ underscore $> UHole

-- letAnnStr :: Parser LetAnn
-- letAnnStr =   (string "instance"   $> InstanceLet)
--           <|> (string "superclass" $> SuperclassLet)
--           <|> (string "noinline"   $> NoInlineLet)

-- topDecl :: Parser SUDecl
-- topDecl = dataDef <|> topLet

-- topLet :: Parser SUDecl
-- topLet = do
--   lAnn <- (char '@' >> letAnnStr <* (eol <|> sc)) <|> return PlainLet
--   ~(ULet _ ann rhs abs) <- decl
--   let (ann', rhs') = addImplicitImplicitArgs ann rhs
--   return $ ULet lAnn ann' rhs' abs

-- -- Given a type signature, find all "implicit implicit args": lower-case
-- -- identifiers, not explicitly bound by Pi binders, not appearing on the left
-- -- hand side of an application. These identifiers are implicit in the sense
-- -- that they will be solved for by type inference, and also implicit in the
-- -- sense that the user did NOT explicitly annotate them as implicit.
-- findImplicitImplicitArgNames :: SUType -> [SourceName]
-- findImplicitImplicitArgNames = undefined
-- -- findImplicitImplicitArgNames typ = filter isLowerCaseName $ envNames $
-- --     freeUVars typ `envDiff` findVarsInAppLHS typ
-- --   where

-- --   isLowerCaseName :: Name n -> Bool
-- --   isLowerCaseName = undefined
-- --   -- isLowerCaseName name = isLower $ head $ nameStrToStr $ getNameStr name
-- --   -- isLowerCaseName _ = False

-- --   -- Finds all variables used in the left hand of an application, which should
-- --   -- be filtered out and not automatically inferred.
-- --   findVarsInAppLHS :: SUType -> Scope SourceNS
-- --   findVarsInAppLHS (WithSrcH _ typ') = case typ' of
-- --     -- base case
-- --     UApp _ (WithSrcH _ (UVar v)) x -> v@>UnitH <> findVarsInAppLHS x
-- --     -- recursive steps
-- --     UVar _ -> mempty
-- --     -- UPi (p, ann) _ ty ->
-- --     --   foldMap findVarsInAppLHS ann <> (findVarsInAppLHS ty `envDiff` boundUVars p)
-- --     UApp _ f x -> findVarsInAppLHS f <> findVarsInAppLHS x
-- --     -- ULam (p, ann)  x ->
-- --     --   foldMap findVarsInAppLHS ann <> (findVarsInAppLHS x `envDiff` boundUVars p)
-- --     -- UDecl _ _ -> error "Unexpected let binding in type annotation"
-- --     UFor _ _ -> error "Unexpected for in type annotation"
-- --     UHole -> mempty
-- --     UTypeAnn v ty -> findVarsInAppLHS v <> findVarsInAppLHS ty
-- --     UTabCon _ -> error "Unexpected table constructor in type annotation"
-- --     UIndexRange low high ->
-- --       foldMap findVarsInAppLHS low <> foldMap findVarsInAppLHS high
-- --     UPrimExpr prim -> foldMap findVarsInAppLHS prim
-- --     UCase _ _ -> error "Unexpected case in type annotation"
-- --     URecord (Ext ulr _) -> foldMap findVarsInAppLHS ulr
-- --     UVariant _ _ val -> findVarsInAppLHS val
-- --     URecordTy (Ext ulr v) ->
-- --       foldMap findVarsInAppLHS ulr <> foldMap findVarsInAppLHS v
-- --     UVariantTy (Ext ulr v) ->
-- --       foldMap findVarsInAppLHS ulr <> foldMap findVarsInAppLHS v
-- --     UVariantLift _ val -> findVarsInAppLHS val
-- --     UIntLit  _ -> mempty
-- --     UFloatLit _ -> mempty

-- addImplicitImplicitArgs :: Maybe SUType -> SUExpr -> (Maybe SUType, SUExpr)
-- addImplicitImplicitArgs Nothing e = (Nothing, e)
-- -- addImplicitImplicitArgs (Just typ) ex =
-- --   let (ty', e') = foldr addImplicitArg (typ, ex) implicitVars
-- --   in (Just ty', e')
-- --   where
-- --     implicitVars = findImplicitImplicitArgNames typ

-- --     addImplicitArg :: SourceName -> (SUType, SUExpr) -> (SUType, SUExpr)
-- --     addImplicitArg v (ty, e) =
-- --       ( ns $ UPi  (uPat, Nothing) ImplicitArrow ty
-- --       , ns $ ULam (uPat, Nothing) ImplicitArrow e)
-- --       where uPat = nameToPat v

-- superclassConstraints :: Parser [SUType]
-- superclassConstraints = optionalMonoid $ brackets $ uType `sepBy` sym ","

-- -- interfaceDef :: Parser SUDecl
-- -- interfaceDef = do
-- --   keyWord InterfaceKW
-- --   superclasses <- superclassConstraints
-- --   tyCon <- tyConDef
-- --   methods <- onePerLine $ do
-- --     v <- anyName
-- --     ty <- annot uType
-- --     return (Just v, ty)
-- --   return $ UInterface superclasses tyCon methods

-- dataDef :: Parser SUDecl
-- dataDef = undefined
-- -- dataDef = do
-- --   keyWord DataKW
-- --   tyCon <- tyConDef
-- --   sym "="
-- --   dataCons <- onePerLine dataConDef
-- --   return $ UData tyCon dataCons

-- -- tyConDef :: Parser UConDef
-- -- tyConDef = undefined
-- -- tyConDef = do
-- --   con <- upperName <|> symName
-- --   bs <- manyNested $ label "type constructor parameter" $ do
-- --     v <- lowerName
-- --     ty <- annot containedExpr <|> return tyKind
-- --     return (Just v, ty)
-- --   return $ UConDef (Just con) bs
-- --   where tyKind = ns $ UPrimExpr $ TCExpr TypeKind

-- -- TODO: dependent types
-- -- dataConDef :: Parser UConDef
-- -- dataConDef = undefined
-- -- dataConDef = UConDef <$> (Just <$> upperName) <*> manyNested dataConDefBinder

-- -- dataConDefBinder :: Parser UAnnBinder
-- -- dataConDefBinder = annBinder <|> ((Nothing,) <$> containedExpr)

-- decl :: Parser SUDecl
-- decl = do
--   lhs <- simpleLet <|> funDefLet
--   rhs <- sym "=" >> blockOrExpr
--   return $ lhs rhs

-- instanceDef :: Bool -> Parser SUDecl
-- instanceDef = undefined
-- -- instanceDef isNamed = do
-- --   name <- case isNamed of
-- --     False -> keyWord InstanceKW $> Nothing
-- --     True  -> keyWord NamedInstanceKW *> (Just . (:>()) <$> anyName) <* sym ":"
-- --   explicitArgs <- many defArg
-- --   constraints <- classConstraints
-- --   classTy <- uType
-- --   let implicitArgs = findImplicitImplicitArgNames $
-- --                        buildPiType explicitArgs Pure $
-- --                          foldr addClassConstraint classTy constraints
-- --   let argBinders =
-- --         [((ns (nameToPat v), Nothing), ImplicitArrow) | v <- implicitArgs] ++
-- --         explicitArgs                                                       ++
-- --         [((ns UPatIgnore, Just c)   , ClassArrow   ) | c <- constraints]
-- --   methods <- onePerLine instanceMethod
-- --   return $ UInstance name (toNest argBinders) classTy methods
-- --   where
-- --     addClassConstraint :: SUType -> SUType -> SUType
-- --     addClassConstraint c ty = ns $ UPi (ns UPatIgnore, Just c) ClassArrow ty

-- instanceMethod :: Parser (UMethodDef SourceNS)
-- instanceMethod = do
--   v <- anyName
--   sym "="
--   rhs <- blockOrExpr
--   return $ UMethodDef v rhs

-- simpleLet :: Parser (SUExpr -> SUDecl)
-- simpleLet = label "let binding" $ do
--   letAnn <- (InstanceLet <$ string "%instance" <* sc) <|> (pure PlainLet)
--   p <- try $ (letPat <|> leafPat) <* lookAhead (sym "=" <|> sym ":")
--   typeAnn <- optional $ annot uType
--   return \expr -> ULet letAnn typeAnn expr p

-- letPat :: Parser SUPat
-- letPat = undefined  -- withSrc $ nameToPat <$> anyName

-- funDefLet :: Parser (SUExpr -> SUDecl)
-- funDefLet = label "function definition" $ mayBreak $ do
--   keyWord DefKW
--   v <- letPat
--   cs <- classConstraints
--   argBinders <- many defArg
--   (eff, ty) <- label "result type annotation" $ annot effectiveType
--   when (null argBinders && eff /= Pure) $ fail "Nullary def can't have effects"
--   let bs = map classAsBinder cs ++ argBinders
--   let funTy = buildPiType bs eff ty
--   let letBinder = Just funTy
--   let lamBinders = flip map bs \(p, _, arr) -> ((p,Nothing), arr)
--   return \body -> ULet PlainLet letBinder (buildLam lamBinders body) v
--   where
--     classAsBinder :: SUType -> (SUPat, Maybe SUType, Arrow)
--     classAsBinder ty = undefined -- ((ns (UPatIgnore UnitH), Just ty), ClassArrow)

-- defArg :: Parser (SUPat, Maybe SUType, Arrow)
-- defArg = label "def arg" $ do
--   (p, ty) <-parens ((,) <$> pat <*> annot uType)
--   arr <- arrow  <|> return PlainArrow
--   return (p, Just ty, arr)

-- classConstraints :: Parser [SUType]
-- classConstraints = label "class constraints" $
--   optionalMonoid $ brackets $ mayNotPair $ uType `sepBy` sym ","

-- buildPiType :: [(SUPat, Maybe SUType, Arrow)] -> EffectRow SourceNS -> SUType -> SUType
-- buildPiType [] Pure ty = ty
-- buildPiType ((p, ~(Just patTy), arr):bs) eff resTy =
--   ns $ UPi arr (buildUPatAbs p Pure) patTy $ buildUPatAbs p bodyTy
--   where bodyTy = case bs of
--           [] -> resTy
--           _  -> buildPiType bs eff resTy

-- effectiveType :: Parser (EffectRow SourceNS, SUType)
-- effectiveType = (,) <$> effects <*> uType

-- effects :: Parser (EffectRow SourceNS)
-- effects = braces someEffects <|> return Pure
--   where
--     someEffects = do
--       effs <- effect `sepBy` sym ","
--       v <- optional $ symbol "|" >> lowerName
--       return $ EffectRow (S.fromList effs) v

-- effect :: Parser (Effect SourceNS)
-- effect =   (RWSEffect <$> rwsName <*> (fromName <$> anyCaseName))
--        <|> (keyWord ExceptKW $> ExceptionEffect)
--        <|> (keyWord IOKW     $> IOEffect)
--        <?> "effect (Accum h | Read h | State h | Except | IO)"

-- rwsName :: Parser RWS
-- rwsName =   (keyWord WriteKW $> Writer)
--         <|> (keyWord ReadKW  $> Reader)
--         <|> (keyWord StateKW $> State)

-- uLamExpr :: Parser SUExpr
-- uLamExpr = do
--   sym "\\"
--   bs <- some patAnn
--   arrowType <-
--     (argTerm >> return PlainArrow)
--     <|> (arrow >>= \case
--           PlainArrow -> fail
--             "To construct an explicit lambda function, use '.' instead of '->'\n"
--           TabArrow -> fail
--             "To construct a table, use 'for i. body' instead of '\\i => body'\n"
--           arr -> return arr)
--   body <- blockOrExpr
--   return $ buildLam (map (,arrowType) bs) body

-- uViewExpr :: Parser SUExpr
-- uViewExpr = do
--   keyWord ViewKW
--   bs <- some patAnn
--   argTerm
--   body <- blockOrExpr
--   return $ buildLam (zip bs (repeat TabArrow)) body

-- uForExpr :: Parser SUExpr
-- uForExpr = do
--   ((dir, trailingUnit), pos) <- withPos $
--           (keyWord ForKW  $> (Fwd, False))
--       <|> (keyWord For_KW $> (Fwd, True ))
--       <|> (keyWord RofKW  $> (Rev, False))
--       <|> (keyWord Rof_KW $> (Rev, True ))
--   e <- buildFor pos dir <$> (some patAnn <* argTerm) <*> blockOrExpr
--   if trailingUnit
--     -- then return $ ns $ UDecl (ULet PlainLet (ns UPatIgnore, Nothing) e) $
--     --                            ns unitExpr
--     then undefined
--     else return e

-- nameToPat :: SourceName -> SUPat'
-- nameToPat v = undefined -- UPatBinder v

-- unitExpr :: SUExpr'
-- unitExpr = UPrimExpr $ ConExpr UnitCon

-- ns :: e n -> WithSrcH e n
-- ns = WithSrcH Nothing

-- blockOrExpr :: Parser SUExpr
-- blockOrExpr =  block <|> expr

-- unitCon :: Parser SUExpr
-- unitCon = withSrc $ symbol "()" $> unitExpr

-- uTabCon :: Parser SUExpr
-- uTabCon = withSrc $ do
--   xs <- brackets $ expr `sepBy` sym ","
--   return $ UTabCon xs

-- type UStatement = (Either SUDecl SUExpr, SrcPos)

-- block :: Parser SUExpr
-- block = withIndent $ do
--   statements <- mayNotBreak $ uStatement `sepBy1` (semicolon <|> try nextLine)
--   case last statements of
--     (Left _, _) -> fail "Last statement in a block must be an expression."
--     _           -> return $ wrapUStatements statements

-- wrapUStatements :: [UStatement] -> SUExpr
-- wrapUStatements statements = case statements of
--   [(Right e, _)] -> e
--   -- (s, pos):rest -> WithSrcH (Just pos) $ case s of
--   --   Left  d -> SUDecl d $ wrapUStatements rest
--   --   Right e -> SUDecl d $ wrapUStatements rest
--   --     where d = ULet PlainLet (ns UPatIgnore, Nothing) e
--   [] -> error "Shouldn't be reachable"

-- uStatement :: Parser UStatement
-- uStatement = withPos $   liftM Left  (instanceDef True <|> decl)
--                      <|> liftM Right expr

-- -- TODO: put the `try` only around the `x:` not the annotation itself
-- uPiType :: Parser SUExpr
-- uPiType = undefined
-- -- uPiType = withSrc $ UPi <$> piBinderPat <*> arrow effects <*> uType
-- --   where piBinderPat = do
-- --           (maybeV, ty@(WithSrc pos _)) <- annBinder
-- --           let v = case maybeV of
-- --                     Just n -> WithSrcH pos $ nameToPat n
-- --                     Nothing -> ns UPatIgnore
-- --           return (v, Just ty)

-- -- annBinder :: Parser UAnnBinder
-- -- annBinder = try $ label "named annoted binder" $ do
-- --   v <-  (Just    <$> lowerName)
-- --     <|> (Nothing <$  underscore)
-- --   ty <- annot containedExpr
-- --   return $ (v, ty)

-- arrowEff :: Parser (Arrow, EffectRow SourceNS)
-- arrowEff = do
--   arr <- arrow
--   case arr of
--     PlainArrow -> (arr,) <$> effects
--     _ -> return (arr, Pure)

-- arrow :: Parser Arrow
-- arrow =   (sym "->"  $> PlainArrow)
--       <|> (sym "=>"  $> TabArrow)
--       <|> (sym "--o" $> LinArrow)
--       <|> (sym "?->" $> ImplicitArrow)
--       <|> (sym "?=>" $> ClassArrow)
--       <?> "arrow"

-- caseExpr :: Parser SUExpr
-- caseExpr = withSrc $ do
--   keyWord CaseKW
--   e <- expr
--   keyWord OfKW
--   alts <- onePerLine $ buildUPatAbs <$> pat <*> (sym "->" *> blockOrExpr)
--   return $ UCase e alts

-- ifExpr :: Parser SUExpr
-- ifExpr = withSrc $ do
--   keyWord IfKW
--   e <- expr
--   (alt1, maybeAlt2) <- oneLineThenElse <|> blockThenElse
--   let alt2 = case maybeAlt2 of
--         Nothing  -> ns unitExpr
--         Just alt -> alt
--   return $ UCase e
--       [ globalEnumPat "True"  alt1
--       , globalEnumPat "False" alt2]

-- oneLineThenElse :: Parser (SUExpr, Maybe SUExpr)
-- oneLineThenElse = do
--   keyWord ThenKW
--   alt1 <- eitherP block expr
--   case alt1 of
--     Left  e -> return (e, Nothing)
--     Right e -> do
--       alt2 <- optional $ keyWord ElseKW >> blockOrExpr
--       return (e, alt2)

-- blockThenElse :: Parser (SUExpr, Maybe SUExpr)
-- blockThenElse = withIndent $ mayNotBreak $ do
--   alt1 <- keyWord ThenKW >> blockOrExpr
--   alt2 <- optional $ do
--     try $ nextLine >> keyWord ElseKW
--     blockOrExpr
--   return (alt1, alt2)

-- globalEnumPat :: String -> SUExpr -> SUAlt
-- globalEnumPat = undefined
-- -- globalEnumPat s body = ns $ UPatCon (fromString s) (Result body)

-- onePerLine :: Parser a -> Parser [a]
-- onePerLine p =   liftM (:[]) p
--              <|> (withIndent $ mayNotBreak $ p `sepBy1` try nextLine)

-- pat :: Parser SUPat
-- pat = mayNotPair $ makeExprParser leafPat patOps

-- leafPat :: Parser SUPat
-- leafPat = undefined
-- -- leafPat =
-- --       (withSrc (symbol "()" $> UPatUnit))
-- --   <|> parens (mayPair $ makeExprParser leafPat patOps)
-- --   <|> (withSrc $
-- --           -- (UPatBinder <$> lowerName)
-- --          (UPatIgnore UnitH <$  underscore)
-- --       -- <|> (UPatCon    <$> upperName <*> manyNested pat)
-- --       -- <|> (variantPat `fallBackTo` recordPat)
-- --       -- <|> brackets (UPatTable <$> leafPat `sepBy` sym ",")
-- --   )
-- --   where pun pos l = nameToPat (Just pos) $ mkName l
-- --         def pos = WithSrcH (Just pos) $ UPatIgnore
-- --         variantPat = parseVariant leafPat UPatVariant UPatVariantLift
-- --         -- recordPat = UPatRecord <$> parseLabeledItems "," "=" leafPat
-- --         --                                              (Just pun) (Just def)

-- -- TODO: add user-defined patterns
-- patOps :: [[Operator Parser SUPat]]
-- patOps = [[InfixR patPairOp]]

-- patPairOp :: Parser (SUPat -> SUPat -> SUPat)
-- patPairOp = do
--   allowed <- asks canPair
--   if allowed
--     then undefined -- sym "," $> \x y -> joinSrc x y $ UPatPair x y
--     else fail "pair pattern not allowed outside parentheses"

-- annot :: Parser a -> Parser a
-- annot p = label "type annotation" $ sym ":" >> p

-- patAnn :: Parser (SUPat, Maybe SUType)
-- patAnn = label "pattern" $ (,) <$> pat <*> optional (annot containedExpr)

-- uPrim :: Parser SUExpr
-- uPrim = withSrc $ do
--   s <- primName
--   case s of
--     "ffi" -> do
--       f <- lexeme $ some nameTailChar
--       retTy <- leafExpr
--       args <- some leafExpr
--       return $ UPrimExpr $ OpExpr $ FFICall f retTy args
--     _ -> case strToPrimName s of
--       Just prim -> UPrimExpr <$> traverse (const leafExpr) prim
--       Nothing -> fail $ "Unrecognized primitive: " ++ s

-- uVariantExpr :: Parser SUExpr
-- uVariantExpr = withSrc $ parseVariant expr UVariant UVariantLift

-- parseVariant :: Parser a -> (LabeledItems () -> Label -> a -> b) -> (LabeledItems () -> a -> b) -> Parser b
-- parseVariant subparser buildLabeled buildExt =
--   bracketed (symbol "{|") (symbol "|}") $ do
--     let parseInactive = try $ fieldLabel <* notFollowedBy (symbol "=")
--     inactiveLabels <- parseInactive `endBy1` (symbol "|") <|> pure []
--     let inactiveItems = foldr (<>) NoLabeledItems $ map (flip labeledSingleton ()) inactiveLabels
--     let parseLabeled = do l <- fieldLabel
--                           symbol "="
--                           buildLabeled inactiveItems l <$> subparser
--     let parseExt = do symbol "..."
--                       buildExt inactiveItems <$> subparser
--     parseLabeled <|> parseExt

-- uLabeledExprs :: Parser SUExpr
-- uLabeledExprs = undefined
-- -- uLabeledExprs = withSrc $
-- --     (URecord <$> build "," "=" (Just varPun) Nothing)
-- --     `fallBackTo` (URecordTy <$> build "&" ":" Nothing Nothing)
-- --     `fallBackTo` (UVariantTy <$> build "|" ":" Nothing Nothing)
-- --   where build sep bindwith = parseLabeledItems sep bindwith expr

-- varPun :: SrcPos -> Label -> SUExpr
-- varPun pos str = WithSrcH (Just pos) $ UVar $ mkName str

-- uDoSugar :: Parser SUExpr
-- uDoSugar = undefined
-- -- uDoSugar = withSrc $ do
-- --   keyWord DoKW
-- --   body <- blockOrExpr
-- --   return $ ULam (WithSrcH Nothing UPatUnit, Nothing) PlainArrow body

-- uIsoSugar :: Parser SUExpr
-- uIsoSugar = undefined
-- -- uIsoSugar = withSrc (char '#' *> options) where
-- --   options = (recordFieldIso <$> fieldLabel)
-- --             <|> char '?' *> (variantFieldIso <$> fieldLabel)
-- --             <|> char '&' *> (recordZipIso <$> fieldLabel)
-- --             <|> char '|' *> (variantZipIso <$> fieldLabel)
-- --   var s = ns $ UVar $ mkName s
-- --   patb s = ns $ nameToPat $ mkName s
-- --   plain = PlainArrow UnitH
-- --   lam p b = ns $ ULam (p, Nothing) plain b
-- --   recordFieldIso field =
-- --     UApp plain (var "MkIso") $
-- --       ns $ URecord $ NoExt $
-- --         labeledSingleton "fwd" (lam
-- --           (ns $ UPatRecord $ Ext (labeledSingleton field (patb "x"))
-- --                                        (Just $ patb "r"))
-- --           $ (var "(,)") `mkApp` (var "x") `mkApp` (var "r")
-- --         )
-- --         <> labeledSingleton "bwd" (lam
-- --           (ns $ UPatPair (patb "x") (patb "r"))
-- --           $ ns $ URecord $ Ext (labeledSingleton field $ var "x")
-- --                                $ Just $ var "r"
-- --         )
-- --   variantFieldIso field =
-- --     UApp plain (var "MkIso") $
-- --       ns $ URecord $ NoExt $
-- --         labeledSingleton "fwd" (lam (patb "v") $ ns $ UCase (var "v")
-- --             [ UAlt (ns $ UPatVariant NoLabeledItems field (patb "x"))
-- --                 $ var "Left" `mkApp` var "x"
-- --             , UAlt (ns $ UPatVariantLift (labeledSingleton field ()) (patb "r"))
-- --                 $ var "Right" `mkApp` var "r"
-- --             ]
-- --         )
-- --         <> labeledSingleton "bwd" (lam (patb "v") $ ns $ UCase (var "v")
-- --             [ UAlt (ns $ UPatCon (mkName "Left") (toUNest [patb "x"]))
-- --                 $ ns $ UVariant NoLabeledItems field $ var "x"
-- --             , UAlt (ns $ UPatCon (mkName "Right") (toUNest [patb "r"]))
-- --                 $ ns $ UVariantLift (labeledSingleton field ()) $ var "r"
-- --             ]
-- --         )
-- --   recordZipIso field =
-- --     UApp plain (var "MkIso") $
-- --       ns $ URecord $ NoExt $
-- --         labeledSingleton "fwd" (lam
-- --           (ns $ UPatPair
-- --             (ns $ UPatRecord $ Ext NoLabeledItems $ Just $ patb "l")
-- --             (ns $ UPatRecord $ Ext (labeledSingleton field $ patb "x")
-- --                                    $ Just $ patb "r"))
-- --           $ (var "(,)")
-- --             `mkApp` (ns $ URecord $ Ext (labeledSingleton field $ var "x")
-- --                                         $ Just $ var "l")
-- --             `mkApp` (ns $ URecord $ Ext NoLabeledItems $ Just $ var "r")
-- --         )
-- --         <> labeledSingleton "bwd" (lam
-- --           (ns $ UPatPair
-- --             (ns $ UPatRecord $ Ext (labeledSingleton field $ patb "x")
-- --                                    $ Just $ patb "l")
-- --             (ns $ UPatRecord $ Ext NoLabeledItems $ Just $ patb "r"))
-- --           $ (var "(,)")
-- --             `mkApp` (ns $ URecord $ Ext NoLabeledItems $ Just $ var "l")
-- --             `mkApp` (ns $ URecord $ Ext (labeledSingleton field $ var "x")
-- --                                         $ Just $ var "r")
-- --         )
-- --   variantZipIso field =
-- --     UApp plain (var "MkIso") $
-- --       ns $ URecord $ NoExt $
-- --         labeledSingleton "fwd" (lam (patb "v") $ ns $ UCase (var "v")
-- --             [ UAlt (ns $ UPatCon (mkName "Left") (toUNest [patb "l"]))
-- --                 $ var "Left" `mkApp` (ns $
-- --                     UVariantLift (labeledSingleton field ()) $ var "l")
-- --             , UAlt (ns $ UPatCon (mkName "Right") (toUNest [patb "w"]))
-- --                 $ ns $ UCase (var "w")
-- --                 [ UAlt (ns $ UPatVariant NoLabeledItems field (patb "x"))
-- --                     $ var "Left" `mkApp` (ns $
-- --                         UVariant NoLabeledItems field $ var "x")
-- --                 , UAlt (ns $ UPatVariantLift (labeledSingleton field ())
-- --                                              (patb "r"))
-- --                     $ var "Right" `mkApp` var "r"
-- --                 ]
-- --             ]
-- --         )
-- --         <> labeledSingleton "bwd" (lam (patb "v") $ ns $ UCase (var "v")
-- --             [ UAlt (ns $ UPatCon (mkName "Left") (toUNest [patb "w"]))
-- --                 $ ns $ UCase (var "w")
-- --                 [ UAlt (ns $ UPatVariant NoLabeledItems field (patb "x"))
-- --                     $ var "Right" `mkApp` (ns $
-- --                         UVariant NoLabeledItems field $ var "x")
-- --                 , UAlt (ns $ UPatVariantLift (labeledSingleton field ())
-- --                                              (patb "r"))
-- --                     $ var "Left" `mkApp` var "r"
-- --                 ]
-- --             , UAlt (ns $ UPatCon (mkName "Right") (toUNest [patb "l"]))
-- --                 $ var "Right" `mkApp` (ns $
-- --                     UVariantLift (labeledSingleton field ()) $ var "l")
-- --             ]
-- --         )

-- -- parseLabeledItems
-- --   :: String -> String -> Parser a
-- --   -> Maybe (SrcPos -> Label -> a) -> Maybe (SrcPos -> a)
-- --   -> Parser (ExtLabeledItems a a)
-- -- parseLabeledItems sep bindwith itemparser punner tailDefault =
-- --   bracketed lBrace rBrace $ atBeginning
-- --   where
-- --     atBeginning = someItems
-- --                   <|> (symbol sep >> (stopAndExtend <|> stopWithoutExtend))
-- --                   <|> stopWithoutExtend
-- --     stopWithoutExtend = return $ NoExt NoLabeledItems
-- --     stopAndExtend = do
-- --       ((), pos) <- withPos $ symbol "..."
-- --       rest <- case tailDefault of
-- --         Just def -> itemparser <|> pure (def pos)
-- --         Nothing -> itemparser
-- --       return $ Ext NoLabeledItems (Just rest)
-- --     beforeSep = (symbol sep >> afterSep) <|> stopWithoutExtend
-- --     afterSep = someItems <|> stopAndExtend <|> stopWithoutExtend
-- --     someItems = do
-- --       (l, pos) <- withPos fieldLabel
-- --       let explicitBound = symbol bindwith *> itemparser
-- --       itemVal <- case punner of
-- --         Just punFn -> explicitBound <|> pure (punFn pos l)
-- --         Nothing -> explicitBound
-- --       rest <- beforeSep
-- --       return $ prefixExtLabeledItems (labeledSingleton l itemVal) rest

-- -- Combine two parsers such that if the first fails, we try the second one.
-- -- If both fail, consume the same amount of input as the parser that
-- -- consumed the most input, and use its error message. Useful if you want
-- -- to parse multiple things, but they share some common starting symbol, and
-- -- you don't want the first one failing to prevent the second from succeeding.
-- -- Unlike using `try` and/or (<|>), if both parsers fail and either one consumes
-- -- input, parsing is aborted. Also, if both parsers consume the same amount of
-- -- input, we combine the symbols each was expecting.
-- fallBackTo :: Parser a -> Parser a -> Parser a
-- fallBackTo optionA optionB = do
--   startState <- getParserState
--   resA <- observing $ optionA
--   case resA of
--     Right val -> return val
--     Left errA -> do
--       stateA <- getParserState
--       updateParserState $ const startState
--       resB <- observing $ optionB
--       case resB of
--         Right val -> return val
--         Left errB -> case compare (errorOffset errA) (errorOffset errB) of
--           LT -> parseError errB
--           GT -> updateParserState (const stateA) >> parseError errA
--           EQ -> case (errA, errB) of
--             -- Combine what each was expecting.
--             (TrivialError offset unexpA expA, TrivialError _ unexpB expB)
--                 -> parseError $ TrivialError offset (unexpA <|> unexpB)
--                                                     (expA <> expB)
--             _ -> fail $ "Multiple failed parse attempts:\n"
--                   <> parseErrorPretty errA <> "\n" <> parseErrorPretty errB

-- -- === infix ops ===

-- -- literal symbols here must only use chars from `symChars`
-- ops :: [[Operator Parser SUExpr]]
-- ops =
--   [ [InfixL $ sym "." $> mkGenApp TabArrow, symOp "!"]
--   , [InfixL $ sc $> mkApp]
--   , [prefixNegOp]
--   , [anySymOp] -- other ops with default fixity
--   , [symOp "+", symOp "-", symOp "||", symOp "&&",
--      InfixR $ sym "=>" $> mkArrow TabArrow,
--      InfixL $ opWithSrc $ backquoteName >>= (return . binApp),
--      symOp "<<<", symOp ">>>", symOp "<<&", symOp "&>>"]
--   , [annotatedExpr]
--   , [InfixR $ mayBreak (infixSym "$") $> mkApp]
--   , [symOp "+=", symOp ":=", InfixL $ pairingSymOpP "|", InfixR infixArrow]
--   , [InfixR $ pairingSymOpP "&", InfixR $ pairingSymOpP ","]
--   , indexRangeOps
--   ]

-- opWithSrc :: Parser (SrcPos -> a -> a -> a)
--           -> Parser (a -> a -> a)
-- opWithSrc p = do
--   (f, pos) <- withPos p
--   return $ f pos

-- anySymOp :: Operator Parser SUExpr
-- anySymOp = InfixL $ opWithSrc $ do
--   s <- label "infix operator" (mayBreak anySym)
--   return $ binApp $ mkSymName s

-- infixSym :: String -> Parser ()
-- infixSym s = mayBreak $ sym s

-- symOp :: String -> Operator Parser SUExpr
-- symOp s = InfixL $ symOpP s

-- symOpP :: String -> Parser (SUExpr -> SUExpr -> SUExpr)
-- symOpP s = opWithSrc $ do
--   label "infix operator" (infixSym s)
--   return $ binApp $ mkSymName s

-- pairingSymOpP :: String -> Parser (SUExpr -> SUExpr -> SUExpr)
-- pairingSymOpP s = opWithSrc $ do
--   allowed <- asks canPair
--   if allowed
--     then infixSym s >> return (binApp (mkSymName s))
--     else fail $ "Unexpected delimiter " <> s

-- mkSymName :: String -> SourceName
-- mkSymName s = mkName $ "(" <> s <> ")"

-- prefixNegOp :: Operator Parser SUExpr
-- prefixNegOp = Prefix $ label "negation" $ do
--   ((), pos) <- withPos $ sym "-"
--   let f = WithSrcH (Just pos) $ UVar "neg"
--   return \case
--     -- Special case: negate literals directly
--     WithSrcH litpos (IntLitExpr i)
--       -> WithSrcH (joinPos (Just pos) litpos) (IntLitExpr (-i))
--     WithSrcH litpos (FloatLitExpr i)
--       -> WithSrcH (joinPos (Just pos) litpos) (FloatLitExpr (-i))
--     x -> mkApp f x

-- binApp :: SourceName -> SrcPos -> SUExpr -> SUExpr -> SUExpr
-- binApp f pos x y = (f' `mkApp` x) `mkApp` y
--   where f' = WithSrcH (Just pos) $ UVar f

-- mkGenApp :: Arrow -> SUExpr -> SUExpr -> SUExpr
-- mkGenApp arr f x = joinSrc f x $ UApp arr f x

-- mkApp :: SUExpr -> SUExpr -> SUExpr
-- mkApp f x = joinSrc f x $ UApp PlainArrow f x

-- infixArrow :: Parser (SUType -> SUType -> SUType)
-- infixArrow = undefined
-- -- infixArrow = do
-- --   notFollowedBy (sym "=>")  -- table arrows have special fixity
-- --   (arr, pos) <- withPos $ arrow effects
-- --   return \a b -> WithSrcH (Just pos) $ UPi (ns UPatIgnore, Just a) arr b

-- mkArrow :: Arrow -> SUExpr -> SUExpr -> SUExpr
-- mkArrow = undefined --  arr a b = joinSrc a b $ UPi (ns UPatIgnore, Just a) arr b

-- withSrc :: Parser (e n) -> Parser (WithSrcH e n)
-- withSrc p = do
--   (x, pos) <- withPos p
--   return $ WithSrcH (Just pos) x

-- joinPos :: Maybe SrcPos -> Maybe SrcPos -> Maybe SrcPos
-- joinPos Nothing p = p
-- joinPos p Nothing = p
-- joinPos (Just (l, h)) (Just (l', h')) = Just (min l l', max h h')

-- indexRangeOps :: [Operator Parser SUExpr]
-- indexRangeOps =
--   [ Prefix    $ symPos ".."   <&> \pos h   -> range pos  Unlimited       (InclusiveLim h)
--   , inpostfix $ symPos ".."   <&> \pos l h -> range pos (InclusiveLim l) (limFromMaybe h)
--   , inpostfix $ symPos "<.."  <&> \pos l h -> range pos (ExclusiveLim l) (limFromMaybe h)
--   , Prefix    $ symPos "..<"  <&> \pos h   -> range pos  Unlimited       (ExclusiveLim h)
--   , InfixL    $ symPos "..<"  <&> \pos l h -> range pos (InclusiveLim l) (ExclusiveLim h)
--   , InfixL    $ symPos "<..<" <&> \pos l h -> range pos (ExclusiveLim l) (ExclusiveLim h) ]
--   where
--     range pos l h = WithSrcH (Just pos) $ UIndexRange l h
--     symPos s = snd <$> withPos (sym s)

-- limFromMaybe :: Maybe a -> Limit a
-- limFromMaybe Nothing = Unlimited
-- limFromMaybe (Just x) = InclusiveLim x

-- annotatedExpr :: Operator Parser SUExpr
-- annotatedExpr = InfixL $ opWithSrc $
--   sym ":" $> (\pos v ty -> WithSrcH (Just pos) $ UTypeAnn v ty)

-- inpostfix :: Parser (SUExpr -> Maybe SUExpr -> SUExpr) -> Operator Parser SUExpr
-- inpostfix = inpostfix' expr

-- inpostfix' :: Parser a -> Parser (a -> Maybe a -> a) -> Operator Parser a
-- inpostfix' p op = Postfix $ do
--   f <- op
--   rest <- optional p
--   return \x -> f x rest

-- mkName :: String -> SourceName
-- mkName = fromString

-- -- === lexemes ===

-- -- These `Lexer` actions must be non-overlapping and never consume input on failure
-- type Lexer = Parser

-- data KeyWord = DefKW | ForKW | For_KW | RofKW | Rof_KW | CaseKW | OfKW
--              | ReadKW | WriteKW | StateKW | DataKW | InterfaceKW
--              | InstanceKW | WhereKW | IfKW | ThenKW | ElseKW | DoKW
--              | ExceptKW | IOKW | ViewKW | ImportKW | NamedInstanceKW

-- upperName :: Lexer SourceName
-- upperName = liftM mkName $ label "upper-case name" $ lexeme $
--   checkNotKeyword $ (:) <$> upperChar <*> many nameTailChar

-- lowerName  :: Lexer SourceName
-- lowerName = liftM mkName $ label "lower-case name" $ lexeme $
--   checkNotKeyword $ (:) <$> lowerChar <*> many nameTailChar

-- anyCaseName  :: Lexer SourceName
-- anyCaseName = lowerName <|> upperName

-- anyName  :: Lexer SourceName
-- anyName = lowerName <|> upperName <|> symName

-- checkNotKeyword :: Parser String -> Parser String
-- checkNotKeyword p = try $ do
--   s <- p
--   failIf (s `elem` keyWordStrs) $ show s ++ " is a reserved word"
--   return s

-- keyWord :: KeyWord -> Lexer ()
-- keyWord kw = lexeme $ try $ string s >> notFollowedBy nameTailChar
--   where
--     s = case kw of
--       DefKW  -> "def"
--       ForKW  -> "for"
--       RofKW  -> "rof"
--       For_KW  -> "for_"
--       Rof_KW  -> "rof_"
--       CaseKW -> "case"
--       IfKW   -> "if"
--       ThenKW -> "then"
--       ElseKW -> "else"
--       OfKW   -> "of"
--       ReadKW  -> "Read"
--       WriteKW -> "Accum"
--       StateKW -> "State"
--       ExceptKW -> "Except"
--       IOKW     -> "IO"
--       DataKW -> "data"
--       InterfaceKW -> "interface"
--       InstanceKW -> "instance"
--       NamedInstanceKW -> "named-instance"
--       WhereKW -> "where"
--       DoKW   -> "do"
--       ViewKW -> "view"
--       ImportKW -> "import"

-- keyWordStrs :: [String]
-- keyWordStrs = ["def", "for", "for_", "rof", "rof_", "case", "of", "llam",
--                "Read", "Write", "Accum", "Except", "IO", "data", "interface",
--                "instance", "named-instance", "where", "if", "then", "else", "do", "view", "import"]

-- fieldLabel :: Lexer Label
-- fieldLabel = label "field label" $ lexeme $
--   checkNotKeyword $ (:) <$> (lowerChar <|> upperChar) <*> many nameTailChar

-- primName :: Lexer String
-- primName = lexeme $ try $ char '%' >> some alphaNumChar

-- charLit :: Lexer Char
-- charLit = lexeme $ char '\'' >> L.charLiteral <* char '\''

-- strLit :: Lexer String
-- strLit = lexeme $ char '"' >> manyTill L.charLiteral (char '"')

-- intLit :: Lexer Int
-- intLit = lexeme $ try $ L.decimal <* notFollowedBy (char '.')

-- doubleLit :: Lexer Double
-- doubleLit = lexeme $
--       try L.float
--   <|> try (fromIntegral <$> (L.decimal :: Parser Int) <* char '.')

-- knownSymStrs :: [String]
-- knownSymStrs = [".", ":", "!", "=", "-", "+", "||", "&&", "$", "&", "|", ",", "+=", ":=",
--                 "->", "=>", "?->", "?=>", "--o", "--", "<<<", ">>>", "<<&", "&>>",
--                 "..", "<..", "..<", "..<", "<..<"]

-- -- string must be in `knownSymStrs`
-- sym :: String -> Lexer ()
-- sym s = lexeme $ try $ string s >> notFollowedBy symChar

-- anySym :: Lexer String
-- anySym = lexeme $ try $ do
--   s <- some symChar
--   -- TODO: consider something faster than linear search here
--   failIf (s `elem` knownSymStrs) ""
--   return s

-- symName :: Lexer SourceName
-- symName = label "symbol name" $ lexeme $ try $ do
--   s <- between (char '(') (char ')') $ some symChar
--   return $ mkName $ "(" <> s <> ")"

-- backquoteName :: Lexer SourceName
-- backquoteName = label "backquoted name" $
--   lexeme $ try $ between (char '`') (char '`') (upperName <|> lowerName)

-- -- brackets and punctuation
-- -- (can't treat as sym because e.g. `((` is two separate lexemes)
-- lParen, rParen, lBracket, rBracket, lBrace, rBrace, semicolon, underscore :: Lexer ()

-- lParen    = notFollowedBy symName >> notFollowedBy unitCon >> charLexeme '('
-- rParen    = charLexeme ')'
-- lBracket  = charLexeme '['
-- rBracket  = charLexeme ']'
-- lBrace    = charLexeme '{'
-- rBrace    = charLexeme '}'
-- semicolon = charLexeme ';'
-- underscore = charLexeme '_'

-- charLexeme :: Char -> Parser ()
-- charLexeme c = void $ lexeme $ char c

-- nameTailChar :: Parser Char
-- nameTailChar = alphaNumChar <|> char '\'' <|> char '_'

-- symChar :: Parser Char
-- symChar = choice $ map char symChars

-- symChars :: [Char]
-- symChars = ".,!$^&*:-~+/=<>|?\\@"

-- -- === Util ===

-- runTheParser :: String -> Parser a -> Either (ParseErrorBundle String Void) a
-- runTheParser s p = parse (runReaderT p (ParseCtx 0 False False)) "" s

-- sc :: Parser ()
-- sc = L.space space lineComment empty

-- lineComment :: Parser ()
-- lineComment = do
--   try $ string "--" >> notFollowedBy (void (char 'o'))
--   void (takeWhileP (Just "char") (/= '\n'))

-- emptyLines :: Parser ()
-- emptyLines = void $ many (sc >> eol)

-- outputLines :: Parser ()
-- outputLines = void $ many (symbol ">" >> takeWhileP Nothing (/= '\n') >> ((eol >> return ()) <|> eof))

-- stringLiteral :: Parser String
-- stringLiteral = char '"' >> manyTill L.charLiteral (char '"') <* sc

-- space :: Parser ()
-- space = do
--   consumeNewLines <- asks canBreak
--   if consumeNewLines
--     then space1
--     else void $ takeWhile1P (Just "white space") (`elem` (" \t" :: String))

-- mayBreak :: Parser a -> Parser a
-- mayBreak p = local (\ctx -> ctx { canBreak = True }) p

-- mayNotBreak :: Parser a -> Parser a
-- mayNotBreak p = local (\ctx -> ctx { canBreak = False }) p

-- mayPair :: Parser a -> Parser a
-- mayPair p = local (\ctx -> ctx { canPair = True }) p

-- mayNotPair :: Parser a -> Parser a
-- mayNotPair p = local (\ctx -> ctx { canPair = False }) p

-- optionalMonoid :: Monoid a => Parser a -> Parser a
-- optionalMonoid p = p <|> return mempty

-- nameString :: Parser String
-- nameString = lexeme . try $ (:) <$> lowerChar <*> many alphaNumChar

-- thisNameString :: String -> Parser ()
-- thisNameString s = lexeme $ try $ string s >> notFollowedBy alphaNumChar

-- uint :: Parser Int
-- uint = L.decimal <* sc

-- lexeme :: Parser a -> Parser a
-- lexeme = L.lexeme sc

-- symbol :: String -> Parser ()
-- symbol s = void $ L.symbol sc s

-- argTerm :: Parser ()
-- argTerm = mayNotBreak $ sym "."

-- bracketed :: Parser () -> Parser () -> Parser a -> Parser a
-- bracketed left right p = between left right $ mayBreak $ sc >> p

-- parens :: Parser a -> Parser a
-- parens p = bracketed lParen rParen p

-- brackets :: Parser a -> Parser a
-- brackets p = bracketed lBracket rBracket p

-- braces :: Parser a -> Parser a
-- braces p = bracketed lBrace rBrace p

-- -- manyNested :: Parser (e n) -> Parser (NestedAbs e UnitH n)
-- -- manyNested p = UNest <$> many p

-- withPos :: Parser a -> Parser (a, SrcPos)
-- withPos p = do
--   n <- getOffset
--   x <- p
--   n' <- getOffset
--   return $ (x, (n, n'))

-- nextLine :: Parser ()
-- nextLine = do
--   eol
--   n <- asks curIndent
--   void $ mayNotBreak $ many $ try (sc >> eol)
--   void $ replicateM n (char ' ')

-- withSource :: Parser a -> Parser (String, a)
-- withSource p = do
--   s <- getInput
--   (x, (start, end)) <- withPos p
--   return (take (end - start) s, x)

-- withIndent :: Parser a -> Parser a
-- withIndent p = do
--   nextLine
--   indent <- liftM length $ some (char ' ')
--   local (\ctx -> ctx { curIndent = curIndent ctx + indent }) $ p

-- eol :: Parser ()
-- eol = void MC.eol

-- eolf :: Parser ()
-- eolf = eol <|> eof

-- failIf :: Bool -> String -> Parser ()
-- failIf True s = fail s
-- failIf False _ = return ()

-- _debug :: Show a => String -> Parser a -> Parser a
-- _debug s m = mapReaderT (Text.Megaparsec.Debug.dbg s) m

-- -- === builder helpers ===

-- buildFor :: SrcPos -> Direction -> [(SUPat, Maybe SUType)] -> SUExpr -> SUExpr
-- buildFor = undefined
-- -- buildFor pos dir binders body = case binders of
-- --   [] -> body
-- --   b:bs -> WithSrcH (Just pos) $ UFor dir b $ buildFor pos dir bs body

-- buildLam :: [((SUPat, Maybe SUType), Arrow)] -> SUExpr -> SUExpr
-- buildLam = undefined
-- -- buildLam binders body@(WithSrc pos _) = case binders of
-- --   [] -> body
-- --   -- TODO: join with source position of binders too
-- --   (b,arr):bs -> WithSrcH (joinPos pos' pos) $ ULam b arr $ buildLam bs body
-- --      where (WithSrcH pos' _, _) = b

-- buildUPatAbs :: SUPat -> e SourceNS -> UPatAbs e SourceNS
-- buildUPatAbs = undefined

-- joinSrc :: H WithSrc a n -> H WithSrc b n -> c n -> H WithSrc c n
-- joinSrc (WithSrcH p1 _) (WithSrcH p2 _) x = WithSrcH (joinPos p1 p2) x
