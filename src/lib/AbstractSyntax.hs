-- Copyright 2022 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

-- The Dex parser is written in two distinct stages:
-- - concrete syntax parsing using Megaparsec (in ConcreteSyntax.hs)
-- - conversion of concrete syntax to abstract syntax (this file).
--
-- We separate these two stages to separate concerns: the concrete
-- syntax deals with grouping (including keywords, primitives, and
-- operator precedence), and the abstract syntax makes sure that the
-- resulting grouping structures are actually valid Dex.
--
-- As an example of the difference, an input like
--   4 + * 3
-- produces a parse error at the concrete syntax stage: `+` and `*`
-- are both infix operators, so cannot be juxtaposed like that.
-- On the other hand, an input like
--   def foo (x + y) = 4
-- groups just fine, but produces a syntax error at the abstract syntax
-- stage because `(x + y)` is not a valid pattern for a function argument.
--
-- A goal we hope to achieve with this separation is to make the
-- concrete syntax relatively uniform: something like `:`, which
-- denotes different bits of abstract syntax in different contexts,
-- can nonetheless be given a definite operator precedence, and a
-- reader of Dex should be able to know which substrings of input are
-- the constitutents of the Dex grammar without having to fully parse
-- it.
--
-- Another goal is more practical: deferring the abstract syntax to a
-- separate traversal means the meaning of a grouping construct like
-- `[]` can depend on what follows after it, without requiring the
-- Megaparsec parser to have unbounded lookahead.  At the
-- character-by-character level, we just parse "group surrounded by
-- square brackets", and then the abstract syntax determines whether
-- to interpret it as a table literal, a table pattern, or a class
-- constraint, depending on where it appears and what follows.
--
-- The separation also turned out to split the code size of the old
-- parser roughly in half, implying that each of the remaining pieces
-- is less complex on its own.  This should make adjusting the syntax,
-- for example to permit grouping parens in more places, that much
-- easier.

module AbstractSyntax (parseExpr, parseDecl, parseBlock, parseTopDeclRepl) where

import Control.Category ((>>>))
import Control.Monad (forM, when)
import Data.Functor
import Data.Either
import Data.Maybe (catMaybes)
import Data.Set qualified as S
import Data.Text (Text)

import ConcreteSyntax
import Err
import Name
import PPrint
import Types.Primitives
import Types.Source
import qualified Types.OpNames as P
import Util

-- === Converting concrete syntax to abstract syntax ===

parseExpr :: Fallible m => GroupW -> m (UExpr VoidS)
parseExpr e = liftSyntaxM $ expr e

parseDecl :: Fallible m => CTopDeclW -> m (UTopDecl VoidS VoidS)
parseDecl d = liftSyntaxM $ topDecl d

parseBlock :: Fallible m => CSBlock -> m (UBlock VoidS)
parseBlock b = liftSyntaxM $ block b

liftSyntaxM :: Fallible m => SyntaxM a -> m a
liftSyntaxM cont = liftExcept cont

parseTopDeclRepl :: Text -> Maybe SourceBlock
parseTopDeclRepl s = case sbContents b of
  UnParseable True _ -> Nothing
  _ -> case checkSourceBlockParses $ sbContents b of
    Success _ -> Just b
    Failure _ -> Nothing
  where b = mustParseSourceBlock s
{-# SCC parseTopDeclRepl #-}

checkSourceBlockParses :: SourceBlock' -> SyntaxM ()
checkSourceBlockParses = \case
  TopDecl (WithSrcs _ _ (CSDecl ann (CExpr e)))-> do
    when (ann /= PlainLet) $ fail "Cannot annotate expressions"
    void $ expr e
  TopDecl d -> void $ topDecl d
  Command _ b -> void $ expr b
  DeclareForeign _ _ ty -> void $ expr ty
  DeclareCustomLinearization _ _ body -> void $ expr body
  Misc _ -> return ()
  UnParseable _ _ -> return ()

-- === Converting concrete syntax to abstract syntax ===

type SyntaxM = Except

topDecl :: CTopDeclW -> SyntaxM (UTopDecl VoidS VoidS)
topDecl (WithSrcs sid sids topDecl') = case topDecl' of
  CSDecl ann d -> ULocalDecl <$> decl ann (WithSrcs sid sids d)
  CData name tyConParams givens constructors -> do
    tyConParams' <- fromMaybeM tyConParams Empty aExplicitParams
    givens' <- aOptGivens givens
    constructors' <- forM constructors \(v, ps) -> do
      ps' <- fromMaybeM ps Empty \(WithSrcs _ _ ps') ->
        toNest <$> mapM (tyOptBinder Explicit) ps'
      return (v, ps')
    return $ UDataDefDecl
      (UDataDef (withoutSrc name) (givens' >>> tyConParams') $
        map (\(name', cons) -> (withoutSrc name', UDataDefTrail cons)) constructors')
      (fromSourceNameW name)
      (toNest $ map (fromSourceNameW . fst) constructors')
  CStruct name params givens fields defs -> do
    params' <- fromMaybeM params Empty aExplicitParams
    givens' <- aOptGivens givens
    fields' <- forM fields \(v, ty) -> (v,) <$> expr ty
    methods <- forM defs \(ann, d) -> do
      (WithSrc _ methodName, lam) <- aDef d
      return (ann, methodName, Abs (WithSrcB sid (UBindSource "self")) lam)
    return $ UStructDecl (fromSourceNameW name) (UStructDef (withoutSrc name) (givens' >>> params') fields' methods)
  CInterface name params methods -> do
    params' <- aExplicitParams params
    (methodNames, methodTys) <- unzip <$> forM methods \(methodName, ty) -> do
      ty' <- expr ty
      return (fromSourceNameW methodName, ty')
    return $ UInterface params' methodTys (fromSourceNameW name) (toNest methodNames)
  CInstanceDecl def -> aInstanceDef def

decl :: LetAnn -> CSDeclW -> SyntaxM (UDecl VoidS VoidS)
decl ann (WithSrcs sid _ d) = WithSrcB sid <$> case d of
  CLet binder rhs -> do
    (p, ty) <- patOptAnn binder
    ULet ann p ty <$> asExpr <$> block rhs
  CBind _ _ -> throw sid TopLevelArrowBinder
  CDefDecl def -> do
    (name, lam) <- aDef def
    return $ ULet ann (fromSourceNameW name) Nothing (WithSrcE sid (ULam lam))
  CExpr g -> UExprDecl <$> expr g
  CPass -> return UPass

aInstanceDef :: CInstanceDef -> SyntaxM (UTopDecl VoidS VoidS)
aInstanceDef (CInstanceDef (WithSrc clNameId clName) args givens methods instNameAndParams) = do
  let clName' = SourceName clNameId clName
  args' <- mapM expr args
  givens' <- aOptGivens givens
  methods' <- catMaybes <$> mapM aMethod methods
  case instNameAndParams of
    Nothing -> return $ UInstance clName' givens' args' methods' NothingB ImplicitApp
    Just (WithSrc sid instName, optParams) -> do
      let instName' = JustB $ WithSrcB sid $ UBindSource instName
      case optParams of
        Just params -> do
          params' <- aExplicitParams params
          return $ UInstance clName' (givens' >>> params') args' methods' instName' ExplicitApp
        Nothing -> return $ UInstance clName' givens' args' methods' instName' ImplicitApp

aDef :: CDef -> SyntaxM (SourceNameW, ULamExpr VoidS)
aDef (CDef name params optRhs optGivens body) = do
  explicitParams <- explicitBindersOptAnn params
  let rhsDefault = (ExplicitApp, Nothing, Nothing)
  (expl, effs, resultTy) <- fromMaybeM optRhs rhsDefault \(expl, optEffs, resultTy) -> do
    effs <- fromMaybeM optEffs UPure aEffects
    resultTy' <- expr resultTy
    return (expl, Just effs, Just resultTy')
  implicitParams <- aOptGivens optGivens
  let allParams = implicitParams >>> explicitParams
  body' <- block body
  return (name, ULamExpr allParams expl effs resultTy body')

stripParens :: GroupW -> GroupW
stripParens (WithSrcs _ _ (CParens [g])) = stripParens g
stripParens g = g

-- === combinators for different sorts of binder lists ===

aOptGivens :: Maybe GivenClause -> SyntaxM (Nest UAnnBinder VoidS VoidS)
aOptGivens optGivens = fromMaybeM optGivens Empty aGivens

binderList
  :: [GroupW] -> (GroupW -> SyntaxM (Nest UAnnBinder VoidS VoidS))
  -> SyntaxM (Nest UAnnBinder VoidS VoidS)
binderList gs cont = concatNests <$> forM gs \case
  WithSrcs _ _ (CGivens gs') -> aGivens gs'
  g -> cont g

withTrailingConstraints
  :: GroupW -> (GroupW -> SyntaxM (UAnnBinder VoidS VoidS))
  -> SyntaxM (Nest UAnnBinder VoidS VoidS)
withTrailingConstraints g cont = case g of
  WithSrcs _ _ (CBin Pipe lhs c) -> do
    Nest (UAnnBinder expl (WithSrcB sid b) ann cs) bs <- withTrailingConstraints lhs cont
    s <- case b of
      UBindSource s -> return s
      UIgnore       -> throw sid CantConstrainAnonBinders
      UBind _ _     -> error "Shouldn't have internal names until renaming pass"
    c' <- expr c
    return $   UnaryNest (UAnnBinder expl (WithSrcB sid b) ann (cs ++ [c']))
           >>> bs
           >>> UnaryNest (asConstraintBinder (mkUVar sid s) c')
  _ -> UnaryNest <$> cont g
  where
    asConstraintBinder :: UExpr VoidS -> UConstraint VoidS -> UAnnBinder VoidS VoidS
    asConstraintBinder v c = do
      let sid = srcPos c
      let t = WithSrcE sid (UApp c [v] [])
      UAnnBinder (Inferred Nothing (Synth Full)) (WithSrcB sid UIgnore) (UAnn t) []

mkUVar :: SrcId -> SourceName -> UExpr VoidS
mkUVar sid v = WithSrcE sid $ UVar $ SourceName sid v

aGivens :: GivenClause -> SyntaxM (Nest UAnnBinder VoidS VoidS)
aGivens ((WithSrcs _ _ implicits), optConstraints) = do
  implicits' <- concatNests <$> forM implicits \b -> withTrailingConstraints b implicitArgBinder
  constraints <- fromMaybeM optConstraints Empty (\(WithSrcs _ _ gs) -> toNest <$> mapM synthBinder gs)
  return $ implicits' >>> constraints

synthBinder :: GroupW -> SyntaxM (UAnnBinder VoidS VoidS)
synthBinder g = tyOptBinder (Inferred Nothing (Synth Full)) g

concatNests :: [Nest b VoidS VoidS] -> Nest b VoidS VoidS
concatNests [] = Empty
concatNests (b:bs) = b >>> concatNests bs

implicitArgBinder :: GroupW -> SyntaxM (UAnnBinder VoidS VoidS)
implicitArgBinder g = do
  UAnnBinder _ b ann cs <- binderOptTy (Inferred Nothing Unify) g
  s <- case b of
    WithSrcB _ (UBindSource s) -> return $ Just s
    _             -> return Nothing
  return $ UAnnBinder (Inferred s Unify) b ann cs

aExplicitParams :: ExplicitParams -> SyntaxM (Nest UAnnBinder VoidS VoidS)
aExplicitParams (WithSrcs _ _ bs) = binderList bs \b -> withTrailingConstraints b \b' ->
  binderOptTy Explicit b'

aPiBinders :: [GroupW] -> SyntaxM (Nest UAnnBinder VoidS VoidS)
aPiBinders bs = binderList bs \b ->
  UnaryNest <$> tyOptBinder Explicit b

explicitBindersOptAnn :: ExplicitParams -> SyntaxM (Nest UAnnBinder VoidS VoidS)
explicitBindersOptAnn (WithSrcs _ _ bs) =
  binderList bs \b -> withTrailingConstraints b \b' -> binderOptTy Explicit b'

-- ===

-- Binder pattern with an optional type annotation
patOptAnn :: GroupW -> SyntaxM (UPat VoidS VoidS, Maybe (UType VoidS))
patOptAnn (WithSrcs _ _ (CBin Colon lhs typeAnn)) = (,) <$> pat lhs <*> (Just <$> expr typeAnn)
patOptAnn (WithSrcs _ _ (CParens [g])) = patOptAnn g
patOptAnn g = (,Nothing) <$> pat g

uBinder :: GroupW -> SyntaxM (UBinder c VoidS VoidS)
uBinder (WithSrcs sid _ b) = case b of
  CLeaf (CIdentifier name) -> return $ fromSourceNameW $ WithSrc sid name
  CLeaf CHole -> return $ WithSrcB sid UIgnore
  _ -> throw sid UnexpectedBinder

-- Type annotation with an optional binder pattern
tyOptPat :: GroupW -> SyntaxM (UAnnBinder VoidS VoidS)
tyOptPat grpTop@(WithSrcs sid _ grp) = case grp of
  -- Named type
  CBin Colon lhs typeAnn ->
    UAnnBinder Explicit <$> uBinder lhs <*> (UAnn <$> expr typeAnn) <*> pure []
  -- Binder in grouping parens.
  CParens [g] -> tyOptPat g
  -- Anonymous type
  _ -> UAnnBinder Explicit (WithSrcB sid UIgnore) <$> (UAnn <$> expr grpTop) <*> pure []

-- Pattern of a case binder.  This treats bare names specially, in
-- that they become (nullary) constructors to match rather than names
-- to bind.
casePat :: GroupW -> SyntaxM (UPat VoidS VoidS)
casePat = \case
  WithSrcs src _ (CLeaf (CIdentifier name)) ->
    return $ WithSrcB src $ UPatCon (fromSourceNameW (WithSrc src name)) Empty
  g -> pat g

pat :: GroupW -> SyntaxM (UPat VoidS VoidS)
pat (WithSrcs sid _ grp) = WithSrcB sid <$> case grp of
  CBin DepComma lhs rhs -> do
    lhs' <- pat lhs
    rhs' <- pat rhs
    return $ UPatDepPair $ PairB lhs' rhs'
  CBrackets gs -> UPatTable . toNest <$> (mapM pat gs)
  -- TODO: use Python-style trailing comma (like `(x,y,)`) for singleton tuples
  CParens gs -> case gs of
    [g] -> do
      WithSrcB _ g' <- casePat g
      return g'
    _   -> UPatProd . toNest <$> mapM pat gs
  CLeaf CHole -> return $ UPatBinder (WithSrcB sid UIgnore)
  CLeaf (CIdentifier name) -> return $ UPatBinder $ fromSourceNameW $ WithSrc sid name
  CJuxtapose True lhs rhs -> do
    case lhs of
      WithSrcs lhsId _ (CJuxtapose True _ _) -> throw lhsId OnlyUnaryWithoutParens
      _ -> return ()
    name <- identifier "pattern constructor name" lhs
    arg <- pat rhs
    return $ UPatCon (fromSourceNameW name) (UnaryNest arg)
  CJuxtapose False lhs rhs -> do
    name <- identifier "pattern constructor name" lhs
    case rhs of
      WithSrcs _ _ (CParens gs) -> do
        gs' <- mapM pat gs
        return $ UPatCon (fromSourceNameW name) (toNest gs')
      _ -> error "unexpected postfix group (should be ruled out at grouping stage)"
  _ -> throw sid IllegalPattern

tyOptBinder :: Explicitness -> GroupW -> SyntaxM (UAnnBinder VoidS VoidS)
tyOptBinder expl (WithSrcs sid sids grp) = case grp of
  CBin Pipe  _ rhs     -> throw (getSrcId rhs) UnexpectedConstraint
  CBin Colon name ty -> do
    b <- uBinder name
    ann <- UAnn <$> expr ty
    return $ UAnnBinder expl b ann []
  g -> do
    ty <- expr (WithSrcs sid sids g)
    return $ UAnnBinder expl (WithSrcB sid UIgnore) (UAnn ty) []

binderOptTy :: Explicitness -> GroupW -> SyntaxM (UAnnBinder VoidS VoidS)
binderOptTy expl = \case
  WithSrcs _ _ (CBin Colon name ty) -> do
    b <- uBinder name
    ann <- UAnn <$> expr ty
    return $ UAnnBinder expl b ann []
  g -> do
    b <- uBinder g
    return $ UAnnBinder expl b UNoAnn []

binderReqTy :: Explicitness -> GroupW -> SyntaxM (UAnnBinder VoidS VoidS)
binderReqTy expl (WithSrcs _ _ (CBin Colon name ty)) = do
  b <- uBinder name
  ann <- UAnn <$> expr ty
  return $ UAnnBinder expl b ann []
binderReqTy _ g = throw (getSrcId g) ExpectedAnnBinder

argList :: [GroupW] -> SyntaxM ([UExpr VoidS], [UNamedArg VoidS])
argList gs = partitionEithers <$> mapM singleArg gs

singleArg :: GroupW -> SyntaxM (Either (UExpr VoidS) (UNamedArg VoidS))
singleArg = \case
  WithSrcs _ _ (CBin CSEqual lhs rhs) -> Right <$>
    ((,) <$> withoutSrc <$> identifier "named argument" lhs <*> expr rhs)
  g -> Left <$> expr g

identifier :: String -> GroupW -> SyntaxM SourceNameW
identifier ctx (WithSrcs sid _ g) = case g of
  CLeaf (CIdentifier name) -> return $ WithSrc sid name
  _ -> throw sid $ ExpectedIdentifier ctx

aEffects :: WithSrcs ([GroupW], Maybe GroupW) -> SyntaxM (UEffectRow VoidS)
aEffects (WithSrcs _ _ (effs, optEffTail)) = do
  lhs <- mapM effect effs
  rhs <- forM optEffTail \effTail ->
    fromSourceNameW <$> identifier "effect row remainder variable" effTail
  return $ UEffectRow (S.fromList lhs) rhs

effect :: GroupW -> SyntaxM (UEffect VoidS)
effect (WithSrcs grpSid _ grp) = case grp of
  CParens [g] -> effect g
  CJuxtapose True (Identifier "Read" ) (WithSrcs sid _ (CLeaf (CIdentifier h))) ->
    return $ URWSEffect Reader $ fromSourceNameW (WithSrc sid h)
  CJuxtapose True (Identifier "Accum") (WithSrcs sid _ (CLeaf (CIdentifier h))) ->
    return $ URWSEffect Writer $ fromSourceNameW (WithSrc sid h)
  CJuxtapose True (Identifier "State") (WithSrcs sid _ (CLeaf (CIdentifier h))) ->
    return $ URWSEffect State $ fromSourceNameW (WithSrc sid h)
  CLeaf (CIdentifier "Except") -> return UExceptionEffect
  CLeaf (CIdentifier "IO"    ) -> return UIOEffect
  _ -> throw grpSid UnexpectedEffectForm

aMethod :: CSDeclW -> SyntaxM (Maybe (UMethodDef VoidS))
aMethod (WithSrcs _ _ CPass) = return Nothing
aMethod (WithSrcs sid _ d) = Just . WithSrcE sid <$> case d of
  CDefDecl def -> do
    (WithSrc nameSid name, lam) <- aDef def
    return $ UMethodDef (SourceName nameSid name) lam
  CLet (WithSrcs lhsSid _ (CLeaf (CIdentifier name))) rhs -> do
    rhs' <- ULamExpr Empty ImplicitApp Nothing Nothing <$> block rhs
    return $ UMethodDef (fromSourceNameW (WithSrc lhsSid name)) rhs'
  _ -> throw sid UnexpectedMethodDef

asExpr :: UBlock VoidS -> UExpr VoidS
asExpr (WithSrcE src b) = case b of
  UBlock Empty e -> e
  _ -> WithSrcE src $ UDo $ WithSrcE src b

block :: CSBlock -> SyntaxM (UBlock VoidS)
block (ExprBlock g) = WithSrcE (srcPos g) . UBlock Empty <$> expr g
block (IndentedBlock sid decls) = do
  (decls', result) <- blockDecls decls
  return $ WithSrcE sid $ UBlock decls' result

blockDecls :: [CSDeclW] -> SyntaxM (Nest UDecl VoidS VoidS, UExpr VoidS)
blockDecls [] = error "shouldn't have empty list of decls"
blockDecls [WithSrcs sid _ d] = case d of
  CExpr g -> (Empty,) <$> expr g
  _ -> throw sid BlockWithoutFinalExpr
blockDecls (WithSrcs sid _ (CBind b rhs):ds) = do
  b' <- binderOptTy Explicit b
  rhs' <- asExpr <$> block rhs
  body <- block $ IndentedBlock sid ds -- Not really the right SrcId
  let lam = ULam $ ULamExpr (UnaryNest b') ExplicitApp Nothing Nothing body
  return (Empty, WithSrcE sid $ extendAppRight rhs' (WithSrcE sid lam))
blockDecls (d:ds) = do
  d' <- decl PlainLet d
  (ds', e) <- blockDecls ds
  return (Nest d' ds', e)

-- === Concrete to abstract syntax of expressions ===

expr :: GroupW -> SyntaxM (UExpr VoidS)
expr (WithSrcs sid sids grp) = WithSrcE sid <$> case grp of
  CLeaf x -> leaf sid x
  CPrim prim xs     -> UPrim prim <$> mapM expr xs
  CParens [g] -> do
    WithSrcE _ result <- expr g
    return result
  CParens gs -> UPrim UTuple <$> mapM expr gs
  -- Table constructors here.  Other uses of square brackets
  -- should be detected upstream, before calling expr.
  CBrackets gs -> UTabCon <$> mapM expr gs
  CGivens _ -> throw sid UnexpectedGivenClause
  CArrow lhs effs rhs -> do
    case lhs of
      WithSrcs _ _ (CParens gs) -> do
        bs <- aPiBinders gs
        effs' <- fromMaybeM effs UPure aEffects
        resultTy <- expr rhs
        return $ UPi $ UPiExpr bs ExplicitApp effs' resultTy
      WithSrcs lhsSid _ _ -> throw lhsSid ArgsShouldHaveParens
  CDo b -> UDo <$> block b
  CJuxtapose hasSpace lhs rhs -> case hasSpace of
    True -> extendAppRight <$> expr lhs <*> expr rhs
    False -> do
      f <- expr lhs
      case rhs of
        WithSrcs _ _ (CParens args) -> do
          (posArgs, namedArgs) <- argList args
          return $ UApp f posArgs namedArgs
        WithSrcs _ _ (CBrackets args) -> do
          args' <- mapM expr args
          return $ UTabApp f args'
        _ -> error "unexpected postfix group (should be ruled out at grouping stage)"
  CBin op lhs rhs -> case op of
    Dollar -> extendAppRight <$> expr lhs <*> expr rhs
    Pipe   -> extendAppLeft  <$> expr lhs <*> expr rhs
    Dot -> do
      lhs' <- expr lhs
      WithSrcs rhsSid _ rhs' <- return rhs
      name <- case rhs' of
        CLeaf (CIdentifier name) -> return $ FieldName name
        CLeaf (CNat i          ) -> return $ FieldNum $ fromIntegral i
        _ -> throw rhsSid BadField
      return $ UFieldAccess lhs' (WithSrc rhsSid name)
    DoubleColon   -> UTypeAnn <$> (expr lhs) <*> expr rhs
    EvalBinOp (WithSrc opSid s) -> do
      let f = WithSrcE opSid (fromSourceNameW (WithSrc opSid s))
      lhs' <- expr lhs
      rhs' <- expr rhs
      return $ explicitApp f [lhs', rhs']
    DepAmpersand  -> do
      lhs' <- tyOptPat lhs
      UDepPairTy . (UDepPairType ExplicitDepPair lhs') <$> expr rhs
    DepComma      -> UDepPair <$> (expr lhs) <*> expr rhs
    CSEqual       -> throw errSid BadEqualSign
    Colon         -> throw errSid BadColon
    ImplicitArrow -> case lhs of
      WithSrcs _ _ (CParens gs) -> do
        bs <- aPiBinders gs
        resultTy <- expr rhs
        return $ UPi $ UPiExpr bs ImplicitApp UPure resultTy
      WithSrcs lhsSid _ _ -> throw lhsSid ArgsShouldHaveParens
    FatArrow      -> do
      lhs' <- tyOptPat lhs
      UTabPi . (UTabPiExpr lhs') <$> expr rhs
   where
     errSid = case sids of
       [sid'] -> sid'
       _ -> sid
  CPrefix (WithSrc prefixSid name) g -> do
    case name of
      "+" -> (withoutSrc <$> expr g) <&> \case
        UNatLit   i -> UIntLit   (fromIntegral i)
        UIntLit   i -> UIntLit   i
        UFloatLit i -> UFloatLit i
        e -> e
      "-" -> expr g <&> \case
        WithSrcE _ (UNatLit   i) -> UIntLit   (-(fromIntegral i))
        WithSrcE _ (UIntLit   i) -> UIntLit   (-i)
        WithSrcE _ (UFloatLit i) -> UFloatLit (-i)
        e -> unaryApp (mkUVar prefixSid "neg") e
      _ -> throw prefixSid $ BadPrefix $ pprint name
  CLambda params body -> do
    params' <- explicitBindersOptAnn $ WithSrcs sid [] $ map stripParens params
    body' <- block body
    return $ ULam $ ULamExpr params' ExplicitApp Nothing Nothing body'
  CFor kind indices body -> do
    let (dir, trailingUnit) = case kind of
          KFor  -> (Fwd, False)
          KFor_ -> (Fwd, True)
          KRof  -> (Rev, False)
          KRof_ -> (Rev, True)
    -- TODO: Can we fetch the source position from the error context, to feed into `buildFor`?
    e <- buildFor sid dir <$> mapM (binderOptTy Explicit) indices <*> block body
    if trailingUnit
      then return $ UDo $ WithSrcE sid $ UBlock (UnaryNest (WithSrcB sid $ UExprDecl e)) (unitExpr sid)
      else return $ withoutSrc e
  CCase scrut alts -> UCase <$> (expr scrut) <*> mapM alternative alts
    where alternative (match, body) = UAlt <$> casePat match <*> block body
  CIf p c a -> do
    p' <- expr p
    c' <- block c
    a' <- case a of
      Nothing -> return $ WithSrcE sid $ UBlock Empty $ unitExpr sid
      (Just alternative) -> block alternative
    return $ UCase p'
      [ UAlt (WithSrcB sid $ UPatCon (SourceName sid "True")  Empty) c'
      , UAlt (WithSrcB sid $ UPatCon (SourceName sid "False") Empty) a']
  CWith lhs rhs -> do
    ty <- expr lhs
    case rhs of
      WithSrcs _ _ [b] -> do
        b' <- binderReqTy Explicit b
        return $ UDepPairTy $ UDepPairType ImplicitDepPair b' ty
      _ -> error "n-ary dependent pairs not implemented"

leaf :: SrcId -> CLeaf -> SyntaxM (UExpr' VoidS)
leaf sid = \case
  -- Binders (e.g., in pi types) should not hit this case
  CIdentifier name  -> return $ fromSourceNameW $ WithSrc sid name
  CNat word         -> return $ UNatLit word
  CInt int          -> return $ UIntLit int
  CString str       -> do
    xs <- return $ map (WithSrcE sid . charExpr) str
    let toListVar = mkUVar sid "to_list"
    return $ explicitApp toListVar [WithSrcE sid (UTabCon xs)]
  CChar char        -> return $ charExpr char
  CFloat num        -> return $ UFloatLit num
  CHole             -> return   UHole

charExpr :: Char -> (UExpr' VoidS)
charExpr c = ULit $ Word8Lit $ fromIntegral $ fromEnum c

unitExpr :: SrcId -> UExpr VoidS
unitExpr sid = WithSrcE sid $ UPrim (UCon $ P.ProdCon) []

-- === Builders ===

-- TODO Does this generalize?  Swap list for Nest?
-- TODO: these SrcIds aren't really correct
buildFor :: SrcId -> Direction -> [UAnnBinder VoidS VoidS] -> UBlock VoidS -> UExpr VoidS
buildFor sid dir binders body = case binders of
  [] -> error "should have nonempty list of binder"
  [b] -> WithSrcE sid $ UFor dir $ UForExpr b body
  b:bs -> WithSrcE sid $ UFor dir $ UForExpr b $
    WithSrcE sid $ UBlock Empty $ buildFor sid dir bs body

-- === Helpers ===

extendAppRight :: UExpr n -> UExpr n -> UExpr' n
extendAppRight (WithSrcE _ (UApp f args kwargs)) x = UApp f (args ++ [x]) kwargs
extendAppRight f x = unaryApp f x

extendAppLeft :: UExpr n -> UExpr n -> UExpr' n
extendAppLeft x (WithSrcE _ (UApp f args kwargs)) = UApp f (x:args) kwargs
extendAppLeft x f = unaryApp f x

unaryApp :: UExpr n -> UExpr n -> UExpr' n
unaryApp f x = UApp f [x] []

explicitApp :: UExpr n -> [UExpr n] -> UExpr' n
explicitApp f xs = UApp f xs []

toNest :: [a VoidS VoidS] -> Nest a VoidS VoidS
toNest = foldr Nest Empty
