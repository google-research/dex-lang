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
import Data.String (fromString)
import Data.Text (Text)

import ConcreteSyntax
import Err
import Name
import PPrint ()
import Types.Primitives
import Types.Source
import qualified Types.OpNames as P
import Util

-- === Converting concrete syntax to abstract syntax ===

parseExpr :: Fallible m => Group -> m (UExpr VoidS)
parseExpr e = liftSyntaxM $ expr e

parseDecl :: Fallible m => CTopDecl -> m (UTopDecl VoidS VoidS)
parseDecl d = liftSyntaxM $ topDecl d

parseBlock :: Fallible m => CSBlock -> m (UBlock VoidS)
parseBlock b = liftSyntaxM $ block b

liftSyntaxM :: Fallible m => SyntaxM a -> m a
liftSyntaxM cont = liftExcept $ runFallibleM cont

parseTopDeclRepl :: Text -> Maybe SourceBlock
parseTopDeclRepl s = case sbContents b of
  UnParseable True _ -> Nothing
  _ -> case runFallibleM (checkSourceBlockParses $ sbContents b) of
    Success _ -> Just b
    Failure _ -> Nothing
  where b = mustParseSourceBlock s
{-# SCC parseTopDeclRepl #-}

checkSourceBlockParses :: SourceBlock' -> SyntaxM ()
checkSourceBlockParses = \case
  TopDecl (WithSrc _ (CSDecl ann (CExpr e)))-> do
    when (ann /= PlainLet) $ fail "Cannot annotate expressions"
    void $ expr e
  TopDecl d -> void $ topDecl d
  Command _ b -> void $ expr b
  DeclareForeign _ _ ty -> void $ expr ty
  DeclareCustomLinearization _ _ body -> void $ expr body
  Misc _ -> return ()
  UnParseable _ _ -> return ()

-- === Converting concrete syntax to abstract syntax ===

type SyntaxM = FallibleM

topDecl :: CTopDecl -> SyntaxM (UTopDecl VoidS VoidS)
topDecl = dropSrc topDecl' where
  topDecl' (CSDecl ann d) = ULocalDecl <$> decl ann (WithSrc Nothing d)
  topDecl' (CData name tyConParams givens constructors) = do
    tyConParams' <- aExplicitParams tyConParams
    givens' <- toNest <$> fromMaybeM givens [] aGivens
    constructors' <- forM constructors \(v, ps) -> do
      ps' <- toNest <$> mapM tyOptBinder ps
      return (v, ps')
    return $ UDataDefDecl
      (UDataDef name (givens' >>> tyConParams') $
        map (\(name', cons) -> (name', UDataDefTrail cons)) constructors')
      (fromString name)
      (toNest $ map (fromString . fst) constructors')
  topDecl' (CStruct name params givens fields defs) = do
    params' <- aExplicitParams params
    givens' <- toNest <$> fromMaybeM givens [] aGivens
    fields' <- forM fields \(v, ty) -> (v,) <$> expr ty
    methods <- forM defs \(ann, d) -> do
      (methodName, lam) <- aDef d
      return (ann, methodName, Abs (UBindSource "self") lam)
    return $ UStructDecl (fromString name) (UStructDef name (givens' >>> params') fields' methods)
  topDecl' (CInterface name params methods) = do
    params' <- aExplicitParams params
    (methodNames, methodTys) <- unzip <$> forM methods \(methodName, ty) -> do
      ty' <- expr ty
      return (fromString methodName, ty')
    return $ UInterface params' methodTys (fromString name) (toNest methodNames)
  topDecl' (CInstanceDecl def) = aInstanceDef def
  topDecl' (CEffectDecl _ _) = error "not implemented"
  topDecl' (CHandlerDecl _ _ _ _ _ _) = error "not implemented"

decl :: LetAnn -> CSDecl -> SyntaxM (UDecl VoidS VoidS)
decl ann = propagateSrcB \case
  CLet binder rhs -> do
    (p, ty) <- patOptAnn binder
    ULet ann p ty <$> asExpr <$> block rhs
  CBind _ _ -> throw SyntaxErr "Arrow binder syntax <- not permitted at the top level, because the binding would have unbounded scope."
  CDefDecl def -> do
    (name, lam) <- aDef def
    return $ ULet ann (fromString name) Nothing (ns $ ULam lam)
  CExpr g -> UExprDecl <$> expr g
  CPass -> return UPass

aInstanceDef :: CInstanceDef -> SyntaxM (UTopDecl VoidS VoidS)
aInstanceDef (CInstanceDef clName args givens methods instNameAndParams) = do
  let clName' = fromString clName
  args' <- mapM expr args
  givens' <- toNest <$> fromMaybeM givens [] aGivens
  methods' <- catMaybes <$> mapM aMethod methods
  case instNameAndParams of
    Nothing -> return $ UInstance clName' givens' args' methods' NothingB ImplicitApp
    Just (instName, optParams) -> do
      let instName' = JustB $ fromString instName
      case optParams of
        Just params -> do
          params' <- aExplicitParams params
          return $ UInstance clName' (givens' >>> params') args' methods' instName' ExplicitApp
        Nothing -> return $ UInstance clName' givens' args' methods' instName' ImplicitApp

aDef :: CDef -> SyntaxM (SourceName, ULamExpr VoidS)
aDef (CDef name params optRhs optGivens body) = do
  explicitParams <- aExplicitParams params
  let rhsDefault = (ExplicitApp, Nothing, Nothing)
  (expl, effs, resultTy) <- fromMaybeM optRhs rhsDefault \(expl, optEffs, resultTy) -> do
    effs <- fromMaybeM optEffs UPure aEffects
    resultTy' <- expr resultTy
    return (expl, Just effs, Just resultTy')
  implicitParams <- toNest <$> fromMaybeM optGivens [] aGivens
  let allParams = implicitParams >>> explicitParams
  body' <- block body
  return (name, ULamExpr allParams expl effs resultTy body')

stripParens :: Group -> Group
stripParens (WithSrc _ (CParens [g])) = stripParens g
stripParens g = g

aExplicitParams :: ExplicitParams -> SyntaxM (Nest (WithExpl UOptAnnBinder) VoidS VoidS)
aExplicitParams gs = generalBinders DataParam Explicit gs

aGivens :: GivenClause -> SyntaxM [WithExpl UOptAnnBinder VoidS VoidS]
aGivens (implicits, optConstraints) = do
  implicits' <- mapM (generalBinder DataParam (Inferred Nothing Unify)) implicits
  constraints <- fromMaybeM optConstraints [] \gs -> do
    mapM (generalBinder TypeParam (Inferred Nothing (Synth Full))) gs
  return $ implicits' <> constraints

generalBinders
  :: ParamStyle -> Explicitness -> [Group]
  -> SyntaxM (Nest (WithExpl UOptAnnBinder) VoidS VoidS)
generalBinders paramStyle expl params = toNest . concat <$>
  forM params \case
    WithSrc _ (CGivens gs) -> aGivens gs
    p -> (:[]) <$> generalBinder paramStyle expl p

generalBinder :: ParamStyle -> Explicitness -> Group
              -> SyntaxM (WithExpl UOptAnnBinder VoidS VoidS)
generalBinder paramStyle expl g = case expl of
  Inferred _ (Synth _) -> WithExpl expl <$> tyOptBinder g
  Inferred _ Unify -> do
    b <- binderOptTy g
    expl' <- return case b of
      UAnnBinder (UBindSource s) _ _ -> Inferred (Just s) Unify
      _ -> expl
    return $ WithExpl expl' b
  Explicit -> WithExpl expl <$> case paramStyle of
    TypeParam -> tyOptBinder g
    DataParam -> binderOptTy g

  -- Binder pattern with an optional type annotation
patOptAnn :: Group -> SyntaxM (UPat VoidS VoidS, Maybe (UType VoidS))
patOptAnn (Binary Colon lhs typeAnn) = (,) <$> pat lhs <*> (Just <$> expr typeAnn)
patOptAnn (WithSrc _ (CParens [g])) = patOptAnn g
patOptAnn g = (,Nothing) <$> pat g

uBinder :: Group -> SyntaxM (UBinder c VoidS VoidS)
uBinder (WithSrc src b) = addSrcContext src $ case b of
  CIdentifier name -> return $ fromString name
  CHole -> return UIgnore
  _ -> throw SyntaxErr "Binder must be an identifier or `_`"

-- Type annotation with an optional binder pattern
tyOptPat :: Group -> SyntaxM (UOptAnnBinder VoidS VoidS)
tyOptPat = \case
  -- Named type
  Binary Colon lhs typeAnn -> UAnnBinder <$> uBinder lhs <*> (UAnn <$> expr typeAnn) <*> pure []
  -- Binder in grouping parens.
  WithSrc _ (CParens [g]) -> tyOptPat g
  -- Anonymous type
  g -> UAnnBinder UIgnore <$> (UAnn <$> expr g) <*> pure []

-- Pattern of a case binder.  This treats bare names specially, in
-- that they become (nullary) constructors to match rather than names
-- to bind.
casePat :: Group -> SyntaxM (UPat VoidS VoidS)
casePat = \case
  (WithSrc src (CIdentifier name)) -> return $ WithSrcB src $ UPatCon (fromString name) Empty
  g -> pat g

pat :: Group -> SyntaxM (UPat VoidS VoidS)
pat = propagateSrcB pat' where
  pat' (CBin (WithSrc _ DepComma) lhs rhs) = do
    lhs' <- pat lhs
    rhs' <- pat rhs
    return $ UPatDepPair $ PairB lhs' rhs'
  pat' (CBrackets gs) = UPatTable . toNest <$> (mapM pat gs)
  -- TODO: use Python-style trailing comma (like `(x,y,)`) for singleton tuples
  pat' (CParens [g]) = dropSrcB <$> casePat g
  pat' (CParens gs) = UPatProd . toNest <$> mapM pat gs
  pat' CHole = return $ UPatBinder UIgnore
  pat' (CIdentifier name) = return $ UPatBinder $ fromString name
  pat' (CBin (WithSrc _ JuxtaposeWithSpace) lhs rhs) = do
    case lhs of
      WithSrc _ (CBin (WithSrc _ JuxtaposeWithSpace) _ _) ->
        throw SyntaxErr "Only unary constructors can form patterns without parens"
      _ -> return ()
    name <- identifier "pattern constructor name" lhs
    arg <- pat rhs
    return $ UPatCon (fromString name) (UnaryNest arg)
  pat' (CBin (WithSrc _ JuxtaposeNoSpace) lhs rhs) = do
    name <- identifier "pattern constructor name" lhs
    case rhs of
      WithSrc _ (CParens gs) -> UPatCon (fromString name) . toNest <$> mapM pat gs
      _ -> error "unexpected postfix group (should be ruled out at grouping stage)"
  pat' _ = throw SyntaxErr "Illegal pattern"

data ParamStyle
 = TypeParam  -- binder optional, used in pi types
 | DataParam  -- type optional  , used in lambda

tyOptBinder :: Group -> SyntaxM (UAnnBinder req VoidS VoidS)
tyOptBinder = \case
  Binary Pipe  _ _     -> throw SyntaxErr "Unexpected constraint"
  Binary Colon name ty -> do
    b <- uBinder name
    ann <- UAnn <$> expr ty
    return $ UAnnBinder b ann []
  g -> do
    ty <- expr g
    return $ UAnnBinder UIgnore (UAnn ty) []

binderOptTy :: Group -> SyntaxM (UOptAnnBinder VoidS VoidS)
binderOptTy g = do
  (g', constraints) <- trailingConstraints g
  case g' of
    Binary Colon name ty -> do
      b <- uBinder name
      ann <- UAnn <$> expr ty
      return $ UAnnBinder b ann constraints
    _ -> do
      b <- uBinder g'
      return $ UAnnBinder b UNoAnn constraints

trailingConstraints :: Group -> SyntaxM (Group, [UConstraint VoidS])
trailingConstraints gTop = go [] gTop where
  go :: [UConstraint VoidS] -> Group -> SyntaxM (Group, [UConstraint VoidS])
  go cs = \case
    Binary Pipe lhs c -> do
      c' <- expr c
      go (c':cs) lhs
    g -> return (g, cs)

argList :: [Group] -> SyntaxM ([UExpr VoidS], [UNamedArg VoidS])
argList gs = partitionEithers <$> mapM singleArg gs

singleArg :: Group -> SyntaxM (Either (UExpr VoidS) (UNamedArg VoidS))
singleArg = \case
  WithSrc src (CBin (WithSrc _ CSEqual) lhs rhs) -> addSrcContext src $ Right <$>
    ((,) <$> identifier "named argument" lhs <*> expr rhs)
  g -> Left <$> expr g

identifier :: String -> Group -> SyntaxM SourceName
identifier ctx = dropSrc identifier' where
  identifier' (CIdentifier name) = return name
  identifier' _ = throw SyntaxErr $ "Expected " ++ ctx ++ " to be an identifier"

aEffects :: ([Group], Maybe Group) -> SyntaxM (UEffectRow VoidS)
aEffects (effs, optEffTail) = do
  lhs <- mapM effect effs
  rhs <- forM optEffTail \effTail ->
    fromString <$> identifier "effect row remainder variable" effTail
  return $ UEffectRow (S.fromList lhs) rhs

effect :: Group -> SyntaxM (UEffect VoidS)
effect (WithSrc _ (CParens [g])) = effect g
effect (Binary JuxtaposeWithSpace (Identifier "Read") (Identifier h)) =
  return $ URWSEffect Reader $ fromString h
effect (Binary JuxtaposeWithSpace (Identifier "Accum") (Identifier h)) =
  return $ URWSEffect Writer $ fromString h
effect (Binary JuxtaposeWithSpace (Identifier "State") (Identifier h)) =
  return $ URWSEffect State $ fromString h
effect (Identifier "Except") = return UExceptionEffect
effect (Identifier "IO") = return UIOEffect
effect (Identifier effName) = return $ UUserEffect (fromString effName)
effect _ = throw SyntaxErr "Unexpected effect form; expected one of `Read h`, `Accum h`, `State h`, `Except`, `IO`, or the name of a user-defined effect."

aMethod :: CSDecl -> SyntaxM (Maybe (UMethodDef VoidS))
aMethod (WithSrc _ CPass) = return Nothing
aMethod (WithSrc src d) = Just . WithSrcE src <$> addSrcContext src case d of
  CDefDecl def -> do
    (name, lam) <- aDef def
    return $ UMethodDef (fromString name) lam
  CLet (WithSrc _ (CIdentifier name)) rhs -> do
    rhs' <- ULamExpr Empty ImplicitApp Nothing Nothing <$> block rhs
    return $ UMethodDef (fromString name) rhs'
  _ -> throw SyntaxErr "Unexpected method definition. Expected `def` or `x = ...`."

asExpr :: UBlock VoidS -> UExpr VoidS
asExpr (WithSrcE src b) = case b of
  UBlock Empty e -> e
  _ -> WithSrcE src $ UDo $ WithSrcE src b

block :: CSBlock -> SyntaxM (UBlock VoidS)
block (ExprBlock g) = WithSrcE Nothing . UBlock Empty <$> expr g
block (IndentedBlock decls) = do
  (decls', result) <- blockDecls decls
  return $ WithSrcE Nothing $ UBlock decls' result

blockDecls :: [CSDecl] -> SyntaxM (Nest UDecl VoidS VoidS, UExpr VoidS)
blockDecls [] = error "shouldn't have empty list of decls"
blockDecls [WithSrc src d] = addSrcContext src case d of
  CExpr g -> (Empty,) <$> expr g
  _ -> throw SyntaxErr "Block must end in expression"
blockDecls (WithSrc pos (CBind b rhs):ds) = do
  WithExpl _ b' <- generalBinder DataParam Explicit b
  rhs' <- asExpr <$> block rhs
  body <- block $ IndentedBlock ds
  let lam = ULam $ ULamExpr (UnaryNest (WithExpl Explicit b')) ExplicitApp Nothing Nothing body
  return (Empty, WithSrcE pos $ extendAppRight rhs' (ns lam))
blockDecls (d:ds) = do
  d' <- decl PlainLet d
  (ds', e) <- blockDecls ds
  return (Nest d' ds', e)

-- === Concrete to abstract syntax of expressions ===

expr :: Group -> SyntaxM (UExpr VoidS)
expr = propagateSrcE expr' where
  expr' CEmpty              = return   UHole
  -- Binders (e.g., in pi types) should not hit this case
  expr' (CIdentifier name)  = return $ fromString name
  expr' (CPrim prim xs)     = UPrim prim <$> mapM expr xs
  expr' (CNat word)         = return $ UNatLit word
  expr' (CInt int)          = return $ UIntLit int
  expr' (CString str)       = return $ explicitApp (fromString "to_list")
    [ns $ UTabCon $ map (ns . charExpr) str]
  expr' (CChar char)        = return $ charExpr char
  expr' (CFloat num)        = return $ UFloatLit num
  expr' CHole               = return   UHole
  expr' (CParens [g])       = dropSrcE <$> expr g
  expr' (CParens gs) = UPrim UTuple <$> mapM expr gs
  -- Table constructors here.  Other uses of square brackets
  -- should be detected upstream, before calling expr.
  expr' (CBrackets gs) = UTabCon <$> mapM expr gs
  expr' (CGivens _) = throw SyntaxErr $ "Unexpected `given` clause"
  expr' (CArrow lhs effs rhs) = do
    case lhs of
      WithSrc _ (CParens gs) -> do
        bs <- generalBinders TypeParam Explicit gs
        effs' <- fromMaybeM effs UPure aEffects
        resultTy <- expr rhs
        return $ UPi $ UPiExpr bs ExplicitApp effs' resultTy
      _ -> throw SyntaxErr "Argument types should be in parentheses"
  expr' (CDo b) = UDo <$> block b
  -- Binders (e.g., in pi types) should not hit this case
  expr' (CBin (WithSrc opSrc op) lhs rhs) =
    case op of
      JuxtaposeNoSpace -> do
        f <- expr lhs
        case rhs of
          WithSrc _ (CParens args) -> do
            (posArgs, namedArgs) <- argList args
            return $ UApp f posArgs namedArgs
          WithSrc _ (CBrackets args) -> do
            args' <- mapM expr args
            return $ UTabApp f args'
          _ -> error "unexpected postfix group (should be ruled out at grouping stage)"
      JuxtaposeWithSpace -> extendAppRight <$> expr lhs <*> expr rhs
      Dollar             -> extendAppRight <$> expr lhs <*> expr rhs
      Pipe               -> extendAppLeft  <$> expr lhs <*> expr rhs
      Dot -> do
        lhs' <- expr lhs
        WithSrc src rhs' <- return rhs
        name <- addSrcContext src $ case rhs' of
          CIdentifier name -> return $ FieldName name
          CNat i           -> return $ FieldNum $ fromIntegral i
          _ -> throw SyntaxErr "Field must be a name or an integer"
        return $ UFieldAccess lhs' (WithSrc src name)
      DoubleColon   -> UTypeAnn <$> (expr lhs) <*> expr rhs
      EvalBinOp s -> evalOp s
      DepAmpersand  -> do
        lhs' <- tyOptPat lhs
        UDepPairTy . (UDepPairType ExplicitDepPair lhs') <$> expr rhs
      DepComma      -> UDepPair <$> (expr lhs) <*> expr rhs
      CSEqual       -> throw SyntaxErr "Equal sign must be used as a separator for labels or binders, not a standalone operator"
      Colon         -> throw SyntaxErr "Colon separates binders from their type annotations, is not a standalone operator.\nIf you are trying to write a dependent type, use parens: (i:Fin 4) => (..i)"
      ImplicitArrow -> case lhs of
        WithSrc _ (CParens gs) -> do
          bs <- generalBinders TypeParam Explicit gs
          resultTy <- expr rhs
          return $ UPi $ UPiExpr bs ImplicitApp UPure resultTy
        _ -> throw SyntaxErr "Argument types should be in parentheses"
      FatArrow      -> do
        lhs' <- tyOptPat lhs
        UTabPi . (UTabPiExpr lhs') <$> expr rhs
    where
      evalOp s = do
        let f = WithSrcE opSrc (fromString s)
        lhs' <- expr lhs
        rhs' <- expr rhs
        return $ explicitApp f [lhs', rhs']
  expr' (CPrefix name g) =
    case name of
      ".." -> range "RangeTo" <$> expr g
      "..<" -> range "RangeToExc" <$> expr g
      "+" -> (dropSrcE <$> expr g) <&> \case
        UNatLit   i -> UIntLit   (fromIntegral i)
        UIntLit   i -> UIntLit   i
        UFloatLit i -> UFloatLit i
        e -> e
      "-" -> expr g <&> \case
        WithSrcE _ (UNatLit   i) -> UIntLit   (-(fromIntegral i))
        WithSrcE _ (UIntLit   i) -> UIntLit   (-i)
        WithSrcE _ (UFloatLit i) -> UFloatLit (-i)
        e -> unaryApp "neg" e
      _ -> throw SyntaxErr $ "Prefix (" ++ name ++ ") not legal as a bare expression"
    where
      range :: UExpr VoidS -> UExpr VoidS -> UExpr' VoidS
      range rangeName lim = explicitApp rangeName [ns UHole, lim]
  expr' (CPostfix name g) =
    case name of
      ".." -> range "RangeFrom" <$> expr g
      "<.." -> range "RangeFromExc" <$> expr g
      _ -> throw SyntaxErr $ "Postfix (" ++ name ++ ") not legal as a bare expression"
    where
      range :: UExpr VoidS -> UExpr VoidS -> UExpr' VoidS
      range rangeName lim = explicitApp rangeName [ns UHole, lim]
  expr' (CLambda params body) = do
    params' <- aExplicitParams $ map stripParens params
    body' <- block body
    return $ ULam $ ULamExpr params' ExplicitApp Nothing Nothing body'
  expr' (CFor kind indices body) = do
    let (dir, trailingUnit) = case kind of
          KFor  -> (Fwd, False)
          KFor_ -> (Fwd, True)
          KRof  -> (Rev, False)
          KRof_ -> (Rev, True)
    -- TODO: Can we fetch the source position from the error context, to feed into `buildFor`?
    e <- buildFor (0, 0) dir <$> mapM binderOptTy indices <*> block body
    if trailingUnit
      then return $ UDo $ ns $ UBlock (UnaryNest (nsB $ UExprDecl e)) (ns unitExpr)
      else return $ dropSrcE e
  expr' (CCase scrut alts) = UCase <$> (expr scrut) <*> mapM alternative alts
    where alternative (match, body) = UAlt <$> casePat match <*> block body
  expr' (CIf p c a) = do
    p' <- expr p
    c' <- block c
    a' <- case a of
      Nothing -> return $ ns $ UBlock Empty $ ns unitExpr
      (Just alternative) -> block alternative
    return $ UCase p'
      [ UAlt (nsB $ UPatCon "True"  Empty) c'
      , UAlt (nsB $ UPatCon "False" Empty) a']
  expr' (CWith lhs rhs) = do
    ty <- expr lhs
    case rhs of
      [b] -> do
        b' <- binderOptTy b
        return $ UDepPairTy $ UDepPairType ImplicitDepPair b' ty
      _ -> error "n-ary dependent pairs not implemented"

charExpr :: Char -> (UExpr' VoidS)
charExpr c = ULit $ Word8Lit $ fromIntegral $ fromEnum c

unitExpr :: UExpr' VoidS
unitExpr = UPrim (UCon $ P.ProdCon) []

-- === Builders ===

-- TODO Does this generalize?  Swap list for Nest?
buildFor :: SrcPos -> Direction -> [UOptAnnBinder VoidS VoidS] -> UBlock VoidS -> UExpr VoidS
buildFor pos dir binders body = case binders of
  [] -> error "should have nonempty list of binder"
  [b] -> WithSrcE (Just pos) $ UFor dir $ UForExpr b body
  b:bs -> WithSrcE (Just pos) $ UFor dir $ UForExpr b $
    ns $ UBlock Empty $ buildFor pos dir bs body

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

ns :: (a n) -> WithSrcE a n
ns = WithSrcE Nothing

nsB :: (b n l) -> WithSrcB b n l
nsB = WithSrcB Nothing

toNest :: [a VoidS VoidS] -> Nest a VoidS VoidS
toNest = foldr Nest Empty

dropSrc :: (t -> SyntaxM a) -> WithSrc t -> SyntaxM a
dropSrc act (WithSrc src x) = addSrcContext src $ act x

propagateSrcE :: (t -> SyntaxM (e n)) -> WithSrc t -> SyntaxM (WithSrcE e n)
propagateSrcE act (WithSrc src x) = addSrcContext src (WithSrcE src <$> act x)

dropSrcE :: WithSrcE e n -> e n
dropSrcE (WithSrcE _ x) = x

propagateSrcB :: (t -> SyntaxM (binder n l)) -> WithSrc t -> SyntaxM (WithSrcB binder n l)
propagateSrcB act (WithSrc src x) = addSrcContext src (WithSrcB src <$> act x)

dropSrcB :: WithSrcB binder n l -> binder n l
dropSrcB (WithSrcB _ x) = x
