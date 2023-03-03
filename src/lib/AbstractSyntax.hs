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

import Control.Monad (forM, when, liftM2)
import Data.Functor
import Data.Maybe
import Data.Set qualified as S
import Data.String (fromString)
import Data.Text (Text)

import ConcreteSyntax
import Err
import Name
import PPrint ()
import IRVariants
import Types.Primitives
import Types.Source

-- === Converting concrete syntax to abstract syntax ===

parseExpr :: Fallible m => Group -> m (UExpr VoidS)
parseExpr e = liftSyntaxM $ expr e

parseDecl :: Fallible m => CTopDecl -> m (UDecl VoidS VoidS)
parseDecl d = liftSyntaxM $ topDecl d

parseBlock :: Fallible m => CSBlock -> m (UExpr VoidS)
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
  TopDecl (WithSrc _ (CSDecl ann (ExprDecl e)))-> do
    when (ann /= PlainLet) $ fail "Cannot annotate expressions"
    void $ expr e
  TopDecl d -> void $ topDecl d
  Command _ b -> void $ block b
  DeclareForeign _ _ ty -> void $ expr ty
  DeclareCustomLinearization _ _ body -> void $ expr body
  Misc _ -> return ()
  UnParseable _ _ -> return ()

-- === Converting concrete syntax to abstract syntax ===

type SyntaxM = FallibleM

topDecl :: CTopDecl -> SyntaxM (UDecl VoidS VoidS)
topDecl = dropSrc topDecl' where
  topDecl' (CSDecl ann d) = decl ann d
  topDecl' (CData name args constructors) = do
    binders <- toNest . concat <$> mapM dataArg args
    constructors' <- mapM dataCon constructors
    return $ UDataDefDecl
      (UDataDef name binders $
        map (\(name', cons) -> (name', UDataDefTrail cons)) constructors')
      (fromString name)
      (toNest $ map (fromString . fst) constructors')
  topDecl' (CStruct name args fields) = do
    binders <- toNest . concat <$> mapM dataArg args
    fields' <- mapM fieldCon fields
    return $ UStructDecl (UStructDef name binders fields') (fromString name)
  topDecl' (CInterface supers self methods) = do
    supers' <- mapM expr supers
    (name, params) <- tyCon self
    (methodNames, methodTys) <- unzip <$> forM methods \(nms, ty) -> do
      (nm:nms') <- mapM (identifier "interface method name or argument") $ nary Juxtapose nms
      ty' <- expr ty
      return (fromString nm, UMethodType (Left nms') ty')
    let methodNames' = toNest methodNames
    return $ UInterface params supers' methodTys
      (fromString name) methodNames'
  topDecl' (CEffectDecl name methods) = do
    let (methodNames, methodPolicies, methodTys) = unzip3 methods
    methodTys' <- mapM expr methodTys
    return $ UEffectDecl (zipWith UEffectOpType methodPolicies methodTys')
      (fromString name) (toNest $ map fromString methodNames)
  topDecl' (CHandlerDecl hName effName bodyTyArg args ty methods) = do
    let bodyTyArg' = fromString bodyTyArg
    args' <- concat <$> (mapM argument $ nary Juxtapose args)
    (effs, returnTy) <- optEffects $ effectsToTop ty
    methods' <- mapM effectOpDef methods
    return $ UHandlerDecl (fromString effName) bodyTyArg' (toNest args')
      effs returnTy methods' (fromString hName)

dataArg :: Group -> SyntaxM [(UAnnBinderArrow (AtomNameC CoreIR)) 'VoidS 'VoidS]
dataArg = \case
  g@(WithSrc _ (CBracket Square _)) -> map classUAnnBinder <$> multiIfaceBinder g
  arg -> do
    binder <- optAnnotatedBinder $ (binOptR Colon) arg
    return $ [plainUAnnBinder binder]

-- This corresponds to tyConDef in the original parser.
-- tyCon differs from dataCon in how they treat a binding without an
-- annotation.  tyCon interprets it as a name that is implicitly of
-- type TypeKind, and dataCon interprets it as a type that isn't bound
-- to a name.
tyCon :: NameAndArgs -> SyntaxM (UConDef VoidS VoidS)
tyCon = generalCon $ binOptR Colon

-- This corresponds to dataConDef in the original parser.
dataCon :: NameAndArgs -> SyntaxM (UConDef VoidS VoidS)
dataCon = generalCon $ binOptL Colon

fieldCon :: NameAndType -> SyntaxM (SourceName, UType VoidS)
fieldCon (name, ty) = (name,) <$> expr ty

-- generalCon is the common part of tyCon and dataCon.
generalCon :: (Group -> (Maybe Group, Maybe Group))
           -> NameAndArgs
           -> SyntaxM (UConDef VoidS VoidS)
generalCon binOpt (name, args) = do
  args' <- mapM (optAnnotatedBinder . binOpt) args
  return $ (name, toNest args')

-- The arguments are the left- and right-hand sides of a binder
-- annotation.  Each is, in different contexts, optional.  If the
-- binder is missing, assume UIgnore; if the anntation is missing,
-- assume TypeKind.
optAnnotatedBinder :: (Maybe Group, Maybe Group)
                   -> SyntaxM (UAnnBinder (AtomNameC CoreIR) VoidS VoidS)
optAnnotatedBinder (lhs, rhs) = do
  lhs' <- mapM (identifier "type-annotated binder") lhs
  rhs' <- mapM expr rhs
  return $ UAnnBinder (maybe UIgnore fromString lhs')
    $ fromMaybe tyKind rhs'
  where tyKind = ns $ UPrim (UPrimTC TypeKind) []

multiIfaceBinder :: Group -> SyntaxM [UAnnBinder (AtomNameC CoreIR) VoidS VoidS]
multiIfaceBinder = dropSrc \case
  (CBracket Square g) -> do tys <- mapM expr $ nary Comma g
                            return $ map (UAnnBinder UIgnore) tys
  g@(CBin (WithSrc _ Juxtapose) _ _) -> concat <$> mapM multiIfaceBinder (nary Juxtapose $ WithSrc Nothing g)
  _ -> fail "Invalid class constraint list; expecting one or more bracketed groups"

effectOpDef :: (SourceName, Maybe UResumePolicy, CSBlock) -> SyntaxM (UEffectOpDef VoidS)
effectOpDef (v, Nothing, rhs) =
  case v of
    "return" -> UReturnOpDef <$> block rhs
    _ -> error "impossible"
effectOpDef (v, Just rp, rhs) = UEffectOpDef rp (fromString v) <$> block rhs

decl :: LetAnn -> CSDecl -> SyntaxM (UDecl VoidS VoidS)
decl ann = dropSrc decl' where
  decl' (CLet binder body) = ULet ann <$> patOptAnn binder <*> block body
  decl' (CBind _ _) = throw SyntaxErr "Arrow binder syntax <- not permitted at the top level, because the binding would have unbounded scope."
  decl' (CDef name params maybeTy body) = do
    params' <- concat <$> (mapM argument $ nary Juxtapose params)
    case maybeTy of
      Just ty -> do
        (effs, returnTy) <- optEffects $ effectsToTop ty
        when (null params' && effs /= UPure) $ throw SyntaxErr "Nullary def can't have effects"
        let funTy = buildPiType params' effs returnTy
        let lamBinders = params' <&> \(UPatAnnArrow (UPatAnn p _) arr) -> (UPatAnnArrow (UPatAnn p Nothing) arr)
        body' <- block body
        return $ ULet ann (UPatAnn (fromString name) (Just funTy)) $ buildLam lamBinders body'
      Nothing -> do
        body' <- block body
        return $ ULet ann (UPatAnn (fromString name) Nothing) $ buildLam params' body'
  decl' (CInstance header givens methods instName) = do
    givens' <- concat <$> (mapM argument $ nary Juxtapose givens)
    let msg = "As of October 2022, instance declarations use `given` for the binders and superclasses\n" ++
          "For example, `instance Add (a & b) given {a b} [Add a, Add b]`"
    clName' <- addContext msg $
      identifier "class name in instance declaration" clName
    args' <- mapM expr args
    methods' <- mapM method methods
    let instName' = case instName of
          Nothing  -> NothingB
          (Just n) -> JustB $ fromString n
    return $ UInstance (fromString clName') (toNest givens') args' methods' instName'
    where
      (clName:args) = nary Juxtapose header
  decl' (CExpr g) = ULet ann (UPatAnn (nsB UPatIgnore) Nothing) <$> expr g

-- Binder pattern with an optional type annotation
patOptAnn :: Group -> SyntaxM (UPatAnn VoidS VoidS)
patOptAnn (Binary Colon lhs typeAnn) = UPatAnn <$> pat lhs <*> (Just <$> expr typeAnn)
patOptAnn (WithSrc _ (CParens (ExprBlock g))) = patOptAnn g
patOptAnn g = flip UPatAnn Nothing <$> pat g

-- Type annotation with an optional binder pattern
tyOptPat :: Group -> SyntaxM (UPatAnn VoidS VoidS)
tyOptPat = \case
  -- Named type
  (Binary Colon lhs typeAnn) -> UPatAnn <$> pat lhs <*> (Just <$> expr typeAnn)
  -- Pattern in grouping parens.
  -- An anonymous tuple type (foo & bar) will group as parens around a
  -- Binary Ampersand, which will fall through to the anonymous case
  -- as desired.
  (WithSrc _ (CParens (ExprBlock g))) -> tyOptPat g
  -- Anonymous type
  g -> UPatAnn (nsB $ UPatBinder UIgnore) . Just <$> expr g

-- Pattern of a case binder.  This treats bare names specially, in
-- that they become (nullary) constructors to match rather than names
-- to bind.
casePat :: Group -> SyntaxM (UPat VoidS VoidS)
casePat = \case
  (WithSrc src (CIdentifier name)) -> return $ WithSrcB src $ UPatCon (fromString name) Empty
  g -> pat g

pat :: Group -> SyntaxM (UPat VoidS VoidS)
pat = propagateSrcB pat' where
  pat' (CBin (WithSrc _ Comma) lhs rhs) = do
    lhs' <- pat lhs
    rhs' <- pat rhs
    return $ UPatPair $ PairB lhs' rhs'
  pat' (CBin (WithSrc _ DepComma) lhs rhs) = do
    lhs' <- pat lhs
    rhs' <- pat rhs
    return $ UPatDepPair $ PairB lhs' rhs'
  pat' (CBracket Curly g) = case g of
    (WithSrc _ CEmpty) -> return $ UPatRecord UEmptyRowPat
    _ -> UPatRecord <$> (fieldRowPatList CSEqual $ nary Comma g)
  pat' (CBracket Square g) = UPatTable . toNest <$> (mapM pat $ nary Comma g)
  -- A single name in parens is also interpreted as a nullary
  -- constructor to match
  pat' (CParens (ExprBlock g)) = dropSrcB <$> casePat g
  pat' CEmpty = return $ UPatUnit UnitB
  pat' CHole = return $ UPatBinder UIgnore
  pat' (CIdentifier name) = return $ UPatBinder $ fromString name
  pat' (CBin (WithSrc _ Juxtapose) lhs rhs) = do
    -- Juxtapose associates to the left, so this is how we get the
    -- first sub-group in the tree.
    -- TODO: This makes all juxtaposed patterns mean "constructor name
    -- followed by patterns for arguments".  This is sensible inside
    -- parens, but it's possible for the concrete syntax to produce
    -- juxtaposed patterns outside parens as well, for example `def
    -- foo (a b:Int)`.  Do we want to treat those differently?
    let (name:args) = nary Juxtapose $ Binary Juxtapose lhs rhs
    name' <- identifier "pattern constructor name" name
    args' <- toNest <$> mapM pat args
    return $ UPatCon (fromString name') args'
  pat' _ = throw SyntaxErr "Illegal pattern"

fieldRowPatList :: Bin' -> [Group] -> SyntaxM (UFieldRowPat VoidS VoidS)
fieldRowPatList bind groups = go groups UEmptyRowPat where
  go [] rest = return rest
  go (g:gs) rest = case g of
    (Binary binder lhs rhs) | binder == bind -> do
      header <- case lhs of
        (Prefix "@..." field) -> UDynFieldsPat . fromString <$>
          identifier "record pattern dynamic remainder name" field
        (Prefix "@"    field) -> UDynFieldPat . fromString <$>
          identifier "record pattern dynamic field name" field
        field -> UStaticFieldPat <$> identifier "record pattern field" field
      rhs' <- pat rhs
      header rhs' <$> go gs rest
    (Prefix "..." field) -> case gs of
      [] -> case field of
        (WithSrc _ CEmpty) -> return $ URemFieldsPat UIgnore
        (WithSrc _ CHole) -> return $ URemFieldsPat UIgnore
        name -> URemFieldsPat . fromString
          <$> identifier "record pattern remainder name" name
      _ -> throw SyntaxErr "Ellipsis-pattern must be last"
    (WithSrc _ (CParens (ExprBlock g'))) -> go (g':gs) rest
    field@(WithSrc src _) -> do
      field' <- identifier "record pattern field pun" field
      UStaticFieldPat (fromString field') (WithSrcB src $ fromString field') <$> go gs rest

-- The single argument case supports one annotated binder per set of
-- brackets.  The list version supports a list of binders, which are
-- either anonymous, in the case of class constraints (square brackets)
-- or not type annoated, in the other cases.
-- TODO: Why not just allow name / type annotations in the list
-- versions as well?
argument :: Group -> SyntaxM [UPatAnnArrow VoidS VoidS]
argument (Bracketed Curly g) = case g of
  (Binary Colon name typ) -> singleArgument ImplicitArrow name typ
  _ -> do
    pats <- mapM pat $ nary Juxtapose g
    return $ map (\x -> UPatAnnArrow (UPatAnn x Nothing) ImplicitArrow) pats
argument (Bracketed Square g) = case g of
  (Binary Colon name typ) -> singleArgument ClassArrow name typ
  _ -> do
    tys <- mapM expr $ nary Comma g
    return $ map (\ty -> UPatAnnArrow (UPatAnn (nsB UPatIgnore) (Just ty)) ClassArrow) tys
argument (WithSrc _ (CParens (ExprBlock g))) = explicitArgument g
argument g = explicitArgument g

singleArgument :: Arrow -> Group -> Group -> SyntaxM [UPatAnnArrow VoidS VoidS]
singleArgument arr name typ = do
  name' <- pat name
  typ' <- expr typ
  return $ [UPatAnnArrow (UPatAnn name' (Just typ')) arr]

explicitArgument :: Group -> SyntaxM [UPatAnnArrow VoidS VoidS]
explicitArgument g = case g of
  (Binary Colon name typ) -> singleArgument PlainArrow name typ
  _ -> do
    x <- pat g
    return $ [UPatAnnArrow (UPatAnn x Nothing) PlainArrow]

identifier :: String -> Group -> SyntaxM SourceName
identifier ctx = dropSrc identifier' where
  identifier' (CIdentifier name) = return name
  identifier' _ = throw SyntaxErr $ "Expected " ++ ctx ++ " to be an identifier"

optEffects :: Group -> SyntaxM (UEffectRow VoidS, UExpr VoidS)
optEffects g = case g of
  (Binary Juxtapose (Bracketed Curly effs) ty) ->
    (,) <$> effects effs <*> expr ty
  _ -> (UPure,) <$> expr g

effects :: Group -> SyntaxM (UEffectRow VoidS)
effects g = do
  rhs' <- mapM (identifier "effect row remainder variable") rhs
  lhs' <- mapM effect $ nary Comma lhs
  return $ UEffectRow (S.fromList lhs') $ fmap fromString rhs'
  where
    (lhs, rhs) = case g of
      (Binary Pipe l r) -> (l, Just r)
      l -> (l, Nothing)

effect :: Group -> SyntaxM (UEffect VoidS)
effect (WithSrc _ (CParens (ExprBlock g))) = effect g
effect (Binary Juxtapose (Identifier "Read") (Identifier h)) =
  return $ URWSEffect Reader $ fromString h
effect (Binary Juxtapose (Identifier "Accum") (Identifier h)) =
  return $ URWSEffect Writer $ fromString h
effect (Binary Juxtapose (Identifier "State") (Identifier h)) =
  return $ URWSEffect State $ fromString h
effect (Identifier "Except") = return UExceptionEffect
effect (Identifier "IO") = return UIOEffect
effect (Identifier effName) = return $ UUserEffect (fromString effName)
effect _ = throw SyntaxErr "Unexpected effect form; expected one of `Read h`, `Accum h`, `State h`, `Except`, `IO`, or the name of a user-defined effect."

method :: (SourceName, CSBlock) -> SyntaxM (UMethodDef VoidS)
method (name, body) = UMethodDef (fromString name) <$> block body

block :: CSBlock -> SyntaxM (UExpr VoidS)
block (CSBlock []) = throw SyntaxErr "Block must end in expression"
block (CSBlock [ExprDecl g]) = expr g
block (CSBlock ((WithSrc pos (CBind binder rhs)):ds)) = do
  binder' <- patOptAnn binder
  rhs' <- block rhs
  body <- block $ CSBlock ds
  return $ WithSrcE pos $ UApp rhs' $ ns $ ULam $ ULamExpr PlainArrow binder' body
block (CSBlock (d@(WithSrc pos _):ds)) = do
  d' <- decl PlainLet d
  e' <- block $ CSBlock ds
  return $ WithSrcE pos $ UDecl $ UDeclExpr d' e'

-- === Concrete to abstract syntax of expressions ===

expr :: Group -> SyntaxM (UExpr VoidS)
expr = propagateSrcE expr' where
  expr' CEmpty              = return   UHole
  -- Binders (e.g., in pi types) should not hit this case
  expr' (CIdentifier name)  = return $ fromString name
  expr' (CPrim prim xs)     = UPrim prim <$> mapM expr xs
  expr' (CNat word)         = return $ UNatLit word
  expr' (CInt int)          = return $ UIntLit int
  expr' (CString str)       = return $ UApp (fromString "to_list")
    $ ns $ UTabCon $ map (ns . charExpr) str
  expr' (CChar char)        = return $ charExpr char
  expr' (CFloat num)        = return $ UFloatLit num
  expr' CHole               = return   UHole
  expr' (CLabel prefix str) = return $ labelExpr prefix str
  expr' (CParens (ExprBlock (WithSrc _ CEmpty))) = return unitExpr
  expr' (CParens blk)       = dropSrcE <$> block blk
  -- Table constructors here.  Other uses of square brackets
  -- should be detected upstream, before calling expr.
  expr' (CBracket Square g) = UTabCon <$> (mapM expr $ nary Comma g)
  expr' (CBracket Curly  g) = labeledExprs g
  expr' (CBin (WithSrc opSrc op) lhs rhs) =
    case op of
      Juxtapose     -> apply mkApp
      Dollar        -> apply mkApp
      IndexingDot   -> apply mkTabApp
      FieldAccessDot -> do
        lhs' <- expr lhs
        WithSrc src rhs' <- return rhs
        addSrcContext src $ case rhs' of
          CIdentifier name -> return $ UFieldAccess lhs' (WithSrc src name)
          _ -> throw SyntaxErr "Field must be a name"
      DoubleColon   -> UTypeAnn <$> (expr lhs) <*> expr rhs
      (EvalBinOp s) -> evalOp s
      Ampersand     -> evalOp "(&)"
      DepAmpersand  -> do
        lhs' <- tyOptPat lhs
        UDepPairTy . (UDepPairType lhs') <$> expr rhs
      Comma         -> evalOp "(,)"
      DepComma      -> UDepPair <$> (expr lhs) <*> expr rhs
      Pipe          -> evalOp "(|)"
      CSEqual       -> throw SyntaxErr "Equal sign must be used as a separator for labels or binders, not a standalone operator"
      Question      -> throw SyntaxErr "Question mark separates labeled row elements, is not a standalone operator"
      Colon         -> throw SyntaxErr "Colon separates binders from their type annotations, is not a standalone operator.\nIf you are trying to write a dependent type, use parens: (i:Fin 4) => (..i)"
      FatArrow      -> do
        lhs' <- tyOptPat lhs
        UTabPi . (UTabPiExpr lhs') <$> expr rhs
      Arrow arr     -> do
        lhs' <- tyOptPat lhs
        (effs, ty) <- optEffects $ effectsToTop rhs
        return $ UPi $ UPiExpr arr lhs' effs ty
    where
      evalOp s = do
        app1 <- mkApp (WithSrcE opSrc (fromString s)) <$> expr lhs
        UApp app1 <$> expr rhs
      apply kind = do
        lhs' <- expr lhs
        dropSrcE . (kind lhs') <$> expr rhs
  expr' (CPrefix name g) =
    case name of
      ".." -> range "RangeTo" <$> expr g
      "..<" -> range "RangeToExc" <$> expr g
      "+" -> dropSrcE <$> expr g <&> \case
        UNatLit   i -> UIntLit   (fromIntegral i)
        UIntLit   i -> UIntLit   i
        UFloatLit i -> UFloatLit i
        e -> e
      "-" -> dropSrcE <$> expr g <&> \case
        UNatLit   i -> UIntLit   (-(fromIntegral i))
        UIntLit   i -> UIntLit   (-i)
        UFloatLit i -> UFloatLit (-i)
        -- TODO propagate source info form `expr g` to the nested
        -- expression `e`, instead of writing `ns e`.
        e -> dropSrcE $ mkApp (ns "neg") $ ns e
      _ -> throw SyntaxErr $ "Prefix (" ++ name ++ ") not legal as a bare expression"
    where
      range :: SourceName -> UExpr VoidS -> UExpr' VoidS
      range rangeName lim =
        UApp (mkApp (ns $ fromString rangeName) (ns UHole)) lim
  expr' (CPostfix name g) =
    case name of
      ".." -> range "RangeFrom" <$> expr g
      "<.." -> range "RangeFromExc" <$> expr g
      _ -> throw SyntaxErr $ "Postfix (" ++ name ++ ") not legal as a bare expression"
    where
      range :: SourceName -> UExpr VoidS -> UExpr' VoidS
      range rangeName lim =
        UApp (mkApp (ns $ fromString rangeName) (ns UHole)) lim
  expr' (CLambda args body) =
    dropSrcE <$> liftM2 buildLam (concat <$> mapM argument args) (block body)
  expr' (CFor kind indices body) = do
    let (dir, trailingUnit) = case kind of
          KFor  -> (Fwd, False)
          KFor_ -> (Fwd, True)
          KRof  -> (Rev, False)
          KRof_ -> (Rev, True)
    -- TODO: Can we fetch the source position from the error context, to feed into `buildFor`?
    e <- buildFor (0, 0) dir <$> mapM patOptAnn indices <*> block body
    if trailingUnit
      then return $ UDecl $ UDeclExpr (ULet PlainLet (UPatAnn (nsB UPatIgnore) Nothing) e) $ ns $ unitExpr
      else return $ dropSrcE e
  expr' (CCase scrut alts) = UCase <$> (expr scrut) <*> mapM alternative alts
    where alternative (match, body) = UAlt <$> casePat match <*> block body
  expr' (CIf p c a) = do
    p' <- expr p
    c' <- block c
    a' <- case a of
      Nothing -> return $ ns $ unitExpr
      (Just alternative) -> block alternative
    return $ UCase p'
      [ UAlt (nsB $ UPatCon "True"  Empty) c'
      , UAlt (nsB $ UPatCon "False" Empty) a']
  expr' (CDo blk) = ULam . (ULamExpr PlainArrow (UPatAnn (nsB $ UPatUnit UnitB) Nothing)) <$> block blk

charExpr :: Char -> (UExpr' VoidS)
charExpr c = UPrim (UPrimCon $ Lit $ Word8Lit $ fromIntegral $ fromEnum c) []

unitExpr :: UExpr' VoidS
unitExpr = UPrim (UPrimCon $ ProdCon []) []

labelExpr :: LabelPrefix -> String -> UExpr' VoidS
labelExpr PlainLabel str = ULabel str

labeledExprs :: Group -> SyntaxM (UExpr' VoidS)
-- We treat {} as an empty record, despite its ambiguity.
labeledExprs (WithSrc _ CEmpty) = return $ URecord []
-- Comma, ampersand, question mark, and pipe imply multi-element
-- lists, or a list where an extra separator was used for
-- disambiguation.  In any case, within curly braces they are unique:
-- comma means record value, colon means record type, question means
-- labeled row, and pipe means variant type.
labeledExprs g@(Binary Comma _ _) =
  URecord <$> (fieldRowList CSEqual $ nary Comma g)
labeledExprs g@(Binary Ampersand _ _) =
  URecordTy <$> (fieldRowList Colon $ nary Ampersand g)
labeledExprs g@(Binary Question _ _) =
  ULabeledRow <$> (fieldRowList Colon $ nary Question g)
-- If we have a singleton, we can try to disambiguate by the internal
-- separator.  Equal always means record.
labeledExprs g@(Binary CSEqual _ _) = URecord . (:[]) <$> oneField CSEqual g
-- URecordTy, ULabeledRow, and UVariantTy all use colon as the
-- internal separator, so a singleton is ambiguous.  Like the previous
-- parser, we disambiguate in favor of records.
labeledExprs g@(Binary Colon _ _) = URecordTy . (:[]) <$> oneField Colon g
-- A bare identifier also parsed in the old parser, as a record value
-- with a single field pun.
labeledExprs (WithSrc src (CIdentifier name)) = return $ URecord $ [fieldPun src name]
labeledExprs _ = throw SyntaxErr "Ambiguous curly-brace expression; needs a , & ? or | to disambiguate"

-- This is a near-duplicate to fieldRowPatList, but deduplicating
-- would require (i) a class to pick the constructors to use (e.g.,
-- UDynField vs UDynFieldPat) and (ii) switching between places where
-- the two structures require subexpressions or subpatterns or
-- identifiers.
fieldRowList :: Bin' -> [Group] -> SyntaxM (UFieldRowElems VoidS)
fieldRowList bind groups = mapM (oneField bind) groups

oneField :: Bin' -> Group -> SyntaxM (UFieldRowElem VoidS)
oneField bind = \case
  (Binary binder lhs rhs) | binder == bind -> do
    header <- case lhs of
      (Prefix "@" field) -> UDynField . fromString
        <$> identifier "variable holding dynamic record field" field
      field -> UStaticField <$> identifier "record field" field
    rhs' <- expr rhs
    return $ header rhs'
  (Prefix "..." field) -> UDynFields <$> expr field
  (WithSrc _ (CParens (ExprBlock g'))) -> oneField bind g'
  (WithSrc src (CIdentifier field')) -> return $ fieldPun src field'
  (WithSrc src _) -> addSrcContext src $ throw SyntaxErr
    $ "Bad field spec.  Expected an explicit field `label " ++ pprint bind ++ " expr`, "
    ++ "a remaining fields expression `... expr`, or a label-field pun `label`."

fieldPun :: SrcPosCtx -> String -> UFieldRowElem VoidS
fieldPun src field = UStaticField (fromString field) (WithSrcE src $ fromString field)

-- === Builders ===

buildPiType :: [UPatAnnArrow VoidS VoidS] -> UEffectRow VoidS -> UType VoidS -> UType VoidS
buildPiType [] UPure ty = ty
buildPiType [] _ _ = error "shouldn't be possible"
buildPiType (UPatAnnArrow p arr : bs) eff resTy = ns case bs of
  [] -> UPi $ UPiExpr arr p eff resTy
  _  -> UPi $ UPiExpr arr p UPure $ buildPiType bs eff resTy

-- TODO Does this generalize?  Swap list for Nest?
buildLam :: [UPatAnnArrow VoidS VoidS] -> UExpr VoidS -> UExpr VoidS
buildLam binders body@(WithSrcE pos _) = case binders of
  [] -> body
  -- TODO: join with source position of binders too
  (UPatAnnArrow b arr):bs -> WithSrcE (joinPos pos' pos) $ ULam lamb
     where UPatAnn (WithSrcB pos' _) _ = b
           lamb = ULamExpr arr b $ buildLam bs body

-- TODO Does this generalize?  Swap list for Nest?
buildFor :: SrcPos -> Direction -> [UPatAnn VoidS VoidS] -> UExpr VoidS -> UExpr VoidS
buildFor pos dir binders body = case binders of
  [] -> body
  b:bs -> WithSrcE (Just pos) $ UFor dir $ UForExpr b $ buildFor pos dir bs body

-- === Helpers ===

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

joinSrcE :: WithSrcE a1 n1 -> WithSrcE a2 n2 -> a3 n3 -> WithSrcE a3 n3
joinSrcE (WithSrcE p1 _) (WithSrcE p2 _) x = WithSrcE (joinPos p1 p2) x

mkApp :: UExpr (n::S) -> UExpr n -> UExpr n
mkApp f x = joinSrcE f x $ UApp f x

mkTabApp :: UExpr (n::S) -> UExpr n -> UExpr n
mkTabApp f x = joinSrcE f x $ UTabApp f x

-- If Group is a Binary tree, check the leftmost leaf.  If that leaf
-- is curly braces and its operator is Juxtapose, reassociate the tree
-- to bring it to the top.  This re-groups a term like {IO} n=>a as
-- {IO} (n=>a), instead of ({IO} n)=>a, which is how it parses
-- otherwise.
effectsToTop :: Group -> Group
effectsToTop g@(Binary Juxtapose (Bracketed Curly _) _) = g
effectsToTop g@(WithSrc pos (CBin op lhs rhs)) = case effectsToTop lhs of
  (WithSrc _ (CBin j@(WithSrc _ Juxtapose) br@(Bracketed Curly _) subRhs)) ->
    WithSrc pos (CBin j br (WithSrc (jointPos subRhs rhs) (CBin op subRhs rhs)))
  _ -> g
effectsToTop g = g
