-- Copyright 2022 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module AbstractSyntax (
  parseUModule, parseUModuleDeps,
  finishUModuleParse, preludeImportBlock,
  parseTopDeclRepl) where

import Control.Monad (forM, when, liftM2)
import Data.Functor
import Data.List.NonEmpty (NonEmpty (..))
import Data.Maybe
import Data.Set qualified as S
import Data.String (IsString, fromString)
import Data.Text (Text)
import Data.Text.Encoding qualified as T

import ConcreteSyntax hiding (sourceBlock)
import ConcreteSyntax qualified as C
import Err
import LabeledItems
import Name
import Types.Primitives hiding (Equal)
import Types.Source
import Util
import Debug.Trace qualified as Tr

import PPrint (pprint)

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
  let blocks = -- (Tr.trace
        -- (pprint $ map sbContents $ mustParseit s C.sourceBlocks)
        (mustParseit s C.sourceBlocks)
  let blocks' = -- (Tr.trace
        -- (pprint $ map sbContents $ map sourceBlock blocks)
        (map sourceBlock blocks)
  let blocks'' = if name == Prelude
        then blocks'
        else preludeImportBlock : blocks'
  let imports = flip foldMap blocks'' \b -> case sbContents b of
                  (Misc (ImportModule moduleName)) -> [moduleName]
                  _ -> []
  UModule name imports blocks'
{-# SCC parseUModule #-}

preludeImportBlock :: SourceBlock
preludeImportBlock = SourceBlockP 0 0 LogNothing ""
  $ Misc $ ImportModule Prelude

parseTopDeclRepl :: Text -> Maybe SourceBlock
parseTopDeclRepl s = case sbContents b of
  UnParseable True _ -> Nothing
  _ -> Just b
  where b = sourceBlock $ mustParseit s C.sourceBlock
{-# SCC parseTopDeclRepl #-}

-- === Converting concrete syntax to abstract syntax ===

type SyntaxM = Except

sourceBlock :: CSourceBlock -> SourceBlock
sourceBlock SourceBlockP {..} = SourceBlockP {sbContents = contents', ..} where
  contents' = runSyntaxM $ sourceBlock' sbContents

runSyntaxM :: SyntaxM SourceBlock' -> SourceBlock'
runSyntaxM (Success b) = b
-- TODO(axch): Reuse parsec error display machinery here
runSyntaxM (Failure e) = UnParseable False $ pprint e

sourceBlock' :: CSourceBlock' -> Except SourceBlock'
sourceBlock' (CTopDecl d) = EvalUDecl <$> topDecl d
sourceBlock' (CCommand typ b) = Command typ <$> block b
sourceBlock' (CDeclareForeign foreignName dexName ty) =
  DeclareForeign foreignName . UAnnBinder (fromString dexName) <$> expr ty
sourceBlock' (CMisc m) = return $ Misc m
sourceBlock' (CUnParseable eof s) = return $ UnParseable eof s

topDecl :: CTopDecl -> Except (UDecl VoidS VoidS)
topDecl (CDecl ann d) = decl ann d
topDecl (CData tyC classes constructors) = do
  tyC' <- tyCon tyC
  classes' <- case classes of
    Nothing -> return []
    (Just g) -> multiIfaceBinder g
  constructors' <- mapM dataCon constructors
  return $ UDataDefDecl
    (UDataDef tyC' (toNest classes') $
      map (\(name, cons) -> (name, UDataDefTrail cons)) constructors')
    (fromString $ fst tyC')
    (toNest $ map (fromString . fst) constructors')
topDecl (CInterface supers self methods) = do
  supers' <- mapM expr supers
  (name, params) <- tyCon self
  (methodNames, methodTys) <- unzip <$> forM methods \(nms, ty) -> do
    (nm:nms') <- mapM identifier $ nary Juxtapose nms
    ty' <- expr ty
    return (fromString nm, UMethodType (Left nms') ty')
  let methodNames' = toNest methodNames
  return $ UInterface params supers' methodTys
    (fromString name) methodNames'

-- This corresponds to tyConDef in the original parser.
-- tyCon differs from dataCon in how they treat a binding without an
-- annotation.  tyCon interprets it as a name that is implicitly of
-- type TypeKind, and dataCon interprets it as a type that isn't bound
-- to a name.
tyCon :: Group -> Except (UConDef VoidS VoidS)
tyCon = generalCon $ binOptR Colon

-- This corresponds to dataConDef in the original parser.
dataCon :: Group -> Except (UConDef VoidS VoidS)
dataCon = generalCon $ binOptL Colon

-- generalCon is the common part of tyCon and dataCon.
generalCon :: (Group -> (Maybe Group, Maybe Group))
           -> Group
           -> Except (UConDef VoidS VoidS)
generalCon binOpt g = case nary Juxtapose g of
  (name:args) -> do
    -- TODO(axch): Enforce that it's upper case or a symbol name here?
    -- In the old parser, tyConDef allows a symbol but dataConDef does
    -- not.
    name' <- identifier name
    args' <- mapM (optAnnotatedBinder . binOpt) args
    return $ (fromString name', toNest args')
  [] -> fail "Shouldn't happen: empty type constructor"

-- The arguments are the left- and right-hand sides of a binder
-- annotation.  Each is, in different contexts, optional.  If the
-- binder is missing, assume UIgnore; if the anntation is missing,
-- assume TypeKind.
optAnnotatedBinder :: (Maybe Group, Maybe Group)
                   -> Except (UAnnBinder AtomNameC VoidS VoidS)
optAnnotatedBinder (lhs, rhs) = do
  lhs' <- mapM identifier lhs
  rhs' <- mapM expr rhs
  return $ UAnnBinder (maybe UIgnore fromString lhs')
    $ fromMaybe tyKind rhs'
  where tyKind = ns $ UPrimExpr $ TCExpr TypeKind
  
-- TODO(axch): I am doing something very similar to this in
-- the square brackets case of `argument`.  De-dup?
multiIfaceBinder :: Group -> Except [UAnnBinder AtomNameC VoidS VoidS]
multiIfaceBinder g = do
  tys <- mapM expr $ nary Comma g
  return $ map (UAnnBinder UIgnore) tys

decl :: LetAnn -> CDecl -> Except (UDecl VoidS VoidS)
decl ann (CLet binder body) = ULet ann <$> patOptAnn binder <*> block body
decl ann (CDef name header body) = do
  (params, effs, returnTy) <- parseHeader
  params' <- concat <$> (mapM argument $ nary Juxtapose params)
  when (null params' && effs /= Pure) $ fail "Nullary def can't have effects"
  let funTy = buildPiType params' effs returnTy
  let lamBinders = params' <&> \(UPatAnnArrow (UPatAnn p _) arr) -> (UPatAnnArrow (UPatAnn p Nothing) arr)
  body' <- block body
  -- TODO(axch) Capture source information about the name
  -- in the CDef ADT
  return $ ULet ann (UPatAnn (fromString name) (Just funTy)) $ buildLam lamBinders body'
  where
    parseHeader = case header of
      (Binary Colon args typeAnn) -> do
        (effs, ty) <- optEffects typeAnn
        return (args, effs, ty)
      _ -> fail "def requires a :-delimited type annotation"
decl _ (CInstance header methods instName) = do
  supers' <- concat <$> mapM argument supers
  clName' <- identifier clName -- TODO(axch) Enforce capitalization?
  args' <- mapM expr args
  methods' <- mapM method methods
  let instName' = case instName of
        Nothing  -> NothingB
        (Just n) -> JustB $ fromString n
  return $ UInstance (fromString clName') (toNest supers') args' methods' instName'
  where
    (supers, (clName:args)) = span isBracketed $ nary Juxtapose header
    isBracketed (Bracketed _ _) = True
    isBracketed _ = False
decl ann (CExpr g) = ULet ann (UPatAnn (nsB UPatIgnore) Nothing) <$> expr g

patOptAnn :: Group -> Except (UPatAnn VoidS VoidS)
patOptAnn (Binary Colon lhs typeAnn) = UPatAnn <$> pat lhs <*> (Just <$> expr typeAnn)
patOptAnn g = flip UPatAnn Nothing <$> pat g

tyOptPat :: Group -> Except (UPatAnn VoidS VoidS)
tyOptPat  (Binary Colon lhs typeAnn) = UPatAnn <$> pat lhs <*> (Just <$> expr typeAnn)
tyOptPat g = UPatAnn (nsB $ UPatBinder UIgnore) . Just <$> expr g

pat :: Group -> Except (UPat VoidS VoidS)
pat = propagateSrcB pat' where
  pat' (CBin (WithSrc _ Comma) lhs rhs) = do
    lhs' <- pat lhs
    rhs' <- pat rhs
    return $ UPatPair $ PairB lhs' rhs'
  pat' (CBracket Curly g) = case g of
    (WithSrc _ CEmpty) -> return $ UPatRecord UEmptyRowPat
    _ -> UPatRecord <$> (fieldRowPatList Equal $ nary Comma g)
  pat' (CBracket Square g) = UPatTable . toNest <$> (mapM pat $ nary Comma g)
  pat' (CBracket CurlyPipe g) = variant (nary Pipe g) >>= \case
    Left (labels, label, g') -> UPatVariant labels label <$> pat g'
    Right (labels, g') -> UPatVariantLift labels <$> pat g'
  -- TODO(axch): Propagate the source info of the parens or the nested
  -- group?
  pat' (CParens (ExprBlock g)) = dropSrcB <$> pat g
  pat' CEmpty = return $ UPatUnit UnitB
  pat' CHole = return $ UPatBinder UIgnore
  pat' (CIdentifier name) = return $ UPatBinder $ fromString name
  pat' (CBin (WithSrc _ Juxtapose) lhs rhs) = do
    -- TODO(axch) Enforce that constructors are capitalized?
    lhs' <- identifier lhs
    rhs' <- toNest <$> (mapM pat $ nary Juxtapose rhs)
    return $ UPatCon (fromString lhs') rhs'
  -- TODO(axch): Source info, and explain what patterns are legal
  pat' _ = fail "Illegal pattern"

-- TODO(axch) Implement the leading separator disambiguation
-- mechanism, either custom or through empty groups on both sides.
-- Unless it's not needed for patterns?
fieldRowPatList :: Bin' -> [Group] -> Except (UFieldRowPat VoidS VoidS)
fieldRowPatList bind groups = go groups UEmptyRowPat where
  go [] rest = return rest
  go (g:gs) rest = case g of
    (Binary binder lhs rhs) | binder == bind -> do
      header <- case lhs of
        (Unary "@..." field) -> UDynFieldsPat . fromString <$> identifier field
        (Unary "@"    field) -> UDynFieldPat . fromString <$> identifier field
        field -> UStaticFieldPat <$> identifier field
      rhs' <- pat rhs  -- TODO(axch) Forbid pair patterns here?
      header rhs' <$> go gs rest
    (Unary "..." field) -> case gs of
      [] -> case field of
        (WithSrc _ CEmpty) -> return $ URemFieldsPat UIgnore
        (WithSrc _ CHole) -> return $ URemFieldsPat UIgnore
        name -> URemFieldsPat . fromString <$> identifier name
      -- TODO(axch) Use source information
      _ -> fail "ellipsis-pattern must be last"
    field@(WithSrc src _) -> do
      field' <- identifier field
      UStaticFieldPat (fromString field') (WithSrcB src $ fromString field') <$> go gs rest

-- TODO(axch): Why do we even have a separate single argument case?  Why
-- not just allow name / type annotations in the list versions as well?
argument :: Group -> Except [UPatAnnArrow VoidS VoidS]
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
argument (WithSrc _ (CParens (ExprBlock g))) = case g of
  (Binary Colon name typ) -> singleArgument PlainArrow name typ
  _ -> do
    x <- pat g
    return $ [UPatAnnArrow (UPatAnn x Nothing) PlainArrow]
argument g = do
  x <- pat g
  return $ [UPatAnnArrow (UPatAnn x Nothing) PlainArrow]

singleArgument :: Arrow -> Group -> Group -> Except [UPatAnnArrow VoidS VoidS]
singleArgument arr name typ = do
  name' <- pat name
  typ' <- expr typ
  return $ [UPatAnnArrow (UPatAnn name' (Just typ')) arr]

identifier :: Group -> Except SourceName
identifier (Identifier name) = return name
-- TODO(axch): Use error information
identifier _ = fail "Expected an identifier"

optEffects :: Group -> Except (UEffectRow VoidS, UExpr VoidS)
optEffects g = case g of
  (Binary Juxtapose (Bracketed Curly effs) ty) ->
    (,) <$> effects effs <*> expr ty
  _ -> (Pure,) <$> expr g

effects :: Group -> Except (UEffectRow VoidS)
effects g = do
  rhs' <- mapM identifier rhs
  lhs' <- mapM effect $ nary Comma lhs
  return $ EffectRow (S.fromList lhs') $ fmap fromString rhs'
  where
    (lhs, rhs) = case g of
      (Binary Pipe l r) -> (l, Just r)
      l -> (l, Nothing)

effect :: Group -> Except (UEffect VoidS)
effect (Binary Juxtapose (Identifier "Read") (Identifier h)) =
  return $ RWSEffect Reader $ (Just $ fromString h)
effect (Binary Juxtapose (Identifier "Accum") (Identifier h)) =
  return $ RWSEffect Writer $ (Just $ fromString h)
effect (Binary Juxtapose (Identifier "State") (Identifier h)) =
  return $ RWSEffect State $ (Just $ fromString h)
effect (Identifier "Except") = return ExceptionEffect
effect (Identifier "IO") = return IOEffect
-- TODO(axch): Better error message, and use available source location
-- information
effect _ = fail "Unexpected effect form"

method :: (SourceName, CBlock) -> Except (UMethodDef VoidS)
method (name, body) = UMethodDef (fromString name) <$> block body

block :: CBlock -> Except (UExpr VoidS)
block (CBlock []) = fail "Block must end in expression"
block (CBlock [CExpr g]) = expr g
block (CBlock (d:ds)) = do
  d' <- decl PlainLet d
  e' <- block $ CBlock ds
  -- TODO(axch) Propagate source location of decls
  return $ WithSrcE Nothing $ UDecl $ UDeclExpr d' e'

-- === Concrete to abstract syntax of expressions ===

expr :: Group -> Except (UExpr VoidS)
expr = propagateSrcE expr' where
  expr' CEmpty              = fail "Should not see an empty group as an expression"
  -- TODO(axch): Make sure binders (e.g., in pi types) do not hit this
  -- case
  expr' (CIdentifier name)  = return $ fromString name
  expr' (CPrim prim)        = UPrimExpr <$> mapM expr prim
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
  expr' (CBracket CurlyPipe g) = variant (nary Pipe g) >>= \case
    Left (labels, label, g') -> UVariant labels label <$> expr g'
    Right (labels, g') -> UVariantLift labels <$> expr g'
  expr' (CBin (WithSrc opSrc op) lhs rhs) =
    case op of
      Juxtapose     -> apply mkApp
      Dollar        -> apply mkApp
      IndexingDot   -> apply mkTabApp
      DoubleColon   -> UTypeAnn <$> (expr lhs) <*> expr rhs
      (EvalBinOp s) -> evalOp s
      Ampersand     -> evalOp "(&)"
      Comma         -> evalOp "(,)"
      Pipe          -> evalOp "(=)"
      Equal         -> fail "Equal sign must be used as a separator for labels or binders, not a standalone operator"
      Question      -> fail "Question mark separates labeled row elements, is not a standalone operator"
      Colon         -> fail "Colon separates binders from their type annotations, is not a standalone operator"
      FatArrow      -> do
        lhs' <- tyOptPat lhs
        UTabPi . (UTabPiExpr lhs') <$> expr rhs
      Arrow arr     -> do
        lhs' <- tyOptPat lhs
        (effs, ty) <- optEffects rhs
        return $ UPi $ UPiExpr arr lhs' effs ty
    where
      evalOp s = do
        app1 <- mkApp (WithSrcE opSrc (fromString s)) <$> expr lhs
        UApp app1 <$> expr rhs
      apply kind = do
        lhs' <- expr lhs
        dropSrcE . (kind lhs') <$> expr rhs
  expr' (CUn name g) =
    case name of
      ".." -> range "RangeTo" <$> expr g
      "..<" -> range "RangeToExc" <$> expr g
      -- TODO(axch): Propagate whether the operator was prefix or postfix
      -- through the concrete syntax
      -- ".." -> range "RangeFrom" <$> expr g
      "<.." -> range "RangeFromExc" <$> expr g
      "+" -> dropSrcE <$> expr g <&> \case
        UNatLit   i -> UIntLit   (fromIntegral i)
        UIntLit   i -> UIntLit   i
        UFloatLit i -> UFloatLit i
        e -> e
      "-" -> dropSrcE <$> expr g <&> \case
        UNatLit   i -> UIntLit   (-(fromIntegral i))
        UIntLit   i -> UIntLit   (-i)
        UFloatLit i -> UFloatLit (-i)
        e -> dropSrcE $ mkApp (ns "neg") $ ns e -- TODO(axch) propagate source info
      _ -> fail $ "Do not expect unary (" ++ name ++ ") as a bare expression"
    where
      range :: SourceName -> UExpr VoidS -> UExpr' VoidS
      range rangeName lim =
        UApp (mkApp (ns $ fromString rangeName) (ns UHole)) lim
  expr' (CLambda args body) = 
    dropSrcE <$> liftM2 buildLam (concat <$> mapM argument args) (block body)
  expr' (CFor KView indices body) =
    dropSrcE <$> (buildTabLam <$> mapM patOptAnn indices <*> block body)
  expr' (CFor kind indices body) = do
    let (dir, trailingUnit) = case kind of
          KFor  -> (Fwd, False)
          KFor_ -> (Fwd, True)
          KRof  -> (Rev, False)
          KRof_ -> (Rev, True)
          KView -> error "Impossible"
    -- TODO(axch): Get source position from the context sensibly
    e <- buildFor (0, 0) dir <$> mapM patOptAnn indices <*> block body
    if trailingUnit
      then return $ UDecl $ UDeclExpr (ULet PlainLet (UPatAnn (nsB UPatIgnore) Nothing) e) $ ns $ unitExpr
      else return $ dropSrcE e
  expr' (CCase scrut alts) = UCase <$> (expr scrut) <*> mapM alternative alts
    where alternative (match, body) = UAlt <$> pat match <*> block body
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
charExpr c = UPrimExpr $ ConExpr $ Lit $ Word8Lit $ fromIntegral $ fromEnum c

unitExpr :: UExpr' VoidS
unitExpr = UPrimExpr $ ConExpr $ ProdCon []

labelExpr :: LabelPrefix -> String -> UExpr' VoidS
labelExpr PlainLabel str = ULabel str
labelExpr RecordIsoLabel field = 
  UApp (ns "MkIso") $
    ns $ URecord
      [ UStaticField "fwd" (lam
          (uPatRecordLit [(field, "x")] (Just "r"))
        $ (ns "(,)") `mkApp` (ns "x") `mkApp` (ns "r"))
      , UStaticField "bwd" (lam
        (nsB $ UPatPair $ toPairB "x" "r")
        $ ns $ URecord [UStaticField field "x", UDynFields "r"])
      ]
labelExpr VariantIsoLabel field =
  UApp "MkIso" $
    ns $ URecord
      [ UStaticField "fwd" (lam "v" $ ns $ UCase "v"
          [ alt (nsB $ UPatVariant NoLabeledItems field "x")
              $ "Left" `mkApp` "x"
          , alt (nsB $ UPatVariantLift (labeledSingleton field ()) "r")
              $ "Right" `mkApp` "r"
          ])
      , UStaticField "bwd" (lam "v" $ ns $ UCase "v"
          [ alt (nsB $ UPatCon "Left" (toNest ["x"]))
              $ ns $ UVariant NoLabeledItems field $ "x"
          , alt (nsB $ UPatCon "Right" (toNest ["r"]))
              $ ns $ UVariantLift (labeledSingleton field ()) $ "r"
          ])
      ]
labelExpr RecordZipIsoLabel field =
  UApp "MkIso" $
    ns $ URecord
      [ UStaticField "fwd" (lam
        (nsB $ UPatPair $ PairB
          (uPatRecordLit [] (Just "l"))
          (uPatRecordLit [(field, "x")] (Just "r")))
        $ "(,)"
          `mkApp` (ns $ URecord [UStaticField field "x", UDynFields "l"])
          `mkApp` (ns $ URecord [UDynFields "r"]))
      , UStaticField "bwd" (lam
        (nsB $ UPatPair $ PairB
          (uPatRecordLit [(field, "x")] (Just "l"))
          (uPatRecordLit [] (Just "r")))
        $ "(,)"
          `mkApp` (ns $ URecord [UDynFields "l"])
          `mkApp` (ns $ URecord [UStaticField field "x", UDynFields"r"]))
      ]
labelExpr VariantZipIsoLabel field =
  UApp "MkIso" $
    ns $ URecord
      [ UStaticField "fwd" (lam "v" $ ns $ UCase "v"
          [ alt (nsB $ UPatCon "Left" (toNest ["l"]))
              $ "Left" `mkApp` (ns $
                  UVariantLift (labeledSingleton field ()) $ "l")
          , alt (nsB $ UPatCon "Right" (toNest ["w"]))
              $ ns $ UCase "w"
              [ alt (nsB $ UPatVariant NoLabeledItems field "x")
                  $ "Left" `mkApp` (ns $
                      UVariant NoLabeledItems field $ "x")
              , alt (nsB $ UPatVariantLift (labeledSingleton field ()) "r")
                  $ "Right" `mkApp` "r"
              ]
          ])
      , UStaticField "bwd" (lam "v" $ ns $ UCase "v"
          [ alt (nsB $ UPatCon "Left" (toNest ["w"]))
              $ ns $ UCase "w"
              [ alt (nsB $ UPatVariant NoLabeledItems field "x")
                  $ "Right" `mkApp` (ns $
                      UVariant NoLabeledItems field $ "x")
              , alt (nsB $ UPatVariantLift (labeledSingleton field ())
                                           "r")
                  $ "Left" `mkApp` "r"
              ]
          , alt (nsB $ UPatCon "Right" (toNest ["l"]))
              $ "Right" `mkApp` (ns $
                  UVariantLift (labeledSingleton field ()) "l")
          ])
      ]

uPatRecordLit :: [(String, UPat VoidS VoidS)] -> Maybe (UPat VoidS VoidS) -> UPat VoidS VoidS
uPatRecordLit labelsPats ext = nsB $ UPatRecord $ foldr addLabel extPat labelsPats
  where
    extPat = case ext of
      Nothing                          -> UEmptyRowPat
      Just (WithSrcB _ (UPatBinder b)) -> URemFieldsPat b
      _                                -> error "unexpected ext pattern"
    addLabel (l, p) rest = UStaticFieldPat l p rest

-- Explicitly specify types for `lam` and `alt` to prevent
-- ambiguous type variable errors referring to the inner scopes
-- defined thereby.
lam :: UPat VoidS VoidS -> UExpr VoidS -> WithSrcE UExpr' VoidS
lam p b = ns $ ULam $ ULamExpr PlainArrow (UPatAnn p Nothing) b

alt :: UPat VoidS VoidS -> UExpr VoidS -> UAlt VoidS
alt = UAlt

labeledExprs :: Group -> Except (UExpr' VoidS)
-- We treat {} as an empty record, despite its ambiguity.
labeledExprs (WithSrc _ CEmpty) = return $ URecord []
labeledExprs g@(Binary Comma _ _) =
  URecord <$> (fieldRowList Equal $ nary Comma g)
labeledExprs g@(Binary Ampersand _ _) =
  URecordTy <$> (fieldRowList Colon $ nary Ampersand g)
labeledExprs g@(Binary Question _ _) =
  ULabeledRow <$> (fieldRowList Colon $ nary Question g)
labeledExprs g@(Binary Pipe _ _) =
  UVariantTy <$> ((fieldRowList Colon $ nary Pipe g) >>= fix) where
    fix :: UFieldRowElems VoidS -> Except (ExtLabeledItems (UExpr VoidS) (UExpr VoidS))
    fix [] = return $ NoExt NoLabeledItems
    fix (UStaticField name e:rest) = prefixExtLabeledItems (labeledSingleton name e) <$> fix rest
    -- TODO(axch) Use the source information
    fix (UDynField _ _:_) = fail "Variant types do not allow computed fields"
    fix (UDynFields e:rest) = do
      rest' <- fix rest
      case rest' of
        NoExt items -> return $ Ext items $ Just e
        _ -> fail "Variant types for not allow two default fields ..."
labeledExprs _ = fail "Ambiguous curly-brace expression; needs a , & ? or | to disambiguate"

-- TODO(axch) Deduplicate vs fieldRowPatList?
fieldRowList :: Bin' -> [Group] -> Except (UFieldRowElems VoidS)
fieldRowList bind groups = go groups [] where
  go [] rest = return rest
  go (g:gs) rest = case g of
    (Binary binder lhs rhs) | binder == bind -> do
      header <- case lhs of
        (Unary "@" field) -> UDynField . fromString <$> identifier field
        field -> UStaticField <$> identifier field
      rhs' <- expr rhs
      rest' <- go gs rest
      return $ header rhs':rest'
    (Unary "..." field) -> do
      dyn <- UDynFields <$> expr field
      rest' <- go gs rest
      return $ dyn:rest'
    field@(WithSrc src _) -> do
      field' <- identifier field
      rest' <- go gs rest
      return $ UStaticField (fromString field') (WithSrcE src $ fromString field'):rest'

variant :: [Group] -> Except (Either (LabeledItems (), Label, Group) (LabeledItems (), Group))
variant [] = fail "Illegal empty variant"
variant (g:gs) = do
  let (first, final) = unsnoc (g:|gs)
  first' <- foldr (<>) NoLabeledItems . map (flip labeledSingleton ()) <$> mapM identifier first
  case final of
    (Binary Equal lhs rhs) -> do
      lhs' <- identifier lhs
      return $ Left (first', lhs', rhs)
    (Unary "..." rhs) -> return $ Right (first', rhs)
    _ -> fail "Last field of variant must be a labeled field foo=bar or a remainder ...bar"

-- === Builders ===

buildPiType :: [UPatAnnArrow VoidS VoidS] -> UEffectRow VoidS -> UType VoidS -> UType VoidS
buildPiType [] Pure ty = ty
buildPiType [] _ _ = error "shouldn't be possible"
buildPiType (UPatAnnArrow p arr : bs) eff resTy = ns case bs of
  [] -> UPi $ UPiExpr arr p eff resTy
  _  -> UPi $ UPiExpr arr p Pure $ buildPiType bs eff resTy

-- TODO Does this generalize?  Swap list for Nest?
buildLam :: [UPatAnnArrow VoidS VoidS] -> UExpr VoidS -> UExpr VoidS
buildLam binders body@(WithSrcE pos _) = case binders of
  [] -> body
  -- TODO: join with source position of binders too
  (UPatAnnArrow b arr):bs -> WithSrcE (joinPos pos' pos) $ ULam lam
     where UPatAnn (WithSrcB pos' _) _ = b
           lam = ULamExpr arr b $ buildLam bs body

buildTabLam :: [UPatAnn VoidS VoidS] -> UExpr VoidS -> UExpr VoidS
buildTabLam binders body@(WithSrcE pos _) = case binders of
  [] -> body
  -- TODO: join with source position of binders too
  b:bs -> WithSrcE (joinPos pos' pos) $ UTabLam lam
   where UPatAnn (WithSrcB pos' _) _ = b
         lam = UTabLamExpr b $ buildTabLam bs body

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

propagateSrcE :: Functor f =>
                 (t -> f (e n)) -> WithSrc t -> f (WithSrcE e n)
propagateSrcE act (WithSrc src x) = WithSrcE src <$> act x

dropSrcE :: WithSrcE e n -> e n
dropSrcE (WithSrcE _ x) = x

propagateSrcB :: Functor f =>
                 (t -> f (binder n l)) -> WithSrc t -> f (WithSrcB binder n l)
propagateSrcB act (WithSrc src x) = WithSrcB src <$> act x

dropSrcB :: WithSrcB binder n l -> binder n l
dropSrcB (WithSrcB _ x) = x

toPairB :: forall a b. (IsString (a VoidS VoidS), IsString (b VoidS VoidS))
           => String -> String -> PairB a b VoidS VoidS
toPairB s1 s2 = PairB parse1 parse2 where
  parse1 :: a VoidS VoidS
  parse1 = fromString s1
  parse2 :: b VoidS VoidS
  parse2 = fromString s2

joinSrcE :: WithSrcE a1 n1 -> WithSrcE a2 n2 -> a3 n3 -> WithSrcE a3 n3
joinSrcE (WithSrcE p1 _) (WithSrcE p2 _) x = WithSrcE (joinPos p1 p2) x

mkApp :: UExpr (n::S) -> UExpr n -> UExpr n
mkApp f x = joinSrcE f x $ UApp f x

mkTabApp :: UExpr (n::S) -> UExpr n -> UExpr n
mkTabApp f x = joinSrcE f x $ UTabApp f x
