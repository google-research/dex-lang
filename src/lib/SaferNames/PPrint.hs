-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE IncoherentInstances #-}  -- due to `ConRef`
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module SaferNames.PPrint ( pprint, pprintList, asStr , atPrec) where

import GHC.Exts (Constraint)
import Data.Foldable (toList)
import qualified Data.List.NonEmpty as NE
import qualified Data.Map.Strict as M
import Data.Text.Prettyprint.Doc.Render.Text
import Data.Text.Prettyprint.Doc
import Data.Text (unpack)
import Data.String (fromString)
import System.IO.Unsafe
import System.Environment

import LabeledItems

import PPrint (PrettyPrec (..), PrecedenceLevel (..), atPrec, pprint,
               prettyFromPrettyPrec, DocPrec, fromInfix, pAppArg)

import SaferNames.Name
import SaferNames.Syntax

type PrettyPrecE e = (forall (n::S)       . PrettyPrec (e n  )) :: Constraint
type PrettyPrecB b = (forall (n::S) (l::S). PrettyPrec (b n l)) :: Constraint

pprintList :: Pretty a => [a] -> String
pprintList xs = asStr $ vsep $ punctuate "," (map p xs)

layout :: LayoutOptions
layout = if unbounded then LayoutOptions Unbounded else defaultLayoutOptions
  where unbounded = unsafePerformIO $ (Just "1"==) <$> lookupEnv "DEX_PPRINT_UNBOUNDED"

asStr :: Doc ann -> String
asStr doc = unpack $ renderStrict $ layoutPretty layout $ doc

p :: Pretty a => a -> Doc ann
p = pretty

pLowest :: PrettyPrec a => a -> Doc ann
pLowest a = prettyPrec a LowestPrec

pApp :: PrettyPrec a => a -> Doc ann
pApp a = prettyPrec a AppPrec

pArg :: PrettyPrec a => a -> Doc ann
pArg a = prettyPrec a ArgPrec

instance Pretty (Block n) where
  pretty (Block _ Empty expr) = group $ line <> pLowest expr
  pretty (Block _ decls expr) = hardline <> prettyLines decls' <> pLowest expr
    where decls' = fromNest decls

fromNest :: Nest b n l -> [b UnsafeS UnsafeS]
fromNest Empty = []
fromNest (Nest b rest) = unsafeCoerceB b : fromNest rest

prettyLines :: (Foldable f, Pretty a) => f a -> Doc ann
prettyLines xs = foldMap (\d -> p d <> hardline) $ toList xs

instance PrettyE ann => Pretty (BinderP c ann n l)
  where pretty (b:>ty) = p b <> ":" <> p ty

instance Pretty (Expr n) where pretty = prettyFromPrettyPrec
instance PrettyPrec (Expr n) where
  prettyPrec (App f x) =
    atPrec AppPrec $ pApp f <+> pArg x
  prettyPrec (Atom x ) = prettyPrec x
  prettyPrec (Op  op ) = prettyPrec op
  prettyPrec (Hof (For ann (Lam lamExpr))) =
    atPrec LowestPrec $ forStr ann <+> prettyLamHelper lamExpr (PrettyFor ann)
  prettyPrec (Hof hof) = prettyPrec hof
  prettyPrec (Case e alts _) = prettyPrecCase "case" e alts

prettyPrecCase :: PrettyE e => Doc ann -> Atom n -> [AltP e n] -> DocPrec ann
prettyPrecCase name e alts = atPrec LowestPrec $ name <+> p e <+> "of" <>
  nest 2 (hardline <> foldMap (\alt -> prettyAlt alt <> hardline) alts)

prettyAlt :: PrettyE e => AltP e n -> Doc ann
prettyAlt (Abs bs body) = hsep (map prettyBinderNoAnn  bs') <+> "->" <> nest 2 (p body)
  where bs' = fromNest bs

prettyBinderNoAnn :: Binder n l -> Doc ann
prettyBinderNoAnn (b:>_) = p $ show b

instance PrettyPrecE e => Pretty     (Abs Binder e n) where pretty = prettyFromPrettyPrec
instance PrettyPrecE e => PrettyPrec (Abs Binder e n) where
  prettyPrec (Abs binder body) = atPrec LowestPrec $ "\\" <> p binder <> "." <> pLowest body

instance PrettyPrecE e => Pretty (PrimCon (e n)) where pretty = prettyFromPrettyPrec
instance Pretty (PrimCon (Atom n)) where pretty = prettyFromPrettyPrec

instance Pretty (DeclBinding n) where
  pretty (DeclBinding ann ty expr) =
    "Decl" <> p ann <> indented (               "type: " <+> p ty
                                 <> hardline <> "value:" <+> p expr)

instance Pretty (Decl n l) where
  pretty decl = case decl of
    -- This is just to reduce clutter a bit. We can comment it out when needed.
    -- Let (v:>Pi _)   bound -> p v <+> "=" <+> p bound
    Let b (DeclBinding ann ty rhs) ->
      align $ p ann <+> p (b:>ty) <+> "=" <> (nest 2 $ group $ line <> pLowest rhs)

instance Pretty (LamExpr n) where pretty = prettyFromPrettyPrec
instance PrettyPrec (LamExpr n) where
  prettyPrec lamExpr = case lamExpr of
    LamExpr (LamBinder _ _ TabArrow _) _ ->
      atPrec LowestPrec $ "\\for"
      <+> prettyLamHelper lamExpr (PrettyLam TabArrow)
    LamExpr (LamBinder _ _ arr _) _ ->
      atPrec LowestPrec $ "\\"
      <> prettyLamHelper lamExpr (PrettyLam arr)

instance Pretty (Atom n) where pretty = prettyFromPrettyPrec
instance PrettyPrec (Atom n) where
  prettyPrec atom = case atom of
    Var v -> atPrec ArgPrec $ p v
    Lam lamExpr -> prettyPrec lamExpr
    Pi piType -> atPrec LowestPrec $ align $ p piType
    TC  e -> prettyPrec e
    Con e -> prettyPrec e
    Eff e -> atPrec ArgPrec $ p e
    DataCon name _ _ _ xs -> case xs of
      [] -> atPrec ArgPrec $ p name
      [l, r] | Just sym <- fromInfix (fromString name) -> atPrec ArgPrec $ align $ group $
        parens $ flatAlt " " "" <> pApp l <> line <> p sym <+> pApp r
      _ ->  atPrec LowestPrec $ pAppArg (p name) xs
    TypeCon (_, DataDef name _ _) params -> case params of
      [] -> atPrec ArgPrec $ p name
      [l, r] | Just sym <- fromInfix (fromString name) ->
        atPrec ArgPrec $ align $ group $
          parens $ flatAlt " " "" <> pApp l <> line <> p sym <+> pApp r
      _  -> atPrec LowestPrec $ pAppArg (p name) params
    LabeledRow items -> prettyExtLabeledItems items (line <> "?") ":"
    Record items -> prettyLabeledItems items (line' <> ",") " ="
    Variant _ label i value -> prettyVariant ls label value where
      ls = LabeledItems $ case i of
            0 -> M.empty
            _ -> M.singleton label $ NE.fromList $ fmap (const ()) [1..i]
    RecordTy items -> prettyExtLabeledItems items (line <> "&") ":"
    VariantTy items -> prettyExtLabeledItems items (line <> "|") ":"
    ACase e alts _ -> prettyPrecCase "acase" e alts
    DataConRef _ params args -> atPrec AppPrec $
      "DataConRef" <+> p params <+> p args
    BoxedRef ptr size (Abs b body) -> atPrec AppPrec $
      "Box" <+> p b <+> "<-" <+> p ptr <+> "[" <> p size <> "]" <+> hardline <> "in" <+> p body
    ProjectElt idxs v ->
      atPrec AppPrec $ "ProjectElt" <+> p idxs <+> p v

instance Pretty (DataConRefBinding n l) where pretty = prettyFromPrettyPrec
instance PrettyPrec (DataConRefBinding n l) where
  prettyPrec (DataConRefBinding b x) = atPrec AppPrec $ p b <+> "<-" <+> p x

prettyExtLabeledItems :: (PrettyPrec a, PrettyPrec b)
  => ExtLabeledItems a b -> Doc ann -> Doc ann -> DocPrec ann
prettyExtLabeledItems (Ext (LabeledItems row) rest) separator bindwith =
  atPrec ArgPrec $ align $ group $ innerDoc
  where
    elems = concatMap (\(k, vs) -> map (k,) (toList vs)) (M.toAscList row)
    fmtElem (label, v) = p label <> bindwith <+> pLowest v
    docs = map fmtElem elems
    final = case rest of
      Just v -> separator <> " ..." <> pArg v
      Nothing -> case length docs of
        0 -> separator
        _ -> mempty
    innerDoc = "{" <> flatAlt " " ""
      <> concatWith (surround (separator <> " ")) docs
      <> final <> "}"

prettyLabeledItems :: PrettyPrec a
  => LabeledItems a -> Doc ann -> Doc ann -> DocPrec ann
prettyLabeledItems items =
  prettyExtLabeledItems $ Ext items (Nothing :: Maybe ())

prettyVariant :: PrettyPrec a
  => LabeledItems () -> Label -> a -> DocPrec ann
prettyVariant labels label value = atPrec ArgPrec $
      "{|" <> left <+> p label <+> "=" <+> pLowest value <+> "|}"
      where left = foldl (<>) mempty $ fmap plabel $ reflectLabels labels
            plabel (l, _) = p l <> "|"

forStr :: ForAnn -> Doc ann
forStr (RegularFor Fwd) = "for"
forStr (RegularFor Rev) = "rof"
forStr ParallelFor      = "pfor"

instance Pretty (PiType n) where
  pretty (PiType (PiBinder b ty arr) eff body) = let
    prettyBinder = if binderName b `isFreeIn` PairE eff body
                     then parens $ p (b:>ty)
                     else p ty
    prettyBody = case body of
      Pi subpi -> pretty subpi
      _ -> pLowest body
    in prettyBinder <> (group $ line <> p arr <+> prettyBody)

data PrettyLamType = PrettyLam Arrow | PrettyFor ForAnn deriving (Eq)

prettyLamHelper :: LamExpr n -> PrettyLamType -> Doc ann
prettyLamHelper lamExpr lamType = let
  rec :: LamExpr n -> Bool -> (Doc ann, Block n)
  rec (LamExpr (LamBinder b ty _ _) body') first =
    let thisOne = (if first then "" else line) <> p (b:>ty)
    in case body' of
      Block _ Empty (Atom (Lam next@(LamExpr (LamBinder _ _ arr' _) _)))
        | lamType == PrettyLam arr' ->
            let (binders', block) = rec next False
            in (thisOne <> binders', unsafeCoerceE block)
      Block _ Empty (Hof (For ann (Lam next)))
        | lamType == PrettyFor ann ->
            let (binders', block) = rec next False
            in (thisOne <> binders', unsafeCoerceE block)
      _ -> (thisOne <> punctuation, unsafeCoerceE body')
        where punctuation = case lamType of
                PrettyFor _ -> "."
                PrettyLam PlainArrow -> "."
                PrettyLam arr -> " " <> p arr
  (binders, body) = rec lamExpr True
  in align (group $ nest 4 $ binders) <> (group $ nest 2 $ p body)

instance Pretty (EffectRow n) where
  pretty (EffectRow effs tailVar) =
    braces $ hsep (punctuate "," (map p (toList effs))) <> tailStr
    where
      tailStr = case tailVar of
        Nothing -> mempty
        Just v  -> "|" <> p v

instance Pretty (Effect n) where
  pretty eff = case eff of
    RWSEffect rws h -> p rws <+> p h
    ExceptionEffect -> "Except"
    IOEffect        -> "IO"

instance PrettyPrec (Name s n) where prettyPrec = atPrec ArgPrec . pretty

instance Pretty (AtomBinding n) where
  pretty binding = case binding of
    LetBound    b -> p b
    LamBound    b -> p b
    PiBound     b -> p b
    MiscBound   t -> p t
    SolverBound b -> p b

instance Pretty (LamBinding n) where
  pretty (LamBinding arr ty) =
    "Lambda binding. Type:" <+> p ty <+> "  Arrow" <+> p arr

instance Pretty (PiBinding n) where
  pretty (PiBinding arr ty) =
    "Pi binding. Type:" <+> p ty <+> "  Arrow" <+> p arr

instance Pretty (SolverBinding n) where
  pretty (InfVarBound  ty _) = "Inference variable of type:" <+> p ty
  pretty (SkolemBound  ty  ) = "Skolem variable of type:"    <+> p ty

instance Pretty (Binding s n) where
  pretty b = case b of
    AtomNameBinding   info -> "Atom name:" <+> pretty info
    DataDefBinding    dataDef -> pretty dataDef
    TyConBinding      dataDefName -> "Type constructor:" <+> pretty dataDefName
    DataConBinding    dataDefName idx ->
      "Data constructor:" <+> pretty dataDefName <+>
      "Constructor index:" <+> pretty idx
    ClassBinding      classDef -> pretty classDef
    SuperclassBinding className idx _ ->
      "Superclass" <+> pretty idx <+> "of" <+> pretty className
    MethodBinding     className idx _ ->
      "Method" <+> pretty idx <+> "of" <+> pretty className

instance Pretty (DataDef n) where
  pretty (DataDef dataDefSourceName _ _) =
    "Data def:" <+> pretty dataDefSourceName

instance Pretty (ClassDef n) where
  pretty (ClassDef classSourceName methodNames _) =
    "Class:" <+> pretty classSourceName <+> pretty methodNames

deriving instance (forall c n. Pretty (v c n)) => Pretty (MaterializedEnv v i o)
deriving instance (forall c n. Pretty (v c n)) => Pretty (RecEnv v o)

instance Pretty (Bindings n) where
  pretty s =
       "bindings: "
    <>   indented (pretty (getBindings s))
    <> "synth candidates:"
    <>   indented (pretty (getSynthCandidates s))
    <> "source map: "
    <>   indented (pretty (getSourceMap s))

instance Pretty SourceBlock where
  pretty block = pretty (sbText block)

instance Pretty (Module n) where pretty = prettyFromPrettyPrec
instance PrettyPrec (Module n) where
  prettyPrec (Module variant decls result) = atPrec ArgPrec $
    "Module" <+> parens (p (show variant)) <> indented body
    where
      body = "unevaluated decls:"
           <>   indented (prettyLines (fromNest decls))
           <> "evaluated bindings:"
           <>   indented (p result)

instance Pretty (UModule n) where
  pretty (UModule decl sm) =
    "UModule" <> hardline <>
    p decl    <> hardline <>
    p sm      <> hardline

instance Pretty SourceUModule where
  pretty (SourceUModule decl) = p decl

instance Pretty (UVar n) where pretty = prettyFromPrettyPrec
instance PrettyPrec (UVar n) where
  prettyPrec uvar = atPrec ArgPrec case uvar of
    UAtomVar    v -> p v
    UTyConVar   v -> p v
    UDataConVar v -> p v
    UClassVar   v -> p v
    UMethodVar  v -> p v

instance NameColor c => Pretty (UBinder c n l) where pretty = prettyFromPrettyPrec
instance NameColor c => PrettyPrec (UBinder c n l) where
  prettyPrec b = atPrec ArgPrec case b of
    UBindSource v -> p v
    UIgnore       -> "_"
    UBind v       -> p v

instance PrettyE e => Pretty (WithSrcE e n) where
  pretty (WithSrcE _ x) = p x

instance PrettyPrecE e => PrettyPrec (WithSrcE e n) where
  prettyPrec (WithSrcE _ x) = prettyPrec x

instance PrettyB b => Pretty (WithSrcB b n l) where
  pretty (WithSrcB _ x) = p x

instance PrettyPrecB b => PrettyPrec (WithSrcB b n l) where
  prettyPrec (WithSrcB _ x) = prettyPrec x

instance PrettyE e => Pretty (SourceNameOr e n) where
  pretty (SourceName   v) = p v
  pretty (InternalName x) = p x

instance Pretty (ULamExpr n) where pretty = prettyFromPrettyPrec
instance PrettyPrec (ULamExpr n) where
  prettyPrec (ULamExpr arr pat body) = atPrec LowestPrec $ align $
    "\\" <> p pat <> punctuation <+> nest 2 (pLowest body)
    where punctuation = case arr of
                          PlainArrow -> "."
                          _          -> " " <> p arr

instance Pretty (UPiExpr n) where pretty = prettyFromPrettyPrec
instance PrettyPrec (UPiExpr n) where
  prettyPrec (UPiExpr arr pat Pure ty) = atPrec LowestPrec $ align $
    p pat <+> pretty arr <+> pLowest ty
  prettyPrec (UPiExpr arr pat _ ty) = atPrec LowestPrec $ align $
    p pat <+> pretty arr <+> "{todo: pretty effects}" <+> pLowest ty

instance Pretty (UDeclExpr n) where pretty = prettyFromPrettyPrec
instance PrettyPrec (UDeclExpr n) where
  prettyPrec (UDeclExpr decl body) = atPrec LowestPrec $ align $
    p decl <> hardline <> pLowest body

instance Pretty (UExpr' n) where pretty = prettyFromPrettyPrec
instance PrettyPrec (UExpr' n) where
  prettyPrec expr = case expr of
    UVar v -> atPrec ArgPrec $ p v
    ULam lam -> prettyPrec lam
    UApp TabArrow f x -> atPrec AppPrec $ pArg f <> "." <> pArg x
    UApp _        f x -> atPrec AppPrec $ pAppArg (pApp f) [x]
    UFor dir (UForExpr binder body) ->
      atPrec LowestPrec $ kw <+> p binder <> "."
                             <+> nest 2 (pLowest body)
      where kw = case dir of Fwd -> "for"
                             Rev -> "rof"
    UPi piType -> prettyPrec piType
    UDecl declExpr -> prettyPrec declExpr
    UHole -> atPrec ArgPrec "_"
    UTypeAnn v ty -> atPrec LowestPrec $
      group $ pApp v <> line <> ":" <+> pApp ty
    UTabCon xs -> atPrec ArgPrec $ p xs
    UIndexRange low high -> atPrec LowestPrec $ low' <> ".." <> high'
      where
        low'  = case low of  InclusiveLim x -> pApp x
                             ExclusiveLim x -> pApp x <> "<"
                             Unlimited      -> ""
        high' = case high of InclusiveLim x -> pApp x
                             ExclusiveLim x -> "<" <> pApp x
                             Unlimited      -> ""
    UPrimExpr prim -> prettyPrec prim
    UCase e alts -> atPrec LowestPrec $ "case" <+> p e <>
      nest 2 (hardline <> prettyLines alts)
    URecord items -> prettyExtLabeledItems items (line' <> ",") " ="
    URecordTy items -> prettyExtLabeledItems items (line <> "&") ":"
    UVariant labels label value -> prettyVariant labels label value
    UVariantTy items -> prettyExtLabeledItems items (line <> "|") ":"
    UVariantLift labels value -> prettyVariantLift labels value
    UIntLit   v -> atPrec ArgPrec $ p v
    UFloatLit v -> atPrec ArgPrec $ p v

prettyVariantLift :: PrettyPrec a
  => LabeledItems () -> a -> DocPrec ann
prettyVariantLift labels value = atPrec ArgPrec $
      "{|" <> left <+> "..." <> pLowest value <+> "|}"
      where left = foldl (<>) mempty $ fmap plabel $ reflectLabels labels
            plabel (l, _) = p l <> "|"

instance Pretty (UAlt n) where
  pretty (UAlt pat body) = p pat <+> "->" <+> p body

instance Pretty (UDecl n l) where
  pretty (ULet ann b rhs) =
    align $ p ann <+> p b <+> "=" <> (nest 2 $ group $ line <> pLowest rhs)
  pretty (UDataDefDecl (UDataDef bParams dataCons) bTyCon bDataCons) =
    "data" <+> p bTyCon <+> p bParams
       <+> "where" <> nest 2
       (hardline <> prettyLines (zip (toList $ fromNest bDataCons) dataCons))
  pretty (UInterface params superclasses methodTys interfaceName methodNames) =
     "interface" <+> p params <+> p superclasses <+> p interfaceName
         <> hardline <> foldMap (<>hardline) methods
     where
       methods = [ hsep (case e of Left e' -> p <$> e'; Right e' -> p <$> e') <+>
                   p (UAnnBinder b (unsafeCoerceE ty))
                 | (b, UMethodType e ty) <- zip (toList $ fromNest methodNames) methodTys]
  pretty (UInstance className bs params methods (RightB UnitB)) =
    "instance" <+> prettyBinderNest bs <+> p className <+> spaced params <+>
       hardline <> prettyLines methods
  pretty (UInstance bs className params methods (LeftB v)) =
    "named-instance" <+> p v <+> ":" <+> p bs <+> p className <+> p params
        <> hardline <> prettyLines methods

prettyBinderNest :: PrettyB b => Nest b n l -> Doc ann
prettyBinderNest bs = spaced $ fromNest bs

instance Pretty (UDataDefTrail n) where
  pretty (UDataDefTrail bs) = p $ fromNest bs

instance Pretty (UPatAnnArrow n l) where
  pretty (UPatAnnArrow b arr) = p b <> ":" <> p arr

instance NameColor c => Pretty (UAnnBinder c n l) where
  pretty (UAnnBinder b ty) = p b <> ":" <> p ty

instance Pretty (UMethodDef n) where
  pretty (UMethodDef b rhs) = p b <+> "=" <+> p rhs

instance Pretty (UPat' n l) where pretty = prettyFromPrettyPrec
instance PrettyPrec (UPat' n l) where
  prettyPrec pat = case pat of
    UPatBinder x -> atPrec ArgPrec $ p x
    UPatPair (PairB x y) -> atPrec ArgPrec $ parens $ p x <> ", " <> p y
    UPatUnit UnitB -> atPrec ArgPrec $ "()"
    UPatCon con pats -> atPrec AppPrec $ parens $ p con <+> spaced (fromNest pats)
    UPatRecord labels _ ->
      prettyExtLabeledItems labels (line' <> ",") " ="
    UPatVariant labels label value -> prettyVariant labels label value
    UPatVariantLift labels value -> prettyVariantLift labels value
    UPatTable pats -> atPrec ArgPrec $ p pats

spaced :: (Foldable f, Pretty a) => f a -> Doc ann
spaced xs = hsep $ map p $ toList xs

instance Pretty (UPatAnn n l) where
  pretty (UPatAnn pat ann) = p pat <> annDoc where
    annDoc = case ann of
      Just ty -> ":" <> pApp ty
      Nothing -> mempty

instance Pretty (BindingsFrag n l) where
  pretty (BindingsFrag bindings effects) =
       "Partial bindings:" <> indented (p bindings)
    <> "Effects candidates:" <+> p effects

instance Pretty (EvaluatedModule n) where
  pretty (EvaluatedModule bindings synthCandidates sourceMap) =
       "decls:"
    <>   indented (p bindings)
    <> "Synthesis candidates:"
    <>   indented (p synthCandidates)
    <> "Source map:"
    <>   indented (p sourceMap)

instance Pretty (SynthCandidates n) where
  pretty scs =
       "lambda dicts:"   <+> p (lambdaDicts       scs) <> hardline
    <> "superclasses:"   <+> p (superclassGetters scs) <> hardline
    <> "instance dicts:" <+> p (instanceDicts     scs)

indented :: Doc ann -> Doc ann
indented doc = nest 2 (hardline <> doc) <> hardline
