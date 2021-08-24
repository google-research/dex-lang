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
import Env (nameTag)

import SaferNames.NameCore (unsafeCoerceE, unsafeCoerceB, getRawName)
import SaferNames.Name hiding (lookupEnv)
import SaferNames.Syntax

type PrettyPrecE e = (forall (n::S). PrettyPrec (e n)) :: Constraint

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

instance Pretty (Binder n l) where pretty (b:>_) = p b

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

instance Pretty (Decl n l) where
  pretty decl = case decl of
    -- This is just to reduce clutter a bit. We can comment it out when needed.
    -- Let (v:>Pi _)   bound -> p v <+> "=" <+> p bound
    Let ann b rhs -> align $ p ann <+> p b <+> "=" <> (nest 2 $ group $ line <> pLowest rhs)

instance Pretty (Atom n) where pretty = prettyFromPrettyPrec
instance PrettyPrec (Atom n) where
  prettyPrec atom = case atom of
    Var v -> atPrec ArgPrec $ p v
    Lam lamExpr@(LamExpr TabArrow _ _ _) ->
      atPrec LowestPrec $ "\\for"
      <+> prettyLamHelper lamExpr (PrettyLam TabArrow)
    Lam lamExpr@(LamExpr arr _ _ _) ->
      atPrec LowestPrec $ "\\"
      <> prettyLamHelper lamExpr (PrettyLam arr)
    Pi piType -> atPrec LowestPrec $ align $ prettyPiTypeHelper piType
    TC  e -> prettyPrec e
    Con e -> prettyPrec e
    Eff e -> atPrec ArgPrec $ p e
    DataCon name _ _ _ xs -> case xs of
      [] -> atPrec ArgPrec $ p name
      [l, r] | Just sym <- fromInfix (fromString name) -> atPrec ArgPrec $ align $ group $
        parens $ flatAlt " " "" <> pApp l <> line <> p sym <+> pApp r
      _ ->  atPrec LowestPrec $ pAppArg (p name) xs
    TypeCon (name, _) params -> case params of
      [] -> atPrec ArgPrec $ p name
      [l, r] | Just sym <- fromInfix (nameTag (getRawName name)) ->
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

prettyPiTypeHelper :: PiType n -> Doc ann
prettyPiTypeHelper (PiType arr binder _ body) = let
  prettyBinder = parens $ p binder
  prettyBody = case body of
    Pi subpi -> prettyPiTypeHelper subpi
    _ -> pLowest body
  in prettyBinder <> (group $ line <> p arr <+> prettyBody)

data PrettyLamType = PrettyLam Arrow | PrettyFor ForAnn deriving (Eq)

prettyLamHelper :: LamExpr n -> PrettyLamType -> Doc ann
prettyLamHelper lamExpr lamType = let
  rec :: LamExpr n -> Bool -> (Doc ann, Block n)
  rec (LamExpr _ binder _ body') first =
    let thisOne = (if first then "" else line) <> p binder
    in case body' of
      Block _ Empty (Atom (Lam next@(LamExpr arr' _ _ _)))
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

instance Pretty (AtomBinderInfo n) where
  pretty = undefined

instance Pretty (Binding s n) where
  pretty b = case b of
    AtomNameBinding   ty info ->
          "Atom name type:" <+> pretty ty
      <+> "binder info:" <+> pretty info
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
    "Data def" <+> pretty dataDefSourceName

instance Pretty (ClassDef n) where
  pretty (ClassDef classSourceName methodNames _) =
    "Class" <+> pretty classSourceName <+> pretty methodNames

instance Pretty (TopBindings n) where
  pretty (TopBindings env) = pretty env

instance Pretty (TopState n) where
  pretty s =
       "bindings: "
    <>   indented (pretty (topBindings s))
    <> "synth candidates:"
    <>   indented (pretty (topSynthCandidates s))
    <> "source map: "
    <>   indented (pretty (topSourceMap s))

instance Pretty (Module n) where pretty = prettyFromPrettyPrec
instance PrettyPrec (Module n) where
  prettyPrec (Module variant decls result) = atPrec ArgPrec $
    "Module" <+> parens (p (show variant)) <> indented body
    where
      body = "unevaluated decls:"
           <>   indented (prettyLines (fromNest decls))
           <> "evaluated bindings:"
           <>   indented (p result)

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
