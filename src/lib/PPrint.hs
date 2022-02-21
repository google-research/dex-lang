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

module PPrint (
  pprint, pprintCanonicalized, pprintList, asStr , atPrec, toJSONStr,
  PrettyPrec(..), PrecedenceLevel (..), printLitBlock) where

import Data.Aeson hiding (Result, Null, Value, Success)
import GHC.Exts (Constraint)
import GHC.Float
import Data.Foldable (toList)
import Data.Functor ((<&>))
import qualified Data.ByteString.Lazy.Char8 as B
import qualified Data.List.NonEmpty as NE
import qualified Data.Map.Strict as M
import Data.Text.Prettyprint.Doc.Render.Text
import Data.Text.Prettyprint.Doc
import Data.Text (Text, uncons, unsnoc, unpack)
import qualified Data.Set        as S
import Data.String (fromString)
import Data.Maybe (isNothing)
import qualified System.Console.ANSI as ANSI
import System.Console.ANSI hiding (Color)
import System.IO.Unsafe
import qualified System.Environment as E
import Numeric

import LabeledItems

import Err
import Name
import Syntax

-- Specifies what kinds of operations are allowed to be printed at this point.
-- Printing at AppPrec level means that applications can be printed
-- with no parentheses, but binops must be parenthesized.
data PrecedenceLevel  = LowestPrec
                      | AppPrec
                      | ArgPrec  -- Only single symbols and parens allowed
                      deriving (Eq, Ord)

type DocPrec ann = PrecedenceLevel -> Doc ann

class PrettyPrec a where
  prettyPrec :: a -> DocPrec ann

-- `atPrec prec doc` will ensure that the precedence level is at most
-- `prec` when running `doc`, wrapping with parentheses if needed.
atPrec :: PrecedenceLevel -> Doc ann -> DocPrec ann
atPrec prec doc requestedPrec =
  if requestedPrec > prec then parens (align doc) else doc

prettyFromPrettyPrec :: PrettyPrec a => a -> Doc ann
prettyFromPrettyPrec = pArg

pAppArg :: (PrettyPrec a, Foldable f) => Doc ann -> f a -> Doc ann
pAppArg name as = align $ name <> group (nest 2 $ foldMap (\a -> line <> pArg a) as)

fromInfix :: Text -> Maybe Text
fromInfix t = do
  ('(', t') <- uncons t
  (t'', ')') <- unsnoc t'
  return t''

type PrettyPrecE e = (forall (n::S)       . PrettyPrec (e n  )) :: Constraint
type PrettyPrecB b = (forall (n::S) (l::S). PrettyPrec (b n l)) :: Constraint

pprintCanonicalized :: (HoistableE e, SubstE Name e, PrettyE e)
                    => e n -> String
pprintCanonicalized e = canonicalizeForPrinting e \e' -> pprint e'

pprintList :: Pretty a => [a] -> String
pprintList xs = asStr $ vsep $ punctuate "," (map p xs)

layout :: LayoutOptions
layout = if unbounded then LayoutOptions Unbounded else defaultLayoutOptions
  where unbounded = unsafePerformIO $ (Just "1"==) <$> E.lookupEnv "DEX_PPRINT_UNBOUNDED"

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

instance PrettyPrec a => PrettyPrec [a] where
  prettyPrec xs = atPrec ArgPrec $ hsep $ map pLowest xs

instance PrettyE ann => Pretty (BinderP c ann n l)
  where pretty (b:>ty) = p b <> ":" <> p ty

instance Pretty (Expr n) where pretty = prettyFromPrettyPrec
instance PrettyPrec (Expr n) where
  prettyPrec (Atom x ) = prettyPrec x
  prettyPrec (App f xs) = atPrec AppPrec $ pApp f <+> spaced (toList xs)
  prettyPrec (Op  op ) = prettyPrec op
  prettyPrec (Hof (For ann (Lam lamExpr))) =
    atPrec LowestPrec $ forStr ann <+> prettyLamHelper lamExpr (PrettyFor ann)
  prettyPrec (Hof hof) = prettyPrec hof
  prettyPrec (Case e alts _ _) = prettyPrecCase "case" e alts

prettyPrecCase :: PrettyE e => Doc ann -> Atom n -> [AltP e n] -> DocPrec ann
prettyPrecCase name e alts = atPrec LowestPrec $ name <+> p e <+> "of" <>
  nest 2 (hardline <> foldMap (\alt -> prettyAlt alt <> hardline) alts)

prettyAlt :: PrettyE e => AltP e n -> Doc ann
prettyAlt (Abs bs body) = hsep (map prettyBinderNoAnn  bs') <+> "->" <> nest 2 (p body)
  where bs' = fromNest bs

prettyBinderNoAnn :: Binder n l -> Doc ann
prettyBinderNoAnn (b:>_) = p b

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

instance Pretty (NaryLamExpr n) where
  pretty (NaryLamExpr (NonEmptyNest b bs) _ body) =
    "\\" <> prettyBinderNest (Nest b bs) <+> "." <> nest 2 (p body)

instance Pretty (NaryPiType n) where
  pretty (NaryPiType (NonEmptyNest b bs) effs resultTy) =
    prettyBinderNest (Nest b bs) <+> "->" <+> "{" <> p effs <> "}" <+> p resultTy

instance Pretty (PiBinder n l) where
  pretty (PiBinder b ty _) = p (b:>ty)

instance Pretty (LamExpr n) where pretty = prettyFromPrettyPrec
instance PrettyPrec (LamExpr n) where
  prettyPrec lamExpr = case lamExpr of
    LamExpr (LamBinder _ _ TabArrow _) _ ->
      atPrec LowestPrec $ "\\for"
      <+> prettyLamHelper lamExpr (PrettyLam TabArrow)
    LamExpr (LamBinder _ _ arr _) _ ->
      atPrec LowestPrec $ "\\"
      <> prettyLamHelper lamExpr (PrettyLam arr)

instance Pretty (DepPairType n) where pretty = prettyFromPrettyPrec
instance PrettyPrec (DepPairType n) where
  prettyPrec (DepPairType b rhs) =
    atPrec ArgPrec $ align $ group $ parens $ p b <+> "&>" <+> p rhs

instance Pretty (Atom n) where pretty = prettyFromPrettyPrec
instance PrettyPrec (Atom n) where
  prettyPrec atom = case atom of
    Var v -> atPrec ArgPrec $ p v
    Lam lamExpr -> prettyPrec lamExpr
    Pi piType -> atPrec LowestPrec $ align $ p piType
    DepPairTy ty -> prettyPrec ty
    DepPair x y _ -> atPrec ArgPrec $ align $ group $
        parens $ p x <> ",>" <+> p y
    TC  e -> prettyPrec e
    Con e -> prettyPrec e
    Eff e -> atPrec ArgPrec $ p e
    DataCon name _ _ _ xs -> case xs of
      [] -> atPrec ArgPrec $ p name
      [l, r] | Just sym <- fromInfix (fromString name) -> atPrec ArgPrec $ align $ group $
        parens $ flatAlt " " "" <> pApp l <> line <> p sym <+> pApp r
      _ ->  atPrec LowestPrec $ pAppArg (p name) xs
    TypeCon name _ params -> case params of
      [] -> atPrec ArgPrec $ p name
      [l, r] | Just sym <- fromInfix (fromString name) ->
        atPrec ArgPrec $ align $ group $
          parens $ flatAlt " " "" <> pApp l <> line <> p sym <+> pApp r
      _  -> atPrec LowestPrec $ pAppArg (p name) params
    LabeledRow elems -> prettyRecordTyRow elems "?"
    Record items -> prettyLabeledItems items (line' <> ",") " ="
    Variant _ label i value -> prettyVariant ls label value where
      ls = LabeledItems $ case i of
            0 -> M.empty
            _ -> M.singleton label $ NE.fromList $ fmap (const ()) [1..i]
    RecordTy elems -> prettyRecordTyRow elems "&"
    VariantTy items -> prettyExtLabeledItems items Nothing (line <> "|") ":"
    ACase e alts _ -> prettyPrecCase "acase" e alts
    DataConRef _ params args -> atPrec LowestPrec $
      "DataConRef" <+> p params <+> p args
    BoxedRef ptrsSizes (Abs b body) -> atPrec LowestPrec $
      "Box" <+> p b <+> "<-" <+> p ptrsSizes <+> hardline <> "in" <+> p body
    ProjectElt idxs v ->
      atPrec LowestPrec $ "ProjectElt" <+> p idxs <+> p v
    DepPairRef l (Abs b r) _ -> atPrec LowestPrec $
      "DepPairRef" <+> p l <+> "as" <+> p b <+> "in" <+> p r

prettyRecordTyRow :: FieldRowElems n -> Doc ann -> DocPrec ann
prettyRecordTyRow elems separator = do
  atPrec ArgPrec $ align $ group $ braces $ (prefix <>) $
    concatWith (surround $ line <> separator <> " ") $ p <$> fromFieldRowElems elems
    where prefix = case fromFieldRowElems elems of
                      [] -> separator
                      [DynFields _] -> separator
                      _ -> mempty

instance Pretty (FieldRowElem n) where
  pretty = \case
    StaticFields items -> concatWith (surround $ line <> "& ") $
      withLabels items <&> \(l, _, ty) -> p l <> ":" <+> pLowest ty
    DynField  l ty -> "@" <> p l <> ":" <+> p ty
    DynFields f    -> "..." <> p f

instance Pretty (DataConRefBinding n l) where pretty = prettyFromPrettyPrec
instance PrettyPrec (DataConRefBinding n l) where
  prettyPrec (DataConRefBinding b x) = atPrec AppPrec $ p b <+> "<-" <+> p x

prettyExtLabeledItems :: (PrettyPrec a, PrettyPrec b)
  => ExtLabeledItems a b -> Maybe (Doc ann) -> Doc ann -> Doc ann -> DocPrec ann
prettyExtLabeledItems (Ext (LabeledItems row) rest) prefix separator bindwith =
  atPrec ArgPrec $ align $ group $ innerDoc
  where
    elems = concatMap (\(k, vs) -> map (k,) (toList vs)) (M.toAscList row)
    fmtElem (label, v) = p label <> bindwith <+> pLowest v
    docs = map fmtElem elems
    suffix = case rest of
      Just v -> separator <> " ..." <> pArg v
      Nothing -> if length docs == 0 && isNothing prefix then separator else mempty
    innerDoc = "{" <> flatAlt " " ""
      <> (case prefix of Nothing -> mempty; Just pref -> pref <> separator <> " ")
      <> concatWith (surround (separator <> " ")) docs
      <> suffix <> "}"

prettyLabeledItems :: PrettyPrec a
  => LabeledItems a -> Doc ann -> Doc ann -> DocPrec ann
prettyLabeledItems items =
  prettyExtLabeledItems (Ext items (Nothing :: Maybe ())) Nothing

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
    PtrLitBound _ ptr -> p ptr
    SimpLamBound ty f -> p ty <> hardline <> p f
    FFIFunBound _ f -> p f

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
    TyConBinding      dataDefName e -> "Type constructor:" <+> pretty dataDefName <+> (parens $ "atom:" <+> p e)
    DataConBinding    dataDefName idx e ->
      "Data constructor:" <+> pretty dataDefName <+>
      "Constructor index:" <+> pretty idx <+> (parens $ "atom:" <+> p e)
    ClassBinding      classDef e -> pretty classDef <+> (parens $ "atom:" <+> p e)
    SuperclassBinding className idx _ ->
      "Superclass" <+> pretty idx <+> "of" <+> pretty className
    MethodBinding     className idx _ ->
      "Method" <+> pretty idx <+> "of" <+> pretty className
    ImpFunBinding f -> pretty f
    ObjectFileBinding _ -> "<object file>"
    ModuleBinding  _ -> "<module>"
    PtrBinding     _ -> "<ptr>"

instance Pretty (Module n) where
  pretty m = prettyRecord
    [ ("moduleSourceName"     , p $ moduleSourceName m)
    , ("moduleDirectDeps"     , p $ S.toList $ moduleDirectDeps m)
    , ("moduleTransDeps"      , p $ S.toList $ moduleTransDeps m)
    , ("moduleExports"        , p $ moduleExports m)
    , ("moduleSynthCandidates", p $ moduleSynthCandidates m)
    , ("moduleObjectFiles"    , p $ moduleObjectFiles m) ]

instance Pretty (ObjectFiles n) where
  pretty (ObjectFiles _) = error "todo"

instance Pretty (DataDef n) where
  pretty (DataDef name bs cons) =
    "data" <+> p name <+> p bs <> hardline <> prettyLines cons

instance Pretty (DataConDef n) where
  pretty (DataConDef name bs) =
    p name <+> ":" <+> p bs

instance Pretty (ClassDef n) where
  pretty (ClassDef classSourceName methodNames _) =
    "Class:" <+> pretty classSourceName <+> pretty methodNames

deriving instance (forall c n. Pretty (v c n)) => Pretty (RecSubst v o)

instance Pretty (TopEnv n) where
  pretty (TopEnv _ defs cache ms) =
    prettyRecord [ ("Defs"          , p defs)
                 , ("Cache"         , p cache)
                 , ("Loaded modules", p ms)]

instance Pretty (ImportStatus n) where
  pretty imports = pretty $ S.toList $ directImports imports

instance Pretty (ModuleEnv n) where
  pretty (ModuleEnv imports sm sc _ effs) =
    prettyRecord [ ("Imports"         , p imports)
                 , ("Source map"      , p sm)
                 , ("Synth candidates", p sc)
                 , ("Effects"         , p effs)]

instance Pretty (Env n) where
  pretty (Env env1 env2) =
    prettyRecord [ ("Top env"   , p env1)
                 , ("Module env", p env2)]

prettyRecord :: [(String, Doc ann)] -> Doc ann
prettyRecord xs = foldMap (\(name, val) -> pretty name <> indented val) xs

instance Pretty SourceBlock where
  pretty block = pretty (sbText block)

prettyDuration :: Double -> Doc ann
prettyDuration d = p (showFFloat (Just 3) (d * mult) "") <+> unit
  where (mult, unit) =      if d >= 1    then (1  , "s")
                       else if d >= 1e-3 then (1e3, "ms")
                       else if d >= 1e-6 then (1e6, "us")
                       else                   (1e9, "ns")

instance Pretty Output where
  pretty (TextOut s) = pretty s
  pretty (HtmlOut _) = "<html output>"
  -- pretty (ExportedFun _ _) = ""
  pretty (BenchResult name compileTime runTime stats) =
    benchName <> hardline <>
    "Compile time: " <> prettyDuration compileTime <> hardline <>
    "Run time:     " <> prettyDuration runTime <+>
    (case stats of Just (runs, _) -> "\t" <> parens ("based on" <+> p runs <+> "runs")
                   Nothing        -> "")
    where benchName = case name of "" -> ""
                                   _  -> "\n" <> p name
  pretty (PassInfo _ s) = p s
  pretty (EvalTime  t _) = "Eval (s):  " <+> p t
  pretty (TotalTime t)   = "Total (s): " <+> p t <+> "  (eval + compile)"
  pretty (MiscLog s) = p s


instance Pretty PassName where
  pretty x = p $ show x

instance Pretty Result where
  pretty (Result outs r) = vcat (map pretty outs) <> maybeErr
    where maybeErr = case r of Failure err -> p err
                               Success () -> mempty

instance Color c => Pretty (UBinder c n l) where pretty = prettyFromPrettyPrec
instance Color c => PrettyPrec (UBinder c n l) where
  prettyPrec b = atPrec ArgPrec case b of
    UBindSource v -> p v
    UIgnore       -> "_"
    UBind v _     -> p v

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
  pretty (InternalName v _) = p v

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
    ULabel name -> atPrec ArgPrec $ "&" <> p name
    ULabeledRow elems -> atPrec ArgPrec $ prettyUFieldRowElems (line <> "?") ": " elems
    URecord   elems -> atPrec ArgPrec $ prettyUFieldRowElems (line' <> ",") "=" elems
    URecordTy elems -> atPrec ArgPrec $ prettyUFieldRowElems (line <> "&") ": " elems
    UVariant labels label value -> prettyVariant labels label value
    UVariantTy items -> prettyExtLabeledItems items Nothing (line <> "|") ":"
    UVariantLift labels value -> prettyVariantLift labels value
    UIntLit   v -> atPrec ArgPrec $ p v
    UFloatLit v -> atPrec ArgPrec $ p v

prettyVariantLift :: PrettyPrec a
  => LabeledItems () -> a -> DocPrec ann
prettyVariantLift labels value = atPrec ArgPrec $
      "{|" <> left <+> "..." <> pLowest value <+> "|}"
      where left = foldl (<>) mempty $ fmap plabel $ reflectLabels labels
            plabel (l, _) = p l <> "|"

prettyUFieldRowElems :: Doc ann -> Doc ann -> UFieldRowElems n -> Doc ann
prettyUFieldRowElems separator bindwith elems =
  braces $ concatWith (surround $ separator <> " ") $ elems <&> \case
    UStaticField l e -> p l <> bindwith <> p e
    UDynField    v e -> p v <> bindwith <> p e
    UDynFields   v   -> "..." <> p v

instance Pretty (UAlt n) where
  pretty (UAlt pat body) = p pat <+> "->" <+> p body

instance Pretty (UDecl n l) where
  pretty (ULet ann b rhs) =
    align $ p ann <+> p b <+> "=" <> (nest 2 $ group $ line <> pLowest rhs)
  pretty (UDataDefDecl (UDataDef bParams bIfaces dataCons) bTyCon bDataCons) =
    "data" <+> p bTyCon <+> p bParams <+> (brackets $ p bIfaces)
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

instance Color c => Pretty (UAnnBinder c n l) where
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
    UPatRecord pats -> atPrec ArgPrec $ prettyUFieldRowPat "," "=" pats
    UPatVariant labels label value -> prettyVariant labels label value
    UPatVariantLift labels value -> prettyVariantLift labels value
    UPatTable pats -> atPrec ArgPrec $ p pats

prettyUFieldRowPat :: forall n l ann. Doc ann -> Doc ann -> UFieldRowPat n l -> Doc ann
prettyUFieldRowPat separator bindwith pat =
  braces $ concatWith (surround $ separator <> " ") $ go pat
  where
    go :: UFieldRowPat n' l' -> [Doc ann]
    go = \case
      UEmptyRowPat          -> []
      URemFieldsPat UIgnore -> ["..."]
      URemFieldsPat b       -> ["..." <> p b]
      UDynFieldsPat   v r rest -> ("@..." <> p v <> bindwith <> p r) : go rest
      UDynFieldPat    v r rest -> ("@" <> p v <> bindwith <> p r) : go rest
      UStaticFieldPat l r rest -> (p l <> bindwith <> p r) : go rest

spaced :: (Foldable f, Pretty a) => f a -> Doc ann
spaced xs = hsep $ map p $ toList xs

instance Pretty (UPatAnn n l) where
  pretty (UPatAnn pat ann) = p pat <> annDoc where
    annDoc = case ann of
      Just ty -> ":" <> pApp ty
      Nothing -> mempty

instance Pretty (EnvFrag n l) where
  pretty (EnvFrag bindings effects) =
       "Partial bindings:" <> indented (p bindings)
    <> "Effects allowed:" <+> p effects

instance Pretty (Cache n) where
  pretty (Cache _ _ _ _ _) = "<cache>" -- TODO

instance Pretty (SynthCandidates n) where
  pretty scs =
       "lambda dicts:"   <+> p (lambdaDicts       scs) <> hardline
    <> "superclasses:"   <+> p (superclassGetters scs) <> hardline
    <> "instance dicts:" <+> p (M.toList $ instanceDicts scs)

instance Pretty (LoadedModules n) where
  pretty _ = "<loaded modules>"

indented :: Doc ann -> Doc ann
indented doc = nest 2 (hardline <> doc) <> hardline

-- ==== Imp IR ===

instance Pretty (IExpr n) where
  pretty (ILit v) = p v
  pretty (IVar v _) = p v

instance PrettyPrec (IExpr n) where prettyPrec = atPrec ArgPrec . pretty

instance Pretty (ImpDecl n l) where
  pretty (ImpLet Empty instr) = p instr
  pretty (ImpLet (Nest b Empty) instr) = p b <+> "=" <+> p instr
  pretty (ImpLet bs instr) = p bs <+> "=" <+> p instr

instance Pretty IFunType where
  pretty (IFunType cc argTys retTys) =
    "Fun" <+> p cc <+> p argTys <+> "->" <+> p retTys

instance Pretty (ImpFunction n) where
  pretty (ImpFunction (IFunType cc _ _) (Abs bs body)) =
    "impfun" <+> p cc <+> prettyBinderNest bs
    <> nest 2 (hardline <> p body) <> hardline
  pretty (FFIFunction _ f) = p f

instance Pretty (ImpBlock n)  where
  pretty (ImpBlock Empty expr) = group $ line <> pLowest expr
  pretty (ImpBlock decls expr) = hardline <> prettyLines decls' <> pLowest expr
    where decls' = fromNest decls

instance Pretty (IBinder n l)  where
  pretty (IBinder b ty) = p b <+> ":" <+> p ty

instance Pretty (ImpInstr n)  where
  pretty (IFor a n (Abs i block)) = forStr (RegularFor a) <+> p i <+> "<" <+> p n <>
                                      nest 4 (hardline <> p block)
  pretty (IWhile body) = "while" <+> nest 2 (p body)
  pretty (ICond predicate cons alt) =
    "if" <+> p predicate <+> "then" <> nest 2 (hardline <> p cons) <>
    hardline <> "else" <> nest 2 (hardline <> p alt)
  pretty (IQueryParallelism f s) = "queryParallelism" <+> p f <+> p s
  pretty (ILaunch f size args) =
    "launch" <+> p f <+> p size <+> spaced args
  pretty (IPrimOp op)     = pLowest op
  pretty (ICastOp t x)    = "cast"  <+> p x <+> "to" <+> p t
  pretty (Store dest val) = "store" <+> p dest <+> p val
  pretty (Alloc Stack t s) = "alloca" <+> p t <> "[" <> p s <> "]"
  pretty (Alloc _ t s)     = "alloc"  <+> p t <> "[" <> p s <> "]"
  pretty (MemCopy dest src numel) = "memcopy" <+> p dest <+> p src <+> p numel
  pretty (Free ptr)       = "free"  <+> p ptr
  pretty ISyncWorkgroup   = "syncWorkgroup"
  pretty IThrowError      = "throwError"
  pretty (ICall f args)   = "call" <+> p f <+> p args

instance Pretty BaseType where pretty = prettyFromPrettyPrec
instance PrettyPrec BaseType where
  prettyPrec b = case b of
    Scalar sb -> prettyPrec sb
    Vector sb -> atPrec ArgPrec $ "<" <> p vectorWidth <+> "x" <+> p sb <> ">"
    PtrType ty -> atPrec AppPrec $ "Ptr" <+> p ty

instance Pretty AddressSpace where
  pretty Stack    = "stack"
  pretty (Heap d) = p (show d)

instance Pretty ScalarBaseType where pretty = prettyFromPrettyPrec
instance PrettyPrec ScalarBaseType where
  prettyPrec sb = atPrec ArgPrec $ case sb of
    Int64Type   -> "Int64"
    Int32Type   -> "Int32"
    Float64Type -> "Float64"
    Float32Type -> "Float32"
    Word8Type   -> "Word8"
    Word32Type  -> "Word32"
    Word64Type  -> "Word64"

instance PrettyPrec e => Pretty (PrimExpr e) where pretty = prettyFromPrettyPrec
instance PrettyPrec e => PrettyPrec (PrimExpr e) where
  prettyPrec (TCExpr  e) = prettyPrec e
  prettyPrec (ConExpr e) = prettyPrec e
  prettyPrec (OpExpr  e) = prettyPrec e
  prettyPrec (HofExpr e) = prettyPrec e


instance PrettyPrec e => Pretty (PrimTC e) where pretty = prettyFromPrettyPrec
instance PrettyPrec e => PrettyPrec (PrimTC e) where
  prettyPrec con = case con of
    BaseType b   -> prettyPrec b
    ProdType []  -> atPrec ArgPrec $ "Unit"
    ProdType as  -> atPrec ArgPrec $ align $ group $
      encloseSep "(" ")" " & " $ fmap pApp as
    SumType  cs  -> atPrec ArgPrec $ align $ group $
      encloseSep "(|" "|)" " | " $ fmap pApp cs
    IntRange a b -> if docAsStr (pArg a) == "0"
      then atPrec AppPrec ("Fin" <+> pArg b)
      else prettyExprDefault $ TCExpr con
    IndexRange _ low high -> atPrec LowestPrec $ low' <> ".." <> high'
      where
        low'  = case low  of InclusiveLim x -> pApp x
                             ExclusiveLim x -> pApp x <> "<"
                             Unlimited      -> ""
        high' = case high of InclusiveLim x -> pApp x
                             ExclusiveLim x -> "<" <> pApp x
                             Unlimited      -> ""
    ParIndexRange n _ _ -> atPrec ArgPrec $ "{" <> pLowest n <> "}"
    RefType (Just h) a -> atPrec AppPrec $ pAppArg "Ref" [h, a]
    RefType Nothing a  -> atPrec AppPrec $ pAppArg "Ref" [a]
    TypeKind -> atPrec ArgPrec "Type"
    EffectRowKind -> atPrec ArgPrec "EffKind"
    LabeledRowKindTC -> atPrec ArgPrec "Fields"
    LabelType -> atPrec ArgPrec "Label"
    _ -> prettyExprDefault $ TCExpr con

instance PrettyPrec e => Pretty (PrimCon e) where pretty = prettyFromPrettyPrec
instance PrettyPrec e => PrettyPrec (PrimCon e) where
  prettyPrec = prettyPrecPrimCon

prettyPrecPrimCon :: PrettyPrec e => PrimCon e -> DocPrec ann
prettyPrecPrimCon con = case con of
  Lit l       -> prettyPrec l
  ProdCon xs  -> atPrec ArgPrec $ align $ group $
    encloseSep "(" ")" ", " $ fmap pLowest xs
  SumCon _ tag payload -> atPrec ArgPrec $
    "(" <> p tag <> "|" <+> pApp payload <+> "|)"
  SumAsProd ty tag payload -> atPrec LowestPrec $
    "SumAsProd" <+> pApp ty <+> pApp tag <+> pApp payload
  ClassDictHole _ _ -> atPrec ArgPrec "_"
  IntRangeVal     l h i -> atPrec LowestPrec $ pApp i <> "@" <> pApp (IntRange     l h)
  IndexRangeVal t l h i -> atPrec LowestPrec $ pApp i <> "@" <> pApp (IndexRange t l h)
  ParIndexCon ty i ->
    atPrec LowestPrec $ pApp i <> "@" <> pApp ty
  IndexSliceVal ty n i ->
    atPrec LowestPrec $ "IndexSlice" <+> pApp ty <+> pApp n <+> pApp i
  BaseTypeRef ptr -> atPrec ArgPrec $ "Ref" <+> pApp ptr
  TabRef tab -> atPrec ArgPrec $ "Ref" <+> pApp tab
  ConRef conRef -> atPrec AppPrec $ "Ref" <+> pApp conRef
  RecordRef _ -> atPrec ArgPrec "Record ref"  -- TODO
  LabelCon name -> atPrec ArgPrec $ "##" <> p name


instance PrettyPrec e => Pretty (PrimOp e) where pretty = prettyFromPrettyPrec
instance PrettyPrec e => PrettyPrec (PrimOp e) where
  prettyPrec op = case op of
    PrimEffect ref (MPut    val   ) -> atPrec LowestPrec $ pApp ref <+> ":=" <+> pApp val
    PrimEffect ref (MExtend _   x ) -> atPrec LowestPrec $ "extend" <+> pApp ref <+> pApp x
    PtrOffset ptr idx -> atPrec LowestPrec $ pApp ptr <+> "+>" <+> pApp idx
    PtrLoad   ptr     -> atPrec AppPrec $ pAppArg "load" [ptr]
    RecordCons items rest -> atPrec LowestPrec $ "RecordCons" <+> pArg items <+> pArg rest
    RecordConsDynamic lab val rec -> atPrec LowestPrec $
      "RecordConsDynamic" <+> pArg lab <+> pArg val <+> pArg rec
    RecordSplit fields val -> atPrec AppPrec $
      "RecordSplit" <+> pArg fields <+> pArg val
    VariantLift types val ->
      prettyVariantLift (fmap (const ()) types) val
    VariantSplit types val -> atPrec AppPrec $
      "VariantSplit" <+> prettyLabeledItems types (line <> "|") ":" ArgPrec
                     <+> pArg val
    SynthesizeDict _ e -> atPrec LowestPrec $ "synthesize" <+> pApp e
    _ -> prettyExprDefault $ OpExpr op

prettyExprDefault :: PrettyPrec e => PrimExpr e -> DocPrec ann
prettyExprDefault expr =
  case length expr of
    0 -> atPrec ArgPrec primName
    _ -> atPrec AppPrec $ pAppArg primName expr
  where primName = p $ "%" ++ showPrimName expr

instance PrettyPrec e => Pretty (PrimHof e) where pretty = prettyFromPrettyPrec
instance PrettyPrec e => PrettyPrec (PrimHof e) where
  prettyPrec hof = case hof of
    For ann lam -> atPrec LowestPrec $ forStr ann <+> pArg lam
    _ -> prettyExprDefault $ HofExpr hof

printDouble :: Double -> Doc ann
printDouble x = p (double2Float x)

printFloat :: Float -> Doc ann
printFloat x = p $ reverse $ dropWhile (=='0') $ reverse $
  showFFloat (Just 6) x ""

instance Pretty LitVal where pretty = prettyFromPrettyPrec
instance PrettyPrec LitVal where
  prettyPrec (Int64Lit   x) = atPrec ArgPrec $ p x
  prettyPrec (Int32Lit   x) = atPrec ArgPrec $ p x
  prettyPrec (Float64Lit x) = atPrec ArgPrec $ printDouble x
  prettyPrec (Float32Lit x) = atPrec ArgPrec $ printFloat  x
  prettyPrec (Word8Lit   x) = atPrec ArgPrec $ p $ show $ toEnum @Char $ fromIntegral x
  prettyPrec (Word32Lit  x) = atPrec ArgPrec $ p $ "0x" ++ showHex x ""
  prettyPrec (Word64Lit  x) = atPrec ArgPrec $ p $ "0x" ++ showHex x ""
  prettyPrec (PtrLit (PtrLitVal ty x)) =
    atPrec ArgPrec $ "Ptr" <+> p ty <+> p (show x)
  prettyPrec (PtrLit (PtrSnapshot _ _)) = atPrec ArgPrec "<ptr snapshot>"
  prettyPrec (VecLit  l) = atPrec ArgPrec $ encloseSep "<" ">" ", " $ fmap p l

instance Pretty CallingConvention where
  pretty = p . show

instance Pretty LetAnn where
  pretty ann = case ann of
    PlainLet      -> ""
    InstanceLet   -> "%instance"
    NoInlineLet   -> "%noinline"

instance PrettyPrec () where prettyPrec = atPrec ArgPrec . pretty

instance Pretty RWS where
  pretty eff = case eff of
    Reader -> "Read"
    Writer -> "Accum"
    State  -> "State"

printLitBlock :: Pretty block => Bool -> block -> Result -> String
printLitBlock isatty block (Result outs result) =
  pprint block ++ concat (map (printOutput isatty) outs) ++ printResult isatty result

printOutput :: Bool -> Output -> String
printOutput isatty out = addPrefix (addColor isatty Cyan ">") $ pprint $ out

printResult :: Bool -> Except () -> String
printResult _ (Success ()) = ""
printResult isatty (Failure err) = addColor isatty Red $ addPrefix ">" $ pprint err

addPrefix :: String -> String -> String
addPrefix prefix str = unlines $ map prefixLine $ lines str
  where prefixLine :: String -> String
        prefixLine s = case s of "" -> prefix
                                 _  -> prefix ++ " " ++ s

addColor :: Bool -> ANSI.Color -> String -> String
addColor False _ s = s
addColor True c s =
  setSGRCode [SetConsoleIntensity BoldIntensity, SetColor Foreground Vivid c]
  ++ s ++ setSGRCode [Reset]

toJSONStr :: ToJSON a => a -> String
toJSONStr = B.unpack . encode

instance ToJSON Result where
  toJSON (Result outs err) = object (outMaps <> errMaps)
    where
      errMaps = case err of
        Failure e   -> ["error" .= String (fromString $ pprint e)]
        Success () -> []
      outMaps = flip foldMap outs $ \case
        BenchResult name compileTime runTime _ ->
          [ "bench_name"   .= toJSON name
          , "compile_time" .= toJSON compileTime
          , "run_time"     .= toJSON runTime ]
        out -> ["result" .= String (fromString $ pprint out)]
