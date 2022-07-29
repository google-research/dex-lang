 -- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE IncoherentInstances #-}  -- due to `ConRef`
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module PPrint (
  pprint, pprintCanonicalized, pprintList, asStr , atPrec, toJSONStr,
  PrettyPrec(..), PrecedenceLevel (..), prettyBlock, printLitBlock, printResult) where

import Data.Aeson hiding (Result, Null, Value, Success)
import GHC.Exts (Constraint)
import GHC.Float
import Data.Foldable (toList, fold)
import Data.Functor ((<&>))
import qualified Data.ByteString.Lazy.Char8 as B
import qualified Data.List.NonEmpty as NE
import qualified Data.Map.Strict as M
import Data.Text.Prettyprint.Doc.Render.Text
import Data.Text.Prettyprint.Doc
import Data.Text (Text, snoc, uncons, unsnoc, unpack)
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
import Types.Core
import Parser (showPrimName)

-- A DocPrec is a slightly context-aware Doc, specifically one that
-- knows the precedence level of the immediately enclosing operation,
-- and can decide to parenthesize itself accordingly.
-- For example, when printing `x = f (g 1)`, we know that
-- - We need parens around `(g 1)` because applying `f` binds
--   tighter than applying `g` (because application is left-associative)
-- - We do not need parens around `g` or 1, because there is nothing
--   there that may bind less tightly than the function applications.
-- - We also do not need parens around the whole RHS `f (g 1)`, because
--   the `=` binds less tightly than applying `f`.
--
-- This is accomplished in the `Expr` instance of `PrettyPrec` by
-- coding function application to require `ArgPrec` from the arguments
-- (via the default behavior of `prettyFromPrettyPrec`), but to
-- provide only `AppPrec` for the application expression itself.  The
-- outer application is not wrapped in parens because the let binding
-- prints its RHS at `LowestPrec`.
type DocPrec ann = PrecedenceLevel -> Doc ann

-- Specifies what kinds of operations are allowed to be printed at
-- this point without wrapping in parens.
data PrecedenceLevel =
    -- Any subexpression is allowed without parens
    LowestPrec
    -- Function application is allowed without parens, but nothing
    -- that binds less tightly
  | AppPrec
    -- Only single symbols and parens allowed
  | ArgPrec
  deriving (Eq, Ord)

class PrettyPrec a where
  prettyPrec :: a -> DocPrec ann

-- `atPrec prec doc` will ensure that the precedence level is at most
-- `prec` when running `doc`, wrapping with parentheses if needed.
-- To wit,
-- - `atPrec LowestPrec` means "wrap unless the context permits all
--   subexpressions unwrapped"
-- - `atPrec AppPrec` means "wrap iff the context requires ArgPrec"
-- - `atPrec ArgPrec` means "never wrap" (unless the
--   `PrecedenceLevel` ADT is extended later).
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
  pretty (Block _ decls expr) = prettyBlock decls expr

prettyBlock :: (PrettyPrec (e l)) => Nest Decl n l -> e l -> Doc ann
prettyBlock Empty expr = group $ line <> pLowest expr
prettyBlock decls expr = prettyLines decls' <> hardline <> pLowest expr
    where decls' = fromNest decls

fromNest :: Nest b n l -> [b UnsafeS UnsafeS]
fromNest Empty = []
fromNest (Nest b rest) = unsafeCoerceB b : fromNest rest

prettyLines :: (Foldable f, Pretty a) => f a -> Doc ann
prettyLines xs = foldMap (\d -> hardline <> p d) $ toList xs

instance PrettyPrec a => PrettyPrec [a] where
  prettyPrec xs = atPrec ArgPrec $ hsep $ map pLowest xs

instance PrettyE ann => Pretty (BinderP c ann n l)
  where pretty (b:>ty) = p b <> ":" <> p ty

instance Pretty (Expr n) where pretty = prettyFromPrettyPrec
instance PrettyPrec (Expr n) where
  prettyPrec (Atom x ) = prettyPrec x
  prettyPrec (App f xs) = atPrec AppPrec $ pApp f <+> spaced (toList xs)
  prettyPrec (TabApp f xs) = atPrec AppPrec $ pApp f <> "." <> dotted (toList xs)
  prettyPrec (Op  op ) = prettyPrec op
  prettyPrec (Hof (For ann _ (Lam lamExpr))) =
    atPrec LowestPrec $ forStr ann <+> prettyLamHelper lamExpr (PrettyFor ann)
  prettyPrec (Hof (Seq ann _ c (Lam (LamExpr (LamBinder b ty _ effs) body)))) =
    atPrec LowestPrec $ "seq" <+> pApp ann <+> pApp c <+> prettyLam (p (b:>ty) <> ".") effs body
  prettyPrec (Hof hof) = prettyPrec hof
  prettyPrec (Case e alts _ effs) = prettyPrecCase "case" e alts effs

prettyPrecCase :: PrettyE e => Doc ann -> Atom n -> [AltP e n] -> EffectRow n -> DocPrec ann
prettyPrecCase name e alts effs = atPrec LowestPrec $
  name <+> pApp e <+> "of" <>
  nest 2 (foldMap (\alt -> hardline <> prettyAlt alt) alts
          <> effectLine effs)
  where
    effectLine Pure = ""
    effectLine row = hardline <> "case annotated with effects" <+> p row

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
  pretty (Let b (DeclBinding ann ty rhs)) =
    align $ annDoc <> p (b:>ty) <+> "=" <> (nest 2 $ group $ line <> pLowest rhs)
    where annDoc = case ann of PlainLet -> mempty; _ -> pretty ann <> " "

instance Pretty (NaryLamExpr n) where
  pretty (NaryLamExpr (NonEmptyNest b bs) _ body) =
    "\\" <> (spaced $ fromNest $ Nest b bs) <+> "." <> nest 2 (p body)

instance Pretty (NaryPiType n) where
  pretty (NaryPiType (NonEmptyNest b bs) effs resultTy) =
    (spaced $ fromNest $ Nest b bs) <+> "->" <+> "{" <> p effs <> "}" <+> p resultTy

instance Pretty (PiBinder n l) where
  pretty (PiBinder b ty _) = p (b:>ty)

instance Pretty (LamExpr n) where pretty = prettyFromPrettyPrec
instance PrettyPrec (LamExpr n) where
  prettyPrec lamExpr = case lamExpr of
    LamExpr (LamBinder _ _ arr _) _ ->
      atPrec LowestPrec $ "\\"
      <> prettyLamHelper lamExpr (PrettyLam arr)

instance Pretty (IxType n) where
  pretty (IxType ty _) = parens $ "IxType" <+> pretty ty

instance Pretty (TabLamExpr n) where pretty = prettyFromPrettyPrec
instance PrettyPrec (TabLamExpr n) where
  prettyPrec (TabLamExpr b body) =
    atPrec LowestPrec $ "view" <+> p b <+> "." <+> p body

instance Pretty (DictExpr n) where
  pretty d = case d of
    InstanceDict name args -> "Instance" <+> p name <+> p args
    InstantiatedGiven v args -> "Given" <+> p v <+> p (toList args)
    SuperclassProj d' i -> "SuperclassProj" <+> p d' <+> p i
    IxFin n -> "Ix (Fin" <+> p n <> ")"

instance Pretty (DictType n) where
  pretty (DictType classSourceName _ params) =
    p classSourceName <+> spaced params

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
    TabLam lamExpr -> prettyPrec lamExpr
    TabPi piType -> atPrec LowestPrec $ align $ p piType
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
    TypeCon "RangeTo"      _ (DataDefParams [_, i] _) -> atPrec LowestPrec $ ".."  <> pApp i
    TypeCon "RangeToExc"   _ (DataDefParams [_, i] _) -> atPrec LowestPrec $ "..<" <> pApp i
    TypeCon "RangeFrom"    _ (DataDefParams [_, i] _) -> atPrec LowestPrec $ pApp i <>  ".."
    TypeCon "RangeFromExc" _ (DataDefParams [_, i] _) -> atPrec LowestPrec $ pApp i <> "<.."
    TypeCon name _ (DataDefParams params _) -> case params of
      [] -> atPrec ArgPrec $ p name
      [l, r] | Just sym <- fromInfix (fromString name) ->
        atPrec ArgPrec $ align $ group $
          parens $ flatAlt " " "" <> pApp l <> line <> p sym <+> pApp r
      _  -> atPrec LowestPrec $ pAppArg (p name) params
    DictCon d -> atPrec LowestPrec $ p d
    DictTy  t -> atPrec LowestPrec $ p t
    LabeledRow elems -> prettyRecordTyRow elems "?"
    Record items -> prettyLabeledItems items (line' <> ",") " ="
    Variant _ label i value -> prettyVariant ls label value where
      ls = LabeledItems $ case i of
            0 -> M.empty
            _ -> M.singleton label $ NE.fromList $ fmap (const ()) [1..i]
    RecordTy elems -> prettyRecordTyRow elems "&"
    VariantTy items -> prettyExtLabeledItems items Nothing (line <> "|") ":"
    ACase e alts _ -> prettyPrecCase "acase" e alts Pure
    DataConRef _ params args -> atPrec LowestPrec $
      "DataConRef" <+> p params <+> p args
    BoxedRef (Abs (NonDepNest b ptrsSizes) body) -> atPrec LowestPrec $
      "Box" <+> p b <+> "<-" <+> p ptrsSizes <+> hardline <> "in" <+> p body
    ProjectElt idxs v ->
      atPrec LowestPrec $ "ProjectElt" <+> p idxs <+> p v
    DepPairRef l (Abs b r) _ -> atPrec LowestPrec $
      "DepPairRef" <+> p l <+> "as" <+> p b <+> "in" <+> p r

instance Pretty (BoxPtr n) where
  pretty (BoxPtr ptrptr sb) = pretty (ptrptr, sb)

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
forStr Fwd = "for"
forStr Rev = "rof"

instance Pretty (PiType n) where
  pretty (PiType (PiBinder b ty arr) eff body) = let
    prettyBinder = prettyBinderHelper (b:>ty) (PairE eff body)
    prettyBody = case body of
      Pi subpi -> pretty subpi
      _ -> pLowest body
    in prettyBinder <> (group $ line <> p arr <+> prettyBody)

instance Pretty (TabPiType n) where
  pretty (TabPiType (b :> IxType ty _) body) = let
    prettyBinder = prettyBinderHelper (b:>ty) body
    prettyBody = case body of
      Pi subpi -> pretty subpi
      _ -> pLowest body
    in prettyBinder <> (group $ line <> "=>" <+> prettyBody)

prettyBinderHelper :: HoistableE e => Binder n l -> e l -> Doc ann
prettyBinderHelper (b:>ty) body =
  if binderName b `isFreeIn` body
    then parens $ p (b:>ty)
    else p ty

data PrettyLamType = PrettyLam Arrow | PrettyFor ForAnn deriving (Eq)

prettyLamHelper :: LamExpr n -> PrettyLamType -> Doc ann
prettyLamHelper lamExpr lamType = let
  rec :: LamExpr n -> Bool -> (Doc ann, EffectRow n, Block n)
  rec (LamExpr (LamBinder b ty _ effs') body') first =
    let thisOne = (if first then "" else line) <> p (b:>ty)
    in case inlineLastDeclBlock body' of
      Abs Empty (Atom (Lam next@(LamExpr (LamBinder _ _ arr' _) _)))
        | lamType == PrettyLam arr' ->
            let (binders', effs'', block) = rec next False
            in (thisOne <> binders', unsafeCoerceE (effs' <> effs''), unsafeCoerceE block)
      Abs Empty (Hof (For ann _ (Lam next)))
        | lamType == PrettyFor ann ->
            let (binders', effs'', block) = rec next False
            in (thisOne <> binders', unsafeCoerceE (effs' <> effs''), unsafeCoerceE block)
      _ -> (thisOne <> punctuation, unsafeCoerceE effs', unsafeCoerceE body')
        where punctuation = case lamType of
                PrettyFor _ -> "."
                PrettyLam PlainArrow -> "."
                PrettyLam arr -> " " <> p arr
  (binders, effs, body) = rec lamExpr True
  in prettyLam binders effs body

prettyLam :: Doc ann -> EffectRow n -> Block n -> Doc ann
prettyLam binders effs body =
  group $ group (nest 4 $ binders) <> group (nest 2 $ p body) <> lamAnnot
  where
    lamAnnot = case effs of
      Pure -> ""
      _ -> line <> "lam annotated with effects" <+> p effs

inlineLastDeclBlock :: Block n -> Abs (Nest Decl) Expr n
inlineLastDeclBlock (Block _ decls expr) = inlineLastDecl decls expr

inlineLastDecl :: Nest Decl n l -> Atom l -> Abs (Nest Decl) Expr n
inlineLastDecl Empty result = Abs Empty $ Atom result
inlineLastDecl (Nest (Let b (DeclBinding _ _ expr)) Empty) (Var v)
  | v == binderName b = Abs Empty expr
inlineLastDecl (Nest decl rest) result =
  case inlineLastDecl rest result of
   Abs decls' result' ->
     Abs (Nest decl decls') result'

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
    IxBound     b -> p b
    MiscBound   t -> p t
    SolverBound b -> p b
    PtrLitBound _ ptr -> p ptr
    TopFunBound _ f -> p f

instance Pretty (TopFunBinding n) where
  pretty = \case
    UnspecializedTopFun _ f -> p f
    SpecializedTopFun f -> p f
    SimpTopFun f -> p f
    FFITopFun  f -> p f

instance Pretty (SpecializationSpec n) where
  pretty (AppSpecialization f (Abs bs (ListE args))) =
    "Specialization" <+> p f <+> p bs <+> p args

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
    ClassBinding    classDef    -> pretty classDef
    InstanceBinding instanceDef -> pretty instanceDef
    MethodBinding className idx _ ->
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

instance Pretty (DataDefParams n) where
  pretty (DataDefParams ps ds) = p ps <+> p ds

instance Pretty (DataDefBinders n l) where
  pretty (DataDefBinders paramBs dictBs) = p paramBs <+> p dictBs

instance Pretty (DataDef n) where
  pretty (DataDef name bs cons) =
    "data" <+> p name <+> p bs <> prettyLines cons

instance Pretty (DataConDef n) where
  pretty (DataConDef name bs) =
    p name <+> ":" <+> p bs

instance Pretty (ClassDef n) where
  pretty (ClassDef classSourceName methodNames params superclasses methodTys) =
    "Class:" <+> pretty classSourceName <+> pretty methodNames
    <> indented (
         line <> "parameter biners:" <+> pretty params <>
         line <> "superclasses:" <+> pretty (superclassTypes superclasses) <>
         line <> "methods:" <+> pretty methodTys)

instance Pretty (InstanceDef n) where
  pretty (InstanceDef className bs params _) =
    "Instance" <+> p className <+> p bs <+> p params

instance Pretty (MethodType n) where
  pretty (MethodType _ ty) = pretty ty

deriving instance (forall c n. Pretty (v c n)) => Pretty (RecSubst v o)

instance Pretty (TopEnv n) where
  pretty (TopEnv defs rules cache ms) =
    prettyRecord [ ("Defs"          , p defs)
                 , ("Rules"         , p rules)
                 , ("Cache"         , p cache)
                 , ("Loaded modules", p ms)]

instance Pretty (CustomRules n) where
  pretty _ = "TODO: Rule printing"

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
  pretty block = pretty $ ensureNewline (sbText block) where
    -- Force the SourceBlock to end in a newline for echoing, even if
    -- it was terminated with EOF in the original program.
    ensureNewline t = case unsnoc t of
      Nothing -> t
      Just (_, '\n') -> t
      _ -> t `snoc` '\n'

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

instance Pretty (UTabLamExpr n) where pretty = prettyFromPrettyPrec
instance PrettyPrec (UTabLamExpr n) where
  prettyPrec (UTabLamExpr pat body) = atPrec LowestPrec $ align $
    "view" <> p pat <> "." <+> nest 2 (pLowest body)

instance Pretty (UPiExpr n) where pretty = prettyFromPrettyPrec
instance PrettyPrec (UPiExpr n) where
  prettyPrec (UPiExpr arr pat Pure ty) = atPrec LowestPrec $ align $
    p pat <+> pretty arr <+> pLowest ty
  prettyPrec (UPiExpr arr pat _ ty) = atPrec LowestPrec $ align $
    p pat <+> pretty arr <+> "{todo: pretty effects}" <+> pLowest ty

instance Pretty (UTabPiExpr n) where pretty = prettyFromPrettyPrec
instance PrettyPrec (UTabPiExpr n) where
  prettyPrec (UTabPiExpr pat ty) = atPrec LowestPrec $ align $
    p pat <+> "=>" <+> pLowest ty

instance Pretty (UDeclExpr n) where pretty = prettyFromPrettyPrec
instance PrettyPrec (UDeclExpr n) where
  prettyPrec (UDeclExpr decl body) = atPrec LowestPrec $ align $
    p decl <> hardline <> pLowest body

instance Pretty (UExpr' n) where pretty = prettyFromPrettyPrec
instance PrettyPrec (UExpr' n) where
  prettyPrec expr = case expr of
    UVar v -> atPrec ArgPrec $ p v
    ULam lam -> prettyPrec lam
    UTabLam lam -> prettyPrec lam
    UApp    f x -> atPrec AppPrec $ pAppArg (pApp f) [x]
    UTabApp f x -> atPrec AppPrec $ pArg f <> "." <> pArg x
    UFor dir (UForExpr binder body) ->
      atPrec LowestPrec $ kw <+> p binder <> "."
                             <+> nest 2 (pLowest body)
      where kw = case dir of Fwd -> "for"
                             Rev -> "rof"
    UPi piType -> prettyPrec piType
    UTabPi piType -> prettyPrec piType
    UDecl declExpr -> prettyPrec declExpr
    UHole -> atPrec ArgPrec "_"
    UTypeAnn v ty -> atPrec LowestPrec $
      group $ pApp v <> line <> ":" <+> pApp ty
    UTabCon xs -> atPrec ArgPrec $ p xs
    UPrimExpr prim -> prettyPrec prim
    UCase e alts -> atPrec LowestPrec $ "case" <+> p e <>
      nest 2 (prettyLines alts)
    ULabel name -> atPrec ArgPrec $ "&" <> p name
    ULabeledRow elems -> atPrec ArgPrec $ prettyUFieldRowElems (line <> "?") ": " elems
    URecord   elems -> atPrec ArgPrec $ prettyUFieldRowElems (line' <> ",") "=" elems
    URecordTy elems -> atPrec ArgPrec $ prettyUFieldRowElems (line <> "&") ": " elems
    UVariant labels label value -> prettyVariant labels label value
    UVariantTy items -> prettyExtLabeledItems items Nothing (line <> "|") ":"
    UVariantLift labels value -> prettyVariantLift labels value
    UNatLit   v -> atPrec ArgPrec $ p v
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
       (prettyLines (zip (toList $ fromNest bDataCons) dataCons))
  pretty (UInterface params superclasses methodTys interfaceName methodNames) =
     "interface" <+> p params <+> p superclasses <+> p interfaceName
         <> hardline <> foldMap (<>hardline) methods
     where
       methods = [ hsep (case e of Left e' -> p <$> e'; Right e' -> p <$> e') <+>
                   p (UAnnBinder b (unsafeCoerceE ty))
                 | (b, UMethodType e ty) <- zip (toList $ fromNest methodNames) methodTys]
  pretty (UInstance className bs params methods (RightB UnitB)) =
    "instance" <+> prettyBinderNest bs <+> p className <+> spaced params <+>
       prettyLines methods
  pretty (UInstance bs className params methods (LeftB v)) =
    "named-instance" <+> p v <+> ":" <+> p bs <+> p className <+> p params
        <> prettyLines methods
  pretty (UEffectDecl opTys effName opNames) =
    "effect" <+> p effName <> hardline <> foldMap (<>hardline) ops
    where ops = [ p pol <+> p (UAnnBinder b (unsafeCoerceE ty))
                 | (b, UEffectOpType pol ty) <- zip (toList $ fromNest opNames) opTys]
  pretty (UHandlerDecl effName tyArgs _retEff retTy opDefs name) =
    "handler" <+> p name <+> "of" <+> p effName <+> prettyBinderNest tyArgs
    <+> ":" <+> "{todo: pretty effects}" <+> p retTy <> hardline
    <> foldMap (<>hardline) ops
    where ops = [ p rp <+> p n <+> "=" <+> p body
                 | UEffectOpDef n rp body <- opDefs ]

instance Pretty UResumePolicy where
  pretty UNoResume = "jmp"
  pretty ULinearResume = "def"
  pretty UAnyResume = "ctl"
  pretty UReturn = ""

prettyBinderNest :: PrettyB b => Nest b n l -> Doc ann
prettyBinderNest bs = nest 6 $ line' <> (sep $ map p $ fromNest bs)

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

dotted :: (Foldable f, Pretty a) => f a -> Doc ann
dotted xs = fold $ punctuate "." $ map p $ toList xs

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
       "lambda dicts:"   <+> p (lambdaDicts scs) <> hardline
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
  pretty (ImpBlock Empty []) = mempty
  pretty (ImpBlock Empty expr) = group $ line <> pLowest expr
  pretty (ImpBlock decls []) = prettyLines $ fromNest decls
  pretty (ImpBlock decls expr) = prettyLines decls' <> hardline <> pLowest expr
    where decls' = fromNest decls

instance Pretty (IBinder n l)  where
  pretty (IBinder b ty) = p b <+> ":" <+> p ty

instance Pretty (ImpInstr n)  where
  pretty (IFor a n (Abs i block)) = forStr a <+> p i <+> "<" <+> p n <>
                                      nest 4 (p block)
  pretty (IWhile body) = "while" <+> nest 2 (p body)
  pretty (ICond predicate cons alt) =
    "if" <+> p predicate <+> "then" <> nest 2 (p cons) <>
    hardline <> "else" <> nest 2 (p alt)
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
  pretty (IVectorBroadcast v _) = "vbroadcast" <+> p v
  pretty (IVectorIota _) = "viota"

instance Pretty BaseType where pretty = prettyFromPrettyPrec
instance PrettyPrec BaseType where
  prettyPrec b = case b of
    Scalar sb -> prettyPrec sb
    Vector shape sb -> atPrec ArgPrec $ encloseSep "<" ">" "x" $ (p <$> shape) ++ [p sb]
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
    -- TODO: we currently use Word32 for `Nat` but we should move to a new type,
    -- at least at the user-visible level
    Word32Type  -> "Nat"
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
    Fin n -> atPrec AppPrec $ "Fin" <+> pArg n
    RefType (Just h) a -> atPrec AppPrec $ pAppArg "Ref" [h, a]
    RefType Nothing a  -> atPrec AppPrec $ pAppArg "Ref" [a]
    TypeKind -> atPrec ArgPrec "Type"
    EffectRowKind -> atPrec ArgPrec "EffKind"
    LabeledRowKindTC -> atPrec ArgPrec "Fields"
    LabelType -> atPrec ArgPrec "Label"

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
  FinVal n i -> atPrec LowestPrec $ pApp i <> "@" <> pApp (Fin n)
  BaseTypeRef ptr -> atPrec ArgPrec $ "Ref" <+> pApp ptr
  TabRef tab -> atPrec ArgPrec $ "Ref" <+> pApp tab
  ConRef conRef -> atPrec AppPrec $ "Ref" <+> pApp conRef
  RecordRef _ -> atPrec ArgPrec "Record ref"  -- TODO
  LabelCon name -> atPrec ArgPrec $ "##" <> p name
  ExplicitDict _ _ -> atPrec ArgPrec $ "ExplicitDict"
  DictHole _ e -> atPrec LowestPrec $ "synthesize" <+> pApp e

instance PrettyPrec e => Pretty (PrimOp e) where pretty = prettyFromPrettyPrec
instance PrettyPrec e => PrettyPrec (PrimOp e) where
  prettyPrec op = case op of
    TabCon _ es -> atPrec ArgPrec $ list $ pApp <$> es
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
    AllocDest ty -> atPrec LowestPrec $ "alloc" <+> pApp ty
    Place r v -> atPrec LowestPrec $ pApp r <+> "r:=" <+> pApp v
    Freeze r  -> atPrec LowestPrec $ "freeze" <+> pApp r
    VectorBroadcast v vty -> atPrec LowestPrec $ "vbroadcast" <+> pApp v <+> pApp vty
    VectorIota vty -> atPrec LowestPrec $ "viota" <+> pApp vty
    VectorSubref ref i _ -> atPrec LowestPrec $ "vrefslice" <+> pApp ref <+> pApp i
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
    For ann _ lam -> atPrec LowestPrec $ forStr ann <+> pArg lam
    _ -> prettyExprDefault $ HofExpr hof

instance PrettyPrec Direction where
  prettyPrec d = atPrec ArgPrec $ case d of
    Fwd -> "fwd"
    Rev -> "rev"

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
  -- print in decimal rather than hex because we use this for the `Nat` alias
  prettyPrec (Word32Lit  x) = atPrec ArgPrec $ p x
  prettyPrec (Word64Lit  x) = atPrec ArgPrec $ p $ "0x" ++ showHex x ""
  prettyPrec (PtrLit (PtrLitVal ty x)) =
    atPrec ArgPrec $ "Ptr" <+> p ty <+> p (show x)
  prettyPrec (PtrLit (PtrSnapshot _ _)) = atPrec ArgPrec "<ptr snapshot>"

instance Pretty CallingConvention where
  pretty = p . show

instance Pretty LetAnn where
  pretty ann = case ann of
    PlainLet      -> ""
    NoInlineLet   -> "%noinline"

instance PrettyPrec () where prettyPrec = atPrec ArgPrec . pretty

instance Pretty RWS where
  pretty eff = case eff of
    Reader -> "Read"
    Writer -> "Accum"
    State  -> "State"

printLitBlock :: Pretty block => Bool -> block -> Result -> String
printLitBlock isatty block result = pprint block ++ printResult isatty result

printResult :: Bool -> Result -> String
printResult isatty (Result outs errs) =
  concat (map printOutput outs) ++ case errs of
    Success ()  -> ""
    Failure err -> addColor isatty Red $ addPrefix ">" $ pprint err
  where
    printOutput :: Output -> String
    printOutput out = addPrefix (addColor isatty Cyan ">") $ pprint $ out

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
