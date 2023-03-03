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
import Control.Monad (void)
import Data.Foldable (toList, fold)
import Data.Functor ((<&>))
import qualified Data.ByteString.Lazy.Char8 as B
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

import ConcreteSyntax
import Err
import LabeledItems
import IRVariants
import Name
import Occurrence (Count (Bounded), UsageInfo (..))
import Occurrence qualified as Occ
import Types.Core
import Types.Imp
import Types.Misc
import Types.Primitives
import Types.Source
import Util (restructure, Tree (..))

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

pprintCanonicalized :: (HoistableE e, RenameE e, PrettyE e) => e n -> String
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

instance IRRep r => Pretty (Block r n) where
  pretty (Block _ decls expr) = prettyBlock decls expr
instance IRRep r => PrettyPrec (Block r n) where
  prettyPrec (Block _ decls expr) = atPrec LowestPrec $ prettyBlock decls expr

prettyBlock :: (IRRep r, PrettyPrec (e l)) => Nest (Decl r) n l -> e l -> Doc ann
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

instance IRRep r => Pretty (Expr r n) where pretty = prettyFromPrettyPrec
instance IRRep r => PrettyPrec (Expr r n) where
  prettyPrec (Atom x) = prettyPrec x
  prettyPrec (App f xs) = atPrec AppPrec $ pApp f <+> spaced (toList xs)
  prettyPrec (TopApp f xs) = atPrec AppPrec $ pApp f <+> spaced (toList xs)
  prettyPrec (TabApp f xs) = atPrec AppPrec $ pApp f <> "." <> dotted (toList xs)
  prettyPrec (Hof hof) = prettyPrec hof
  prettyPrec (Case e alts _ effs) = prettyPrecCase "case" e alts effs
  prettyPrec (TabCon _ _ es) = atPrec ArgPrec $ list $ pApp <$> es
  prettyPrec (UserEffectOp op) = prettyPrec op
  prettyPrec (RecordOp op) = prettyPrec op
  prettyPrec (PrimOp op) = prettyPrec op
  prettyPrec (DAMOp op) = prettyPrec op
  prettyPrec (ProjMethod d i) = atPrec AppPrec $ "projectMethod" <+> p d <+> p i
  prettyPrec (RefOp ref eff) = atPrec LowestPrec case eff of
    MAsk        -> "ask" <+> pApp ref
    MExtend _ x -> "extend" <+> pApp ref <+> pApp x
    MGet        -> "get" <+> pApp ref
    MPut x      -> pApp ref <+> ":=" <+> pApp x
    IndexRef i  -> pApp ref <+> "!" <+> pApp i
    ProjRef  i  -> "proj" <+> pApp ref <+> p i

instance IRRep r => Pretty (RecordOp (Atom r n)) where pretty = prettyFromPrettyPrec
instance IRRep r => PrettyPrec (RecordOp (Atom r n)) where
  prettyPrec = \case
    RecordCons items rest -> atPrec LowestPrec $ "RecordCons" <+> pArg items <+> pArg rest
    RecordConsDynamic lab val rec -> atPrec LowestPrec $
      "RecordConsDynamic" <+> pArg lab <+> pArg val <+> pArg rec
    RecordSplit fields val -> atPrec AppPrec $
      "RecordSplit" <+> pArg fields <+> pArg val
    op -> atPrec ArgPrec $ p (show  op)

instance Pretty (UserEffectOp n) where pretty = prettyFromPrettyPrec
instance PrettyPrec (UserEffectOp n) where
  prettyPrec (Handle v args body) = atPrec LowestPrec $ p v <+> p args <+> prettyLam "\\_." body
  prettyPrec _ = error "not implemented"

prettyPrecCase :: IRRep r => Doc ann -> Atom r n -> [Alt r n] -> EffectRow r n -> DocPrec ann
prettyPrecCase name e alts effs = atPrec LowestPrec $
  name <+> pApp e <+> "of" <>
  nest 2 (foldMap (\alt -> hardline <> prettyAlt alt) alts
          <> effectLine effs)
  where
    effectLine :: IRRep r => EffectRow r n -> Doc ann
    effectLine Pure = ""
    effectLine row = hardline <> "case annotated with effects" <+> p row

prettyAlt :: IRRep r => Alt r n -> Doc ann
prettyAlt (Abs b body) = prettyBinderNoAnn b <+> "->" <> nest 2 (p body)

prettyBinderNoAnn :: Binder r n l -> Doc ann
prettyBinderNoAnn (b:>_) = p b

instance (IRRep r, PrettyPrecE e) => Pretty     (Abs (Binder r) e n) where pretty = prettyFromPrettyPrec
instance (IRRep r, PrettyPrecE e) => PrettyPrec (Abs (Binder r) e n) where
  prettyPrec (Abs binder body) = atPrec LowestPrec $ "\\" <> p binder <> "." <> pLowest body

instance IRRep r => Pretty (DeclBinding r n) where
  pretty (DeclBinding ann ty expr) =
    "Decl" <> p ann <> indented (               "type: " <+> p ty
                                 <> hardline <> "value:" <+> p expr)

instance IRRep r => Pretty (Decl r n l) where
  pretty (Let b (DeclBinding ann ty rhs)) =
    align $ annDoc <> p (b:>ty) <+> "=" <> (nest 2 $ group $ line <> pLowest rhs)
    where annDoc = case ann of NoInlineLet -> pretty ann <> " "; _ -> pretty ann

instance IRRep r => Pretty (NaryPiType r n) where
  pretty (NaryPiType bs effs resultTy) =
    (spaced $ fromNest $ bs) <+> "->" <+> "{" <> p effs <> "}" <+> p resultTy

instance IRRep r => Pretty (LamExpr r n) where pretty = prettyFromPrettyPrec
instance IRRep r => PrettyPrec (LamExpr r n) where
  prettyPrec (LamExpr bs body) = atPrec LowestPrec $ prettyLam (p bs) body

instance IRRep r => Pretty (DestLamExpr r n) where pretty = prettyFromPrettyPrec
instance IRRep r => PrettyPrec (DestLamExpr r n) where
  prettyPrec (DestLamExpr bs body) = atPrec LowestPrec $ prettyLam (p bs) body

instance IRRep r => Pretty (IxType r n) where
  pretty (IxType ty dict) = parens $ "IxType" <+> pretty ty <> prettyIxDict dict

instance Pretty (DictExpr n) where
  pretty d = case d of
    InstanceDict name args -> "Instance" <+> p name <+> p args
    InstantiatedGiven v args -> "Given" <+> p v <+> p (toList args)
    SuperclassProj d' i -> "SuperclassProj" <+> p d' <+> p i
    IxFin n -> "Ix (Fin" <+> p n <> ")"
    DataData a -> "Data " <+> p a

instance IRRep r => Pretty (IxDict r n) where
  pretty = \case
    IxDictAtom x -> p x
    IxDictRawFin n  -> "Ix (RawFin " <> p n <> ")"
    IxDictSpecialized _ d xs -> p d <+> p xs

instance Pretty (DictType n) where
  pretty (DictType classSourceName _ params) =
    p classSourceName <+> spaced params

instance IRRep r => Pretty (DepPairType r n) where pretty = prettyFromPrettyPrec
instance IRRep r => PrettyPrec (DepPairType r n) where
  prettyPrec (DepPairType b rhs) =
    atPrec ArgPrec $ align $ group $ parens $ p b <+> "&>" <+> p rhs

instance Pretty (EffectOpType n) where
  pretty (EffectOpType pol ty) = "[" <+> p pol <+> ":" <+> p ty <+> "]"

instance IRRep r => Pretty (Atom r n) where pretty = prettyFromPrettyPrec
instance IRRep r => PrettyPrec (Atom r n) where
  prettyPrec atom = case atom of
    Var v -> atPrec ArgPrec $ p v
    Lam lam arr _ -> atPrec LowestPrec $ "\\" <> prettyLamHelper arr lam PrettyLam
    Pi piType -> atPrec LowestPrec $ align $ p piType
    TabPi piType -> atPrec LowestPrec $ align $ p piType
    DepPairTy ty -> prettyPrec ty
    DepPair x y _ -> atPrec ArgPrec $ align $ group $
        parens $ p x <+> ",>" <+> p y
    TC  e -> prettyPrec e
    Con e -> prettyPrec e
    Eff e -> atPrec ArgPrec $ p e
    PtrVar v -> atPrec ArgPrec $ p v
    DictCon d -> atPrec LowestPrec $ p d
    DictTy  t -> atPrec LowestPrec $ p t
    RepValAtom x -> atPrec LowestPrec $ pretty x
    ProjectElt idxs v ->
      atPrec LowestPrec $ "ProjectElt" <+> p idxs <+> p v
    NewtypeCon con x -> prettyPrecNewtype con x
    NewtypeTyCon con -> prettyPrec con
    SimpInCore x -> prettyPrec x
    DictHole _ e -> atPrec LowestPrec $ "synthesize" <+> pApp e

instance Pretty (SimpInCore n) where pretty = prettyFromPrettyPrec
instance PrettyPrec (SimpInCore n) where
  prettyPrec = \case
    LiftSimp ty x -> atPrec ArgPrec $ "<embedded-simp-atom " <+> p x <+> " : " <+> p ty <+> ">"
    LiftSimpFun ty x -> atPrec ArgPrec $ "<embedded-simp-function " <+> p x <+> " : " <+> p ty <+> ">"
    ACase e alts _ -> atPrec AppPrec $ "acase" <+> p e <+> p alts
    TabLam _ lamExpr -> atPrec AppPrec $ "tablam" <+> p lamExpr

instance IRRep r => Pretty (RepVal r n) where
  pretty (RepVal ty tree) = "<RepVal " <+> p tree <+> ":" <+> p ty <> ">"

instance Pretty a => Pretty (Tree a) where
  pretty = \case
    Leaf x -> pretty x
    Branch xs -> pretty xs

instance Pretty Projection where
  pretty = \case
    UnwrapNewtype -> "u"
    ProjectProduct i -> p i

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

forStr :: ForAnn -> Doc ann
forStr Fwd = "for"
forStr Rev = "rof"

instance Pretty (PiType n) where
  pretty (PiType (b:>ty) arr eff body) = let
    prettyBinder = prettyBinderHelper (b:>ty) (PairE eff body)
    prettyBody = case body of
      Pi subpi -> pretty subpi
      _ -> pLowest body
    prettyEff = case eff of
      Pure -> space
      _    -> space <> pretty eff <> space
    in prettyBinder <> (group $ line <> p arr <> prettyEff <> prettyBody)

instance IRRep r => Pretty (TabPiType r n) where
  pretty (TabPiType (b :> IxType ty dict) body) = let
    prettyBody = case body of
      Pi subpi -> pretty subpi
      _ -> pLowest body
    prettyBinder = case dict of
      IxDictRawFin n -> if binderName b `isFreeIn` body
        then parens $ p b <> ":" <> prettyTy
        else prettyTy
        where prettyTy = "RawFin" <+> p n
      _ -> prettyBinderHelper (b:>ty) body
    in prettyBinder <> prettyIxDict dict <> (group $ line <> "=>" <+> prettyBody)

-- A helper to let us turn dict printing on and off.  We mostly want it off to
-- reduce clutter in prints and error messages, but when debugging synthesis we
-- want it on.
prettyIxDict :: IRRep r => IxDict r n -> Doc ann
prettyIxDict dict = if False then " " <> p dict else mempty

prettyBinderHelper :: IRRep r => HoistableE e => Binder r n l -> e l -> Doc ann
prettyBinderHelper (b:>ty) body =
  if binderName b `isFreeIn` body
    then parens $ p (b:>ty)
    else p ty

data PrettyLamType = PrettyLam | PrettyFor ForAnn deriving (Eq)

prettyLamHelper :: IRRep r => Arrow -> LamExpr r n -> PrettyLamType -> Doc ann
prettyLamHelper arr' lamExpr lamType = uncurry prettyLam $ rec arr' lamExpr True
 where
  wrap :: Arrow -> Doc ann -> Doc ann
  wrap arr arg = case lamType of
    PrettyLam -> case arr of
      PlainArrow    -> arg
      LinArrow      -> arg
      ImplicitArrow -> "{" <> arg <> "}"
      ClassArrow    -> "[" <> arg <> "]"
    PrettyFor _ -> arg
  rec :: IRRep r => Arrow -> LamExpr r n -> Bool -> (Doc ann, Block r n)
  rec arr lam first = case lam of
    UnaryLamExpr (b:>ty) body' -> do
      let thisOne = (if first then "" else line) <> wrap arr (p (b:>ty))
      case inlineLastDeclBlock body' of
        Abs Empty (Atom (Lam next arrNext _)) ->
          let (binders', block) = rec arrNext next False
          in (thisOne <> binders', unsafeCoerceE block)
        Abs Empty (Hof (For ann dict next))
          | lamType == PrettyFor ann ->
              let (binders', block) = rec PlainArrow next False
              in (thisOne <> prettyIxDict dict <> binders', unsafeCoerceE block)
        _ -> (thisOne <> ".", unsafeCoerceE body')
    _ -> error "expected a unary lambda expression"

prettyLam :: Pretty a => Doc ann -> a -> Doc ann
prettyLam binders body = group $ group (nest 4 $ binders) <> group (nest 2 $ p body)

inlineLastDeclBlock :: IRRep r => Block r n -> Abs (Nest (Decl r)) (Expr r) n
inlineLastDeclBlock (Block _ decls expr) = inlineLastDecl decls expr

inlineLastDecl :: IRRep r => Nest (Decl r) n l -> Atom r l -> Abs (Nest (Decl r)) (Expr r) n
inlineLastDecl Empty result = Abs Empty $ Atom result
inlineLastDecl (Nest (Let b (DeclBinding _ _ expr)) Empty) (Var v)
  | v == binderName b = Abs Empty expr
inlineLastDecl (Nest decl rest) result =
  case inlineLastDecl rest result of
   Abs decls' result' ->
     Abs (Nest decl decls') result'

instance IRRep r => Pretty (EffectRow r n) where
  pretty (EffectRow effs t) =
    braces $ hsep (punctuate "," (map p (eSetToList effs))) <> p t

instance IRRep r => Pretty (EffectRowTail r n) where
  pretty = \case
    NoTail -> mempty
    EffectRowTail v  -> "|" <> p v

instance IRRep r => Pretty (Effect r n) where
  pretty eff = case eff of
    RWSEffect rws h -> p rws <+> p h
    ExceptionEffect -> "Except"
    IOEffect        -> "IO"
    UserEffect name -> p name
    InitEffect      -> "Init"

instance Pretty (UEffect n) where
  pretty eff = case eff of
    URWSEffect rws h -> p rws <+> p h
    UExceptionEffect -> "Except"
    UIOEffect        -> "IO"
    UUserEffect name -> p name
    UInitEffect      -> "Init"

instance PrettyPrec (Name s n) where prettyPrec = atPrec ArgPrec . pretty

instance IRRep r => Pretty (AtomBinding r n) where
  pretty binding = case binding of
    LetBound    b -> p b
    MiscBound   t -> p t
    SolverBound b -> p b
    FFIFunBound s _ -> p s
    NoinlineFun ty _ -> "Top function with type: " <+> p ty
    TopDataBound (RepVal ty _) -> "Top data with type: " <+> p ty

instance Pretty (SpecializationSpec n) where
  pretty (AppSpecialization f (Abs bs (ListE args))) =
    "Specialization" <+> p f <+> p bs <+> p args

instance Pretty IxMethod where
  pretty method = p $ show method

instance Pretty (SolverBinding n) where
  pretty (InfVarBound  ty _) = "Inference variable of type:" <+> p ty
  pretty (SkolemBound  ty  ) = "Skolem variable of type:"    <+> p ty

instance Pretty (Binding c n) where
  pretty b = case b of
    -- using `unsafeCoerceIRE` here because otherwise we don't have `IRRep`
    -- TODO: can we avoid printing needing IRRep? Presumably it's related to
    -- manipulating sets or something, which relies on Eq/Ord, which relies on renaming.
    AtomNameBinding   info -> "Atom name:" <+> pretty (unsafeCoerceIRE @CoreIR info)
    DataDefBinding dataDef _ -> pretty dataDef
    TyConBinding   dataDefName e -> "Type constructor:" <+> pretty dataDefName <+> (parens $ "atom:" <+> p e)
    DataConBinding    dataDefName idx e -> "Data constructor:" <+> pretty dataDefName <+> "Constructor index:" <+> pretty idx <+> (parens $ "atom:" <+> p e)
    ClassBinding    classDef -> pretty classDef
    InstanceBinding instanceDef -> pretty instanceDef
    MethodBinding className idx _ -> "Method" <+> pretty idx <+> "of" <+> pretty className
    TopFunBinding f -> pretty f
    FunObjCodeBinding _ _ -> "<object file>"
    ModuleBinding  _ -> "<module>"
    PtrBinding   _ _ -> "<ptr>"
    -- TODO(alex): do something actually useful here
    EffectBinding _ -> "<effect-binding>"
    HandlerBinding _ -> "<handler-binding>"
    EffectOpBinding _ -> "<effect-op-binding>"
    SpecializedDictBinding _ -> "<specialized-dict-binding>"
    ImpNameBinding ty -> "Imp name of type: " <+> p ty

instance Pretty (Module n) where
  pretty m = prettyRecord
    [ ("moduleSourceName"     , p $ moduleSourceName m)
    , ("moduleDirectDeps"     , p $ S.toList $ moduleDirectDeps m)
    , ("moduleTransDeps"      , p $ S.toList $ moduleTransDeps m)
    , ("moduleExports"        , p $ moduleExports m)
    , ("moduleSynthCandidates", p $ moduleSynthCandidates m) ]

instance Pretty (DataDefParams n) where
  pretty (DataDefParams bs) = hsep $ map bracketize bs where
    bracketize (PlainArrow, x) = p x
    bracketize (ClassArrow, x) = "[" <> p x <> "]"
    bracketize (ImplicitArrow, x) = "{" <> p x <> "}"
    bracketize (LinArrow, x) = p x

instance Pretty (DataDef n) where
  pretty (DataDef name bs cons) =
    "data" <+> p name <+> (spaced $ fromNest bs) <> prettyLines cons

instance Pretty (DataConDef n) where
  pretty (DataConDef name _ repTy _) =
    p name <+> ":" <+> p repTy

instance Pretty (ClassDef n) where
  pretty (ClassDef classSourceName methodNames params superclasses methodTys) =
    "Class:" <+> pretty classSourceName <+> pretty methodNames
    <> indented (
         line <> "parameter biners:" <+> pretty params <>
         line <> "superclasses:" <+> pretty (superclassTypes superclasses) <>
         line <> "methods:" <+> pretty methodTys)

instance Pretty ParamRole where
  pretty r = p (show r)

instance Pretty (RolePiBinder n l) where
  pretty (RolePiBinder b ty _ _) = p (b:>ty)

instance Pretty (InstanceDef n) where
  pretty (InstanceDef className bs params _) =
    "Instance" <+> p className <+> p bs <+> p params

instance Pretty (MethodType n) where
  pretty (MethodType _ ty) = pretty ty

deriving instance (forall c n. Pretty (v c n)) => Pretty (RecSubst v o)

instance Pretty (TopEnv n) where
  pretty (TopEnv defs rules cache _ _) =
    prettyRecord [ ("Defs"          , p defs)
                 , ("Rules"         , p rules)
                 , ("Cache"         , p cache) ]

instance Pretty (CustomRules n) where
  pretty _ = "TODO: Rule printing"

instance Pretty (ImportStatus n) where
  pretty imports = pretty $ S.toList $ directImports imports

instance Pretty (ModuleEnv n) where
  pretty (ModuleEnv imports sm sc) =
    prettyRecord [ ("Imports"         , p imports)
                 , ("Source map"      , p sm)
                 , ("Synth candidates", p sc) ]

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
    (case stats of
       Just (runs, _) ->
         "\t" <> parens ("based on" <+> p runs <+> plural "run" "runs" runs)
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

instance Pretty (UBinder c n l) where pretty = prettyFromPrettyPrec
instance PrettyPrec (UBinder c n l) where
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

instance Pretty (SourceOrInternalName c n) where
  pretty (SourceOrInternalName sn) = p sn

instance Pretty (ULamExpr n) where pretty = prettyFromPrettyPrec
instance PrettyPrec (ULamExpr n) where
  prettyPrec (ULamExpr arr pat body) = atPrec LowestPrec $ align $
    "\\" <> p pat <> punctuation <+> nest 2 (pLowest body)
    where punctuation = case arr of
                          PlainArrow -> "."
                          _          -> " " <> p arr
instance Pretty (UPiExpr n) where pretty = prettyFromPrettyPrec
instance PrettyPrec (UPiExpr n) where
  prettyPrec (UPiExpr arr pat UPure ty) = atPrec LowestPrec $ align $
    p pat <+> pretty arr <+> pLowest ty
  prettyPrec (UPiExpr arr pat eff ty) = atPrec LowestPrec $ align $
    p pat <+> pretty arr <+> p eff <+> pLowest ty

instance Pretty (UTabPiExpr n) where pretty = prettyFromPrettyPrec
instance PrettyPrec (UTabPiExpr n) where
  prettyPrec (UTabPiExpr pat ty) = atPrec LowestPrec $ align $
    p pat <+> "=>" <+> pLowest ty

instance Pretty (UDepPairType n) where pretty = prettyFromPrettyPrec
instance PrettyPrec (UDepPairType n) where
  prettyPrec (UDepPairType pat ty) = atPrec LowestPrec $ align $
    p pat <+> "&>" <+> pLowest ty

instance Pretty (UDeclExpr n) where pretty = prettyFromPrettyPrec
instance PrettyPrec (UDeclExpr n) where
  prettyPrec (UDeclExpr decl body) = atPrec LowestPrec $ align $
    p decl <> hardline <> pLowest body

instance Pretty (UExpr' n) where pretty = prettyFromPrettyPrec
instance PrettyPrec (UExpr' n) where
  prettyPrec expr = case expr of
    UVar v -> atPrec ArgPrec $ p v
    ULam lam -> prettyPrec lam
    UApp    f x -> atPrec AppPrec $ pAppArg (pApp f) [x]
    UTabApp f x -> atPrec AppPrec $ pArg f <> "." <> pArg x
    UFor dir (UForExpr binder body) ->
      atPrec LowestPrec $ kw <+> p binder <> "."
                             <+> nest 2 (pLowest body)
      where kw = case dir of Fwd -> "for"
                             Rev -> "rof"
    UPi piType -> prettyPrec piType
    UTabPi piType -> prettyPrec piType
    UDepPairTy depPairType -> prettyPrec depPairType
    UDepPair lhs rhs -> atPrec ArgPrec $ parens $
      p lhs <+> ",>" <+> p rhs
    UDecl declExpr -> prettyPrec declExpr
    UHole -> atPrec ArgPrec "_"
    UTypeAnn v ty -> atPrec LowestPrec $
      group $ pApp v <> line <> ":" <+> pApp ty
    UTabCon xs -> atPrec ArgPrec $ p xs
    UPrim prim xs -> atPrec AppPrec $ p (show prim) <+> p xs
    UCase e alts -> atPrec LowestPrec $ "case" <+> p e <>
      nest 2 (prettyLines alts)
    ULabel name -> atPrec ArgPrec $ "&" <> p name
    ULabeledRow elems -> atPrec ArgPrec $ prettyUFieldRowElems (line <> "?") ": " elems
    UFieldAccess x (WithSrc _ f) -> atPrec AppPrec $ p x <> "~" <> p f
    URecord   elems -> atPrec ArgPrec $ prettyUFieldRowElems (line' <> ",") "=" elems
    URecordTy elems -> atPrec ArgPrec $ prettyUFieldRowElems (line <> "&") ": " elems
    UNatLit   v -> atPrec ArgPrec $ p v
    UIntLit   v -> atPrec ArgPrec $ p v
    UFloatLit v -> atPrec ArgPrec $ p v

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
  pretty (UDataDefDecl (UDataDef nm bs dataCons) bTyCon bDataCons) =
    "data" <+> p bTyCon <+> p nm <+> spaced (fromNest bs) <+> "where" <> nest 2
       (prettyLines (zip (toList $ fromNest bDataCons) dataCons))
  pretty (UStructDecl (UStructDef nm bs fields) bTyCon) =
    "struct" <+> p bTyCon <+> p nm <+> spaced (fromNest bs) <+> "where" <> nest 2
       (prettyLines fields)
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
  pretty (UHandlerDecl effName bodyTyArg tyArgs retEff retTy opDefs name) =
    "handler" <+> p name <+> "of" <+> p effName <+> p bodyTyArg <+> prettyBinderNest tyArgs
    <+> ":" <+> p retEff <+> p retTy <> hardline
    <> foldMap ((<>hardline) . p) opDefs

instance Pretty (UEffectOpDef n) where
  pretty (UEffectOpDef rp n body) = p rp <+> p n <+> "=" <+> p body
  pretty (UReturnOpDef body) = "return =" <+> p body

instance Pretty UResumePolicy where
  pretty UNoResume = "jmp"
  pretty ULinearResume = "def"
  pretty UAnyResume = "ctl"

instance Pretty (UEffectRow n) where
  pretty (UEffectRow x Nothing) = encloseSep "<" ">" "," $ (p <$> toList x)
  pretty (UEffectRow x (Just y)) = "{" <> (hsep $ punctuate "," (p <$> toList x)) <+> "|" <+> p y <> "}"

prettyBinderNest :: PrettyB b => Nest b n l -> Doc ann
prettyBinderNest bs = nest 6 $ line' <> (sep $ map p $ fromNest bs)

instance Pretty (UDataDefTrail n) where
  pretty (UDataDefTrail bs) = p $ fromNest bs

instance Pretty (UPatAnnArrow n l) where
  pretty (UPatAnnArrow b arr) = p b <> ":" <> p arr

instance Pretty (UAnnBinder c n l) where
  pretty (UAnnBinder b ty) = p b <> ":" <> p ty

instance Pretty (UAnnBinderArrow c n l) where
  pretty (UAnnBinderArrow b ty PlainArrow) = p b <> ":" <> p ty
  pretty (UAnnBinderArrow b ty ClassArrow) = "[" <> p b <> ":" <> p ty <> "]"
  pretty (UAnnBinderArrow b ty ImplicitArrow) = "{" <> p b <> ":" <> p ty <> "}"
  pretty (UAnnBinderArrow b ty LinArrow) = p b <> ":" <> p ty

instance Pretty (UMethodDef n) where
  pretty (UMethodDef b rhs) = p b <+> "=" <+> p rhs

instance Pretty (UPat' n l) where pretty = prettyFromPrettyPrec
instance PrettyPrec (UPat' n l) where
  prettyPrec pat = case pat of
    UPatBinder x -> atPrec ArgPrec $ p x
    UPatPair (PairB x y) -> atPrec ArgPrec $ parens $ p x <> ", " <> p y
    UPatDepPair (PairB x y) -> atPrec ArgPrec $ parens $ p x <> ",> " <> p y
    UPatUnit UnitB -> atPrec ArgPrec $ "()"
    UPatCon con pats -> atPrec AppPrec $ parens $ p con <+> spaced (fromNest pats)
    UPatRecord pats -> atPrec ArgPrec $ prettyUFieldRowPat "," "=" pats
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
  pretty (EnvFrag bindings) = p bindings

instance Pretty (Cache n) where
  pretty (Cache _ _ _ _ _ _) = "<cache>" -- TODO

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
  pretty (IPtrVar v _) = p v

instance PrettyPrec (IExpr n) where prettyPrec = atPrec ArgPrec . pretty

instance Pretty (ImpDecl n l) where
  pretty (ImpLet Empty instr) = p instr
  pretty (ImpLet (Nest b Empty) instr) = p b <+> "=" <+> p instr
  pretty (ImpLet bs instr) = p bs <+> "=" <+> p instr

instance Pretty IFunType where
  pretty (IFunType cc argTys retTys) =
    "Fun" <+> p cc <+> p argTys <+> "->" <+> p retTys

instance Pretty (TopFunDef n) where
  pretty = \case
    Specialization       s -> p s
    LinearizationPrimal  _ -> "<linearization primal>"
    LinearizationTangent _ -> "<linearization tangent>"

instance Pretty (TopFun n) where
  pretty = \case
    DexTopFun def ty simp lowering ->
      "Top-level Function"
         <> hardline <+> "definition:" <+> pretty def
         <> hardline <+> "type:"       <+> pretty ty
         <> hardline <+> "simplified:" <+> pretty simp
         <> hardline <+> "lowering:" <+> pretty lowering
    FFITopFun f _ -> p f

instance Pretty a => Pretty (EvalStatus a) where
  pretty = \case
    Waiting    -> "<waiting>"
    Running    -> "<running>"
    Finished a -> pretty a

instance Pretty (ImpFunction n) where
  pretty (ImpFunction (IFunType cc _ _) (Abs bs body)) =
    "impfun" <+> p cc <+> prettyBinderNest bs
    <> nest 2 (hardline <> p body) <> hardline

instance Pretty (ImpBlock n)  where
  pretty (ImpBlock Empty []) = mempty
  pretty (ImpBlock Empty expr) = group $ line <> pLowest expr
  pretty (ImpBlock decls []) = prettyLines $ fromNest decls
  pretty (ImpBlock decls expr) = prettyLines decls' <> hardline <> pLowest expr
    where decls' = fromNest decls

instance Pretty (IBinder n l)  where
  pretty (IBinder b ty) = p b <+> ":" <+> p ty

instance Pretty (ImpInstr n)  where
  pretty = \case
    IFor a n (Abs i block) -> forStr a <+> p i <+> "<" <+> p n <>
                                      nest 4 (p block)
    IWhile body -> "while" <+> nest 2 (p body)
    ICond predicate cons alt ->
       "if" <+> p predicate <+> "then" <> nest 2 (p cons) <>
       hardline <> "else" <> nest 2 (p alt)
    IQueryParallelism f s -> "queryParallelism" <+> p f <+> p s
    ILaunch f size args ->
       "launch" <+> p f <+> p size <+> spaced args
    ICastOp t x    -> "cast"  <+> p x <+> "to" <+> p t
    IBitcastOp t x -> "bitcast"  <+> p x <+> "to" <+> p t
    Store dest val -> "store" <+> p dest <+> p val
    Alloc _ t s    -> "alloc" <+> p t <> "[" <> sizeStr s <> "]"
    StackAlloc t s -> "alloca" <+> p t <> "[" <> sizeStr s <> "]"
    MemCopy dest src numel -> "memcopy" <+> p dest <+> p src <+> p numel
    InitializeZeros ptr numel -> "initializeZeros" <+> p ptr <+> p numel
    GetAllocSize ptr -> "getAllocSize" <+> p ptr
    Free ptr       -> "free"  <+> p ptr
    ISyncWorkgroup   -> "syncWorkgroup"
    IThrowError      -> "throwError"
    ICall f args   -> "call" <+> p f <+> p args
    IVectorBroadcast v _ -> "vbroadcast" <+> p v
    IVectorIota _ -> "viota"
    DebugPrint s x -> "debug_print" <+> p (show s) <+> p x
    IPtrLoad ptr   -> "load" <+> p ptr
    IPtrOffset ptr idx -> p ptr <+> "+>" <+> p idx
    IBinOp op x y -> opDefault (UPrimOp $ BinOp op () ()) [x, y]
    IUnOp  op x   -> opDefault (UPrimOp $ UnOp  op ()   ) [x]
    ISelect x y z -> opDefault (UPrimOp $ MiscOp (Select () () ())) [x, y, z]
    IOutputStream -> "outputStream"
    IShowScalar ptr x -> "show_scalar" <+> p ptr <+> p x
    where opDefault name xs = prettyOpDefault name xs $ AppPrec

sizeStr :: IExpr n -> Doc ann
sizeStr s = case s of
  ILit (Word32Lit x) -> p x  -- print in decimal because it's more readable
  _ -> p s

instance Pretty BaseType where pretty = prettyFromPrettyPrec
instance PrettyPrec BaseType where
  prettyPrec b = case b of
    Scalar sb -> prettyPrec sb
    Vector shape sb -> atPrec ArgPrec $ encloseSep "<" ">" "x" $ (p <$> shape) ++ [p sb]
    PtrType ty -> atPrec AppPrec $ "Ptr" <+> p ty

instance Pretty AddressSpace where pretty d = p (show d)

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

instance PrettyPrec e => Pretty (PrimTC r e) where pretty = prettyFromPrettyPrec
instance PrettyPrec e => PrettyPrec (PrimTC r e) where
  prettyPrec con = case con of
    BaseType b   -> prettyPrec b
    ProdType []  -> atPrec ArgPrec $ "Unit"
    ProdType [a] -> atPrec ArgPrec $ "(" <> pArg a <> "&)"
    ProdType as  -> atPrec ArgPrec $ align $ group $
      encloseSep "(" ")" " & " $ fmap pApp as
    SumType  cs  -> atPrec ArgPrec $ align $ group $
      encloseSep "(|" "|)" " | " $ fmap pApp cs
    RefType h a -> atPrec AppPrec $ pAppArg "Ref" [h, a]
    TypeKind -> atPrec ArgPrec "Type"
    HeapType -> atPrec ArgPrec "Heap"

prettyPrecNewtype :: NewtypeCon n -> CAtom n -> DocPrec ann
prettyPrecNewtype con x = case (con, x) of
  (NatCon, (IdxRepVal n)) -> atPrec ArgPrec $ pretty n
  (RecordCon labels, ProdVal itemList) ->
    prettyLabeledItems (restructure itemList labels) (line' <> ",") " ="
  (_, x') -> prettyPrec x'

instance Pretty (NewtypeTyCon n) where pretty = prettyFromPrettyPrec
instance PrettyPrec (NewtypeTyCon n) where
  prettyPrec = \case
    Nat   -> atPrec ArgPrec $ "Nat"
    Fin n -> atPrec AppPrec $ "Fin" <+> pArg n
    RecordTyCon elems -> prettyRecordTyRow elems "&"
    EffectRowKind -> atPrec ArgPrec "EffKind"
    LabeledRowKindTC -> atPrec ArgPrec "Fields"
    LabelType -> atPrec ArgPrec "Label"
    LabelCon name -> atPrec ArgPrec $ "##" <> p name
    LabeledRowCon elems -> prettyRecordTyRow elems "?"
    UserADTType "RangeTo"      _ (DataDefParams [_, (PlainArrow, i)])
      -> atPrec LowestPrec $ ".."  <> pApp i
    UserADTType "RangeToExc"   _ (DataDefParams [_, (PlainArrow, i)])
      -> atPrec LowestPrec $ "..<" <> pApp i
    UserADTType "RangeFrom"    _ (DataDefParams [_, (PlainArrow, i)])
      -> atPrec LowestPrec $ pApp i <>  ".."
    UserADTType "RangeFromExc" _ (DataDefParams [_, (PlainArrow, i)])
      -> atPrec LowestPrec $ pApp i <> "<.."
    UserADTType name _ (DataDefParams params) -> case params of
      [] -> atPrec ArgPrec $ p name
      [(PlainArrow, l), (PlainArrow, r)]
        | Just sym <- fromInfix (fromString name) ->
        atPrec ArgPrec $ align $ group $
          parens $ flatAlt " " "" <> pApp l <> line <> p sym <+> pApp r
      _  -> atPrec LowestPrec $ pAppArg (p name) $ plainArrows params


instance (IRRep r, PrettyPrec e) => Pretty (PrimCon r e) where pretty = prettyFromPrettyPrec
instance (IRRep r, PrettyPrec e) => PrettyPrec (PrimCon r e) where
  prettyPrec = prettyPrecPrimCon
-- TODO: Define Show instances in user-space and avoid those overlapping instances!
instance IRRep r => Pretty (PrimCon r (Atom r n)) where pretty = prettyFromPrettyPrec
instance IRRep r => PrettyPrec (PrimCon r (Atom r n)) where
  prettyPrec con = prettyPrecPrimCon con

prettyPrecPrimCon :: PrettyPrec e => PrimCon r e -> DocPrec ann
prettyPrecPrimCon con = case con of
  Lit l        -> prettyPrec l
  ProdCon [x]  -> atPrec ArgPrec $ "(" <> pLowest x <> ",)"
  ProdCon xs  -> atPrec ArgPrec $ align $ group $
    encloseSep "(" ")" ", " $ fmap pLowest xs
  SumCon _ tag payload -> atPrec ArgPrec $
    "(" <> p tag <> "|" <+> pApp payload <+> "|)"
  HeapVal -> atPrec ArgPrec "HeapValue"

instance PrettyPrec e => Pretty (PrimOp e) where pretty = prettyFromPrettyPrec
instance PrettyPrec e => PrettyPrec (PrimOp e) where
  prettyPrec = \case
    MemOp    op -> prettyPrec op
    VectorOp op -> prettyPrec op
    op -> prettyOpDefault (UPrimOp $ void op) (toList op)

instance PrettyPrec e => Pretty (MemOp e) where pretty = prettyFromPrettyPrec
instance PrettyPrec e => PrettyPrec (MemOp e) where
  prettyPrec = \case
    PtrOffset ptr idx -> atPrec LowestPrec $ pApp ptr <+> "+>" <+> pApp idx
    PtrLoad   ptr     -> atPrec AppPrec $ pAppArg "load" [ptr]
    op -> prettyOpDefault (UPrimOp $ MemOp $ void op) (toList op)

instance PrettyPrec e => Pretty (VectorOp e) where pretty = prettyFromPrettyPrec
instance PrettyPrec e => PrettyPrec (VectorOp e) where
  prettyPrec = \case
    VectorBroadcast v vty -> atPrec LowestPrec $ "vbroadcast" <+> pApp v <+> pApp vty
    VectorIota vty -> atPrec LowestPrec $ "viota" <+> pApp vty
    VectorSubref ref i _ -> atPrec LowestPrec $ "vrefslice" <+> pApp ref <+> pApp i

prettyOpDefault :: PrettyPrec a => PrimName -> [a] -> DocPrec ann
prettyOpDefault name args =
  case length args of
    0 -> atPrec ArgPrec primName
    _ -> atPrec AppPrec $ pAppArg primName args
  where primName = p name

instance Pretty PrimName where
   pretty primName = p $ "%" ++ showPrimName primName

instance IRRep r => Pretty (Hof r n) where pretty = prettyFromPrettyPrec
instance IRRep r => PrettyPrec (Hof r n) where
  prettyPrec hof = atPrec LowestPrec case hof of
    For ann _ lam -> forStr ann <+> prettyLamHelper PlainArrow lam (PrettyFor ann)
    While body    -> "while" <+> pArg body
    RunReader x body    -> "runReader" <+> pArg x <> nest 2 (line <> p body)
    RunWriter _ bm body -> "runWriter" <+> pArg bm <> nest 2 (line <> p body)
    RunState  _ x body  -> "runState"  <+> pArg x <> nest 2 (line <> p body)
    RunIO body          -> "runIO" <+> pArg body
    RunInit body        -> "runInit" <+> pArg body
    CatchException body -> "catchException" <+> pArg body
    Linearize body x    -> "linearize" <+> pArg body <+> pArg x
    Transpose body x    -> "transpose" <+> pArg body <+> pArg x

instance IRRep r => Pretty (DAMOp r n) where pretty = prettyFromPrettyPrec
instance IRRep r => PrettyPrec (DAMOp r n) where
  prettyPrec op = atPrec LowestPrec case op of
    Seq ann d c lamExpr -> case lamExpr of
      UnaryLamExpr b body -> do
        let rawFinPretty = case d of
              IxDictRawFin n -> parens $ "RawFin" <+> p n
              _ -> mempty
        "seq" <+> rawFinPretty <+> pApp ann <+> pApp c <+> prettyLam (p b <> ".") body
      _ -> p (show op) -- shouldn't happen, but crashing pretty printers make debugging hard
    RememberDest x y    -> "rememberDest" <+> pArg x <+> pArg y
    Place r v -> pApp r <+> "r:=" <+> pApp v
    Freeze r  -> "freeze" <+> pApp r
    AllocDest ty -> "alloc" <+> pApp ty

instance IRRep r => Pretty (DestBlock r n) where pretty = prettyFromPrettyPrec
instance IRRep r => PrettyPrec (DestBlock r n) where
  prettyPrec (DestBlock b body) = prettyPrec $ Abs b body

instance IRRep r => Pretty (BaseMonoid r n) where pretty = prettyFromPrettyPrec
instance IRRep r => PrettyPrec (BaseMonoid r n) where
  prettyPrec (BaseMonoid x f) =
    atPrec LowestPrec $ "baseMonoid" <+> pArg x <> nest 2 (line <> pArg f)

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
  prettyPrec (Word32Lit  x) = atPrec ArgPrec $ p $ "0x" ++ showHex x ""
  prettyPrec (Word64Lit  x) = atPrec ArgPrec $ p $ "0x" ++ showHex x ""
  prettyPrec (PtrLit ty (PtrLitVal x)) =
    atPrec ArgPrec $ "Ptr" <+> p ty <+> p (show x)
  prettyPrec (PtrLit _ NullPtr) = atPrec ArgPrec $ "NullPtr"
  prettyPrec (PtrLit _ (PtrSnapshot _)) = atPrec ArgPrec "<ptr snapshot>"

instance Pretty CallingConvention where
  pretty = p . show

instance Pretty LetAnn where
  pretty ann = case ann of
    PlainLet        -> ""
    NoInlineLet     -> "%noinline"
    OccInfoPure   u -> p u <> line
    OccInfoImpure u -> p u <> ", impure" <> line

instance Pretty UsageInfo where
  pretty (UsageInfo static (ixDepth, ct)) =
    "occurs in" <+> p static <+> "places, read"
    <+> p ct <+> "times, to depth" <+> p (show ixDepth)

instance Pretty Count where
  pretty (Bounded ct) = "<=" <+> pretty ct
  pretty Occ.Unbounded = "many"

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

-- === Concrete syntax rendering ===

instance Pretty SourceBlock' where
  pretty (TopDecl decl) = p decl
  pretty d = fromString $ show d

instance Pretty CTopDecl where
  pretty (WithSrc _ d) = p d

instance Pretty CTopDecl' where
  pretty (CSDecl ann decl) = annDoc <> p decl
    where annDoc = case ann of
            PlainLet -> mempty
            _ -> p ann <> " "
  pretty d = fromString $ show d

instance Pretty CSDecl where
  pretty (WithSrc _ d) = p d

instance Pretty CSDecl' where
  pretty (CLet pat blk) = pArg pat <+> "=" <+> p blk
  pretty (CBind pat blk) = pArg pat <+> "<-" <+> p blk
  pretty (CDef name args (Just ty) blk) =
    "def " <> fromString name <> " " <> pArg args <> " : " <> pArg ty <> " ="
      <> nest 2 (hardline <> p blk)
  pretty (CDef name args Nothing blk) =
    "def " <> fromString name <> " " <> pArg args <> " ="
      <> nest 2 (hardline <> p blk)
  pretty (CInstance header givens methods name) =
    name' <> p header <> givens' <> prettyLines methods where
    name' = case name of
      Nothing  -> "instance "
      (Just n) -> "named-instance " <> p n <> " "
    givens' = case givens of
      (WithSrc _ CEmpty) -> ""
      _ -> " given" <+> p givens <> " "
  pretty (CExpr e) = p e

instance Pretty CSBlock where
  pretty (ExprBlock g) = pArg g
  pretty (CSBlock decls) = nest 2 $ prettyLines decls

instance PrettyPrec Group where
  prettyPrec (WithSrc _ g) = prettyPrec g

instance Pretty Group where
  pretty = prettyFromPrettyPrec

instance PrettyPrec Group' where
  prettyPrec (CIdentifier n) = atPrec ArgPrec $ fromString n
  prettyPrec (CPrim prim args) = prettyOpDefault prim args
  prettyPrec (CParens blk)  =
    atPrec ArgPrec $ "(" <> p blk <> ")"
  prettyPrec (CBracket b g) =
    atPrec ArgPrec $ open_bracket b <> pLowest g <> close_bracket b
  prettyPrec (CBin (WithSrc _ Juxtapose) lhs rhs) =
    atPrec AppPrec $ pApp lhs <+> pArg rhs
  prettyPrec (CBin op lhs rhs) =
    atPrec LowestPrec $ pArg lhs <+> p op <+> pArg rhs
  prettyPrec (CLambda args body) =
    atPrec LowestPrec $ "\\" <> spaced args <> "." <> p body
  prettyPrec (CCase scrut alts) =
    atPrec LowestPrec $ "case " <> p scrut <> " of " <> prettyLines alts
  prettyPrec g = atPrec ArgPrec $ fromString $ show g

open_bracket :: Bracket -> Doc a
open_bracket Square = "["
open_bracket Curly  = "{"

close_bracket :: Bracket -> Doc a
close_bracket Square = "]"
close_bracket Curly  = "}"

instance Pretty Bin where
  pretty (WithSrc _ b) = p b

instance Pretty Bin' where
  pretty (EvalBinOp name) = fromString name
  pretty Juxtapose = " "
  pretty Ampersand = "&"
  pretty DepAmpersand = "&>"
  pretty IndexingDot = "."
  pretty FieldAccessDot = "~"
  pretty Comma = ","
  pretty DepComma = ",>"
  pretty Colon = ":"
  pretty DoubleColon = "::"
  pretty Dollar = "$"
  pretty (Arrow arr) = p arr
  pretty FatArrow = "=>"
  pretty Question = "?"
  pretty Pipe = "|"
  pretty CSEqual = "="
