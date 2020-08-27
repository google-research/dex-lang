-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module PPrint (pprint, pprintList, printLitBlock, asStr,
               assertEq, ignoreExcept, PrecedenceLevel(..), DocPrec,
               PrettyPrec(..), atPrec, toJSONStr) where

import Data.Aeson hiding (Result, Null, Value, Array)
import Control.Monad.Except hiding (Except)
import GHC.Float
import GHC.Stack
import Data.Foldable (toList)
import qualified Data.List.NonEmpty as NE
import qualified Data.Map.Strict as M
import qualified Data.ByteString.Lazy.Char8 as B
import Data.String (fromString)
import Data.Text.Prettyprint.Doc.Render.Text
import Data.Text.Prettyprint.Doc
import Data.Text (unpack)
import System.Console.ANSI
import Numeric

import Env
import Array
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

pprint :: Pretty a => a -> String
pprint x = asStr $ pretty x

pprintList :: Pretty a => [a] -> String
pprintList xs = asStr $ vsep $ punctuate "," (map p xs)

asStr :: Doc ann -> String
asStr doc = unpack $ renderStrict $ layoutPretty defaultLayoutOptions $ doc

p :: Pretty a => a -> Doc ann
p = pretty

pLowest :: PrettyPrec a => a -> Doc ann
pLowest a = prettyPrec a LowestPrec

pApp :: PrettyPrec a => a -> Doc ann
pApp a = prettyPrec a AppPrec

pArg :: PrettyPrec a => a -> Doc ann
pArg a = prettyPrec a ArgPrec

prettyFromPrettyPrec :: PrettyPrec a => a -> Doc ann
prettyFromPrettyPrec = pArg

pAppArg :: (PrettyPrec a, Foldable f) => Doc ann -> f a -> Doc ann
pAppArg name as = align $ name <> group (nest 2 $ foldMap (\a -> line <> pArg a) as)

instance Pretty Err where
  pretty (Err e _ s) = p e <> p s

instance Pretty ErrType where
  pretty e = case e of
    -- NoErr tags a chunk of output that was promoted into the Err ADT
    -- by appending Results.
    NoErr             -> ""
    ParseErr          -> "Parse error:"
    TypeErr           -> "Type error:"
    KindErr           -> "Kind error:"
    LinErr            -> "Linearity error: "
    IRVariantErr      -> "Internal IR validation error: "
    UnboundVarErr     -> "Error: variable not in scope: "
    RepeatedVarErr    -> "Error: variable already defined: "
    NotImplementedErr -> "Not implemented:"
    CompilerErr       ->
      "Compiler bug!" <> line <>
      "Please report this at github.com/google-research/dex-lang/issues\n" <> line
    DataIOErr         -> "IO error: "
    MiscErr           -> "Error:"
    RuntimeErr        -> "Runtime error"

instance Pretty TyQual where
  pretty (TyQual v c) = p c <+> p v

instance Pretty BaseType where pretty = prettyFromPrettyPrec
instance PrettyPrec BaseType where
  prettyPrec b = case b of
    Scalar sb -> prettyPrec sb
    Vector sb -> atPrec ArgPrec $ "<" <> p vectorWidth <+> "x" <+> p sb <> ">"

instance Pretty ScalarBaseType where pretty = prettyFromPrettyPrec
instance PrettyPrec ScalarBaseType where
  prettyPrec sb = atPrec ArgPrec $ case sb of
    Int64Type   -> "Int64"
    Int32Type   -> "Int32"
    Int8Type    -> "Int8"
    Float64Type -> "Float64"
    Float32Type -> "Float32"

printDouble :: Double -> Doc ann
printDouble x = p (double2Float x)

instance Pretty LitVal where pretty = prettyFromPrettyPrec
instance PrettyPrec LitVal where
  prettyPrec (Int64Lit   x) = atPrec ArgPrec $ p x
  prettyPrec (Int32Lit   x) = atPrec ArgPrec $ p x
  prettyPrec (Int8Lit    x) = atPrec ArgPrec $ p x
  prettyPrec (Float64Lit x) = atPrec ArgPrec $ printDouble x
  prettyPrec (Float32Lit x) = atPrec ArgPrec $ p x
  prettyPrec (VecLit  l) = atPrec ArgPrec $ encloseSep "<" ">" ", " $ fmap p l

instance Pretty Block where
  pretty (Block Empty expr) = group $ line <> pLowest expr
  pretty (Block decls expr) = hardline <> prettyLines decls <> pLowest expr

prettyLines :: (Foldable f, Pretty a) => f a -> Doc ann
prettyLines xs = foldMap (\d -> p d <> hardline) $ toList xs

instance Pretty Expr where pretty = prettyFromPrettyPrec
instance PrettyPrec Expr where
  prettyPrec (App f x) =
    atPrec AppPrec $ pApp f <+> pArg x
  prettyPrec (Atom x ) = prettyPrec x
  prettyPrec (Op  op ) = prettyPrec op
  prettyPrec (Hof hof) = prettyPrec hof
  prettyPrec (Case e alts _) = atPrec LowestPrec $ "case" <+> p e <+> "of" <>
    nest 2 (hardline <> foldMap (\alt -> prettyAlt alt <> hardline) alts)

prettyAlt :: Alt -> Doc ann
prettyAlt (Abs bs body) =
  hsep (map prettyBinderNoAnn $ toList bs) <+> "->" <> nest 2 (p body)

prettyBinderNoAnn :: BinderP a -> Doc ann
prettyBinderNoAnn (Ignore _) = "_"
prettyBinderNoAnn (Bind (v:>_)) = p v

prettyExprDefault :: PrettyPrec e => PrimExpr e -> DocPrec ann
prettyExprDefault expr =
  case length expr of
    0 -> atPrec ArgPrec primName
    _ -> atPrec AppPrec $ pAppArg primName expr
  where primName = p $ "%" ++ showPrimName expr

instance PrettyPrec e => Pretty (Abs Binder e) where pretty = prettyFromPrettyPrec
instance PrettyPrec e => PrettyPrec (Abs Binder e) where
  prettyPrec (Abs binder body) = atPrec LowestPrec $ "\\" <> p binder <> "." <> pLowest body

instance PrettyPrec e => Pretty (PrimExpr e) where pretty = prettyFromPrettyPrec
instance PrettyPrec e => PrettyPrec (PrimExpr e) where
  prettyPrec (TCExpr  e) = prettyPrec e
  prettyPrec (ConExpr e) = prettyPrec e
  prettyPrec (OpExpr  e) = prettyPrec e
  prettyPrec (HofExpr e) = prettyPrec e


instance PrettyPrec e => Pretty (PrimTC e) where pretty = prettyFromPrettyPrec
instance PrettyPrec e => PrettyPrec (PrimTC e) where
  prettyPrec con = case con of
    BaseType b     -> prettyPrec b
    CharType       -> atPrec ArgPrec "Char"
    ArrayType ty   -> atPrec ArgPrec $ "Arr[" <> pLowest ty <> "]"
    PairType a b   -> atPrec ArgPrec $ parens $ pApp a <+> "&" <+> pApp b
    UnitType       -> atPrec ArgPrec "Unit"
    IntRange a b -> if asStr (pArg a) == "0"
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
    RefType h a -> atPrec AppPrec $ pAppArg "Ref" [h, a]
    TypeKind -> atPrec ArgPrec "Type"
    EffectRowKind -> atPrec ArgPrec "EffKind"
    LabeledRowKindTC -> atPrec ArgPrec "Fields"
    _ -> prettyExprDefault $ TCExpr con

instance PrettyPrec e => Pretty (PrimCon e) where pretty = prettyFromPrettyPrec
instance {-# OVERLAPPING #-} Pretty (PrimCon Atom) where pretty = prettyFromPrettyPrec

instance PrettyPrec e => PrettyPrec (PrimCon e) where
  prettyPrec = prettyPrecPrimCon

instance {-# OVERLAPPING #-} PrettyPrec (PrimCon Atom) where
  prettyPrec con = case (Con con) of
    CharLit c -> atPrec ArgPrec $ p $ show $ toEnum @Char $ fromIntegral c
    _         -> prettyPrecPrimCon con

prettyPrecPrimCon :: PrettyPrec e => PrimCon e -> DocPrec ann
prettyPrecPrimCon con = case con of
  Lit l       -> prettyPrec l
  CharCon e   -> atPrec LowestPrec $ "Char" <+> pApp e
  ArrayLit _ array -> atPrec ArgPrec $ p array
  PairCon x y -> atPrec ArgPrec $ parens $ pApp x <> "," <+> pApp y
  UnitCon     -> atPrec ArgPrec "()"
  Coerce t i  -> atPrec LowestPrec $ pApp i <> "@" <> pApp t
  AnyValue t  -> atPrec AppPrec $ pAppArg "%anyVal" [t]
  SumAsProd ty tag payload -> atPrec LowestPrec $
    "SumAsProd" <+> pApp ty <+> pApp tag <+> pApp payload
  ClassDictHole _ _ -> atPrec ArgPrec "_"

instance PrettyPrec e => Pretty (PrimOp e) where pretty = prettyFromPrettyPrec
instance PrettyPrec e => PrettyPrec (PrimOp e) where
  prettyPrec op = case op of
    PrimEffect ref (MPut val ) -> atPrec LowestPrec $ pApp ref <+> ":=" <+> pApp val
    PrimEffect ref (MTell val) -> atPrec LowestPrec $ pApp ref <+> "+=" <+> pApp val
    ArrayOffset arr idx off -> atPrec LowestPrec $ pApp arr <+> "+>" <+> pApp off <+> (parens $ "index:" <+> pLowest idx)
    ArrayLoad arr       -> atPrec AppPrec $ pAppArg "load" [arr]
    RecordCons items rest ->
      prettyExtLabeledItems (Ext items $ Just rest) (line' <> ",") " ="
    RecordSplit types val -> atPrec AppPrec $
      "RecordSplit" <+> prettyLabeledItems types (line <> "&") ":" ArgPrec
                    <+> pArg val
    VariantLift types val ->
      prettyVariantLift (fmap (const ()) types) val
    VariantSplit types val -> atPrec AppPrec $
      "VariantSplit" <+> prettyLabeledItems types (line <> "|") ":" ArgPrec
                     <+> pArg val
    _ -> prettyExprDefault $ OpExpr op

instance PrettyPrec e => Pretty (PrimHof e) where pretty = prettyFromPrettyPrec
instance PrettyPrec e => PrettyPrec (PrimHof e) where
  prettyPrec hof = case hof of
    For dir lam -> atPrec LowestPrec $ dirStr dir <+> pArg lam
    _ -> prettyExprDefault $ HofExpr hof

instance Pretty a => Pretty (VarP a) where
  pretty (v :> ann) = p v <> ":" <> p ann

instance Pretty ClassName where
  pretty name = case name of
    DataClass -> "Data"
    VSpace -> "VS"
    IdxSet -> "Ix"
    Eq     -> "Eq"
    Ord    -> "Ord"

instance Pretty Decl where
  pretty decl = case decl of
    Let _ (Ignore _) bound -> pLowest bound
    -- This is just to reduce clutter a bit. We can comment it out when needed.
    -- Let (v:>Pi _)   bound -> p v <+> "=" <+> p bound
    Let _  b  rhs -> align $ p b  <+> "=" <> (nest 2 $ group $ line <> pLowest rhs)
    Unpack bs rhs -> align $ p (toList bs) <+> "=" <> (nest 2 $ group $ line <> pLowest rhs)

instance Pretty Atom where pretty = prettyFromPrettyPrec
instance PrettyPrec Atom where
  prettyPrec atom = case atom of
    Var (x:>_)  -> atPrec ArgPrec $ p x
    Lam (Abs b (TabArrow, body))   -> atPrec LowestPrec $ align $ nest 2 $ "for " <> p b <> "." <+> p body
    Lam (Abs b (_, body)) -> atPrec LowestPrec $ align $ nest 2 $ "\\" <> p b <> "." <+> p body
    Pi  (Abs (Ignore a) (arr, b)) -> atPrec LowestPrec $ pArg a <+> p arr <+> pLowest b
    Pi  (Abs a           (arr, b)) -> atPrec LowestPrec $ parens (p a) <+> p arr <+> pLowest b
    TC  e -> prettyPrec e
    Con e -> prettyPrec e
    Eff e -> atPrec ArgPrec $ p e
    DataCon (DataDef _ _ cons) _ con xs -> case xs of
      [] -> atPrec ArgPrec $ p name
      _ ->  atPrec LowestPrec $ p name <+> hsep (map p xs)
      where (DataConDef name _) = cons !! con
    TypeCon (DataDef name _ _) params -> case params of
      [] -> atPrec ArgPrec $ p name
      _  -> atPrec LowestPrec $ p name <+> hsep (map p params)
    LabeledRow items -> prettyExtLabeledItems items (line <> "?") ":"
    Record items -> prettyLabeledItems items (line' <> ",") " ="
    Variant _ label i value -> prettyVariant ls label value where
      ls = LabeledItems $ case i of
            0 -> M.empty
            _ -> M.singleton label $ NE.fromList $ fmap (const ()) [1..i]
    RecordTy items -> prettyExtLabeledItems items (line <> "&") ":"
    VariantTy items -> prettyExtLabeledItems items (line <> "|") ":"

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
    innerDoc = "{"
      <> line'
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

prettyVariantLift :: PrettyPrec a
  => LabeledItems () -> a -> DocPrec ann
prettyVariantLift labels value = atPrec ArgPrec $
      "{|" <> left <+> "..." <> pLowest value <+> "|}"
      where left = foldl (<>) mempty $ fmap plabel $ reflectLabels labels
            plabel (l, _) = p l <> "|"

instance Pretty IExpr where
  pretty (ILit v) = p v
  pretty (IVar (v:>_)) = p v

instance PrettyPrec IExpr where prettyPrec = atPrec ArgPrec . pretty

instance Pretty IType where
  pretty (IRefType t) = "Ref" <+> (parens $ p t)
  pretty (IValType t) = p t
  pretty IVoidType = "Void"

instance PrettyPrec IType where prettyPrec = atPrec ArgPrec . pretty

instance Pretty instr => Pretty (IStmt instr) where
  pretty (IInstr (Ignore _, instr)) = p instr
  pretty (IInstr (b       , instr)) = p b <+> "=" <+> p instr
  pretty (IFor d i n block)         = dirStr d <+> p i <+> "<" <+> p n <>
                                      nest 4 (hardline <> p block)
  pretty (IWhile (cond, mcExpr) body) = "while" <+>
                                        nest 2 condDoc <+> "do" <>
                                        nest 4 (hardline <> p body)
    where condDoc = case mcExpr of
                      Just cExpr -> hardline <> p cond <> line <> p cExpr
                      Nothing    -> "??"
  pretty (ICond predicate cons alt) =
    "if" <+> p predicate <+> "then" <> nest 2 (hardline <> p cons) <>
    hardline <> "else" <> nest 2 (hardline <> p alt)

instance Pretty ImpFunction where
  pretty (ImpFunction vsOut vsIn body) =
                   "in:        " <> p vsIn
    <> hardline <> "out:       " <> p vsOut
    <> hardline <> p body

instance Pretty ImpInstr where
  pretty (IPrimOp op)            = pLowest op
  pretty (ICastOp t x)           = "cast"  <+> p x <+> "to" <+> p t
  pretty (Load ref)              = "load"  <+> p ref
  pretty (Store dest val)        = "store" <+> p dest <+> p val
  pretty (Alloc t s)             = "alloc" <+> p (scalarTableBaseType t) <> "[" <> p s <> "]" <+> "@" <> p t
  pretty (IOffset expr lidx t)   = p expr  <+> "++" <+> p lidx <+> (parens $ "coerced to:" <+> p t)
  pretty (Free (v:>_))           = "free"  <+> p v
  pretty IThrowError = "throwError"

instance Pretty k => Pretty (MDImpFunction k) where
  pretty (MDImpFunction vsOut vsIn body) =
                   "in:        " <> p vsIn
    <> hardline <> "out:       " <> p vsOut
    <> hardline <> p body

instance Pretty k => Pretty (MDImpInstr k) where
  pretty (MDLaunch size args kernel) = "launch_kernel" <+> p size <+> p args <> nest 2 (hardline <> p kernel)
  pretty (MDAlloc t s)    = "device_alloc" <+> p (scalarTableBaseType t) <> "[" <> p s <> "]" <+> "@" <> p t
  pretty (MDFree v)       = "free" <+> p v
  pretty (MDLoadScalar v) = "device_load" <+> p v
  pretty (MDStoreScalar v x) = "device_store" <+> p v <+> p x
  pretty (MDHostInstr instr) = pretty instr

instance Pretty ImpKernel where
  pretty (ImpKernel args idxVar kernel) = parens (p idxVar <+> p args) <> nest 2 (hardline <> p kernel)

dirStr :: Direction -> Doc ann
dirStr Fwd = "for"
dirStr Rev = " rof"

instance Pretty a => Pretty (SetVal a) where
  pretty NotSet = ""
  pretty (Set a) = p a

instance Pretty Output where
  pretty (TextOut s) = pretty s
  pretty (BenchResult name compileTime runTime) =
    benchName <>
    "\nCompile time: " <> p (showFFloat (Just 3) compileTime "") <+> "s" <>
    "\nRun time:     " <> p (showFFloat (Just 3) runTime     "") <+> "s"
    where benchName = case name of "" -> ""
                                   _  -> "\n" <> p name
  pretty (HeatmapOut _ _ _ _) = "<graphical output>"
  pretty (ScatterOut _ _  ) = "<graphical output>"
  pretty (PassInfo name s) = "===" <+> p name <+> "===" <> hardline <> p s
  pretty (EvalTime    t) = "Eval (s):  " <+> p t
  pretty (TotalTime t)   = "Total (s): " <+> p t <+> "  (eval + compile)"
  pretty (MiscLog s) = "===" <+> p s <+> "==="


instance Pretty PassName where
  pretty x = p $ show x

instance Pretty SourceBlock where
  pretty block = pretty (sbText block)

instance Pretty Result where
  pretty (Result outs r) = vcat (map pretty outs) <> maybeErr
    where maybeErr = case r of Left err -> p err
                               Right () -> mempty

instance Pretty Module where
  pretty (Module variant decls bindings) =
    "Module" <+> parens (p (show variant)) <> nest 2 body
    where
      body = hardline <> "unevaluated decls:"
          <> hardline <> prettyLines decls
          <> hardline <> "evaluated bindings:"
          <> hardline <> p bindings  -- TODO: print these like decls (need the type)

instance (Pretty a, Pretty b) => Pretty (Either a b) where
  pretty (Left  x) = "Left"  <+> p x
  pretty (Right x) = "Right" <+> p x

instance Pretty BinderInfo where
  pretty b = case b of
    LamBound _    -> "<lambda binder>"
    LetBound _ e  -> p e
    PiBound       -> "<pi binder>"
    DataBoundTypeCon _   -> "<type constructor>"
    DataBoundDataCon _ _ -> "<data constructor>"
    UnknownBinder -> "<unknown binder>"
    PatBound      -> "<pattern binder>"

instance Pretty UModule where
  pretty (UModule decls) = prettyLines decls

instance Pretty a => Pretty (WithSrc a) where
  pretty (WithSrc _ x) = p x

instance PrettyPrec a => PrettyPrec (WithSrc a) where
  prettyPrec (WithSrc _ x) = prettyPrec x

instance Pretty UExpr' where pretty = prettyFromPrettyPrec
instance PrettyPrec UExpr' where
  prettyPrec expr = case expr of
    UVar (v:>_) -> atPrec ArgPrec $ p v
    ULam binder h body ->
      atPrec LowestPrec $ align $ "\\" <> annImplicity h (prettyUBinder binder)
                                      <> "." <+> nest 2 (pLowest body)
    UApp TabArrow f x -> atPrec AppPrec $ pArg f <> "." <> pArg x
    UApp _        f x -> atPrec AppPrec $ pAppArg (pApp f) [x]
    UFor dir binder body ->
      atPrec LowestPrec $ kw <+> prettyUBinder binder <> "."
                            <+> nest 2 (pLowest body)
      where kw = case dir of Fwd -> "for"
                             Rev -> "rof"
    UPi a arr b -> atPrec LowestPrec $ p a <+> pretty arr <+> pLowest b
    UDecl decl body -> atPrec LowestPrec $ align $ p decl <> hardline
                                                         <> pLowest body
    UHole -> atPrec ArgPrec "_"
    UTabCon xs ann -> atPrec ArgPrec $ p xs <> foldMap (prettyAnn . p) ann
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
    UIntLit  v -> atPrec ArgPrec $ p v
    UCharLit v -> atPrec ArgPrec $ p v
    UFloatLit v -> atPrec ArgPrec $ p v

instance Pretty UAlt where
  pretty (UAlt pat body) = p pat <+> "->" <+> p body

prettyAnn :: Doc ann -> Doc ann
prettyAnn ty = ":" <+> ty

instance Pretty a => Pretty (Limit a) where
  pretty Unlimited = "unlimited"
  pretty (ExclusiveLim x) = "excLim" <+> p x
  pretty (InclusiveLim x) = "incLim" <+> p x

instance Pretty UDecl where
  pretty (ULet _ b rhs) =
    align $ prettyUBinder b <+> "=" <> (nest 2 $ group $ line <> pLowest rhs)
  pretty (UData tyCon dataCons) =
    "data" <+> p tyCon <+> "where" <> nest 2 (hardline <> prettyLines dataCons)

instance Pretty UConDef where
  pretty (UConDef con bs) = p con <+> spaced bs

instance Pretty UPat' where pretty = prettyFromPrettyPrec
instance PrettyPrec UPat' where
  prettyPrec pat = case pat of
    UPatBinder x -> atPrec ArgPrec $ p x
    UPatPair x y -> atPrec ArgPrec $ parens $ p x <> ", " <> p y
    UPatUnit -> atPrec ArgPrec $ "()"
    UPatCon con pats -> atPrec AppPrec $ parens $ p con <+> spaced pats
    UPatRecord pats -> prettyExtLabeledItems pats (line <> "&") ":"
    UPatVariant labels label value -> prettyVariant labels label value
    UPatVariantLift labels value -> prettyVariantLift labels value

prettyUBinder :: UPatAnn -> Doc ann
prettyUBinder (pat, ann) = p pat <> annDoc where
  annDoc = case ann of
    Just ty -> ":" <> pApp ty
    Nothing -> mempty

spaced :: (Foldable f, Pretty a) => f a -> Doc ann
spaced xs = hsep $ map p $ toList xs

instance Pretty EffectRow where
  pretty (EffectRow [] Nothing) = mempty
  pretty (EffectRow effs tailVar) =
    braces $ hsep (punctuate "," (fmap prettyEff effs)) <> tailStr
    where
      prettyEff (effName, region) = p effName <+> p region
      tailStr = case tailVar of
        Nothing -> mempty
        Just v  -> "|" <> p v

instance Pretty EffectName where
  pretty eff = case eff of
    Reader -> "Read"
    Writer -> "Accum"
    State  -> "State"

annImplicity :: ArrowP a -> Doc ann -> Doc ann
annImplicity ImplicitArrow x = braces x
annImplicity _ x = x

instance Pretty eff => Pretty (ArrowP eff) where
  pretty arr = case arr of
    PlainArrow eff -> "->" <> p eff
    TabArrow       -> "=>"
    LinArrow       -> "--o"
    ImplicitArrow  -> "?->"
    ClassArrow     -> "?=>"

instance Pretty Array where
  pretty a = p b <> "[" <> p size <> "]"
    where (size, b) = arrayType a

instance Pretty ArrayRef where
  pretty (ArrayRef (size, b) ptr) = p b <> "[" <> p size <> "]@" <> (pretty $ show ptr)

instance PrettyPrec () where prettyPrec = atPrec ArgPrec . pretty
instance PrettyPrec Name where prettyPrec = atPrec ArgPrec . pretty

instance PrettyPrec a => PrettyPrec [a] where
  prettyPrec xs = atPrec ArgPrec $ hsep $ map pLowest xs

instance Pretty a => Pretty (Nest a) where
  pretty xs = pretty $ toList xs

instance {-# OVERLAPPING #-} Pretty instr => Pretty (IProg instr) where
  pretty prog = vcat $ toList $ pretty <$> prog

printLitBlock :: Bool -> SourceBlock -> Result -> String
printLitBlock isatty block (Result outs result) =
  pprint block ++ concat (map (printOutput isatty) outs) ++ printResult isatty result

printOutput :: Bool -> Output -> String
printOutput isatty out = addPrefix (addColor isatty Cyan ">") $ pprint $ out

printResult :: Bool -> Except () -> String
printResult _ (Right ()) = ""
printResult isatty (Left err) = addColor isatty Red $ addPrefix ">" $ pprint err

addPrefix :: String -> String -> String
addPrefix prefix str = unlines $ map prefixLine $ lines str
  where prefixLine :: String -> String
        prefixLine s = case s of "" -> prefix
                                 _  -> prefix ++ " " ++ s

addColor :: Bool -> Color -> String -> String
addColor False _ s = s
addColor True c s =
  setSGRCode [SetConsoleIntensity BoldIntensity, SetColor Foreground Vivid c]
  ++ s ++ setSGRCode [Reset]

assertEq :: (MonadError Err m, Show a, Pretty a, Eq a) => a -> a -> String -> m ()
assertEq x y s = if x == y then return ()
                           else throw CompilerErr msg
  where msg = "assertion failure (" ++ s ++ "):\n"
              ++ pprint x ++ " != " ++ pprint y ++ "\n"

ignoreExcept :: HasCallStack => Except a -> a
ignoreExcept (Left e) = error $ pprint e
ignoreExcept (Right x) = x

toJSONStr :: ToJSON a => a -> String
toJSONStr = B.unpack . encode

instance ToJSON Result where
  toJSON (Result outs err) = object (outMaps <> errMaps)
    where
      errMaps = case err of
        Left e   -> ["error" .= String (fromString $ pprint e)]
        Right () -> []
      outMaps = flip foldMap outs $ \case
        BenchResult name compileTime runTime ->
          [ "bench_name"   .= toJSON name
          , "compile_time" .= toJSON compileTime
          , "run_time"     .= toJSON runTime ]
        out -> ["result" .= String (fromString $ pprint out)]
