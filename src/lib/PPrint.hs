-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE IncoherentInstances #-}  -- due to `ConRef`
{-# OPTIONS_GHC -Wno-orphans #-}

module PPrint (pprint, docAsStr, printLitBlock, PrecedenceLevel(..), DocPrec,
               PrettyPrec(..), atPrec, toJSONStr, prettyFromPrettyPrec,
               pAppArg, fromInfix) where

import Data.Aeson hiding (Result, Null, Value, Success)
import GHC.Float
import Data.Functor ((<&>))
import Data.Foldable (toList)
import qualified Data.List.NonEmpty as NE
import qualified Data.Map.Strict as M
import qualified Data.ByteString.Lazy.Char8 as B
import Data.String (fromString)
import Data.Text.Prettyprint.Doc
import Data.Text (Text, uncons, unsnoc)
import System.Console.ANSI
import Numeric

import Env
import Err
import LabeledItems
import Syntax
import Util (enumerate)

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

instance Pretty TyQual where
  pretty (TyQual v c) = p c <+> p v

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
  prettyPrec (PtrLit ty x) = atPrec ArgPrec $ "Ptr" <+> p ty <+> p (show x)
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
  prettyPrec (Hof (For ann (Lam lamExpr))) =
    atPrec LowestPrec $ forStr ann <+> prettyLamHelper lamExpr (PrettyFor ann)
  prettyPrec (Hof hof) = prettyPrec hof
  prettyPrec (Case e alts _) = prettyPrecCase "case" e alts

prettyPrecCase :: Pretty b => Doc ann -> Atom -> [AltP b] -> DocPrec ann
prettyPrecCase name e alts = atPrec LowestPrec $ name <+> p e <+> "of" <>
  nest 2 (hardline <> foldMap (\alt -> prettyAlt alt <> hardline) alts)

prettyAlt :: Pretty b => AltP b -> Doc ann
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


instance PrettyPrec e => Pretty (PrimOp e) where pretty = prettyFromPrettyPrec
instance PrettyPrec e => PrettyPrec (PrimOp e) where
  prettyPrec op = case op of
    PrimEffect ref (MPut    val   ) -> atPrec LowestPrec $ pApp ref <+> ":=" <+> pApp val
    PrimEffect ref (MExtend update) -> atPrec LowestPrec $ "extend" <+> pApp ref <+> "using" <+> pLowest update
    PtrOffset ptr idx -> atPrec LowestPrec $ pApp ptr <+> "+>" <+> pApp idx
    PtrLoad   ptr     -> atPrec AppPrec $ pAppArg "load" [ptr]
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
    For ann lam -> atPrec LowestPrec $ forStr ann <+> pArg lam
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
    Let ann (Ignore _) bound -> p ann <+> pLowest bound
    -- This is just to reduce clutter a bit. We can comment it out when needed.
    -- Let (v:>Pi _)   bound -> p v <+> "=" <+> p bound
    Let PlainLet b rhs ->           p b <+> "=" <> (nest 2 $ group $ line <> pLowest rhs)
    Let ann      b rhs -> p ann <+> p b <+> "=" <> (nest 2 $ group $ line <> pLowest rhs)

instance Pretty LetAnn where
  pretty ann = case ann of
    PlainLet      -> ""
    InstanceLet   -> "%instance"
    NoInlineLet   -> "%noinline"

prettyPiTypeHelper :: PiType -> Doc ann
prettyPiTypeHelper (Abs binder (arr, body)) = let
  prettyBinder = case binder of
    Ignore a -> pArg a
    _ -> parens $ p binder
  prettyBody = case body of
    Pi subpi -> prettyPiTypeHelper subpi
    _ -> pLowest body
  in prettyBinder <> (group $ line <> p arr <+> prettyBody)

data PrettyLamType = PrettyLam Arrow | PrettyFor ForAnn deriving (Eq)

prettyLamHelper :: LamExpr -> PrettyLamType -> Doc ann
prettyLamHelper lamExpr lamType = let
  rec :: LamExpr -> Bool -> (Doc ann, Block)
  rec (Abs binder (_, body')) first =
    let thisOne = (if first then "" else line) <> p binder
    in case body' of
      Block Empty (Atom (Lam next@(Abs _ (arr', _))))
        | lamType == PrettyLam arr' ->
            let (binders', block) = rec next False
            in (thisOne <> binders', block)
      Block Empty (Hof (For ann (Lam next)))
        | lamType == PrettyFor ann ->
            let (binders', block) = rec next False
            in (thisOne <> binders', block)
      _ -> (thisOne <> punctuation, body')
        where punctuation = case lamType of
                PrettyFor _ -> "."
                PrettyLam PureArrow -> "."
                PrettyLam arr -> " " <> p arr
  (binders, body) = rec lamExpr True
  in align (group $ nest 4 $ binders) <> (group $ nest 2 $ p body)

instance Pretty Atom where pretty = prettyFromPrettyPrec
instance PrettyPrec Atom where
  prettyPrec atom = case atom of
    Var (x:>_)  -> atPrec ArgPrec $ p x
    Lam lamExpr@(Abs _ (TabArrow, _)) ->
      atPrec LowestPrec $ "\\for"
      <+> prettyLamHelper lamExpr (PrettyLam TabArrow)
    Lam lamExpr@(Abs _ (arr, _)) ->
      atPrec LowestPrec $ "\\"
      <> prettyLamHelper lamExpr (PrettyLam arr)
    Pi piType -> atPrec LowestPrec $ align $ prettyPiTypeHelper piType
    TC  e -> prettyPrec e
    Con e -> prettyPrec e
    Eff e -> atPrec ArgPrec $ p e
    DepPairTy (Abs b ty) -> atPrec ArgPrec $ align $ group $
        parens $ p b <+> "&>" <+> p ty
    DepPair x y _ -> atPrec ArgPrec $ align $ group $
        parens $ p x <> ",>" <+> p y
    DataCon (_, DataDef _ _ cons) _ con xs -> case xs of
      [] -> atPrec ArgPrec $ p name
      [l, r] | Just sym <- fromInfix (fromString name) -> atPrec ArgPrec $ align $ group $
        parens $ flatAlt " " "" <> pApp l <> line <> p sym <+> pApp r
      _ ->  atPrec LowestPrec $ pAppArg (p name) xs
      where (DataConDef name _) = cons !! con
    TypeCon (_, DataDef name _ _) params -> case params of
      [] -> atPrec ArgPrec $ p name
      [l, r] | Just sym <- fromInfix (fromString name) -> atPrec ArgPrec $ align $ group $
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
    DepPairRef l (Abs b r) _ -> atPrec LowestPrec $
      "DepPairRef" <+> p l <+> "as" <+> p b <+> "in" <+> p r
    BoxedRef b ptr size body -> atPrec AppPrec $
      "Box" <+> p b <+> "<-" <+> p ptr <+> "[" <> p size <> "]" <+> hardline <> "in" <+> p body
    ProjectElt idxs x -> prettyProjection idxs x

instance Pretty DataConRefBinding where pretty = prettyFromPrettyPrec
instance PrettyPrec DataConRefBinding where
  prettyPrec (DataConRefBinding b x) = atPrec AppPrec $ p b <+> "<-" <+> p x

fromInfix :: Text -> Maybe Text
fromInfix t = do
  ('(', t') <- uncons t
  (t'', ')') <- unsnoc t'
  return t''

-- TODO: we don't want to show `proj x [0,1]` etc to users, but this rewrite is
-- bad for debugging the compiler because it obscures what's actually going on.
-- We should just have a separate path for user-facing printing.
prettyProjection :: NE.NonEmpty Int -> Var -> DocPrec ann
-- prettyProjection idxs v = atPrec ArgPrec $ "proj" <+> p idxs <+> p v
prettyProjection idxs (name :> fullTy) = atPrec ArgPrec $ pretty uproj where
  -- Builds a source expression that performs the given projection.
  uproj = UApp (PlainArrow ()) (nosrc ulam) (nosrc uvar)
  ulam = ULam (UPatAnn upat Nothing) (PlainArrow ()) (nosrc $ UVar target)
  uvar = UVar $ UInternalVar name
  (upat, target) = buildProj fullTy $ NE.reverse idxs

  buildProj :: Type -> NE.NonEmpty Int -> (UPat, UVar)
  buildProj ty (i NE.:| is) = case ty of
      TypeCon (_, def) params ->
        rec subTy (UInternalVar hint) \pat ->
          UPatCon (USourceVar conName) $ enumerate bs <&> \(j, _) ->
            if i == j then pat else uignore
        where
          [DataConDef conName bs] = applyDataDefParams def params
          b = toList bs !! i
          (hint, subTy) = case b of
            Bind   (n :> t) -> (n, t)
            Ignore t        -> ("elt", t)
      RecordTy (NoExt types) ->
        rec subTy hint \pat ->
          UPatRecord $ NoExt $ enumerate types <&> \(j, _) ->
            if i == j then pat else uignore
        where
          subTy = toList types !! i
          (fieldName, _) = toList (reflectLabels types) !! i
          hint = USourceVar fieldName
      PairTy x _ | i == 0 -> rec x "a" \pat -> UPatPair pat uignore
      PairTy _ y | i == 1 -> rec y "b" \pat -> UPatPair uignore pat
      ProdTy tys -> rec (tys !! i) "x" \pat -> UPatTable $
        enumerate tys <&> \(j, _) -> if i == j then pat else uignore
      DepPairTy (Abs b _) | i == 0 -> rec (binderType b) "a" \pat -> UPatPair pat uignore
      DepPairTy (Abs _ t) | i == 1 -> rec t              "b" \pat -> UPatPair uignore pat
      _ -> error $ "Bad projection: " ++ pprint i ++ " from " ++ show ty
    where
      rec :: Type -> UVar -> (UPat -> UPat') -> (UPat, UVar)
      rec subTy nameHint patBuilder = case NE.nonEmpty is of
        Just is' -> (nosrc $ patBuilder subpat, targetName)
          where (subpat, targetName) = buildProj subTy is'
        Nothing  -> (nosrc $ patBuilder $ nosrc $ UPatBinder pat, nameHint)
          where pat = case nameHint of USourceVar v -> UBindSource v
                                       UInternalVar v -> UBind v

  nosrc = WithSrc Nothing
  uignore = nosrc $ UPatIgnore

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

instance Pretty ImpDecl where
  pretty (ImpLet [] instr) = p instr
  pretty (ImpLet [b] instr) = p b <+> "=" <+> p instr
  pretty (ImpLet bs instr) = p bs <+> "=" <+> p instr

instance Pretty IFunType where
  pretty (IFunType cc argTys retTys) =
    "Fun" <+> p cc <+> p argTys <+> "->" <+> p retTys

instance Pretty CallingConvention where
  pretty = p . show

instance Pretty ImpFunction where
  pretty (ImpFunction (f:>IFunType cc _ _) bs body) =
    "def" <+> p f <+> p cc <+> p bs
    <> nest 2 (hardline <> p body) <> hardline
  pretty (FFIFunction f) = p f

instance Pretty ImpInstr where
  pretty (IFor a i n block) = forStr (RegularFor a) <+> p i <+> "<" <+> p n <>
                                nest 4 (hardline <> p block)
  pretty (IWhile body) = "while" <+> nest 2 (p body)
  pretty (ICond predicate cons alt) =
    "if" <+> p predicate <+> "then" <> nest 2 (hardline <> p cons) <>
    hardline <> "else" <> nest 2 (hardline <> p alt)
  pretty (IQueryParallelism f s) = "queryParallelism" <+> p (varName f) <+> p s
  pretty (ILaunch f size args) =
    "launch" <+> p (varName f) <+> p size <+> spaced args
  pretty (IPrimOp op)     = pLowest op
  pretty (ICastOp t x)    = "cast"  <+> p x <+> "to" <+> p t
  pretty (Store dest val) = "store" <+> p dest <+> p val
  pretty (Alloc _ t s)    = "alloc" <+> p t <> "[" <> p s <> "]"
  pretty (MemCopy dest src numel) = "memcopy" <+> p dest <+> p src <+> p numel
  pretty (Free ptr)       = "free"  <+> p ptr
  pretty ISyncWorkgroup   = "syncWorkgroup"
  pretty IThrowError      = "throwError"
  pretty (ICall f args)   = "call" <+> p f <+> p args

forStr :: ForAnn -> Doc ann
forStr (RegularFor Fwd) = "for"
forStr (RegularFor Rev) = "rof"
forStr ParallelFor      = "pfor"

instance Pretty a => Pretty (SetVal a) where
  pretty NotSet = ""
  pretty (Set a) = p a

prettyDuration :: Double -> Doc ann
prettyDuration d = p (showFFloat (Just 3) (d * mult) "") <+> unit
  where (mult, unit) =      if d >= 1    then (1  , "s")
                       else if d >= 1e-3 then (1e3, "ms")
                       else if d >= 1e-6 then (1e6, "us")
                       else                   (1e9, "ns")

instance Pretty Output where
  pretty (TextOut s) = pretty s
  pretty (HtmlOut _) = "<html output>"
  pretty (ExportedFun _ _) = ""
  pretty (BenchResult name compileTime runTime stats) =
    benchName <> hardline <>
    "Compile time: " <> prettyDuration compileTime <> hardline <>
    "Run time:     " <> prettyDuration runTime <+>
    (case stats of Just (runs, _) -> "\t" <> parens ("based on" <+> p runs <+> "runs")
                   Nothing        -> "")
    where benchName = case name of "" -> ""
                                   _  -> "\n" <> p name
  pretty (PassInfo name s) = "===" <+> p name <+> "===" <> hardline <> p s
  pretty (EvalTime  t _) = "Eval (s):  " <+> p t
  pretty (TotalTime t)   = "Total (s): " <+> p t <+> "  (eval + compile)"
  pretty (MiscLog s) = "===" <+> p s <+> "==="


instance Pretty PassName where
  pretty x = p $ show x

instance Pretty SourceBlock where
  pretty block = pretty (sbText block)

instance Pretty Result where
  pretty (Result outs r) = vcat (map pretty outs) <> maybeErr
    where maybeErr = case r of Failure err -> p err
                               Success () -> mempty

instance Pretty Module where pretty = prettyFromPrettyPrec
instance PrettyPrec Module where
  prettyPrec (Module variant decls result) = atPrec LowestPrec $
    "Module" <+> parens (p (show variant)) <> nest 2 body
    where
      body = hardline <> "unevaluated decls:"
          <> hardline <> prettyLines decls
          <> hardline <> "evaluated bindings:"
          <> hardline <> p result

instance Pretty EvaluatedModule where
  pretty (EvaluatedModule bindings synthCandidates sourceMap) =
     p bindings <> hardline <> p synthCandidates <> hardline <> p sourceMap

instance Pretty SynthCandidates where
  pretty scs =
    "lambda dicts:"   <+> p (lambdaDicts       scs) <> hardline <>
    "superclasses:"   <+> p (superclassGetters scs) <> hardline <>
    "instance dicts:" <+> p (instanceDicts     scs)

instance Pretty SourceMap where
  pretty (SourceMap m) = pretty $ M.toAscList m

instance Pretty SourceNameDef where
  pretty name = case name of
    SrcAtomName    v -> "Let/lambda name"       <+> p v
    SrcTyConName   v -> "Type constructor name" <+> p v
    SrcDataConName v -> "Data constructor name" <+> p v
    SrcClassName   v -> "Class name"            <+> p v
    SrcMethodName  v -> "Method name"           <+> p v

instance (Pretty a, Pretty b) => Pretty (Either a b) where
  pretty (Left  x) = "Left"  <+> p x
  pretty (Right x) = "Right" <+> p x

instance Pretty BinderInfo where
  pretty b = case b of
    LamBound _    -> "<lambda binder>"
    LetBound _ e  -> p e
    PiBound       -> "<pi binder>"
    UnknownBinder -> "<unknown binder>"
    PatBound      -> "<pattern binder>"

instance Pretty AnyBinderInfo where
  pretty info = case info of
    AtomBinderInfo ty binfo -> "<atom binder>" <+> p ty <+> p binfo
    DataDefName  dataDef -> "<data def>" <+> p dataDef
    ClassDefName classDef -> "<class def>" <+> p classDef
    TyConName    dataDef -> "<type con name>" <+> p dataDef
    DataConName  dataDef i -> "<data con name>" <+> parens ("idx:" <+> p i) <+> p dataDef
    SuperclassName dataDef i getter ->
      "<superclass name>" <+> parens ("idx:" <+> p i) <+> p dataDef <+> p getter
    MethodName     dataDef i getter ->
      "<method name>"     <+> parens ("idx:" <+> p i) <+> p dataDef <+> p getter
    LocalUExprBound      -> "UExpr name"
    ImpBound             -> "Imp name"
    TrulyUnknownBinder   -> "<unknown binder (really)>"

instance Pretty a => Pretty (SubstVal a) where
  pretty (SubstVal x) = "subst with" <+> p x
  pretty (Rename   n) = "rename to" <+> p n

instance Pretty DataDef where
  pretty (DataDef name bs cons) =
    "data" <+> p name <+> p bs <> hardline <> prettyLines cons

instance Pretty ClassDef where
  pretty (ClassDef dataDef methodNames) =
    "interface" <+> p dataDef <+> p methodNames

instance Pretty DataConDef where
  pretty (DataConDef name bs) =
    p name <+> ":" <+> p bs

instance Pretty SourceUModule where
  pretty (SourceUModule decl) = p decl

instance Pretty UModule where
  pretty (UModule decl sourceMap) = p decl <> hardline <> p sourceMap

instance Pretty a => Pretty (WithSrc a) where
  pretty (WithSrc _ x) = p x

instance PrettyPrec a => PrettyPrec (WithSrc a) where
  prettyPrec (WithSrc _ x) = prettyPrec x

instance Pretty UVar where pretty = prettyFromPrettyPrec
instance PrettyPrec UVar where
  prettyPrec uvar = atPrec ArgPrec case uvar of
    USourceVar   v -> p v
    UInternalVar v -> p v

instance Pretty UBinder where pretty = prettyFromPrettyPrec
instance PrettyPrec UBinder where
  prettyPrec b = atPrec ArgPrec case b of
   UBindSource v -> p v
   UIgnore       -> "_"
   UBind v       -> p v

instance Pretty UExpr' where pretty = prettyFromPrettyPrec
instance PrettyPrec UExpr' where
  prettyPrec expr = case expr of
    UVar v -> atPrec ArgPrec $ p v
    ULam binder arr body ->
      atPrec LowestPrec $ align $ "\\" <> p binder
                                      <> punctuation <+> nest 2 (pLowest body)
      where punctuation = case arr of
                            PlainArrow () -> "."
                            _ -> " " <> p arr
    UApp TabArrow f x -> atPrec AppPrec $ pArg f <> "." <> pArg x
    UApp _        f x -> atPrec AppPrec $ pAppArg (pApp f) [x]
    UFor dir binder body ->
      atPrec LowestPrec $ kw <+> p binder <> "."
                            <+> nest 2 (pLowest body)
      where kw = case dir of Fwd -> "for"
                             Rev -> "rof"
    UPi binder arr ty -> atPrec LowestPrec $
      p binder <+> pretty arr <+> pLowest ty
    UDecl decl body -> atPrec LowestPrec $ align $ p decl <> hardline
                                                         <> pLowest body
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

instance Pretty UAlt where
  pretty (UAlt pat body) = p pat <+> "->" <+> p body

instance Pretty a => Pretty (Limit a) where
  pretty Unlimited = "unlimited"
  pretty (ExclusiveLim x) = "excLim" <+> p x
  pretty (InclusiveLim x) = "incLim" <+> p x

instance Pretty UDecl where
  pretty (ULet ann b rhs) =
    align $ p ann <+> p b <+> "=" <> (nest 2 $ group $ line <> pLowest rhs)
  pretty (UDataDefDecl (UDataDef bParams dataCons) bTyCon bDataCons) =
    "data" <+> p bTyCon <+> p bParams
      <+> "where" <> nest 2 (hardline <> prettyLines (zip (toList bDataCons) dataCons))
  pretty (UInterface params superclasses methodTys interfaceName methodNames) =
    "interface" <+> p params <+> p superclasses <+> p interfaceName
      <> hardline <> foldMap (<>hardline) methods
    where
      methods = [hsep (p <$> e) <+> p (UAnnBinder b ty) |
                 (b, UMethodType e ty) <- zip (toList methodNames) methodTys]
  pretty (UInstance bs className params methods Nothing) =
    "instance" <+> p bs <+> p className <+> p params <+> hardline <> prettyLines methods
  pretty (UInstance bs className params methods (Just v)) =
    "named-instance" <+> p v <+> ":" <+> p bs <+> p className <+> p params
        <> hardline <> prettyLines methods

instance Pretty UPatAnnArrow where
  pretty (UPatAnnArrow b arr) = p b <> ":" <> p arr

instance Pretty UAnnBinder where
  pretty (UAnnBinder b ty) = p b <> ":" <> p ty

instance Pretty UMethodDef where
  pretty (UMethodDef b rhs) = p b <+> "=" <+> p rhs

instance Pretty UPat' where pretty = prettyFromPrettyPrec
instance PrettyPrec UPat' where
  prettyPrec pat = case pat of
    UPatBinder x -> atPrec ArgPrec $ p x
    UPatIgnore -> atPrec ArgPrec "_"
    UPatPair x y -> atPrec ArgPrec $ parens $ p x <> ", " <> p y
    UPatUnit -> atPrec ArgPrec $ "()"
    UPatCon con pats -> atPrec AppPrec $ parens $ p con <+> spaced pats
    UPatRecord pats -> prettyExtLabeledItems pats (line' <> ",") " ="
    UPatVariant labels label value -> prettyVariant labels label value
    UPatVariantLift labels value -> prettyVariantLift labels value
    UPatTable pats -> atPrec ArgPrec $ p pats


instance Pretty UPatAnn where
  pretty (UPatAnn pat ann) = p pat <> annDoc where
    annDoc = case ann of
      Just ty -> ":" <> pApp ty
      Nothing -> mempty

spaced :: (Foldable f, Pretty a) => f a -> Doc ann
spaced xs = hsep $ map p $ toList xs

instance (Ord name, Pretty name) => Pretty (EffectRowP name) where
  pretty Pure = mempty
  pretty (EffectRow effs tailVar) =
    braces $ hsep (punctuate "," (map p (toList effs))) <> tailStr
    where
      tailStr = case tailVar of
        Nothing -> mempty
        Just v  -> "|" <> p v

instance (Ord name, Pretty name) => Pretty (EffectP name) where
  pretty eff = case eff of
    RWSEffect rws h -> p rws <+> p h
    ExceptionEffect -> "Except"
    IOEffect        -> "IO"

instance Pretty RWS where
  pretty eff = case eff of
    Reader -> "Read"
    Writer -> "Accum"
    State  -> "State"

instance Pretty eff => Pretty (ArrowP eff) where
  pretty arr = case arr of
    PlainArrow eff -> "->" <> p eff
    TabArrow       -> "=>"
    LinArrow       -> "--o"
    ImplicitArrow  -> "?->"
    ClassArrow     -> "?=>"

instance PrettyPrec () where prettyPrec = atPrec ArgPrec . pretty
instance PrettyPrec Name where prettyPrec = atPrec ArgPrec . pretty

instance PrettyPrec a => PrettyPrec [a] where
  prettyPrec xs = atPrec ArgPrec $ hsep $ map pLowest xs

instance Pretty a => Pretty (Nest a) where
  pretty xs = pretty $ toList xs

instance Pretty ImpModule where
  pretty (ImpModule fs) = vcat (map p fs)

instance Pretty ImpBlock where
  pretty (ImpBlock statements results) =
    (vcat $ map pretty $ toList statements) <> resultDoc
    where resultDoc = case results of
                       [] -> ""
                       _  -> hardline <> "return" <+> p results

printLitBlock :: Bool -> SourceBlock -> Result -> String
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

addColor :: Bool -> Color -> String -> String
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

instance Pretty TopState where
  pretty s =
    "bindings: "         <> hardline <> pretty (topBindings s)        <> hardline <>
    "synth candidates: " <> hardline <> pretty (topSynthCandidates s) <> hardline <>
    "source map: "       <> hardline <> pretty (topSourceMap s)       <> hardline
