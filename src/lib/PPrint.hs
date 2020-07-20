-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module PPrint (pprint, pprintList, printLitBlock, asStr,
               assertEq, ignoreExcept, PrecedenceLevel(..), DocPrec,
               PrettyPrec(..), atPrec) where

import Control.Monad.Except hiding (Except)
import GHC.Float
import GHC.Stack
import Data.Text.Prettyprint.Doc.Render.Text
import Data.Text.Prettyprint.Doc
import Data.Text (unpack)
import System.Console.ANSI

import Env
import Array
import Syntax

-- Specifies what kinds of operations are allowed to be printed at this point.
-- Printing at AppPrec level means that applications can be printed
-- with no parentheses, but binops must be parenthesized. 
data PrecedenceLevel  = BinOpPrec
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

pBinOp :: PrettyPrec a => a -> Doc ann
pBinOp a = prettyPrec a BinOpPrec

pArg :: PrettyPrec a => a -> Doc ann
pArg a = prettyPrec a ArgPrec

pApp :: PrettyPrec a => a -> Doc ann
pApp a = prettyPrec a AppPrec

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
    IntType  -> "Int"
    BoolType -> "Bool"
    RealType -> "Real"
    StrType  -> "Str"

printDouble :: Double -> Doc ann
printDouble x = p (double2Float x)

instance Pretty LitVal where pretty = prettyFromPrettyPrec
instance PrettyPrec LitVal where
  prettyPrec (IntLit  x) = atPrec ArgPrec $ p x
  prettyPrec (RealLit x) = atPrec ArgPrec $ printDouble x
  prettyPrec (StrLit  x) = atPrec ArgPrec $ p x
  prettyPrec (VecLit  l) = atPrec ArgPrec $ encloseSep "<" ">" ", " $ fmap p l
  prettyPrec (BoolLit b) = atPrec ArgPrec $ if b then "True" else "False"

instance Pretty Block where
  pretty (Block [] expr) = group $ line <> pBinOp expr
  pretty (Block decls expr) = hardline <> prettyLines decls <> pBinOp expr

prettyLines :: Pretty a => [a] -> Doc ann
prettyLines xs = foldMap (\d -> p d <> hardline) xs

instance Pretty Expr where pretty = prettyFromPrettyPrec
instance PrettyPrec Expr where
  prettyPrec (App f x) =
    atPrec AppPrec $ pApp f <+> pArg x
  prettyPrec (Atom x ) = prettyPrec x
  prettyPrec (Op  op ) = prettyPrec op
  prettyPrec (Hof hof) = prettyPrec hof

prettyExprDefault :: PrettyPrec e => PrimExpr e -> DocPrec ann
prettyExprDefault expr =
  case length expr of
    0 -> atPrec ArgPrec primName
    _ -> atPrec AppPrec $ pAppArg primName expr
  where primName = p $ "%" ++ showPrimName expr

instance PrettyPrec e => Pretty (Abs e) where pretty = prettyFromPrettyPrec
instance PrettyPrec e => PrettyPrec (Abs e) where
  prettyPrec (Abs binder body) = atPrec BinOpPrec $ "\\" <> p binder <> "." <> pBinOp body

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
    ArrayType ty   -> atPrec ArgPrec $ "Arr[" <> pBinOp ty <> "]"
    PairType a b   -> atPrec BinOpPrec $ pApp a <+> "&" <+> pApp b
    SumType  a b   -> atPrec BinOpPrec $ pApp a <+> "|" <+> pApp b
    UnitType       -> atPrec ArgPrec "Unit"
    IntRange a b -> if asStr (pArg a) == "0"
      then atPrec AppPrec ("Fin" <+> pArg b)
      else prettyExprDefault $ TCExpr con
    IndexRange _ low high -> atPrec BinOpPrec $ low' <> ".." <> high'
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
    NewtypeApp f xs -> atPrec AppPrec $ pAppArg (pApp f) xs
    _ -> prettyExprDefault $ TCExpr con

instance PrettyPrec e => Pretty (PrimCon e) where pretty = prettyFromPrettyPrec
instance PrettyPrec e => PrettyPrec (PrimCon e) where
  prettyPrec con = case con of
    Lit l       -> prettyPrec l
    ArrayLit _ array -> atPrec ArgPrec $ p array
    PairCon x y -> atPrec ArgPrec $ parens $ pApp x <> "," <+> pApp y
    UnitCon     -> atPrec ArgPrec "()"
    RefCon _ _  -> atPrec ArgPrec "RefCon"
    Coerce t i  -> atPrec BinOpPrec $ pApp i <> "@" <> pApp t
    AnyValue t  -> atPrec AppPrec $ pAppArg "%anyVal" [t]
    SumCon c l r -> atPrec AppPrec $ case asStr (pArg c) of
      "True"  -> pAppArg "Left" [l]
      "False" -> pAppArg "Right" [r]
      _ -> pAppArg "SumCon" [c, l, r]
    NewtypeCon f xs -> atPrec AppPrec $ pAppArg (pApp f) [xs]
    ClassDictHole _ -> atPrec ArgPrec "_"
    Todo e -> atPrec ArgPrec $ "<undefined " <> pArg e <> ">"

instance PrettyPrec e => Pretty (PrimOp e) where pretty = prettyFromPrettyPrec
instance PrettyPrec e => PrettyPrec (PrimOp e) where
  prettyPrec op = case op of
    SumGet e isLeft -> atPrec AppPrec $ (if isLeft then "getLeft" else "getRight") <+> pArg e
    SumTag e        -> atPrec AppPrec $ pAppArg "getTag" [e]
    PrimEffect ref (MPut val ) -> atPrec BinOpPrec $ pApp ref <+> ":=" <+> pApp val
    PrimEffect ref (MTell val) -> atPrec BinOpPrec $ pApp ref <+> "+=" <+> pApp val
    ArrayOffset arr idx off -> atPrec BinOpPrec $ pApp arr <+> "+>" <+> pApp off <+> (parens $ "index:" <+> pBinOp idx)
    ArrayLoad arr       -> atPrec AppPrec $ pAppArg "load" [arr]
    _ -> prettyExprDefault $ OpExpr op

instance PrettyPrec e => Pretty (PrimHof e) where pretty = prettyFromPrettyPrec
instance PrettyPrec e => PrettyPrec (PrimHof e) where
  prettyPrec hof = case hof of
    For dir lam -> atPrec BinOpPrec $ dirStr dir <+> pArg lam
    SumCase c l r -> atPrec BinOpPrec $ "case" <+> pArg c <> hardline
                  <> nest 2 (pBinOp l)            <> hardline
                  <> nest 2 (pBinOp r)
    _ -> prettyExprDefault $ HofExpr hof

instance Pretty a => Pretty (VarP a) where
  pretty (v :> ann) = p v <> ":" <> p ann

instance Pretty ClassName where
  pretty name = case name of
    Data   -> "Data"
    VSpace -> "VS"
    IdxSet -> "Ix"
    Eq     -> "Eq"
    Ord    -> "Ord"

instance Pretty Decl where
  pretty decl = case decl of
    Let _ (NoName:>_) bound -> pBinOp bound
    -- This is just to reduce clutter a bit. We can comment it out when needed.
    -- Let (v:>Pi _)   bound -> p v <+> "=" <+> p bound
    Let _ b bound -> align $ p b <+> "=" <> (nest 2 $ group $ line <> pBinOp bound)

instance Pretty Atom where pretty = prettyFromPrettyPrec
instance PrettyPrec Atom where
  prettyPrec atom = case atom of
    Var (x:>_)  -> atPrec ArgPrec $ p x
    Lam (Abs b (TabArrow, body))   -> atPrec BinOpPrec $ align $ nest 2 $ "for " <> p b <> "." <+> p body
    Lam (Abs b (_, body)) -> atPrec BinOpPrec $ align $ nest 2 $ "\\" <> p b <> "." <+> p body
    Pi  (Abs (NoName:>a) (arr, b)) -> atPrec BinOpPrec $ pArg a <+> p arr <+> pBinOp b
    Pi  (Abs a           (arr, b)) -> atPrec BinOpPrec $ parens (p a) <+> p arr <+> pBinOp b
    TC  e -> prettyPrec e
    Con e -> prettyPrec e
    Eff e -> atPrec ArgPrec $ p e

instance Pretty IExpr where
  pretty (ILit v) = p v
  pretty (IVar (v:>_)) = p v

instance PrettyPrec IExpr where prettyPrec = atPrec ArgPrec . pretty 

instance Pretty IType where
  pretty (IRefType t) = "Ref" <+> (parens $ p t)
  pretty (IValType t) = p t

instance PrettyPrec IType where prettyPrec = atPrec ArgPrec . pretty 

instance Pretty ImpProg where
  pretty (ImpProg block) = vcat (map prettyStatement block)

instance Pretty ImpFunction where
  pretty (ImpFunction vsOut vsIn body) =
                   "in:        " <> p vsIn
    <> hardline <> "out:       " <> p vsOut
    <> hardline <> p body

prettyStatement :: (Maybe IVar, ImpInstr) -> Doc ann
prettyStatement (Nothing, instr) = p instr
prettyStatement (Just b , instr) = p b <+> "=" <+> p instr

instance Pretty ImpInstr where
  pretty (IPrimOp op)            = pBinOp op
  pretty (Load ref)              = "load"  <+> p ref
  pretty (Store dest val)        = "store" <+> p dest <+> p val
  pretty (Alloc t s)             = "alloc" <+> p (scalarTableBaseType t) <> "[" <> p s <> "]" <+> "@" <> p t
  pretty (IOffset expr lidx t)   = p expr <+> "++" <+> p lidx <+> (parens $ "coerced to:" <+> p t)
  pretty (Free (v:>_))           = "free"  <+> p v
  pretty (Loop d i n block)      = dirStr d <+> p i <+> "<" <+> p n <>
                                   nest 4 (hardline <> p block)
  pretty (IWhile cond body)      = "while" <+>
                                     nest 2 (hardline <> p cond) <> "do" <>
                                     nest 2 (hardline <> p body)

dirStr :: Direction -> Doc ann
dirStr Fwd = "for"
dirStr Rev = " rof"

instance Pretty a => Pretty (SetVal a) where
  pretty NotSet = ""
  pretty (Set a) = p a

instance Pretty Output where
  pretty (TextOut s) = pretty s
  pretty (HeatmapOut _ _ _) = "<graphical output>"
  pretty (ScatterOut _ _  ) = "<graphical output>"
  pretty (PassInfo name s) = "===" <+> p name <+> "===" <> hardline <> p s
  pretty (EvalTime t) = "=== Eval time: " <+> p t <> "s ==="
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
    UnknownBinder -> "<unknown binder>"

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
      atPrec BinOpPrec $ align $ "\\" <> annImplicity h (prettyUBinder binder)
                                      <> "." <+> nest 2 (pBinOp body)
    UApp TabArrow f x -> atPrec AppPrec $ pArg f <> "." <> pArg x
    UApp _        f x -> atPrec AppPrec $ pAppArg (pApp f) [x]
    UFor dir binder body ->
      atPrec BinOpPrec $ kw <+> prettyUBinder binder <> "."
                            <+> nest 2 (pBinOp body)
      where kw = case dir of Fwd -> "for"
                             Rev -> "rof"
    UPi a arr b -> atPrec BinOpPrec $ p a <+> pretty arr <+> pBinOp b
    UDecl decl body -> atPrec BinOpPrec $ align $ p decl <> hardline
                                                         <> pBinOp body
    UHole -> atPrec ArgPrec "_"
    UTabCon xs ann -> atPrec ArgPrec $ p xs <> foldMap (prettyAnn . p) ann
    UIndexRange low high -> atPrec BinOpPrec $ low' <> ".." <> high'
      where
        low'  = case low of  InclusiveLim x -> pApp x
                             ExclusiveLim x -> pApp x <> "<"
                             Unlimited      -> ""
        high' = case high of InclusiveLim x -> pApp x
                             ExclusiveLim x -> "<" <> pApp x
                             Unlimited      -> ""
    UPrimExpr prim -> prettyPrec prim

prettyAnn :: Doc ann -> Doc ann
prettyAnn ty = ":" <+> ty

instance Pretty a => Pretty (Limit a) where
  pretty Unlimited = "unlimited"
  pretty (ExclusiveLim x) = "excLim" <+> p x
  pretty (InclusiveLim x) = "incLim" <+> p x

instance Pretty UDecl where
  pretty (ULet _ b rhs) =
    align $ prettyUBinder b <+> "=" <> (nest 2 $ group $ line <> pBinOp rhs)

instance Pretty UPat' where
  pretty pat = case pat of
    PatBind (x:>()) -> p x
    PatPair x y -> parens $ p x <> ", " <> p y
    PatUnit -> "()"

prettyUBinder :: UBinder -> Doc ann
prettyUBinder (pat, ann) = p pat <> annDoc where
  annDoc = case ann of
    Just ty -> ":" <> pApp ty
    Nothing -> mempty

instance Pretty EffectRow where
  pretty (EffectRow [] Nothing) = mempty
  pretty (EffectRow effs tailVar) =
    braces $ hsep (punctuate "," (map prettyEff effs)) <> tailStr
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
