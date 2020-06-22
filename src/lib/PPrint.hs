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
               assertEq, ignoreExcept) where

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

pprint :: Pretty a => a -> String
pprint x = asStr $ pretty x

pprintList :: Pretty a => [a] -> String
pprintList xs = asStr $ vsep $ punctuate "," (map p xs)

asStr :: Doc ann -> String
asStr doc = unpack $ renderStrict $ layoutPretty defaultLayoutOptions $ doc

p :: Pretty a => a -> Doc ann
p = pretty

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

instance Pretty BaseType where
  pretty t = case t of
    IntType  -> "Int"
    BoolType -> "Bool"
    RealType -> "Real"
    StrType  -> "Str"

printDouble :: Double -> Doc ann
printDouble x = p (double2Float x)

instance Pretty LitVal where
  pretty (IntLit x ) = p x
  pretty (RealLit x) = printDouble x
  pretty (StrLit x ) = p x
  pretty (BoolLit b) = if b then "True" else "False"

instance Pretty Block where
  pretty (Block [] expr) = " " <> p expr
  pretty (Block decls expr) = nest 2 $ hardline <> prettyLines decls <> p expr

prettyLines :: Pretty a => [a] -> Doc ann
prettyLines xs = foldMap (\d -> p d <> hardline) xs

instance Pretty Expr where
  pretty (App f x) = parens (p f) <+> parens (p x)
  pretty (Atom x ) = p x
  pretty (Op  op ) = p op
  pretty (Hof hof) = p hof

prettyExprDefault :: Pretty e => PrimExpr e -> Doc ann
prettyExprDefault expr =
  p ("%" ++ showPrimName expr) <> foldMap (\x -> " " <> p x) expr

instance Pretty e => Pretty (Abs e) where
  pretty (Abs binder body) = "\\" <> p binder <> "." <> p body

instance Pretty e => Pretty (PrimExpr e) where
  pretty (TCExpr  e) = p e
  pretty (ConExpr e) = p e
  pretty (OpExpr  e) = p e
  pretty (HofExpr e) = p e

instance Pretty e => Pretty (PrimTC e) where
  pretty con = case con of
    BaseType b     -> p b
    PairType a b   -> parens $ p a <+> "&" <+> p b
    UnitType       -> "Unit"
    IntRange a b -> if s1 == "0...<" then parens ("Fin" <+> p s2) else ans
      where ans = p a <> "...<" <> p b
            (s1, s2) = splitAt 5 (asStr ans)
    IndexRange _ low high -> low' <> "." <> high'
      where
        low'  = case low  of InclusiveLim x -> p x <> "."
                             ExclusiveLim x -> p x <> "<"
                             Unlimited      ->        "."
        high' = case high of InclusiveLim x -> "." <> p x
                             ExclusiveLim x -> "<" <> p x
                             Unlimited      -> "."
    TypeKind -> "Type"
    EffectRowKind -> "EffKind"
    _ -> prettyExprDefault $ TCExpr con

instance Pretty e => Pretty (PrimCon e) where
  pretty con = case con of
    Lit l       -> p l
    ArrayLit _ array -> p array
    PairCon x y -> parens $ p x <+> "," <+> p y
    UnitCon     -> "()"
    RefCon _ _  -> "RefCon"
    AFor n body -> parens $ "afor *:" <> p n <+> "." <+> p body
    AGet e      -> "aget" <+> p e
    AsIdx n i   -> p i <> "@" <> parens (p n)
    AnyValue t  -> parens $ "AnyValue @" <> p t
    SumCon c l r -> parens $ case pprint c of
      "True"  -> "Left"  <+> p l
      "False" -> "Right" <+> p r
      _ -> "SumCon" <+> p c <+> p l <+> p r
    ClassDict _ _ _ -> "<dictionary>"
    ClassDictHole _ -> "_"
    Todo e -> "<undefined " <> p e <> ""

instance Pretty e => Pretty (PrimOp e) where
  pretty op = case op of
    SumGet e isLeft -> parens $ (if isLeft then "projLeft" else "projRight") <+> p e
    SumTag e        -> parens $ "projTag" <+> p e
    PrimEffect ref (MPut val ) ->  p ref <+> ":=" <+> p val
    PrimEffect ref (MTell val) ->  p ref <+> "+=" <+> p val
    _ -> prettyExprDefault $ OpExpr op

instance Pretty e => Pretty (PrimHof e) where
  pretty hof = case hof of
    For dir lam -> dirStr dir <+> p lam
    SumCase c l r -> "case" <+> parens (p c) <> hardline
                  <> nest 2 (p l)            <> hardline
                  <> nest 2 (p r)
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
    Let _ (NoName:>_) bound -> p bound
    -- This is just to reduce clutter a bit. We can comment it out when needed.
    -- Let (v:>Pi _)   bound -> p v <+> "=" <+> p bound
    Let _ b bound -> p b <+> "=" <+> p bound

instance Pretty Atom where
  pretty atom = case atom of
    Var (x:>_)  -> p x
    Lam (Abs b (_, body)) -> "\\" <> p b <> "." <> p body
    Pi  (Abs (NoName:>a) (arr, b)) -> parens $ p a <> p arr <> p b
    Pi  (Abs a           (arr, b)) -> parens $ p a <> p arr <> p b
    TC  e -> p e
    Con e -> p e
    Eff e -> p e

instance Pretty IExpr where
  pretty (ILit v) = p v
  pretty (IVar (v:>_)) = p v

instance Pretty IType where
  pretty (IRefType t) = "Ref" <+> (parens $ p t)
  pretty (IValType b) = p b

instance Pretty IDimType where
  pretty (IUniform (ILit (IntLit sz))) = p sz
  pretty (IUniform _)     = "<uniform, dependent>"
  pretty (IPrecomputed _) = "<precomptued>"

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
  pretty (IPrimOp op)         = p op
  pretty (Load ref)           = "load"  <+> p ref
  pretty (Store dest val)     = "store" <+> p dest <+> p val
  pretty (Copy dest source s) = "copy"  <+> p dest <+> p source <+> parens (p s <+> "elems")
  pretty (Alloc t s)          = "alloc" <+> p (scalarTableBaseType t) <> "[" <> p s <> "]" <+> "@" <> p t
  pretty (IOffset expr idx)   = p expr <+> "+>" <+> p idx
  pretty (Free (v:>_))        = "free"  <+> p v
  pretty (Loop d i n block)   = dirStr d <+> p i <+> "<" <+> p n <>
                                nest 4 (hardline <> p block)

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
  pretty (Module decls) = prettyLines decls

instance (Pretty a, Pretty b) => Pretty (Either a b) where
  pretty (Left  x) = "Left"  <+> p x
  pretty (Right x) = "Right" <+> p x

instance Pretty BinderInfo where
  pretty b = case b of
    LamBound _ _  -> "(lambda binder)"
    LetBound _ e  -> p e
    PiBound _     -> "(pi binder)"
    UnknownBinder -> "(unknown)"

instance Pretty UModule where
  pretty (UModule decls) = prettyLines decls

instance Pretty a => Pretty (WithSrc a) where
  pretty (WithSrc _ x) = p x

instance Pretty UExpr' where
  pretty expr = case expr of
    UVar (v:>_) -> p v
    ULam pat h body ->
      "\\" <> annImplicity h (p pat) <> "." <> nest 2 (hardline <> p body)
    UApp TabArrow f x -> p f <> "." <> p x
    UApp _        f x -> p f <+> p x
    UFor dir pat body ->
      kw <+> p pat <+> "." <> nest 2 (hardline <> p body)
      where kw = case dir of Fwd -> "for"
                             Rev -> "rof"
    UPi a arr b -> parens (p a) <> pretty arr <> p b
    UDecl decl body -> p decl <> hardline <> p body
    UHole -> "_"
    UTabCon xs ann -> p xs <> foldMap (prettyAnn . p) ann
    UIndexRange low high -> "IndexRange" <+> p low <+> p high
    UPrimExpr prim -> p prim

prettyAnn :: Doc ann -> Doc ann
prettyAnn ty = ":" <+> ty

instance Pretty a => Pretty (Limit a) where
  pretty Unlimited = "unlimited"
  pretty (ExclusiveLim x) = "excLim" <+> p x
  pretty (InclusiveLim x) = "incLim" <+> p x

instance Pretty UDecl where
  pretty (ULet _ pat rhs) = p pat <+> "=" <+> p rhs

instance Pretty a => Pretty (PatP' a) where
  pretty pat = case pat of
    PatBind x -> p x
    PatPair x y -> parens $ p x <> ", " <> p y
    PatUnit -> "()"

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
