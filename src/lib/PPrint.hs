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
  pretty (Block [] expr) = p expr
  pretty (Block decls expr) = nest 2 $
    hardline <> foldMap (\d -> p d <> hardline) decls <> p expr

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
    PairType a b   -> parens $ p a <+> "**" <+> p b
    RecType r      -> p $ fmap (asStr . p) r
    ArrayType (shape, b) -> p b <> p shape
    IntRange a b -> if s1 == "0...<" then p s2 else ans
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
    EffectsKind -> "EffectKind"
    _ -> prettyExprDefault $ TCExpr con

instance Pretty e => Pretty (PrimCon e) where
  pretty con = case con of
    Lit l       -> p l
    ArrayLit array -> p array
    PairCon x y -> parens $ p x <+> "," <+> p y
    UnitCon     -> "()"
    RefCon _ _  -> "RefCon"
    RecCon r    -> p r
    AFor n body -> parens $ "afor *:" <> p n <+> "." <+> p body
    AGet e      -> "aget" <+> p e
    AsIdx n i   -> p i <> "@" <> p n
    AnyValue t  -> parens $ "AnyValue @" <> p t
    SumCon c l r -> parens $ "SumCon" <+> p c <+> p l <+> p r


instance Pretty e => Pretty (PrimOp e) where
  pretty op = case op of
    ArrayGep x i ->  p x <> "." <> p i
    FFICall s _ _ xs -> "%%" <> p s <+> tup xs
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
    Let (NoName:>_) bound -> p bound
    Let b bound -> p b <+> "=" <+> p bound

instance Pretty Atom where
  pretty atom = case atom of
    Var (x:>_)  -> p x
    Lam (Abs b (_, body)) -> "\\" <> p b <> "." <> p body
    Pi  (Abs a (arr, b)) -> parens $ prettyArrow arr (p a) (p b)
    TC  e -> p e
    Con e -> p e
    Eff e -> p e

instance Pretty e => Pretty (PrimEff e) where
  pretty PureEff = "|"
  pretty (ExtendEff (effName, region) rest) =
    p effName <+> p region <> "," <+> p rest

tup :: Pretty a => [a] -> Doc ann
tup [x] = p x
tup xs  = tupled $ map p xs

instance Pretty IExpr where
  pretty (ILit v) = p v
  pretty (IVar (v:>_)) = p v

instance Pretty IType where
  pretty (IRefType (ty, shape)) = "Ptr (" <> p ty <> p shape <> ")"
  pretty (IValType b) = p b

instance Pretty ImpProg where
  pretty (ImpProg block) = vcat (map prettyStatement block)

instance Pretty ImpFunction where
  pretty (ImpFunction vsOut vsIn body) =
                   "in:  " <> p vsIn
    <> hardline <> "out: " <> p vsOut
    <> hardline <> p body

prettyStatement :: (Maybe IVar, ImpInstr) -> Doc ann
prettyStatement (Nothing, instr) = p instr
prettyStatement (Just b , instr) = p b <+> "=" <+> p instr

instance Pretty ImpInstr where
  pretty (IPrimOp op)       = p op
  pretty (Load ref)         = "load"  <+> p ref
  pretty (Store dest val)   = "store" <+> p dest <+> p val
  pretty (Copy dest source) = "copy"  <+> p dest <+> p source
  pretty (Alloc ty)         = "alloc" <+> p ty
  pretty (IGet expr idx)    = p expr <> "." <> p idx
  pretty (Free (v:>_))      = "free"  <+> p v
  pretty (Loop d i n block) = dirStr d <+> p i <+> "<" <+> p n <>
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
  pretty (Module _ imports exports body) =
       "imports:" <+> p imports
    <> hardline <> p body
    <> hardline <> "exports:" <+> p exports

instance (Pretty a, Pretty b) => Pretty (Either a b) where
  pretty (Left  x) = "Left"  <+> p x
  pretty (Right x) = "Right" <+> p x

instance Pretty TopEnv where
  pretty (TopEnv infEnv simpEnv ruleEnv) =
    "Inference env:     " <+> p infEnv  <> hardline <>
    "Simplification env:" <+> p simpEnv <> hardline <>
    "RuleEnv env:       " <+> p ruleEnv <> hardline

instance Pretty UModule where
  pretty (UModule imports exports decls) =
                     "imports:" <+> p imports
       <> hardline <> foldMap (\decl -> p decl <> hardline) decls
       <> hardline <> "exports:" <+> p exports

instance Pretty UExpr where
  pretty (UPos _ expr) = p expr

instance Pretty UExpr' where
  pretty expr = case expr of
    UVar (v:>_) -> p v
    ULam pat h body -> "\\" <> annImplicity h (p pat) <> "." <> nest 2 (p body)
    UApp f x -> p f <+> p x
    UFor dir pat body -> kw <+> p pat <+> "." <+> p body
      where kw = case dir of Fwd -> "for"
                             Rev -> "rof"
    UPi a arr b -> prettyArrow arr (parens (p a)) (eff' <> p b)
       where eff' = case arr of PlainArrow UPure -> mempty
                                PlainArrow eff   -> p eff
                                _ -> mempty
    UDecl decl body -> p decl <> hardline <> p body
    UPrimExpr prim -> p prim

instance Pretty UDecl where
  pretty (ULet pat rhs) = p pat <+> "=" <+> p rhs

instance Pretty Arrow where
  pretty ah = prettyArrow ah mempty mempty

instance Pretty UEffects where
  pretty (UEffects [] Nothing) = mempty
  pretty (UEffects effs tailVar) =
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

prettyArrow :: ArrowP a -> Doc ann -> Doc ann -> Doc ann
prettyArrow arr a b = case arr of
  PlainArrow _  -> a <> "->"  <> b
  TabArrow      -> a <> "=>"  <> b
  LinArrow      -> a <> "--o" <> b
  ImplicitArrow -> "{" <> a <> "} ->" <> b

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

assertEq :: (MonadError Err m, Pretty a, Eq a) => a -> a -> String -> m ()
assertEq x y s = if x == y then return ()
                           else throw CompilerErr msg
  where msg = s ++ ": " ++ pprint x ++ " != " ++ pprint y ++ "\n"

ignoreExcept :: HasCallStack => Except a -> a
ignoreExcept (Left e) = error $ pprint e
ignoreExcept (Right x) = x
