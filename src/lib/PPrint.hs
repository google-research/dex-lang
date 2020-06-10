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
               assertEq, assertNoShadow, ignoreExcept) where

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

instance Pretty Type where
  pretty ty = case ty of
    TypeVar v   -> p v
    ArrowType l (Pi a (eff, b))
      | isPure eff -> parens $ p a <+> arrStr l <+>           p b
      | otherwise  -> parens $ p a <+> arrStr l <+> p eff <+> p b
    TabType (Pi a b)  -> parens $ p a <> "=>" <> p b
    Forall bs qs body -> header <+> p body
      where
        header = "A" <+> hsep (map p bs) <> qual <> "."
        qual = case qs of
                 [] -> mempty
                 _  -> " |" <+> hsep (punctuate "," (map p qs))
    TypeAlias _ _ -> "<type alias>"  -- TODO
    Effect row t -> "{" <> row' <+> tailVar <> "}"
      where
        row' = hsep $ punctuate "," $
                 [(p eff <+> p v) | (v, (eff,_)) <- envPairs row]
        tailVar = case t of Nothing -> mempty
                            Just v  -> "|" <+> p v
    NoAnn  -> "-"
    TC con -> p con
    where
      arrStr :: Type -> Doc ann
      arrStr Lin = "--o"
      arrStr _        = "->"

instance Pretty ty => Pretty (TyCon ty Atom) where
  pretty con = case con of
    BaseType b     -> p b
    RecType r      -> p $ fmap (asStr . p) r
    SumType (l, r) -> "Either" <+> p l <+> p r
    RefType t      -> "Ref" <+> p t
    TypeApp f xs   -> p f <+> hsep (map p xs)
    JArrayType dims b    -> p b <> p dims <> "j"
    ArrayType  b         -> p b <> "*"
    -- This rule forces us to specialize to Atom. Is there a better way?
    IntRange (IntVal 0) (IntVal n) -> p n
    IntRange a b -> p a <> "...<" <> p b
    IndexRange _ low high -> low' <> "." <> high'
      where
        low'  = case low  of InclusiveLim x -> p x <> "."
                             ExclusiveLim x -> p x <> "<"
                             Unlimited      ->        "."
        high' = case high of InclusiveLim x -> "." <> p x
                             ExclusiveLim x -> "<" <> p x
                             Unlimited      -> "."
    LinCon    -> "Lin"
    NonLinCon -> "NonLin"

instance Pretty b => Pretty (PiType b) where
  pretty (Pi a b) = "Pi" <+> p a <+> p b

instance Pretty EffectName where
  pretty x = p (show x)

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

instance Pretty Expr where
  pretty (Decl decl body) = p decl <> hardline <> p body
  pretty (CExpr expr) = p (OpExpr expr)
  pretty (Atom atom) = p atom

instance Pretty FExpr where
  pretty expr = case expr of
    FVar (v:>_) -> p v
    FDecl decl body -> p decl <> hardline <> p body
    FPrimExpr (OpExpr  e) -> parens $ p e
    FPrimExpr (ConExpr e) -> p e
    SrcAnnot subexpr _ -> p subexpr
    Annot subexpr ty -> p subexpr <+> ":" <+> p ty

instance Pretty FDecl where
  -- TODO: special-case annotated leaf var (print type on own line)
  pretty (LetMono pat expr) = p pat <+> "=" <+> p expr
  pretty (LetPoly (v:>ty) (FTLam _ _ body)) =
    p v <+> ":" <+> p ty <> line <>
    p v <+> "="  <+> p body
  pretty (TyDef v ty) = "type" <+> p v <+> "=" <+> p ty

instance (Pretty ty, Pretty e, PrettyLam lam) => Pretty (PrimExpr ty e lam) where
  pretty (OpExpr  op ) = p op
  pretty (ConExpr con) = p con

instance (Pretty ty, Pretty e, PrettyLam lam) => Pretty (PrimOp ty e lam) where
  pretty (App _ e1 e2) = p e1 <+> p e2
  pretty (TApp e ts) = p e <+> hsep (map (\t -> "@" <> p t) ts)
  pretty (For d lam) = dirStr d <+> i <+> "." <+> nest 3 (line <> body)
    where (i, body) = prettyLam lam
  pretty (TabCon _ _ xs) = list (map pretty xs)
  pretty (TabGet   x i) = p x <> "." <> p i
  pretty (RecGet   x i) = p x <> "#" <> p i
  pretty (Cmp cmpOp _ x y) = "%cmp" <> p (show cmpOp) <+> p x <+> p y
  pretty (Select ty b x y) = "%select @" <> p ty <+> p b <+> p x <+> p y
  pretty (FFICall s _ _ xs) = "%%" <> p s <+> tup xs
  pretty (SumGet e isLeft) = parens $ (if isLeft then "projLeft" else "projRight") <+> p e
  pretty (SumTag e)        = parens $ "projTag" <+> p e
  pretty (SumCase c l r) = "case (" <+> p c <> ")" <> nest 2 ("\n" <> prettyL l) <+> nest 2 ("\n" <> prettyL r)
  pretty (PrimEffect ref (MPut val))  = p ref <+> ":=" <+> p val
  pretty (PrimEffect ref (MTell val)) = p ref <+> "+=" <+> p val
  pretty (PrimEffect ref MAsk) = "ask" <+> p ref
  pretty (PrimEffect ref MGet) = "get" <+> p ref
  pretty op = prettyExprDefault (OpExpr op)

prettyPrimCon :: (Pretty ty, Pretty e, PrettyLam lam) => PrimCon ty e lam -> Doc ann
prettyPrimCon (Lit l)       = p l
prettyPrimCon (ArrayLit array) = p array
prettyPrimCon (Lam _ _ lam) = parens $ prettyL lam
prettyPrimCon (RecCon r)    = p r
prettyPrimCon (AFor n body) = parens $ "afor *:" <> p n <+> "." <+> p body
prettyPrimCon (AGet e)      = "aget" <+> p e
prettyPrimCon (AsIdx n i)   = p i <> "@" <> p n
prettyPrimCon (AnyValue t)  = parens $ "AnyValue @" <> p t
prettyPrimCon (SumCon c l r) = parens $ "SumCon" <+> p c <+> p l <+> p r
prettyPrimCon con = prettyExprDefault (ConExpr con)

instance {-# OVERLAPPABLE #-} (Pretty ty, Pretty e, PrettyLam lam) => Pretty (PrimCon ty e lam) where
  pretty = prettyPrimCon

instance (Pretty ty, PrettyLam lam) => Pretty (PrimCon ty Atom lam) where
  pretty (SumCon (Con (Lit (BoolLit True)))  l _) = "Left"  <+> p l
  pretty (SumCon (Con (Lit (BoolLit False))) _ r) = "Right" <+> p r
  pretty con = prettyPrimCon con

prettyExprDefault :: (Pretty e, PrettyLam lam) => PrimExpr ty e lam -> Doc ann
prettyExprDefault expr =
  p ("%" ++ nameToStr blankExpr) <+> hsep (map p xs ++ map (nest 2 . ("\n"<>) . prettyL) lams)
  where (blankExpr, (_, xs, lams)) = unzipExpr expr

prettyL :: PrettyLam a => a -> Doc ann
prettyL lam = "\\" <> v <+> "." <> nest 3 (line <> body)
  where (v, body) = prettyLam lam

class PrettyLam a where
  prettyLam :: a -> (Doc ann, Doc ann)

instance PrettyLam LamExpr where
  prettyLam (LamExpr b e) = (p b, p e)

instance PrettyLam FLamExpr where
  prettyLam (FLamExpr pat e) = (p pat, p e)

instance PrettyLam () where
  prettyLam () = ("", "")

instance (Pretty a, Pretty b) => PrettyLam (a, b) where
  prettyLam (x, y) = (p x, p y)

instance PrettyLam (PiType EffectiveType) where
  prettyLam (Pi a (eff, b)) = (p a, p eff <+> p b)

instance PrettyLam (PiType Type) where
  prettyLam (Pi a b) = (p a, p b)

instance Pretty Kind where
  pretty TyKind      = "Type"
  pretty MultKind    = "Mult"
  pretty EffectKind  = "Effect"
  pretty k = p $ show k

instance Pretty a => Pretty (VarP a) where
  pretty (v :> ann) =
    case asStr ann' of
      "-"    -> p v
      "Type" -> p v
      _      -> p v <> ":" <> ann'
    where ann' = p ann

instance Pretty ClassName where
  pretty name = case name of
    Data   -> "Data"
    VSpace -> "VS"
    IdxSet -> "Ix"
    Eq     -> "Eq"
    Ord    -> "Ord"

instance Pretty Decl where
  pretty decl = case decl of
    Let (NoName:>_) bound -> p (OpExpr bound)
    Let b bound -> p b <+> "=" <+> p (OpExpr bound)

instance Pretty Atom where
  pretty atom = case atom of
    Var (x:>_)  -> p x
    TLam vs qs body -> "tlam" <+> p vs <+> "|" <+> p qs <+> "." <+> p body
    Con con -> p (ConExpr con)

tup :: Pretty a => [a] -> Doc ann
tup [x] = p x
tup xs  = tupled $ map p xs

instance Pretty IExpr where
  pretty (ILit v) = p v
  pretty (IVar (v:>_)) = p v

instance Pretty IType where
  pretty (IRefType (dimTypes, ty)) = "Ptr (" <> p ty <> p dimTypes <> ")"
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
  pretty (IPrimOp op)       = p op
  pretty (Load ref)         = "load"  <+> p ref
  pretty (Store dest val)   = "store" <+> p dest <+> p val
  pretty (Copy dest source) = "copy"  <+> p dest <+> p source
  pretty (CastArray v t)    = "cast"  <+> p v <+> "as" <+> p t
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

instance (Pretty a, Pretty b) => Pretty (LorT a b) where
  pretty (L x) = "L" <+> p x
  pretty (T x) = "T" <+> p x

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

instance Pretty body => Pretty (ModuleP body) where
  pretty (Module _ (imports, exports) body) = "imports:" <+> p imports
                             <> hardline <> p body
                             <> hardline <> "exports:" <+> p exports

instance (Pretty a, Pretty b) => Pretty (Either a b) where
  pretty (Left  x) = "Left"  <+> p x
  pretty (Right x) = "Right" <+> p x

instance Pretty Array where
  pretty a = p b <> "[" <> p size <> "]@vec"
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

assertEq :: (MonadError Err m, Pretty a, Eq a) => a -> a -> String -> m ()
assertEq x y s = if x == y then return ()
                           else throw CompilerErr msg
  where msg = s ++ ": " ++ pprint x ++ " != " ++ pprint y ++ "\n"

assertNoShadow :: (MonadError Err m, Pretty b) => Env a -> VarP b -> m ()
assertNoShadow env v = do
  if v `isin` env
    then throw CompilerErr $ pprint v ++ " shadowed"
    else return ()

ignoreExcept :: HasCallStack => Except a -> a
ignoreExcept (Left e) = error $ pprint e
ignoreExcept (Right x) = x
