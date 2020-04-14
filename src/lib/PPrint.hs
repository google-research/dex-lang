-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module PPrint (pprint, pprintList,
               assertEq, ignoreExcept, printLitBlock, asStr) where

import Control.Monad.Except hiding (Except)
import GHC.Float
import Data.Text.Prettyprint.Doc.Render.Text
import Data.Text.Prettyprint.Doc
import Data.Text (unpack)

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

instance Pretty Type where
  pretty ty = case ty of
    BaseType b  -> p b
    TypeVar v   -> p v
    ArrowType l (Pi a (eff, b))
      | isPure eff -> parens $ p a <+> arrStr l <+>           p b
      | otherwise  -> parens $ p a <+> arrStr l <+> p eff <+> p b
    TabType a b -> parens $ p a <> "=>" <> p b
    RecType r   -> p $ fmap (asStr . p) r
    Ref t       -> "Ref" <+> p t
    ArrayType shape b -> p b <> p shape
    TypeApp f xs -> p f <+> hsep (map p xs)
    Forall bs qs body -> header <+> p body
      where
        header = "A" <+> hsep (map p bs) <> qual <> "."
        qual = case qs of
                 [] -> mempty
                 _  -> " |" <+> hsep (punctuate "," (map p qs))
    TypeAlias _ _ -> "<type alias>"  -- TODO
    IdxSetLit i -> p i
    Range a b -> "Range" <+> p a <+> p b
    DepLit x  -> "(DepLit" <+> p x <+> ")"
    Dep x  -> "(Dep" <+> p x <+> ")"
    NoDep  -> "NoDep"
    Lin    -> "Lin"
    NonLin -> "NonLin"
    Effect row t -> "{" <> row' <+> tailVar <> "}"
      where
        row' = hsep $ punctuate "," $
                 [(p eff <+> p v) | (v, (eff,_)) <- envPairs row]
        tailVar = case t of Nothing -> mempty
                            Just v  -> "|" <+> p v
    NoAnn  -> ""
    where
      arrStr :: Type -> Doc ann
      arrStr Lin = "--o"
      arrStr _   = "->"

instance Pretty PiType where
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
  pretty (FRuleDef _ _ _) = "<TODO: rule def>"
  pretty (TyDef v ty) = "type" <+> p v <+> "=" <+> p ty

instance (Pretty ty, Pretty e, PrettyLam lam) => Pretty (PrimExpr ty e lam) where
  pretty (OpExpr  op ) = p op
  pretty (ConExpr con) = p con

instance (Pretty ty, Pretty e, PrettyLam lam) => Pretty (PrimOp ty e lam) where
  pretty (App _ _ e1 e2) = p e1 <+> p e2
  pretty (TApp e ts) = p e <+> hsep (map (\t -> "@" <> p t) ts)
  pretty (For lam) = "for" <+> i <+> "." <+> nest 3 (line <> body)
    where (i, body) = prettyLam lam
  pretty (TabCon _ _ xs) = list (map pretty xs)
  pretty (TabGet   x i) = p x <> "." <> p i
  pretty (RecGet   x i) = p x <> "#" <> p i
  pretty (ArrayGep x i) = p x <> "." <> p i
  pretty (LoadScalar x) = "load(" <> p x <> ")"
  pretty (Cmp cmpOp _ x y) = "%cmp" <> p (show cmpOp) <+> p x <+> p y
  pretty (FFICall s _ _ xs) = "%%" <> p s <> tup xs
  pretty op = prettyExprDefault (OpExpr op)

instance (Pretty ty, Pretty e, PrettyLam lam) => Pretty (PrimCon ty e lam) where
  pretty (Lit l)       = p l
  pretty (Lam _ _ lam) = parens $ prettyL lam
  pretty (RecCon r)    = p r
  pretty (AFor n body) = parens $ "afor *::" <> p n <+> "." <+> p body
  pretty (AsIdx n i)   = p i <> "@" <> p n
  pretty (ArrayRef array) = p array
  pretty con = prettyExprDefault (ConExpr con)

prettyExprDefault :: (Pretty e, PrettyLam lam) => PrimExpr ty e lam -> Doc ann
prettyExprDefault expr =
  p ("%" ++ nameToStr blankExpr) <+> hsep (map p xs ++ map prettyL lams)
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

instance PrettyLam PiType where
  prettyLam (Pi a (eff,b)) = (p a, p eff <+> p b)

instance Pretty Kind where
  pretty TyKind     = "Type"
  pretty MultKind   = "Mult"
  pretty EffectKind = "Effect"
  pretty k = p $ show k

instance Pretty a => Pretty (VarP a) where
  pretty (v :> ann) =
    case asStr ann' of
      ""     -> p v
      "Type" -> p v
      _      -> p v <> ":" <> ann'
    where ann' = p ann

instance Pretty ClassName where
  pretty name = case name of
    Data   -> "Data"
    VSpace -> "VS"
    IdxSet -> "Ix"

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
  pretty (IGet expr idx) = p expr <> "." <> p idx
  pretty (IRef ref) = p ref

instance Pretty IType where
  pretty (IRefType (ty, shape)) = "Ptr (" <> p ty <> p shape <> ")"
  pretty (IValType b) = p b

instance Pretty ImpProg where
  pretty (ImpProg block) = vcat (map prettyStatement block)

prettyStatement :: (Maybe IVar, ImpInstr) -> Doc ann
prettyStatement (Nothing, instr) = p instr
prettyStatement (Just b , instr) = p b <+> "=" <+> p instr

instance Pretty ImpInstr where
  pretty (IPrimOp op)       = p op
  pretty (Load ref)         = "load"  <+> p ref
  pretty (Store dest val)   = "store" <+> p dest <+> p val
  pretty (Copy dest source) = "copy"  <+> p dest <+> p source
  pretty (Alloc ty)         = "alloc" <+> p ty
  pretty (Free (v:>_))      = "free"  <+> p v
  pretty (Loop i n block)   = "for"   <+> p i <+> "<" <+> p n <>
                               nest 4 (hardline <> p block)

instance Pretty Array where
  pretty (Array shape b _) = "Ref::" <> p b <> p shape

instance Pretty a => Pretty (SetVal a) where
  pretty NotSet = ""
  pretty (Set a) = p a

instance (Pretty a, Pretty b) => Pretty (LorT a b) where
  pretty (L x) = "L" <+> p x
  pretty (T x) = "T" <+> p x

instance Pretty Output where
  pretty (TextOut   s) = pretty s
  pretty (HeatmapOut _ _ _) = "<graphical output>"
  pretty (ScatterOut _ _  ) = "<graphical output>"
  pretty (PassInfo name t s) = "===" <+> p name <+> "===" <> hardline <> p s <> t'
    where t' = case t of "" -> ""
                         _  -> hardline <> "time:" <+> p t

instance Pretty PassName where
  pretty x = p $ show x

instance Pretty SourceBlock where
  pretty block = pretty (sbText block)

instance Pretty Result where
  pretty (Result outs r) = vcat (map pretty outs) <> maybeErr
    where maybeErr = case r of Left err -> p err
                               Right () -> mempty

instance Pretty TopEnv where
  pretty (TopEnv _ subEnv _) = p subEnv

instance Pretty body => Pretty (ModuleP body) where
  pretty (Module (imports, exports) body) = "imports:" <+> p imports
                             <> hardline <> p body
                             <> hardline <> "exports:" <+> p exports

instance Pretty FModBody where
  pretty (FModBody decls tyDefs) = vsep (map p decls) <> hardline <> p tyDefs

instance Pretty ModBody where
  pretty (ModBody decls result) =
    vsep (map p decls) <> hardline <> "result:" <+> p result

instance Pretty ImpModBody where
  pretty (ImpModBody vs prog result) =
    p vs <> hardline <> p prog <> hardline <> p result

instance (Pretty a, Pretty b) => Pretty (Either a b) where
  pretty (Left  x) = "Left"  <+> p x
  pretty (Right x) = "Right" <+> p x

printLitBlock :: SourceBlock -> Result -> String
printLitBlock block result = pprint block ++ resultStr
  where
    resultStr = unlines $ map addPrefix $ lines $ pprint result
    addPrefix :: String -> String
    addPrefix s = case s of "" -> ">"
                            _  -> "> " ++ s

assertEq :: (MonadError Err m, Pretty a, Eq a) => a -> a -> String -> m ()
assertEq x y s = if x == y then return ()
                           else throw CompilerErr msg
  where msg = s ++ ": " ++ pprint x ++ " != " ++ pprint y

ignoreExcept :: Except a -> a
ignoreExcept (Left e) = error $ pprint e
ignoreExcept (Right x) = x
