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
import Data.String
import Data.Text.Prettyprint.Doc.Render.Text
import Data.Text.Prettyprint.Doc
import Data.Text (unpack)
import Data.Foldable (toList)

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
  pretty t = prettyTyDepth 0 t

prettyTyDepth :: Int -> Type -> Doc ann
prettyTyDepth d ty = case ty of
  BaseType b  -> p b
  TypeVar v   -> p v
  BoundTVar n -> p (tvars d n)
  ArrowType l a b -> parens $ recur a <+> arrStr l <+> recur b
  TabType a b -> parens $ recur a <> "=>" <> recur b
  RecType r   -> p $ fmap (asStr . recur) r
  ArrayType shape b -> p b <> p shape
  TypeApp f xs -> recur f <+> hsep (map recur xs)
  Monad eff a -> "Monad" <+> hsep (map recur (toList eff)) <+> recur a
  Lens a b    -> "Lens" <+> recur a <+> recur b
  Forall []    t -> prettyTyDepth d t
  Forall kinds t -> header <+> prettyTyDepth (d + n) t
    where n = length kinds
          header = "A" <+> hsep binders <> "."
          boundvars :: [Name]
          boundvars = [tvars 0 i | i <- [-n..(-1)]]
          binders = map p $ zipWith (:>) boundvars kinds
  TypeAlias _ _ -> "<type alias>"  -- TODO
  IdxSetLit i -> p i
  Mult l      -> p (show l)
  NoAnn       -> ""
  where recur = prettyTyDepth d
        recurWith n = prettyTyDepth (d + n)

instance Pretty ty => Pretty (EffectTypeP ty) where
  pretty (Effect r w s) = "[" <> p r <+> p w <+> p s <> "]"

tvars :: Int -> Int -> Name
tvars d i = fromString s
  where s = case d - i - 1 of i' | i' >= 0 -> [['a'..'z'] !! i']
                                 | otherwise -> "#ERR#"

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
  pretty (Decl decl body) = align $ p decl <> hardline <> p body
  pretty (CExpr expr) = p (OpExpr expr)
  pretty (Atom atom) = p atom

instance Pretty FExpr where
  pretty expr = case expr of
    FVar (v:>ann) ts -> foldl (<+>) (p v) ["@" <> p t | t <- ts]
    FDecl decl body -> align $ p decl <> hardline <> p body
    FPrimExpr e -> p e
    SrcAnnot subexpr _ -> p subexpr
    Annot subexpr ty -> p subexpr <+> "::" <+> p ty

instance Pretty FDecl where
  -- TODO: special-case annotated leaf var (print type on own line)
  pretty (LetMono pat expr) = p pat <+> "=" <+> p expr
  pretty (LetPoly (v:>ty) (FTLam _ body)) =
    p v <+> "::" <+> p ty <> line <>
    p v <+> "="  <+> p body
  pretty (FRuleDef ann ty tlam) = "<TODO: rule def>"
  pretty (TyDef v ty) = "type" <+> p v <+> "=" <+> p ty

instance (Pretty ty, Pretty e, PrettyLam lam) => Pretty (PrimExpr ty e lam) where
  pretty (OpExpr  op ) = p op
  pretty (ConExpr con) = p con

instance (Pretty ty, Pretty e, PrettyLam lam) => Pretty (PrimOp ty e lam) where
  pretty (App _ e1 e2) = p e1 <+> p e2
  pretty (TApp e ts) = p e <+> hsep (map (\t -> "@" <> p t) ts)
  pretty (For lam) = "for" <+> i <+> "." <+> body
    where (i, body) = prettyLam lam
  pretty (TabCon _ _ xs) = list (map pretty xs)
  pretty (TabGet e1 e2) = parens (p e1) <> "." <> parens (p e2)
  pretty (RecGet e1 i ) = p e1 <> "#" <> parens (p i)
  pretty (ArrayGep x i) = parens (p x) <> "." <> p i
  pretty (LoadScalar x) = "load(" <> p x <> ")"
  pretty (Cmp cmpOp _ x y) = "%cmp" <> p (show cmpOp) <+> p x <+> p y
  pretty (MonadRun r s m) = "run" <+> align (p r <+> p s <> hardline <> p m)
  pretty (FFICall s _ _ xs) = "%%" <> p s <> tup xs
  pretty op = prettyExprDefault (OpExpr op)

instance (Pretty ty, Pretty e, PrettyLam lam) => Pretty (PrimCon ty e lam) where
  pretty (Lit l)       = p l
  pretty (Lam _ lam)   = prettyL lam
  pretty (RecCon r) = p r
  pretty (AFor n body) = "afor *::" <> p n <+> "." <+> p body
  pretty (AsIdx n i) = p i <> "@" <> p n
  pretty (Bind m f) = align $ v <+> "<-" <+> p m <> hardline <> body
    where (v, body) = prettyLam f
  pretty (ArrayRef array) = p array
  pretty con = prettyExprDefault (ConExpr con)

prettyExprDefault :: (Pretty e, PrettyLam lam) => PrimExpr ty e lam -> Doc ann
prettyExprDefault expr =
  p (nameToStr blankExpr) <> tupled (map p xs ++ map prettyL lams)
  where (blankExpr, (_, xs, lams)) = unzipExpr expr

prettyL :: PrettyLam a => a -> Doc ann
prettyL lam = parens $ align $ group $ "lam" <+> v <+> "." <> line <> align body
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

instance Pretty Kind where
  pretty (TyKind cs) = case cs of
    []  -> ""
    [c] -> p c
    _   -> tupled $ map p cs
  pretty Multiplicity = "Mult"

instance Pretty a => Pretty (VarP a) where
  pretty (v :> ann) =
    case asStr ann' of "" -> p v
                       _  -> p v <> "::" <> ann'
    where ann' = p ann

instance Pretty ClassName where
  pretty name = case name of
    Data   -> "Data"
    VSpace -> "VS"
    IdxSet -> "Ix"

instance Pretty Decl where
  pretty decl = case decl of
    Let b bound -> p b <+> "=" <+> p (OpExpr bound)

instance Pretty Atom where
  pretty atom = case atom of
    Var (x:>_)  -> p x
    TLam ks body -> "tlam" <+> p ks <+> "." <+> p body
    Con con -> p (ConExpr con)

arrStr :: Type -> Doc ann
arrStr (Mult Lin) = "--o"
arrStr _          = "->"

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
  pretty (ValOut Printed atom) = pretty atom
  pretty (ValOut _ _) = "<graphical output>"
  pretty (TextOut   s) = pretty s
  pretty (PassInfo name t s) = "===" <+> p name <+> "==="
    <> hardline <> p s <> hardline <> "time:" <+> p t

instance Pretty SourceBlock where
  pretty block = pretty (sbText block)

instance Pretty Result where
  pretty (Result outs r) = vcat (map pretty outs) <> maybeErr
    where maybeErr = case r of Left err -> p err
                               Right () -> mempty

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
