-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module PPrint (pprint, pprintEsc, addErrSrc, printLitBlock) where

import GHC.Float
import Data.Text.Prettyprint.Doc.Render.Text
import Data.Text.Prettyprint.Doc
import Data.Text (unpack)

import Record
import Env
import Syntax
import Util (findReplace, highlightRegion)

pprint :: Pretty a => a -> String
pprint x = asStr $ pretty x

pprintEsc :: Pretty a => a -> String
pprintEsc x = findReplace "; ..\n" "\n" $ findReplace "\n" " ..\n" $ pprint x

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
    LinErr            -> "Linearity error:"
    UnboundVarErr     -> "Error: variable not in scope: "
    RepeatedVarErr    -> "Error: variable already defined: "
    NotImplementedErr -> "Not implemented:"
    CompilerErr       -> "Compiler bug!"
    MiscErr           -> "Error:"

instance Pretty Type where
  pretty t = prettyTyDepth 0 t

prettyTyDepth :: Int -> Type -> Doc ann
prettyTyDepth d ty = case ty of
  BaseType b  -> p b
  TypeVar v   -> p v
  BoundTVar n -> p (tvars d n)
  ArrType l a b -> parens $ recur a <+> arrStr l <+> recur b
  TabType a b -> parens $ recur a <> "=>" <> recur b
  RecType Cart r -> p $ fmap (asStr . recur) r
  RecType Tens (Tup xs) -> parens $ hsep $ punctuate " :" (map p xs)
  RecType Tens _ -> error "Not implemented"
  Exists body -> parens $ "E" <> p (tvars d (-1)) <> "." <> recurWith 1 body
  IdxSetLit i -> p i
  where recur = prettyTyDepth d
        recurWith n = prettyTyDepth (d + n)

instance Pretty SigmaType where
  pretty (Forall []    t) = prettyTyDepth 0 t
  pretty (Forall kinds t) = header <+> prettyTyDepth n t
    where n = length kinds
          header = "A" <+> hsep binders <> "."
          boundvars :: [Name]
          boundvars = [Name (tvars 0 i) 0 | i <- [-n..(-1)]]
          binders = map p $ zipWith (:>) boundvars kinds

tvars :: Int -> Int -> String
tvars d i = case d - i - 1 of i' | i' >= 0 -> [['a'..'z'] !! i']
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

instance Pretty b => Pretty (ExprP b) where
  pretty expr = case expr of
    Lit val -> p val
    Var v ts -> foldl (<+>) (p v) ["@" <> p t | t <- ts]
    PrimOp b ts xs -> parens $ p b <> targs <> args
      where targs = case ts of [] -> mempty; _ -> list   (map p ts)
            args  = tupled (map p xs)
    Decl decl body -> prettyDecl decl body
    Lam l pat e    -> parens $ align $ group $ lamStr l <+> p pat <+> "."
                        <> line <> align (p e)
    App e1 e2    -> align $ parens $ group $ p e1 <+> p e2
    For b e      -> parens $ "for " <+> p b <+> "." <> nest 4 (hardline <> p e)
    Get e ie     -> p e <> "." <> p ie
    RecCon Cart r   -> p r
    RecCon Tens (Tup r) -> parens $ hsep $ punctuate " :" (map p r)
    RecCon Tens _ -> error "Not implemented"
    TabCon _ xs -> list (map pretty xs)
    Pack e ty exTy -> "pack" <+> p e <> "," <+> p ty <> "," <+> p exTy
    IdxLit _ i -> p i
    SrcAnnot subexpr _ -> p subexpr
    Annot subexpr ty -> p subexpr <+> "::" <+> p ty

prettyDecl :: (Pretty decl, Pretty body) => decl -> body -> Doc ann
prettyDecl decl body = align $ "(" <> p decl <> ";" <> line <> p body <> ")"

instance Pretty Ann where
  pretty NoAnn = ""
  pretty (Ann ty) = pretty ty

instance Pretty Kind where
  pretty (Kind cs) = case cs of
    []  -> ""
    [c] -> p c
    _   -> tupled $ map p cs

instance Pretty a => Pretty (BinderP a) where
  pretty (v :> ann) =
    case asStr ann' of "" -> p v
                       _  -> p v <> "::" <> ann'
    where ann' = p ann

instance Pretty ClassName where
  pretty name = case name of
    Show   -> "Show"
    VSpace -> "VSpace"
    IdxSet -> "Ix"

instance Pretty b => Pretty (DeclP b) where
  -- TODO: special-case annotated leaf var (print type on own line)
  pretty (LetMono pat expr) = p pat <+> "=" <+> p expr
  pretty (LetPoly (v:>ty) (TLam _ body)) =
    p v <+> "::" <+> p ty <> line <>
    p v <+> "="  <+> p body
  pretty (TAlias v ty) = "type" <+> p v <+> "=" <+> p ty
  pretty (Unpack b tv expr) = p b <> "," <+> p tv <+> "= unpack" <+> p expr

instance Pretty b => Pretty (TLamP b) where
  pretty (TLam binders body) = "Lam" <+> p binders <> "." <+> align (p body)

instance Pretty b => Pretty (TopDeclP b) where
  pretty (TopDecl decl) = p decl
  pretty (EvalCmd _ ) = error $ "EvalCmd not implemented" -- TODO

instance Pretty Builtin where
  pretty b = p (show b)

instance Pretty NExpr where
  pretty expr = case expr of
    NDecl decl body -> prettyDecl decl body
    NScan b [] [] body -> parens $ "for " <+> p b <+> "." <+> nest 4 (hardline <> p body)
    NScan b bs xs body -> parens $ "forM " <+> p b <+> hsep (map p bs) <+> "."
                            <+> hsep (map p xs) <> ","
                            <+> nest 4 (hardline <> p body)
    NPrimOp b ts xs -> parens $ p b <> targs <> args
      where targs = case ts of [] -> mempty; _ -> list   (map p ts)
            args  = case xs of [] -> mempty; _ -> tupled (map p xs)
    NApp f xs -> align $ group $ p f <+> hsep (map p xs)
    NAtoms xs -> tup xs
    NTabCon _ _ xs -> list (map pretty xs)

instance Pretty NDecl where
  pretty decl = case decl of
    NLet bs bound   -> tup bs <+> "=" <+> p bound
    NUnpack bs tv e -> tup bs <> "," <+> p tv <+> "= unpack" <+> p e

instance Pretty NAtom where
  pretty atom = case atom of
    NLit v -> p v
    NVar x -> p x
    NGet e i -> p e <> "." <> p i
    NLam l bs body -> parens $ align $ group $ lamStr l <+> hsep (map p bs) <+> "."
                       <> line <> align (p body)
    NAtomicFor b e -> parens $ "afor " <+> p b <+> "." <+> nest 4 (hardline <> p e)

instance Pretty NType where
  pretty ty = case ty of
    NBaseType b  -> p b
    NTypeVar v   -> p v
    NBoundTVar n -> "BV" <> p n  -- TODO: invent some variable names
    NArrType l as bs -> parens $ tup as <+> arrStr l <+> tup bs
    NTabType a  b  -> p a <> "=>" <> p b
    NExists tys -> "E" <> "." <> list (map p tys)
    NIdxSetLit i -> p i

lamStr :: Lin -> Doc ann
lamStr NonLin = "lam"
lamStr Lin = "llam"

arrStr :: Lin -> Doc ann
arrStr NonLin = "->"
arrStr Lin = "--o"

tup :: Pretty a => [a] -> Doc ann
tup [x] = p x
tup xs  = tupled $ map p xs

instance Pretty IExpr where
  pretty (ILit v) = p v
  pretty (IVar v) = p v
  pretty (IGet expr idx) = p expr <> "." <> p idx

instance Pretty IType where
  pretty (IType ty shape) = p ty <> p shape

instance Pretty ImpProg where
  pretty (ImpProg block) = vcat (map p block)

instance Pretty Statement where
  pretty (Alloc b body) = p b <> braces (hardline <> p body)
  pretty (Update v idxs b _ exprs) = p v <> p idxs <+>
                                       ":=" <+> p b <+> hsep (map p exprs)
  pretty (Loop i n block) = "for" <+> p i <+> "<" <+> p n <>
                               nest 4 (hardline <> p block)

instance Pretty Value where
  pretty (Value (BaseType IntType ) (RecLeaf (IntVec  [v]))) = p v
  pretty (Value (BaseType RealType) (RecLeaf (RealVec [v]))) = printDouble v
  pretty (Value (BaseType BoolType ) (RecLeaf (IntVec  [v]))) | mod v 2 == 0 = "False"
                                                              | mod v 2 == 1 = "True"
  pretty (Value (RecType _ r) (RecTree r')) = p (recZipWith Value r r')
  pretty (Value (TabType n ty) v) = list $ map p (splitTab n ty v)
  pretty v = error $ "Can't print: " ++ show v

splitTab :: IdxSet -> Type -> RecTree Vec -> [Value]
splitTab (IdxSetLit n) ty v = map (Value ty) $ transposeRecTree (fmap splitVec v)
  where
    splitVec :: Vec -> [Vec]
    splitVec (IntVec  xs) = map IntVec  $ chunk (length xs `div` n) xs
    splitVec (RealVec xs) = map RealVec $ chunk (length xs `div` n) xs

    -- TODO: this is O(N^2)
    transposeRecTree :: RecTree [a] -> [RecTree a]
    transposeRecTree tree = [fmap (!!i) tree | i <- [0..n-1]]

    chunk :: Int -> [a] -> [[a]]
    chunk _ [] = []
    chunk m xs = take m xs : chunk m (drop m xs)
splitTab _ _ _ = error $ "Not implemented" -- TODO

instance Pretty Vec where
  pretty (IntVec  xs) = p xs
  pretty (RealVec xs) = p xs

instance Pretty a => Pretty (SetVal a) where
  pretty NotSet = ""
  pretty (Set a) = p a

instance Pretty Output where
  pretty (ValOut Printed val) = p val
  pretty (ValOut _ _) = "<graphical output>"
  pretty (TextOut s) = p s
  pretty NoOutput = ""

instance (Pretty a, Pretty b) => Pretty (LorT a b) where
  pretty (L x) = "L" <+> p x
  pretty (T x) = "T" <+> p x

instance Pretty SourceBlock where
  pretty block = p (sbText block)

instance Pretty Result where
  pretty (Result r) = case r of
    Left err -> p err
    Right NoOutput -> mempty
    Right out -> p out

printLitBlock :: SourceBlock -> Result -> String
printLitBlock block result = pprint block ++ resultStr
  where
    resultStr = unlines $ map addPrefix $ lines $ pprint result
    addPrefix :: String -> String
    addPrefix s = case s of "" -> ">"
                            _  -> "> " ++ s

-- TODO: add line numbers back (makes the quines a little brittle)
addErrSrc :: SourceBlock -> Result -> Result
addErrSrc block result = case result of
  Result (Left (Err e (Just (start, stop)) s')) ->
    Result $ Left $ Err e Nothing $ s' ++ "\n\n" ++ ctx
      where
        n = sbOffset block
        ctx = highlightRegion (start - n, stop - n) (sbText block)
  _ -> result
