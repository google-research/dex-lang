-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module PPrint (pprint, addErrSrc) where

import GHC.Float
import Data.String
import Data.Text.Prettyprint.Doc.Render.Text
import Data.Text.Prettyprint.Doc
import Data.Text (unpack)
import Data.Foldable (toList)

import Record
import Env
import Syntax
import Util (highlightRegion)

pprint :: Pretty a => a -> String
pprint x = asStr $ pretty x

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
  ArrType (Mult l) a b -> parens $ recur a <+> arrStr l <+> recur b
  ArrType m a b -> recur a <+> "--(" <> recur m <> ")" <+> recur b
  TabType a b -> parens $ recur a <> "=>" <> recur b
  RecType Cart r -> p $ fmap (asStr . recur) r
  RecType Tens (Tup xs) -> parens $ hsep $ punctuate " :" (map p xs)
  RecType Tens _ -> error "Not implemented"
  TypeApp f xs -> p f <+> hsep (map p xs)
  Monad eff a -> "Monad" <+> hsep (map p (toList eff)) <+> p a
  Lens a b    -> "Lens" <+> p a <+> p b
  Exists body -> parens $ "E" <> p (tvars d (-1)) <> "." <> recurWith 1 body
  IdxSetLit i -> p i
  Mult Lin    -> "Lin"
  Mult NonLin -> "NonLin"
  where recur = prettyTyDepth d
        recurWith n = prettyTyDepth (d + n)

instance Pretty SigmaType where
  pretty (Forall []    t) = prettyTyDepth 0 t
  pretty (Forall kinds t) = header <+> prettyTyDepth n t
    where n = length kinds
          header = "A" <+> hsep binders <> "."
          boundvars :: [Name]
          boundvars = [tvars 0 i | i <- [-n..(-1)]]
          binders = map p $ zipWith (:>) boundvars kinds

instance Pretty ty => Pretty (EffectTypeP ty) where
  pretty = undefined

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

instance Pretty b => Pretty (ExprP b) where
  pretty expr = case expr of
    Lit val -> p val
    Var v _ ts -> foldl (<+>) (p v) ["@" <> p t | t <- ts]
    PrimOp b ts xs -> parens $ p b <> targs <> args
      where targs = case ts of [] -> mempty; _ -> list   (map p ts)
            args  = tupled (map p xs)
    Decl decl body -> prettyDecl decl body
    -- TODO: show linearity annotations somehow
    Lam _ pat e -> parens $ align $ group $ "lam" <+> p pat <+> "."
                     <> line <> align (p e)
    App e1 e2    -> align $ parens $ group $ p e1 <+> p e2
    For b e      -> parens $ "for " <+> p b <+> "." <> nest 4 (hardline <> p e)
    Get e ie     -> p e <> "." <> p ie
    RecCon Cart r   -> p r
    RecCon Tens (Tup r) -> parens $ hsep $ punctuate " :" (map p r)
    RecCon Tens _ -> error "Not implemented"
    TabCon _ xs -> list (map pretty xs)
    Pack e ty exTy -> "pack" <+> p e <> "," <+> p ty <> "," <+> p exTy
    IdxLit n i -> p i <> "@" <> p (IdxSetLit n)
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
    Data   -> "Data"
    VSpace -> "VS"
    IdxSet -> "Ix"

instance Pretty b => Pretty (DeclP b) where
  -- TODO: special-case annotated leaf var (print type on own line)
  pretty (LetMono pat expr) = p pat <+> "=" <+> p expr
  pretty (LetPoly (v:>ty) (TLam _ body)) =
    p v <+> "::" <+> p ty <> line <>
    p v <+> "="  <+> p body
  pretty (DoBind pat expr) = p pat <+> "<-" <+> p expr
  pretty (TyDef deftype v bs ty) = keyword <+> p v <+> p bs <+> "=" <+> p ty
    where keyword = case deftype of TyAlias -> "type"
                                    NewType -> "newtype"
  pretty (Unpack b tv expr) = p b <> "," <+> p tv <+> "= unpack" <+> p expr

instance Pretty b => Pretty (TLamP b) where
  pretty (TLam binders body) = "Lam" <+> p binders <> "." <+> align (p body)

instance Pretty b => Pretty (TopDeclP b) where
  pretty (TopDecl _ decl) = p decl
  pretty (RuleDef _ _ _) = error "Not implemented"
  pretty (EvalCmd _ ) = error $ "EvalCmd not implemented" -- TODO

instance Pretty RuleAnn where
  pretty = undefined

instance Pretty Builtin where
  pretty b = p (show b)

instance Pretty NExpr where
  pretty expr = case expr of
    NDecl decl body -> prettyDecl decl body
    NScan [] (NLamExpr ~[b] body) -> parens $ "for " <+> p b <+> "." <+> nest 4 (hardline <> p body)
    NScan xs (NLamExpr ~(b:bs) body) ->
      parens $ "forM " <+> p b <+> hsep (map p bs) <+> "."
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
    NLet    bs bound -> tup bs <+> "=" <+> p bound
    NUnpack bs tv e  -> tup bs <> "," <+> p tv <+> "= unpack" <+> p e

instance Pretty NAtom where
  pretty atom = case atom of
    NLit v -> p v
    NVar x _ -> p x
    NGet e i -> p e <> "." <> p i
    NLam l (NLamExpr bs body) ->
      parens $ align $ group $ lamStr l <+> hsep (map p bs) <+> "." <>
      line <> align (p body)
    NAtomicFor b e -> parens $ "afor " <+> p b <+> "." <+> nest 4 (hardline <> p e)
    NAtomicPrimOp b ts xs -> p (NPrimOp b ts xs)
    NDoBind m (NLamExpr bs body) -> prettyDecl (asStr (tup bs <+> "<-" <+> p m)) body

instance Pretty NType where
  pretty ty = case ty of
    NBaseType b  -> p b
    NTypeVar v   -> p v
    NBoundTVar n -> "BV" <> p n  -- TODO: invent some variable names
    NArrType l as bs -> parens $ tup as <+> arrStr l <+> tup bs
    NTabType a  b  -> p a <> "=>" <> p b
    NMonad eff a -> "Monad" <+> hsep (map p (toList eff)) <+> p a
    NLens a b    -> "Lens"  <+> p a <+> p b
    NExists tys -> "E" <> "." <> list (map p tys)
    NIdxSetLit i -> p i

lamStr :: Multiplicity -> Doc ann
lamStr NonLin = "lam"
lamStr Lin    = "llam"

arrStr :: Multiplicity -> Doc ann
arrStr NonLin = "->"
arrStr Lin    = "--o"

tup :: Pretty a => [a] -> Doc ann
tup [x] = p x
tup xs  = tupled $ map p xs

instance Pretty IExpr where
  pretty (ILit v)   = p v
  pretty (IVar v _) = p v
  pretty (IGet expr idx) = p expr <> "." <> p idx
  pretty (IRef ref) = p ref

instance Pretty IType where
  pretty (IRefType (ty, shape)) = "Ptr (" <> p ty <> p shape <> ")"
  pretty (IValType b) = p b

instance Pretty ImpProg where
  pretty (ImpProg block) = vcat (map prettyStatement block)

prettyStatement :: (Maybe IBinder, ImpInstr) -> Doc ann
prettyStatement (Nothing, instr) = p instr
prettyStatement (Just b , instr) = p b <+> "=" <+> p instr

instance Pretty ImpInstr where
  pretty (IPrimOp b tys xs) = p b <> p tys <> tup xs
  pretty (Load ref)         = "load"  <+> p ref
  pretty (Store dest val)   = "store" <+> p dest <+> p val
  pretty (Copy dest source) = "copy"  <+> p dest <+> p source
  pretty (Alloc ty)         = "alloc" <+> p ty
  pretty (Free name _)      = "free"  <+> p name
  pretty (Loop i n block)   = "for"   <+> p i <+> "<" <+> p n <>
                               nest 4 (hardline <> p block)

instance Pretty a => Pretty (FlatValP a) where
  pretty (FlatVal ty refs) = "FlatVal (ty=" <> p ty <> ", refs= " <> p refs <> ")"

instance Pretty a => Pretty (ArrayP a) where
  pretty (Array shape ref) = p ref <> p shape

instance Pretty VecRef' where
  pretty (IntVecRef  ptr) = p $ show ptr
  pretty (RealVecRef ptr) = p $ show ptr
  pretty (BoolVecRef ptr) = p $ show ptr

instance Pretty Vec where
  pretty (IntVec  xs) = p xs
  pretty (RealVec xs) = p xs
  pretty (BoolVec xs) = p xs

instance Pretty a => Pretty (SetVal a) where
  pretty NotSet = ""
  pretty (Set a) = p a

instance (Pretty a, Pretty b) => Pretty (LorT a b) where
  pretty (L x) = "L" <+> p x
  pretty (T x) = "T" <+> p x

-- TODO: add line numbers back (makes the quines a little brittle)
addErrSrc :: SourceBlock -> Result -> Result
addErrSrc block result = case result of
  Result (Left (Err e (Just (start, stop)) s')) ->
    Result $ Left $ Err e Nothing $ s' ++ "\n\n" ++ ctx
      where
        n = sbOffset block
        ctx = highlightRegion (start - n, stop - n) (sbText block)
  _ -> result
