{-# LANGUAGE OverloadedStrings #-}

module PPrint (pprint) where

import Data.Text.Prettyprint.Doc.Render.Text
import Data.Text.Prettyprint.Doc
import Data.Text (unpack)
import qualified Data.Map.Strict as M

import Syntax
import Env
import Record
import Fresh

pprint :: Pretty a => a -> String
pprint x = unpack $ renderStrict $ layoutPretty defaultLayoutOptions $ (pretty x)

p :: Pretty a => a -> Doc ann
p = pretty

instance Pretty Err where
  pretty e = case e of
    ParseErr s           -> p s
    UnificationErr t1 t2 -> "Can't unify" <+> p t1 <+> "and" <+> p t2
    TypeErr s            -> "Type error:" <+> p s
    InfiniteTypeErr      -> "Infinite type"
    UnboundVarErr v      -> "Unbound variable:" <+> p v
    RepVarPatternErr v   -> "Repeated variable in pattern:" <+> p v
    CompilerErr s        -> "Compiler bug!" <+> p s
    NotImplementedErr s  -> "Not implemented:"<+> p s
    PrintErr s           -> "Print error:" <+> p s

instance Pretty Type where
  pretty t = case t of
    BaseType b  -> p b
    TypeVar v   -> p v
    ArrType a b -> parens $ p a <+> "->" <+> p b
    TabType a b -> p a <> "=>" <> p b
    RecType r   -> p r
    Forall kinds t -> "A" <> p kinds <> "." <+> p t
    Exists body -> "E" <+> p body

instance Pretty Kind where
  pretty IdxSetKind = "I"
  pretty TyKind = "T"

instance Pretty BaseType where
  pretty t = case t of
    IntType  -> "Int"
    BoolType -> "Bool"
    RealType -> "Real"
    StrType  -> "Str"

-- TODO: this needs to be injective but it's probably not currently
instance Pretty Var where
  pretty VarRoot = ""
  pretty (Qual var name n) = prefix <> p name <> suffix
    where prefix = case var of VarRoot -> ""
                               _       -> p var <> "_"
          suffix = case n of 0 -> ""
                             _ -> "_" <> p n
  pretty (BoundVar n) = "<BV" <> p n <> ">"

instance Pretty LitVal where
  pretty (IntLit x ) = p x
  pretty (RealLit x) = p x
  pretty (StrLit x ) = p x

instance Pretty Expr where
  pretty expr = case expr of
    Lit val      -> p val
    Var v        -> p v
    Builtin b    -> p b
    Let pat e1 e2  -> align $ parens $ "let" <+> pPat pat <+> "=" <+> p e1 <> line <>
                                       "in" <+> p e2
    Lam pat e    -> parens $ "lam" <+> pPat pat <+> ":" <+> align (p e)
    App e1 e2    -> parens $ p e1 <+> p e2
    For t e      -> parens $ "for " <+> p (binder t) <+> ":" <+> align (p e)
    Get e ie     -> p e <> "." <> p ie
    RecCon r     -> p r
    BuiltinApp b ts expr -> parens $ p b <+>  "[" <+> p ts <+> "]" <+> p expr
    Unpack v i e1 e2 ->
      align $ parens $ "{" <> p (binder v) <> "," <+> p i <> "} = unpack"
                                    <+> p e1 <> line <>
                       "in" <+> p e2
    TLam binders expr -> "Lam" <+> hcat (map (p . binder) binders) <> ":"
                               <+> align (p expr)
    TApp expr ts -> p expr <+> "[" <+> p ts <+> "]"
    where pPat pat = p $ fmap binder pat

data BinderWrap v t = BinderWrap v t
binder = uncurry BinderWrap

instance (Pretty v, Pretty t) => Pretty (BinderWrap v t) where
  pretty (BinderWrap v t) = p v <> "::" <> p t

instance Pretty a => Pretty (Record a) where
  pretty r = tupled $ case r of
                        Rec m  -> [p k <> "=" <> p v | (k,v) <- M.toList m]
                        Tup xs -> map p xs -- TODO: add trailing comma to singleton tuple

instance Pretty a => Pretty (RecTree a) where
  pretty (RecTree r) = p r
  pretty (RecLeaf x) = p x

instance Pretty Builtin where
  pretty b = case b of
    Add      -> "+"
    Sub      -> "-"
    Mul      -> "*"
    Pow      -> "pow"
    Exp      -> "exp"
    Log      -> "log"
    Sqrt     -> "sqrt"
    Sin      -> "sin"
    Cos      -> "cos"
    Tan      -> "tan"
    Iota     -> "iota"
    Doubleit -> "doubleit"
    Hash     -> "hash"
    Rand     -> "rand"
    Randint  -> "randint"
    Fold     -> "fold"
    FoldDeFunc _ _ -> "folddefunc"

instance Pretty Statement where
  pretty (Update v idxs expr) = p v <> p idxs <+> ":=" <+> p expr
  pretty (ImpLet b expr) = p (binder b) <+> "=" <+> p expr
  pretty (Loop i n block) = "for" <+> p i <+> "<" <+> p n <>
                               nest 4 (hardline <> vcat (map p block))
  pretty (Alloc v ty) = "cell" <+> p (binder (v,ty))

instance Pretty IExpr where
  pretty (ILit v) = p v
  pretty (IVar v) = p v
  pretty (IGet expr idx) = p expr <> "." <> p idx
  pretty (IBuiltinApp b exprs) = parens $ p b <+> hsep (map p exprs)

instance Pretty IType where
  pretty (IType ty shape) = p ty <> p shape

instance Pretty RecIdx where
  pretty (RecIdx s) = p s
  pretty (TupIdx n) = p n

instance Pretty ImpProgram where
  pretty (ImpProgram block exprs) = vcat (map p block) <>
                                      nest 2 (hardline <> (vcat (map p exprs)))

instance Pretty Value where
  pretty (Value ty vecs) = p vecs

instance Pretty Vec where
  pretty (IntVec  xs) = p xs
  pretty (RealVec xs) = p xs
