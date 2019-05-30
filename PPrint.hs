{-# LANGUAGE OverloadedStrings #-}

module PPrint (pprint) where

import Data.Text.Prettyprint.Doc.Render.Text
import Data.Text.Prettyprint.Doc
import Data.Text (unpack)
import qualified Data.Map.Strict as M

import Syntax
import Record

pprint :: Pretty a => a -> String
pprint x = asStr (pretty x)

asStr :: Doc ann -> String
asStr doc = unpack $ renderStrict $ layoutPretty defaultLayoutOptions $ doc

p :: Pretty a => a -> Doc ann
p = pretty

instance Pretty Err where
  pretty (Err e s) = p e <+> p s

instance Pretty ErrType where
  pretty e = case e of
    -- NoErr tags a chunk of output that was promoted into the Err ADT
    -- by appending Results.
    NoErr             -> ""
    ParseErr          -> "Parse error:"
    TypeErr           -> "Type error:"
    CompilerErr       -> "Compiler bug!"
    UnboundVarErr     -> "Variable not in scope:"
    RepeatedVarErr    -> "Variable redefined:"
    NotImplementedErr -> "Not implemented:"
    OtherErr          -> "Error:"
    UpstreamErr       -> "Upstream failure"

instance Pretty Type where
  pretty t = prettyTyDepth 0 t

prettyTyDepth :: Int -> Type -> Doc ann
prettyTyDepth d t = case t of
  BaseType b  -> p b
  TypeVar v   -> p v
  BoundTVar n -> p (tvars n)
  ArrType a b -> parens $ recur a <+> "->" <+> recur b
  TabType a b -> recur a <> "=>" <> recur b
  RecType r   -> p $ fmap (asStr . recur) r
  Forall kinds t -> header <+> recurWith n t
                    where n = length kinds
                          header = "A" <+> hsep boundvars <> "."
                          boundvars = map (p . tvars) [-n..(-1)]
  Exists body -> "E" <> p (tvars (-1)) <> "." <> recurWith 1 body
  IdxSetLit i -> "0.." <> p i
  where recur = prettyTyDepth d
        recurWith n = prettyTyDepth (d + n)
        tvars i = [['a'..'z'] !! (d - i - 1)] -- TODO: distinguish kinds

instance Pretty Kind where
  pretty IdxSetKind = "R"
  pretty TyKind = "T"

instance Pretty BaseType where
  pretty t = case t of
    IntType  -> "Int"
    BoolType -> "Bool"
    RealType -> "Real"
    StrType  -> "Str"

instance Pretty LitVal where
  pretty (IntLit x ) = p x
  pretty (RealLit x) = p x
  pretty (StrLit x ) = p x

instance Pretty b => Pretty (ExprP b) where
  pretty expr = case expr of
    Lit val      -> p val
    Var v        -> p v
    Builtin b    -> p b
    Decls decls body -> parens $ align $ "let" <+> align (vcat (map p decls))
                                      <> line <> "in" <+> p body
    Lam pat e    -> parens $ align $ group $ "lam" <+> p pat <+> "." <> line <> align (p e)
    App e1 e2    -> align $ group $ p e1 <+> p e2
    For b e      -> parens $ "for " <+> p b <+> ":" <+> align (p e)
    Get e ie     -> p e <> "." <> p ie
    RecCon r     -> p r
    TLam binders expr -> "Lam" <+> p binders <> ":"
                               <+> align (p expr)
    TApp expr ts -> p expr <> p ts

instance Pretty b => Pretty (DeclP b) where
  pretty (Let b expr) = p b <+> "=" <+> p expr
  pretty (Unpack b tv expr) = p b <> "," <+> p tv <+> "= unpack" <+> p expr

instance Pretty Builtin where
  pretty b = case b of
    Add      -> "+"
    Sub      -> "-"
    Mul      -> "*"
    FAdd     -> "%fadd"
    FSub     -> "%fsub"
    FMul     -> "%fmul"
    FDiv     -> "%fdiv"
    Pow      -> "%pow"
    Exp      -> "%exp"
    Log      -> "%log"
    Sqrt     -> "%sqrt"
    Sin      -> "%sin"
    Cos      -> "%cos"
    Tan      -> "%tan"
    Iota     -> "%iota"
    Range    -> "%range"
    Hash     -> "%hash"
    Rand     -> "%rand"
    Randint  -> "%randint"
    Fold     -> "%fold"
    IntToReal -> "%real"
    Copy     -> "%copy"

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
  pretty (Update v idxs b exprs) = p v <> p idxs <+> ":=" <+> p b <+> hsep (map p exprs)
  pretty (Loop i n block) = "for" <+> p i <+> "<" <+> p n <>
                               nest 4 (hardline <> p block)

instance Pretty Value where
  pretty (Value _ vecs) = p vecs

instance Pretty Vec where
  pretty (IntVec  xs) = p xs
  pretty (RealVec xs) = p xs

instance Pretty EvalStatus where
  pretty Complete = ""
  pretty (Failed err) = p err

instance Pretty a => Pretty (SetVal a) where
  pretty NotSet = ""
  pretty (Set a) = p a

instance Pretty Result where
  pretty (Result x y z) = p x <> p y <> p z
