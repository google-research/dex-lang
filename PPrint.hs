{-# LANGUAGE OverloadedStrings #-}

module PPrint (pprint) where

import Data.Text.Prettyprint.Doc.Render.Text
import Data.Text.Prettyprint.Doc
import Data.Text (unpack)
import Record
import Syntax

pprint :: Pretty a => a -> String
pprint x = asStr (pretty x)

asStr :: Doc ann -> String
asStr doc = unpack $ renderStrict $ layoutPretty defaultLayoutOptions $ doc

p :: Pretty a => a -> Doc ann
p = pretty

instance Pretty Err where
  pretty (Err e _ s) = p e <+> p s

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
  IdxSetLit i -> "{.." <> p i <> "}"
  where recur = prettyTyDepth d
        recurWith n = prettyTyDepth (d + n)
        tvars i = [['a'..'z'] !! (d - i - 1)] -- TODO: distinguish kinds

instance Pretty Kind where
--  pretty IdxSetKind = "R"
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
    PrimOp b ts xs -> parens $ p b <> targs <> args
      where targs = case ts of [] -> mempty; _ -> brackets (hsep (map p ts))
            args  = case xs of [] -> mempty; _ -> " " <> hsep (map p xs)
    Decls decls body -> parens $ align $ "let" <+> align (vcat (map p decls))
                                      <> line <> "in" <+> p body
    Lam pat e    -> parens $ align $ group $ "lam" <+> p pat <+> "." <> line <> align (p e)
    App e1 e2    -> align $ group $ p e1 <+> p e2
    For b e      -> parens $ "for " <+> p b <+> ":" <+> nest 4 (hardline <> p e)
    Get e ie     -> p e <> "." <> p ie
    RecCon r     -> p r
    RecGet e field -> p e <> "~" <> p field
    TabCon _ _ xs -> list (map pretty xs)
    TLam binders expr -> "Lam" <+> p binders <> ":"
                               <+> align (p expr)
    TApp expr ts -> p expr <> p ts
    SrcAnnot expr _ -> p expr
    Annot expr ty -> p expr <+> "::" <+> p ty

instance Pretty b => Pretty (DeclP b) where
  pretty (Let b expr) = p b <+> "=" <+> p expr
  pretty (Unpack b tv expr) = p b <> "," <+> p tv <+> "= unpack" <+> p expr

instance Pretty Builtin where
  pretty b = p (show b)

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
  pretty (Value (BaseType IntType ) (RecLeaf (IntVec  [v]))) = p v
  pretty (Value (BaseType RealType) (RecLeaf (RealVec [v]))) = p v
  pretty (Value (RecType r) (RecTree r')) = p (recZipWith Value r r')
  pretty (Value (TabType n ty) v) = list $ map p (splitTab n ty v)

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

instance (Pretty a, Pretty b) => Pretty (LorT a b) where
  pretty (L x) = "L" <+> p x
  pretty (T x) = "T" <+> p x
