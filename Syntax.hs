{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Syntax (ExprP (..), Expr, Type (..), IdxSet, IdxSetVal, Builtin (..), Var,
               UExpr (..), UTopDecl (..), UDecl (..), ImpDecl (..), TopDeclP (..),
               DeclP (..), Decl, TopDecl, Command (..), UPat, Pat, SrcPos,
               CmdName (..), IdxExpr, Kind (..), UBinder (..), PatP,
               LitVal (..), BaseType (..), Binder, TBinder, lbind, tbind,
               Except, Err (..), ErrType (..), OutputElt (..), OutFormat (..),
               throw, addContext, addErrSource, addErrSourcePos,
               FullEnv, (-->), (==>), LorT (..), fromL, fromT,
               lhsVars, Size, unitTy, unitCon,
               ImpProg (..), Statement (..), IExpr (..), IType (..), IBinder,
               Value (..), Vec (..), Result (..), freeVars,
               Output, Nullable (..), SetVal (..), EvalStatus (..),
               MonMap (..), resultSource, resultText, resultErr, resultComplete,
               Index, wrapDecls, strToBuiltin, idxSetKind,
               preludeNames, preludeApp, naryApp, tApp,
               NExpr (..), NDecl (..), NAtom (..), NType (..), NTopDecl (..),
               NBinder
               ) where

import Fresh
import Record
import Env
import Util

import qualified Data.Map.Strict as M

import Data.Foldable (fold)
import Data.Tuple (swap)
import Data.Maybe (fromJust)
import Control.Monad.Except hiding (Except)

-- === core IR ===

data ExprP b = Lit LitVal
          | Var Var
          | PrimOp Builtin [Type] [ExprP b]
          | Decls [DeclP b] (ExprP b)
          | Lam (PatP b) (ExprP b)
          | App (ExprP b) (ExprP b)
          | For (PatP b) (ExprP b)
          | Get (ExprP b) (ExprP b)
          | TLam [TBinder] (ExprP b)
          | TApp (ExprP b) [Type]
          | RecCon (Record (ExprP b))
          | TabCon IdxSetVal Type [ExprP b]
          | Annot (ExprP b) Type
          | DerivAnnot (ExprP b) (ExprP b)
          | SrcAnnot (ExprP b) SrcPos
             deriving (Eq, Ord, Show)

data Type = BaseType BaseType
          | TypeVar Var
          | ArrType Type Type
          | TabType IdxSet Type
          | RecType (Record Type)
          | Forall [Kind] Type
          | Exists Type
          | IdxSetLit IdxSetVal
          | BoundTVar Int
             deriving (Eq, Ord, Show)

type Expr    = ExprP    Type
type Binder  = BinderP  Type
type Decl    = DeclP    Type
type TopDecl = TopDeclP Type
type Pat     = PatP     Type

type Var = Name

-- TODO: figure out how to treat index set kinds
-- data Kind = idxSetKind | TyKind  deriving (Show, Eq, Ord)
data Kind = TyKind  deriving (Show, Eq, Ord)
idxSetKind = TyKind

data DeclP b = Let    (PatP b)     (ExprP b)
             | Unpack (BinderP b) Var (ExprP b)
               deriving (Eq, Ord, Show)

type PatP b = RecTree (BinderP b)

-- TODO: just use Decl
data TopDeclP b = TopDecl (DeclP b)
                | EvalCmd (Command (ExprP b))

data Command expr = Command CmdName expr | NoOp  deriving (Show)

type TBinder = BinderP Kind
type IdxSet = Type
type IdxExpr = Var
type IdxSetVal = Int
type SrcPos = (Int, Int)

data LitVal = IntLit  Int
            | RealLit Double
            | BoolLit Bool
            | StrLit  String
              deriving (Eq, Ord, Show)

data BaseType = IntType | BoolType | RealType | StrType
                   deriving (Eq, Ord, Show)

data Builtin = IAdd | ISub | IMul | FAdd | FSub | FMul | FDiv
             | FLT | FGT | ILT | IGT | Pow | IntToReal | BoolToInt
             | Range | Scan | Copy | Deriv | PartialEval | Transpose
             | VZero | VAdd | VSingle | VSum | IndexAsInt
             | FFICall Int String
                deriving (Eq, Ord)

builtinNames = M.fromList [
  ("iadd", IAdd), ("isub", ISub), ("imul", IMul),
  ("fadd", FAdd), ("fsub", FSub), ("fmul", FMul),
  ("fdiv", FDiv), ("pow", Pow),
  ("fgt", FLT), ("flt", FGT), ("igt", ILT), ("ilt", IGT),
  ("scan", Scan), ("range", Range),
  ("inttoreal", IntToReal), ("booltoint", BoolToInt),
  ("deriv", Deriv), ("partialEval", PartialEval), ("transpose", Transpose),
  ("copy", Copy), ("asint", IndexAsInt),
  ("vzero", VZero), ("vadd", VAdd), ("vsingle", VSingle), ("vsum", VSum)]

builtinStrs = M.fromList $ map swap (M.toList builtinNames)

strToBuiltin :: String -> Maybe Builtin
strToBuiltin name = M.lookup name builtinNames

instance Show Builtin where
  show (FFICall _ s) = "%%" ++ s
  show b = "%" ++ fromJust (M.lookup b builtinStrs)

data CmdName = GetType | Passes | LLVM | Asm | TimeIt | Flops
             | Interpret | EvalExpr OutFormat
                deriving  (Show, Eq)


data Value = Value Type (RecTree Vec)  deriving (Show, Eq)
data Vec = IntVec [Int] | RealVec [Double]  deriving (Show, Eq)

unitTy = RecType (Tup [])
unitCon = RecCon (Tup [])

-- === functions available from the prelude ===

preludeNames :: Env ()
preludeNames = fold [rawName v @> ()
                    | v <- ["fanout", "fmulDeriv", "vsumImpl",
                            "forUnzip"]]

preludeApp :: String -> [Type] -> [Expr] -> Expr
preludeApp s ts xs = naryApp (tApp (Var (rawName s)) ts) xs

naryApp :: Expr -> [Expr] -> Expr
naryApp f xs = foldl App f xs

tApp :: Expr -> [Type] -> Expr
tApp f [] = f
tApp f ts = TApp f ts

-- === source AST ===

data UExpr = ULit LitVal
           | UVar Var
           | UPrimOp Builtin [UExpr]
           | UDecls [UDecl] UExpr
           | ULam UPat UExpr
           | UApp UExpr UExpr
           | UFor UPat UExpr
           | UGet UExpr UExpr
           | URecCon (Record UExpr)
           | UTabCon [UExpr]
           | UAnnot UExpr Type
           | UDerivAnnot UExpr UExpr
           | USrcAnnot UExpr SrcPos
                deriving (Show, Eq)

data UBinder = UBind (BinderP (Maybe Type)) | IgnoreBind  deriving (Show, Eq)
data UDecl = ULet UPat UExpr
           | UTAlias Var Type
           | UUnpack UBinder Var UExpr  deriving (Show, Eq)

data UTopDecl = UTopDecl UDecl
              | UEvalCmd (Command UExpr)  deriving (Show)

type UPat = RecTree UBinder

-- === tuple-free ANF-ish normalized IR ===

data NExpr = NDecls [NDecl] NExpr
           | NScan NBinder [NBinder] [NAtom] NExpr
           | NPrimOp Builtin [NType] [NAtom]
           | NApp NAtom [NAtom]
           | NAtoms [NAtom]
           | NTabCon IdxSetVal [NType] [[NAtom]]
             deriving (Show)

data NDecl = NLet [NBinder] NExpr
           | NUnpack [NBinder] Var NExpr
              deriving (Show)

data NAtom = NLit LitVal
           | NVar Var
           | NGet NAtom NAtom
           | NLam [NBinder] NExpr
           | NAtomicFor NBinder NAtom
           | NDerivAnnot NAtom NAtom
           | NDeriv NAtom
              deriving (Show)

data NType = NBaseType BaseType
           | NTypeVar Var
           | NArrType [NType] [NType]
           | NTabType NType NType
           | NExists [NType]
           | NIdxSetLit IdxSetVal
           | NBoundTVar Int
              deriving (Eq, Show)

data NTopDecl = NTopDecl NDecl
              | NEvalCmd (Command (Type, [NType], NExpr))
                 deriving (Show)

type NBinder = BinderP NType

-- === imperative IR ===

newtype ImpProg = ImpProg [Statement]  deriving (Show, Semigroup, Monoid)

data Statement = Alloc IBinder ImpProg
               | Update Var [Index] Builtin [IType] [IExpr]
               | Loop Var Size ImpProg
                   deriving (Show)

data IExpr = ILit LitVal
           | IVar Var
           | IGet IExpr Index
               deriving (Show, Eq)

data ImpDecl = ImpTopLet [IBinder] ImpProg
             | ImpEvalCmd (Env Int -> [Vec] -> Value) [IBinder] (Command ImpProg)
             --            ^ temporary hack until we do existential packing

type IBinder = BinderP IType
data IType = IType BaseType [Size]  deriving (Show, Eq)
type Size  = IExpr
type Index = IExpr

-- === some handy monoids ===

data Nullable a = Valid a | Null
data SetVal a = Set a | NotSet
newtype MonMap k v = MonMap (M.Map k v)

instance Semigroup (SetVal a) where
  x <> NotSet = x
  _ <> Set x  = Set x

instance Monoid (SetVal a) where
  mempty = NotSet

instance Semigroup a => Semigroup (Nullable a) where
  Null <> _ = Null
  _ <> Null = Null
  Valid x <> Valid y = Valid (x <> y)

instance Monoid a => Monoid (Nullable a) where
  mempty = Valid mempty

instance (Ord k, Semigroup v) => Semigroup (MonMap k v) where
  MonMap m <> MonMap m' = MonMap $ M.unionWith (<>) m m'

instance (Ord k, Semigroup v) => Monoid (MonMap k v) where
  mempty = MonMap mempty

-- === outputs ===

data EvalStatus = Complete | Failed Err
type Source = String
type Output = [OutputElt]

data OutputElt = TextOut String | ValOut OutFormat Value  deriving (Show, Eq)

data OutFormat = Printed | Heatmap | Scatter  deriving (Show, Eq)

data Result = Result (SetVal Source) (SetVal EvalStatus) Output

resultSource s = Result (Set s) mempty mempty
resultText   s = Result mempty mempty s
resultErr    e = Result mempty (Set (Failed e)) mempty
resultComplete = Result mempty (Set Complete)   mempty

data Err = Err ErrType (Maybe SrcPos) String  deriving (Show)

data ErrType = NoErr
             | ParseErr
             | TypeErr
             | UnboundVarErr
             | RepeatedVarErr
             | CompilerErr
             | NotImplementedErr
             | UpstreamErr
             | OtherErr
  deriving (Show)

type Except a = Either Err a

throw :: MonadError Err m => ErrType -> String -> m a
throw e s = throwError $ Err e Nothing s

modifyErr :: MonadError e m => m a -> (e -> e) -> m a
modifyErr m f = catchError m $ \e -> throwError (f e)


addContext :: MonadError Err m => String -> m a -> m a
addContext s m = modifyErr m $ \(Err e p s') ->
                                 Err e p (s' ++ "\ncontext:\n" ++ s)

addErrSource :: MonadError Err m => String -> m a -> m a
addErrSource s m = modifyErr m $ \(Err e p s') ->
  case p of
    Nothing -> Err e p s'
    Just pos -> Err e p $ s' ++ "\n\n" ++ highlightRegion pos s

addErrSourcePos :: MonadError Err m => SrcPos -> m a -> m a
addErrSourcePos pNew m = modifyErr m $ \(Err e pPrev s) ->
  case pPrev of
    Nothing -> Err e (Just pNew) s
    _ -> Err e pPrev s

instance Semigroup Result where
  Result x y z <> Result x' y' z' = Result (x<>x') (y<>y') (z<>z')

instance Monoid Result where
  mempty = Result mempty mempty mempty

-- === misc ===

infixr 1 -->
infixr 2 ==>
(-->) = ArrType
(==>) = TabType

data LorT a b = L a | T b  deriving (Show, Eq)

fromL :: LorT a b -> a
fromL (L x) = x

fromT :: LorT a b -> b
fromT (T x) = x

lbind :: BinderP a -> FullEnv a b
lbind (v:>x) = v @> L x

tbind :: BinderP b -> FullEnv a b
tbind (v:>x) = v @> T x

type FullEnv v t = Env (LorT v t)
type Vars = FullEnv () ()

wrapDecls :: [DeclP b] -> ExprP b -> ExprP b
wrapDecls [] expr = expr
wrapDecls decls expr = case expr of
  Decls decls' body -> Decls (decls ++ decls') body
  _ -> Decls decls expr

-- === substitutions ===

class HasVars a where
  freeVars :: a -> Vars

instance HasVars b => HasVars (ExprP b) where
  freeVars expr = case expr of
    Var v -> v @> L ()
    Lit _ -> mempty
    PrimOp _ ts xs -> foldMap freeVars ts <> foldMap freeVars xs
    Decls decls body -> let (bvs, fvs) = declVars decls
                        in fvs <> (freeVars body `envDiff` bvs)
    Lam p body    -> withBinders p body
    App fexpr arg -> freeVars fexpr <> freeVars arg
    For b body    -> withBinders b body
    Get e ie      -> freeVars e <> freeVars ie
    RecCon r      -> foldMap freeVars r
    TLam vs expr  -> freeVars expr `envDiff` foldMap bind vs
    TApp expr ts  -> freeVars expr <> foldMap freeVars ts
    where
      withBinders p e = foldMap freeVars p
                          <> (freeVars e `envDiff` foldMap lhsVars p)

instance HasVars Type where
  freeVars ty = case ty of
    BaseType _ -> mempty
    TypeVar v  -> v @> T ()
    ArrType a b -> freeVars a <> freeVars b
    TabType a b -> freeVars a <> freeVars b
    RecType r   -> foldMap freeVars r
    Exists body -> freeVars body
    Forall _ body -> freeVars body
    IdxSetLit _ -> mempty
    BoundTVar _ -> mempty

instance HasVars UExpr where
  freeVars expr = case expr of
    ULit _ -> mempty
    UVar v -> v @> L ()
    UPrimOp _ xs -> foldMap freeVars xs
    UDecls decls body -> let (bvs, fvs) = declVars decls
                         in fvs <> (freeVars body `envDiff` bvs)
    ULam p body    -> withPat p body
    UApp fexpr arg -> freeVars fexpr <> freeVars arg
    UFor p body    -> withPat p body
    UGet e ie  -> freeVars e <> freeVars ie
    URecCon r  -> foldMap freeVars r
    UTabCon xs -> foldMap freeVars xs
    UAnnot e ty    -> freeVars e <> freeVars ty
    USrcAnnot e _ -> freeVars e
    where
      withPat p e = foldMap freeVars p <>
                      (freeVars e `envDiff` foldMap lhsVars p)

instance HasVars NExpr where
  freeVars expr = case expr of
    NDecls decls body -> let (bvs, fvs) = declVars decls
                         in fvs <> (freeVars body `envDiff` bvs)
    NPrimOp _ ts xs -> foldMap freeVars ts <> foldMap freeVars xs
    NApp f xs -> freeVars f <> foldMap freeVars xs
    NAtoms xs -> foldMap freeVars xs

instance HasVars NAtom where
  freeVars atom = case atom of
    NLit _ -> mempty
    NVar v -> v @> L ()
    NGet e i -> freeVars e <> freeVars i
    -- AFor b body -> freeVars b <> (freeVars body `envDiff` lhsVars b)
    NLam bs body -> foldMap freeVars bs <>
                      (freeVars body `envDiff` foldMap lhsVars bs)

instance HasVars NDecl where
  freeVars (NLet bs expr) = foldMap freeVars bs <> freeVars expr
  freeVars (NUnpack bs _ expr) = foldMap freeVars bs <> freeVars expr

instance HasVars NType where
  freeVars ty = case ty of
    NBaseType _ -> mempty
    NTypeVar v -> v @> T ()
    NArrType as bs -> foldMap freeVars as <> foldMap freeVars bs
    NTabType a b -> freeVars a <> freeVars b
    NExists ts -> foldMap freeVars ts
    NIdxSetLit _ -> mempty
    NBoundTVar _ -> mempty

instance HasVars UBinder where
  freeVars (UBind (_ :> Just ty)) = freeVars ty
  freeVars _= mempty

instance HasVars b => HasVars (BinderP b) where
  freeVars (_ :> b) = freeVars b

instance HasVars b => HasVars (DeclP b) where
   freeVars (Let    p   expr) = foldMap freeVars p <> freeVars expr
   freeVars (Unpack b _ expr) = freeVars b <> freeVars expr

instance HasVars UDecl where
  freeVars (ULet p expr) = foldMap freeVars p <> freeVars expr
  freeVars (UTAlias _ ty) = freeVars ty
  freeVars (UUnpack b _ expr) = freeVars b <> freeVars expr

instance HasVars UTopDecl where
  freeVars (UTopDecl decl) = freeVars decl
  freeVars (UEvalCmd NoOp) = mempty
  freeVars (UEvalCmd (Command _ expr)) = freeVars expr

instance (HasVars a, HasVars b) => HasVars (LorT a b) where
  freeVars (L x) = freeVars x
  freeVars (T x) = freeVars x

class BindsVars a where
  lhsVars :: a -> Vars

instance BindsVars UBinder where
  lhsVars (UBind (v:>_)) = v @> L ()
  lhsVars IgnoreBind = mempty

instance BindsVars (BinderP a) where
  lhsVars (v:>_) = v @> L ()

instance BindsVars (DeclP b) where
  lhsVars (Let    p    _) = foldMap lhsVars p
  lhsVars (Unpack b tv _) = lhsVars b <> tv @> T ()

instance BindsVars UDecl where
  lhsVars (ULet p _) = foldMap lhsVars p
  lhsVars (UTAlias  v _) = v @> T ()
  lhsVars (UUnpack b tv _) = lhsVars b <> tv @> T ()

instance BindsVars NDecl where
  lhsVars (NLet bs _) = foldMap lhsVars bs
  lhsVars (NUnpack bs tv _) = foldMap lhsVars bs <> tv @> T ()

instance BindsVars UTopDecl where
  lhsVars (UTopDecl decl) = lhsVars decl
  lhsVars _ = mempty

declVars :: (HasVars a, BindsVars a) => [a] -> (Vars, Vars)
declVars [] = (mempty, mempty)
declVars (decl:rest) = (bvs <> bvsRest, fvs <> (fvsRest `envDiff` bvs))
  where
    (bvs, fvs) = (lhsVars decl, freeVars decl)
    (bvsRest, fvsRest) = declVars rest
