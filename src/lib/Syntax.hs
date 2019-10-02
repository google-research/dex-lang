{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Syntax (ExprP (..), Expr, Type (..), IdxSet, IdxSetVal, Builtin (..),
               UExpr, UTopDecl, UDecl, ImpDecl (..), TopDeclP (..),
               DeclP (..), Decl, TopDecl, Command (..), UPat, Pat, SrcPos,
               CmdName (..), IdxExpr, Kind (..), UBinder, PatP, Ann (..),
               LitVal (..), BaseType (..), Binder, TBinder, lbind, tbind,
               Except, Err (..), ErrType (..), OutFormat (..),
               throw, addContext, FullEnv, (-->), (==>), LorT (..), fromL, fromT,
               lhsVars, Size, unitTy, unitCon,
               ImpProg (..), Statement (..), IExpr (..), IType (..), IBinder,
               Value (..), Vec (..), Result, freeVars,
               Output (..), Nullable (..), SetVal (..), MonMap (..),
               Index, wrapDecls, strToBuiltin, builtinNames, idxSetKind,
               NExpr (..), NDecl (..), NAtom (..), NType (..), NTopDecl (..),
               NBinder, stripSrcAnnot, stripSrcAnnotTopDecl,
               SigmaType (..), TLamP (..), TLam, UTLam, asSigma, HasVars,
               SourceBlock (..), SourceBlock' (..), LitProg, EvalBlock (..)
               ) where

import Record
import Env

import qualified Data.Map.Strict as M

import Data.Tuple (swap)
import Data.Maybe (fromJust)
import Control.Monad.Except hiding (Except)
import GHC.Generics

-- === core IR ===

data ExprP b =
            Lit LitVal
          | Var Name [Type]
          | PrimOp Builtin [Type] [ExprP b]
          | Decl (DeclP b) (ExprP b)
          | Lam (PatP b) (ExprP b)
          | App (ExprP b) (ExprP b)
          | For (PatP b) (ExprP b)
          | Get (ExprP b) (ExprP b)
          | RecCon (Record (ExprP b))
          | TabCon b [ExprP b]
          | IdxLit IdxSetVal Int
          | Annot (ExprP b) Type
          | DerivAnnot (ExprP b) (ExprP b)
          | SrcAnnot (ExprP b) SrcPos
          | Pack (ExprP b) Type Type
             deriving (Eq, Ord, Show, Generic)

data DeclP b = LetMono (PatP b) (ExprP b)
             | LetPoly (BinderP SigmaType) (TLamP b)
             | TAlias Name Type
             | Unpack (BinderP b) Name (ExprP b)
               deriving (Eq, Ord, Show, Generic)

type PatP b = RecTree (BinderP b)

data Type = BaseType BaseType
          | TypeVar Name
          | ArrType Type Type
          | TabType IdxSet Type
          | RecType (Record Type)
          | Exists Type
          | IdxSetLit IdxSetVal
          | BoundTVar Int
             deriving (Eq, Ord, Show, Generic)

data SigmaType = Forall [Kind] Type  deriving (Eq, Ord, Show, Generic)
data TLamP b = TLam [TBinder] (ExprP b)  deriving (Eq, Ord, Show, Generic)

asSigma :: Type -> SigmaType
asSigma ty = Forall [] ty

type Expr    = ExprP    Type
type Binder  = BinderP  Type
type Decl    = DeclP    Type
type TopDecl = TopDeclP Type
type Pat     = PatP     Type
type TLam    = TLamP    Type

-- TODO: figure out how to treat index set kinds
-- data Kind = idxSetKind | TyKind  deriving (Show, Eq, Ord)
data Kind = TyKind  deriving (Show, Eq, Ord, Generic)

idxSetKind :: Kind
idxSetKind = TyKind

data TopDeclP b = TopDecl (DeclP b)
                | EvalCmd (Command (ExprP b))  deriving (Show, Eq, Generic)

data Command expr = Command CmdName expr  deriving (Show, Eq, Generic)

type TBinder = BinderP Kind
type IdxSet = Type
type IdxExpr = Name
type IdxSetVal = Int
type SrcPos = (Int, Int)

data LitVal = IntLit  Int
            | RealLit Double
            | BoolLit Bool
            | StrLit  String
              deriving (Eq, Ord, Show, Generic)

data BaseType = IntType | BoolType | RealType | StrType
                   deriving (Eq, Ord, Show, Generic)

data Builtin = IAdd | ISub | IMul | FAdd | FSub | FMul | FDiv
             | FLT | FGT | ILT | IGT | Pow | IntToReal | BoolToInt
             | Range | Scan | Copy | Deriv | PartialEval | Transpose
             | VZero | VAdd | VSingle | VSum | IndexAsInt | IntAsIndex
             | Mod | FFICall Int String | Filter
                deriving (Eq, Ord, Generic)

builtinNames :: M.Map String Builtin
builtinNames = M.fromList [
  ("iadd", IAdd), ("isub", ISub), ("imul", IMul),
  ("fadd", FAdd), ("fsub", FSub), ("fmul", FMul),
  ("fdiv", FDiv), ("pow", Pow), ("mod", Mod),
  ("fgt", FLT), ("flt", FGT), ("igt", ILT), ("ilt", IGT),
  ("scan", Scan), ("range", Range),
  ("inttoreal", IntToReal), ("booltoint", BoolToInt),
  ("deriv", Deriv), ("partialEval", PartialEval), ("transpose", Transpose),
  ("copy", Copy), ("asint", IndexAsInt), ("asidx", IntAsIndex),
  ("filter", Filter), ("vzero", VZero), ("vadd", VAdd),
  ("vsingle", VSingle), ("vsum", VSum)]

builtinStrs :: M.Map Builtin String
builtinStrs = M.fromList $ map swap (M.toList builtinNames)

strToBuiltin :: String -> Maybe Builtin
strToBuiltin name = M.lookup name builtinNames

instance Show Builtin where
  show (FFICall _ s) = "%%" ++ s
  show b = "%" ++ fromJust (M.lookup b builtinStrs)

data CmdName = GetType | Passes | LLVM | Asm | TimeIt | Flops
             | EvalExpr OutFormat
                deriving  (Show, Eq, Generic)


data Value = Value Type (RecTree Vec)  deriving (Show, Eq, Generic)
data Vec = IntVec [Int] | RealVec [Double]  deriving (Show, Eq, Generic)

unitTy :: Type
unitTy = RecType (Tup [])

unitCon :: ExprP b
unitCon = RecCon (Tup [])

-- === source AST ===

data SourceBlock = SourceBlock
  { sbLine     :: Int
  , sbOffset   :: Int
  , sbText     :: String
  , sbContents :: SourceBlock' }  deriving (Show)

data SourceBlock' = UTopDecl UTopDecl
                  | ProseBlock String
                  | CommentLine
                  | EmptyLines
                  | UnParseable String
                    deriving (Show, Eq, Generic)

data Ann = Ann Type | NoAnn  deriving (Show, Eq, Generic)

type UExpr    = ExprP    Ann
type UBinder  = BinderP  Ann
type UDecl    = DeclP    Ann
type UTopDecl = TopDeclP Ann
type UPat     = PatP     Ann
type UTLam    = TLamP    Ann

-- === tuple-free ANF-ish normalized IR ===

data NExpr = NDecl NDecl NExpr
           | NScan NBinder [NBinder] [NAtom] NExpr
           | NPrimOp Builtin [NType] [NAtom]
           | NApp NAtom [NAtom]
           | NAtoms [NAtom]
           | NTabCon NType [NType] [NExpr]
             deriving (Show)

data NDecl = NLet [NBinder] NExpr
           | NUnpack [NBinder] Name NExpr
              deriving (Show)

data NAtom = NLit LitVal
           | NVar Name
           | NGet NAtom NAtom
           | NLam [NBinder] NExpr
           | NAtomicFor NBinder NAtom
           | NDerivAnnot NAtom NAtom
           | NDeriv NAtom
              deriving (Show)

data NType = NBaseType BaseType
           | NTypeVar Name
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
               | Update Name [Index] Builtin [IType] [IExpr]
               | Loop Name Size ImpProg
                   deriving (Show)

data IExpr = ILit LitVal
           | IVar Name
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

data EvalBlock = EvalBlock SourceBlock Result
type LitProg = [EvalBlock]
type Result = Except Output

data Output = ValOut OutFormat Value | TextOut String | NoOutput
                deriving (Show, Eq, Generic)

data OutFormat = Printed | Heatmap | Scatter  deriving (Show, Eq, Generic)

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

-- === misc ===

infixr 1 -->
infixr 2 ==>

(-->) :: Type -> Type -> Type
(-->) = ArrType

(==>) :: Type -> Type -> Type
(==>) = TabType

data LorT a b = L a | T b  deriving (Show, Eq)

fromL :: LorT a b -> a
fromL (L x) = x
fromL _ = error "Not a let-bound thing"

fromT :: LorT a b -> b
fromT (T x) = x
fromT _ = error "Not a type-ish thing"

lbind :: BinderP a -> FullEnv a b
lbind (v:>x) = v @> L x

tbind :: BinderP b -> FullEnv a b
tbind (v:>x) = v @> T x

type FullEnv v t = Env (LorT v t)
type Vars = FullEnv () ()

wrapDecls :: [DeclP b] -> ExprP b -> ExprP b
wrapDecls [] expr = expr
wrapDecls (decl:decls) expr = Decl decl (wrapDecls decls expr)

-- === substitutions ===

class HasVars a where
  freeVars :: a -> Vars

instance HasVars b => HasVars (ExprP b) where
  freeVars expr = case expr of
    Var v ts -> v @> L () <> foldMap freeVars ts
    Lit _ -> mempty
    PrimOp _ ts xs -> foldMap freeVars ts <> foldMap freeVars xs
    Decl decl body -> let (bvs, fvs) = declVars [decl]
                      in fvs <> (freeVars body `envDiff` bvs)
    Lam p body    -> withBinders p body
    App fexpr arg -> freeVars fexpr <> freeVars arg
    For b body    -> withBinders b body
    Get e ie      -> freeVars e <> freeVars ie
    -- TApp fexpr ts -> freeVars fexpr <> foldMap freeVars ts
    RecCon r      -> foldMap freeVars r
    TabCon ty xs -> freeVars ty <> foldMap freeVars xs
    IdxLit _ _ -> mempty
    Annot e ty -> freeVars e <> freeVars ty
    DerivAnnot e1 e2 -> freeVars e1 <> freeVars e2
    SrcAnnot e _ -> freeVars e
    Pack e ty exTy -> freeVars e <> freeVars ty <> freeVars exTy
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
    IdxSetLit _ -> mempty
    BoundTVar _ -> mempty

instance HasVars SigmaType where
  freeVars (Forall _ body) = freeVars body

instance HasVars Ann where
  freeVars NoAnn = mempty
  freeVars (Ann ty) = freeVars ty

instance HasVars NExpr where
  freeVars expr = case expr of
    NDecl decl body -> let (bvs, fvs) = declVars [decl]
                        in fvs <> (freeVars body `envDiff` bvs)
    NPrimOp _ ts xs -> foldMap freeVars ts <> foldMap freeVars xs
    NApp f xs -> freeVars f <> foldMap freeVars xs
    NAtoms xs -> foldMap freeVars xs
    NScan _ _ _ _ -> error $ "NScan not implemented" -- TODO
    NTabCon _ _ _ -> error $ "NTabCon not implemented" -- TODO

instance HasVars NAtom where
  freeVars atom = case atom of
    NLit _ -> mempty
    NVar v -> v @> L ()
    NGet e i -> freeVars e <> freeVars i
    -- AFor b body -> freeVars b <> (freeVars body `envDiff` lhsVars b)
    NLam bs body -> foldMap freeVars bs <>
                      (freeVars body `envDiff` foldMap lhsVars bs)
    NAtomicFor _ _  -> error $ "NAtomicFor not implemented" -- TODO
    NDerivAnnot _ _ -> error $ "NDerivAnnot not implemented" -- TODO
    NDeriv _        -> error $ "NDeriv not implemented" -- TODO

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

instance HasVars b => HasVars (BinderP b) where
  freeVars (_ :> b) = freeVars b

instance HasVars () where
  freeVars () = mempty

instance HasVars b => HasVars (DeclP b) where
   freeVars (LetMono p expr) = foldMap freeVars p <> freeVars expr
   freeVars (LetPoly b tlam) = freeVars b <> freeVars tlam
   freeVars (Unpack b _ expr) = freeVars b <> freeVars expr
   freeVars (TAlias _ ty) = freeVars ty

instance HasVars b => HasVars (TopDeclP b) where
  freeVars (TopDecl decl) = freeVars decl
  freeVars (EvalCmd (Command _ expr)) = freeVars expr

instance HasVars b => HasVars (TLamP b) where
  freeVars (TLam tbs expr) = freeVars expr `envDiff` foldMap bind tbs

instance (HasVars a, HasVars b) => HasVars (LorT a b) where
  freeVars (L x) = freeVars x
  freeVars (T x) = freeVars x

instance HasVars SourceBlock where
  freeVars block = case sbContents block of
    UTopDecl decl -> freeVars decl
    _ -> mempty

class BindsVars a where
  lhsVars :: a -> Vars

instance BindsVars (BinderP a) where
  lhsVars (v:>_) = v @> L ()

instance BindsVars (DeclP b) where
  lhsVars (LetMono p _ ) = foldMap lhsVars p
  lhsVars (LetPoly b _) = lhsVars b
  lhsVars (Unpack b tv _) = lhsVars b <> tv @> T ()
  lhsVars (TAlias v _) = v @> T ()

instance BindsVars (TopDeclP b) where
  lhsVars (TopDecl decl) = lhsVars decl
  lhsVars _ = mempty

instance BindsVars NDecl where
  lhsVars (NLet bs _) = foldMap lhsVars bs
  lhsVars (NUnpack bs tv _) = foldMap lhsVars bs <> tv @> T ()

instance BindsVars SourceBlock where
  lhsVars block = case sbContents block of
    UTopDecl decl -> lhsVars decl
    _ -> mempty

declVars :: (HasVars a, BindsVars a) => [a] -> (Vars, Vars)
declVars [] = (mempty, mempty)
declVars (decl:rest) = (bvs <> bvsRest, fvs <> (fvsRest `envDiff` bvs))
  where
    (bvs, fvs) = (lhsVars decl, freeVars decl)
    (bvsRest, fvsRest) = declVars rest

stripSrcAnnot :: ExprP b -> ExprP b
stripSrcAnnot expr = case expr of
  Var _ _ -> expr
  Lit _ -> expr
  PrimOp op ts xs -> PrimOp op ts (map recur xs)
  Decl decl body -> Decl (stripSrcAnnotDecl decl) (recur body)
  Lam p body    -> Lam p (recur body)
  App fexpr arg -> App (recur fexpr) (recur arg)
  For b body    -> For b (recur body)
  Get e ie      -> Get (recur e) (recur ie)
  RecCon r      -> RecCon (fmap recur r)
  -- TLam vs body  -> TLam vs (recur body)
  -- TApp fexpr ts -> TApp (recur fexpr) ts
  DerivAnnot e1 e2 -> DerivAnnot (recur e1) (recur e2)
  SrcAnnot e _ -> recur e
  Pack e t1 t2 -> Pack (recur e) t1 t2
  TabCon _ _ -> error $ "TabCon not implemented" -- TODO
  IdxLit _ _ -> error $ "IdxLit not implemented" -- TODO
  Annot _ _  -> error $ "Annot not implemented"  -- TODO
  where recur = stripSrcAnnot

stripSrcAnnotDecl :: DeclP b -> DeclP b
stripSrcAnnotDecl decl = case decl of
  LetMono p body -> LetMono p (stripSrcAnnot body)
  LetPoly b (TLam tbs body) -> LetPoly b (TLam tbs (stripSrcAnnot body))
  TAlias _ _ -> decl
  Unpack b v body -> Unpack b v (stripSrcAnnot body)

stripSrcAnnotTopDecl :: TopDeclP b -> TopDeclP b
stripSrcAnnotTopDecl (TopDecl decl) = TopDecl $ stripSrcAnnotDecl decl
stripSrcAnnotTopDecl (EvalCmd (Command cmd expr)) = EvalCmd (Command cmd (stripSrcAnnot expr))

instance RecTreeZip Type where
  recTreeZip (RecTree r) (RecType r') = RecTree $ recZipWith recTreeZip r r'
  recTreeZip (RecLeaf x) x' = RecLeaf (x, x')
  recTreeZip (RecTree _) _ = error "Bad zip"
