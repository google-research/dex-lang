-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Syntax (ExprP (..), Expr, Type (..), IdxSet, IdxSetVal, Builtin (..),
               UExpr, UTopDecl, UDecl, ImpDecl (..), TopDeclP (..),
               DeclP (..), Decl, TopDecl, Command (..), UPat, Pat, SrcPos,
               CmdName (..), IdxExpr, UBinder, PatP, Ann (..),
               LitVal (..), BaseType (..), Binder, TBinder, lbind, tbind,
               Except, Err (..), ErrType (..), OutFormat (..), ProdKind (..),
               throw, throwIf, Kind (..), TyDefType (..),
               addContext, addSrcContext, Lin, Multiplicity (..),
               FullEnv, (-->), (==>), (--@), LorT (..), fromL, fromT,
               lhsVars, Size, unitTy, unitCon,
               ImpProg (..), ImpInstr (..), ImpStatement, Val,
               IExpr (..), IType (..), IBinder, ArrayType, IVal, Ptr,
               VecRef, VecRef' (..), Vec (..),
               ArrayP (..), Array, ArrayRef, FlatValP (..), FlatVal, FlatValRef,
               Result (..), Result', freeVars, freeNVars,
               Output (..), Nullable (..), SetVal (..), MonMap (..),
               Index, wrapDecls, builtinNames, commandNames, DataFormat (..),
               NExpr (..), NDecl (..), NAtom (..), NType (..), SrcCtx,
               NTopDecl (..), NBinder, stripSrcAnnot, stripSrcAnnotTopDecl,
               SigmaType (..), TLamP (..), TLam, UTLam, asSigma, HasVars, HasNVars,
               SourceBlock (..), SourceBlock' (..), LitProg, ClassName (..),
               RuleAnn (..), DeclAnn (..), CmpOp (..), catchIOExcept)  where

import Record
import Env

import qualified Data.Map.Strict as M

import Data.Tuple (swap)
import Data.Maybe (fromJust)
import Control.Monad.Except hiding (Except)
import Control.Exception  (Exception, catch)
import GHC.Generics
import Foreign.Ptr

-- === core IR ===

data ExprP b =
            Lit LitVal
          | Var Name b [Type]
          | PrimOp Builtin [Type] [ExprP b]
          | Decl (DeclP b) (ExprP b)
          | Lam b (PatP b) (ExprP b)
          | App (ExprP b) (ExprP b)
          | For (PatP b) (ExprP b)
          | Get (ExprP b) (ExprP b)
          | RecCon ProdKind (Record (ExprP b))
          | TabCon b [ExprP b]
          | IdxLit IdxSetVal Int
          | Annot (ExprP b) Type
          | SrcAnnot (ExprP b) SrcPos
          | Pack (ExprP b) Type Type
             deriving (Eq, Ord, Show, Generic)

data DeclP b = LetMono (PatP b) (ExprP b)
             | LetPoly (BinderP SigmaType) (TLamP b)
             | TyDef TyDefType Name Type
             | Unpack (BinderP b) Name (ExprP b)
               deriving (Eq, Ord, Show, Generic)

data TyDefType = TyAlias | NewType  deriving (Eq, Ord, Show, Generic)

type PatP b = RecTree (BinderP b)

data ProdKind = Cart | Tens  deriving (Eq, Ord, Show, Generic)

data ClassName = Data | VSpace | IdxSet deriving (Eq, Ord, Show, Generic)
newtype Kind = Kind [ClassName]  deriving (Eq, Ord, Show, Generic)

data Type = BaseType BaseType
          | TypeVar Name
          | ArrType Lin Type Type
          | TabType IdxSet Type
          | RecType ProdKind (Record Type)
          | Exists Type
          | IdxSetLit IdxSetVal
          | Mult Multiplicity
          | BoundTVar Int
             deriving (Eq, Ord, Show, Generic)

type Lin = Type -- only TypeVar, BoundTVar and Mult constructors
data Multiplicity = Lin | NonLin  deriving (Eq, Ord, Show, Generic)

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

data TopDeclP b = TopDecl DeclAnn (DeclP b)
                | RuleDef RuleAnn SigmaType (TLamP b)
                | EvalCmd (Command (ExprP b))  deriving (Show, Eq, Generic)

data RuleAnn = LinearizationDef Name deriving (Show, Eq, Generic)
data DeclAnn = PlainDecl | ADPrimitive  deriving (Show, Eq, Generic)

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

data Builtin = IAdd | ISub | IMul | FAdd | FSub | FMul | FDiv | FNeg
             | Cmp CmpOp | Pow | IntToReal | BoolToInt
             | And | Or | Not
             | Range | Scan | Linearize | Transpose
             | VZero | VAdd | VSingle | VSum | IndexAsInt | IntAsIndex | IdxSetSize
             | Rem | FFICall Int String | Filter | Todo | NewtypeCast | Select
             | MemRef [ArrayRef]
                deriving (Eq, Ord, Generic)

data CmpOp = Less | Greater | Equal | LessEqual | GreaterEqual  deriving (Eq, Ord, Show, Generic)

builtinNames :: M.Map String Builtin
builtinNames = M.fromList [
  ("iadd", IAdd), ("isub", ISub), ("imul", IMul),
  ("fadd", FAdd), ("fsub", FSub), ("fmul", FMul),
  ("fdiv", FDiv), ("fneg", FNeg), ("pow", Pow), ("rem", Rem),
  ("and", And), ("or", Or), ("not", Not),
  ("lt", Cmp Less), ("gt", Cmp Greater), ("eq", Cmp Equal),
  ("le", Cmp LessEqual), ("ge", Cmp GreaterEqual),
  ("scan", Scan), ("range", Range),
  ("inttoreal", IntToReal), ("booltoint", BoolToInt),
  ("idxSetSize", IdxSetSize),
  ("linearize", Linearize), ("linearTranspose", Transpose),
  ("asint", IndexAsInt), ("asidx", IntAsIndex),
  ("filter", Filter), ("vzero", VZero), ("vadd", VAdd),
  ("vsingle", VSingle), ("vsum", VSum), ("todo", Todo),
  ("newtypecast", NewtypeCast), ("select", Select)]

commandNames :: M.Map String CmdName
commandNames = M.fromList [
  ("p", EvalExpr Printed), ("t", GetType), ("typed", ShowTyped),
  ("llvm", ShowLLVM), ("deshadowed", ShowDeshadowed),
  ("normalized", ShowNormalized), ("imp", ShowImp), ("asm", ShowAsm),
  ("time", TimeIt), ("plot", EvalExpr Scatter), ("simp", ShowSimp),
  ("deriv", ShowDeriv), ("plotmat", EvalExpr Heatmap),
  ("flops", Flops), ("parse", ShowParse)]

builtinStrs :: M.Map Builtin String
builtinStrs = M.fromList $ map swap (M.toList builtinNames)

instance Show Builtin where
  show (FFICall _ s) = "%%" ++ s
  show (MemRef xs) = "%%memref" ++ show xs
  show b = "%" ++ fromJust (M.lookup b builtinStrs)

data CmdName = GetType | ShowParse | ShowTyped | ShowLLVM | ShowDeshadowed
             | ShowNormalized | ShowSimp | ShowImp | ShowAsm | TimeIt | Flops
             | EvalExpr OutFormat | ShowDeriv | Dump DataFormat String
                deriving  (Show, Eq, Generic)

unitTy :: Type
unitTy = RecType Cart (Tup [])

unitCon :: ExprP b
unitCon = RecCon Cart (Tup [])

-- === runtime data representations ===

-- Closed term limited to constructors Lit, RecCon, TabCon, IdxLit, Pack
type Val = Expr

-- TODO: use Data.Vector instead of lists
data FlatValP a = FlatVal Type [ArrayP a]  deriving (Show, Eq, Ord, Generic)
data ArrayP a = Array [Int] a     deriving (Show, Eq, Ord, Generic)

type FlatVal    = FlatValP Vec
type FlatValRef = FlatValP VecRef

type Array    = ArrayP Vec
type ArrayRef = ArrayP VecRef

data Vec = IntVec  [Int]
         | RealVec [Double]
         | BoolVec [Int]
            deriving (Show, Eq, Ord, Generic)

type VecRef = (Int, VecRef')
data VecRef' = IntVecRef  (Ptr Int)
             | RealVecRef (Ptr Double)
             | BoolVecRef (Ptr Int)
                deriving (Show, Eq, Ord, Generic)

-- === source AST ===

data SourceBlock = SourceBlock
  { sbLine     :: Int
  , sbOffset   :: Int
  , sbText     :: String
  , sbContents :: SourceBlock' }  deriving (Show)

type ReachedEOF = Bool
data SourceBlock' = UTopDecl UTopDecl
                  | IncludeSourceFile String
                  | LoadData UPat DataFormat String
                  | ProseBlock String
                  | CommentLine
                  | EmptyLines
                  | UnParseable ReachedEOF String
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
           | NPrimOp Builtin [[NType]] [NAtom]
           | NApp NAtom [NAtom]
           | NAtoms [NAtom]
           | NTabCon NType NType [NAtom]
             deriving (Show)

data NDecl = NLet [NBinder] NExpr
           | NUnpack [NBinder] Name NExpr
              deriving (Show)

data NAtom = NLit LitVal
           | NVar Name NType
           | NGet NAtom NAtom
           | NLam Multiplicity [NBinder] NExpr
           -- Only used internally in the simplification pass as book-keeping
           -- for compile-time tables of functions etc.
           | NAtomicFor NBinder NAtom
              deriving (Show)

data NType = NBaseType BaseType
           | NTypeVar Name
           | NArrType Multiplicity [NType] [NType]
           | NTabType NType NType
           | NExists [NType]
           | NIdxSetLit IdxSetVal
           | NBoundTVar Int
              deriving (Eq, Show)

data NTopDecl = NTopDecl DeclAnn NDecl
              | NRuleDef RuleAnn NType NExpr
              | NEvalCmd (Command (Type, NExpr))
                 deriving (Show)

type NBinder = BinderP NType

-- === imperative IR ===

newtype ImpProg = ImpProg [ImpStatement]  deriving (Show, Semigroup, Monoid)

type ImpStatement = (Maybe IBinder, ImpInstr)

data ImpInstr = IPrimOp Builtin [BaseType] [IExpr]
              | Load  IExpr
              | Store IExpr IExpr  -- destination first
              | Copy  IExpr IExpr  -- destination first
              | Alloc ArrayType
              | Free Name ArrayType
              | Loop Name Size ImpProg
                  deriving (Show)

data IExpr = ILit LitVal
           | IRef ArrayRef
           | IVar Name IType
           | IGet IExpr Index
               deriving (Show, Eq)

type IVal = IExpr  -- only ILit and IRef constructors

data ImpDecl = ImpTopLet [IBinder] ImpProg
             | ImpEvalCmd (Command (Type, [IBinder], ImpProg))

type IBinder = BinderP IType

data IType = IValType BaseType
           | IRefType ArrayType
              deriving (Show, Eq)

type ArrayType = (BaseType, [Size])

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

type LitProg = [(SourceBlock, Result)]
type Result' = Except Output
type SrcCtx = Maybe SrcPos
newtype Result = Result Result' deriving (Show, Eq)

data Output = ValOut OutFormat FlatVal | TextOut String | NoOutput
                deriving (Show, Eq, Generic)

data OutFormat = Printed | Heatmap | Scatter   deriving (Show, Eq, Generic)
data DataFormat = DexObject | DexBinaryObject  deriving (Show, Eq, Generic)

data Err = Err ErrType SrcCtx String  deriving (Show, Eq)
instance Exception Err

data ErrType = NoErr
             | ParseErr
             | TypeErr
             | LinErr
             | UnboundVarErr
             | RepeatedVarErr
             | CompilerErr
             | NotImplementedErr
             | DataIOErr
             | MiscErr
  deriving (Show, Eq)

type Except a = Either Err a

throw :: MonadError Err m => ErrType -> String -> m a
throw e s = throwError $ Err e Nothing s

throwIf :: MonadError Err m => Bool -> ErrType -> String -> m ()
throwIf True  e s = throw e s
throwIf False _ _ = return ()

modifyErr :: MonadError e m => m a -> (e -> e) -> m a
modifyErr m f = catchError m $ \e -> throwError (f e)

addContext :: MonadError Err m => String -> m a -> m a
addContext s m = modifyErr m $ \(Err e p s') ->
                                 Err e p (s' ++ "\ncontext:\n" ++ s)

addSrcContext :: MonadError Err m => SrcCtx -> m a -> m a
addSrcContext ctx m = modifyErr m updateErr
  where
    updateErr :: Err -> Err
    updateErr (Err e ctx' s) = case ctx' of Nothing -> Err e ctx  s
                                            Just _  -> Err e ctx' s

catchIOExcept :: IO a -> IO (Except a)
catchIOExcept m = catch (liftM Right m) $ \e -> return (Left (e::Err))

-- === misc ===

infixr 1 -->
infixr 1 --@
infixr 2 ==>

(-->) :: Type -> Type -> Type
(-->) = ArrType (Mult NonLin)

(--@) :: Type -> Type -> Type
(--@) = ArrType (Mult Lin)

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
    Var v ty ts -> v @> L () <> freeVars ty <> foldMap freeVars ts
    Lit _ -> mempty
    PrimOp _ ts xs -> foldMap freeVars ts <> foldMap freeVars xs
    Decl decl body -> let (bvs, fvs) = declVars [decl]
                      in fvs <> (freeVars body `envDiff` bvs)
    Lam _ p body    -> withBinders p body
    App fexpr arg -> freeVars fexpr <> freeVars arg
    For b body    -> withBinders b body
    Get e ie      -> freeVars e <> freeVars ie
    -- TApp fexpr ts -> freeVars fexpr <> foldMap freeVars ts
    RecCon _ r    -> foldMap freeVars r
    TabCon ty xs -> freeVars ty <> foldMap freeVars xs
    IdxLit _ _ -> mempty
    Annot e ty -> freeVars e <> freeVars ty
    SrcAnnot e _ -> freeVars e
    Pack e ty exTy -> freeVars e <> freeVars ty <> freeVars exTy
    where
      withBinders p e = foldMap freeVars p
                          <> (freeVars e `envDiff` foldMap lhsVars p)

instance HasVars Type where
  freeVars ty = case ty of
    BaseType _ -> mempty
    TypeVar v  -> v @> T ()
    ArrType _ a b -> freeVars a <> freeVars b
    TabType a b -> freeVars a <> freeVars b
    RecType _ r -> foldMap freeVars r
    Exists body -> freeVars body
    IdxSetLit _ -> mempty
    BoundTVar _ -> mempty
    Mult      _ -> mempty

instance HasVars SigmaType where
  freeVars (Forall _ body) = freeVars body

instance HasVars Ann where
  freeVars NoAnn = mempty
  freeVars (Ann ty) = freeVars ty

instance HasVars b => HasVars (BinderP b) where
  freeVars (_ :> b) = freeVars b

instance HasVars () where
  freeVars () = mempty

instance HasVars b => HasVars (DeclP b) where
   freeVars (LetMono p expr) = foldMap freeVars p <> freeVars expr
   freeVars (LetPoly b tlam) = freeVars b <> freeVars tlam
   freeVars (Unpack b _ expr) = freeVars b <> freeVars expr
   freeVars (TyDef _ _ ty) = freeVars ty

instance HasVars b => HasVars (TopDeclP b) where
  freeVars (TopDecl _ decl) = freeVars decl
  freeVars (RuleDef ann ty body) = freeVars ann <> freeVars ty <> freeVars body
  freeVars (EvalCmd (Command _ expr)) = freeVars expr

instance HasVars RuleAnn where
  freeVars (LinearizationDef v) = v @> L ()

instance HasVars b => HasVars (TLamP b) where
  freeVars (TLam tbs expr) = freeVars expr `envDiff` foldMap bind tbs

instance (HasVars a, HasVars b) => HasVars (LorT a b) where
  freeVars (L x) = freeVars x
  freeVars (T x) = freeVars x

instance HasVars SourceBlock where
  freeVars block = case sbContents block of
    UTopDecl decl -> freeVars decl
    _ -> mempty

type NVars = FullEnv NType ()

class HasNVars a where
  freeNVars :: a -> NVars

instance HasNVars NExpr where
  freeNVars expr = case expr of
    NDecl decl body -> freeNVars decl <> (freeNVars body `envDiff` bvs)
      where bvs = case decl of NLet bs _       -> foldMap lhsVars bs
                               NUnpack bs tv _ -> foldMap lhsVars bs <> tv @> T ()
    NPrimOp _ ts xs -> foldMap (foldMap freeNVars) ts <> foldMap freeNVars xs
    NApp f xs -> freeNVars f <> foldMap freeNVars xs
    NAtoms xs -> foldMap freeNVars xs
    NScan b bs x0 body -> foldMap freeNVars x0 <>
      ((freeNVars body `envDiff` lhsVars b) `envDiff` foldMap lhsVars bs)
    NTabCon n ty xs -> freeNVars n <> freeNVars ty <> foldMap freeNVars xs

instance HasNVars NAtom where
  freeNVars atom = case atom of
    NLit _ -> mempty
    NVar v ty -> v @> L ty <> freeNVars ty
    NGet e i -> freeNVars e <> freeNVars i
    NLam _ bs body -> foldMap freeNVars bs <>
                      (freeNVars body `envDiff` foldMap lhsVars bs)
    NAtomicFor b body ->  freeNVars b <> (freeNVars body `envDiff` lhsVars b)

instance HasNVars NDecl where
  freeNVars (NLet bs expr) = foldMap freeNVars bs <> freeNVars expr
  freeNVars (NUnpack bs _ expr) = foldMap freeNVars bs <> freeNVars expr

instance HasNVars NType where
  freeNVars ty = case ty of
    NBaseType _ -> mempty
    NTypeVar v -> v @> T ()
    NArrType _ as bs -> foldMap freeNVars as <> foldMap freeNVars bs
    NTabType a b -> freeNVars a <> freeNVars b
    NExists ts -> foldMap freeNVars ts
    NIdxSetLit _ -> mempty
    NBoundTVar _ -> mempty

instance HasNVars b => HasNVars (BinderP b) where
  freeNVars (_ :> b) = freeNVars b

class BindsVars a where
  lhsVars :: a -> Vars

instance BindsVars (BinderP a) where
  lhsVars (v:>_) = v @> L ()

instance BindsVars (DeclP b) where
  lhsVars (LetMono p _ ) = foldMap lhsVars p
  lhsVars (LetPoly b _) = lhsVars b
  lhsVars (Unpack b tv _) = lhsVars b <> tv @> T ()
  lhsVars (TyDef _ v _) = v @> T ()

instance BindsVars (TopDeclP b) where
  lhsVars (TopDecl _ decl) = lhsVars decl
  lhsVars _ = mempty

instance BindsVars SourceBlock where
  lhsVars block = case sbContents block of
    UTopDecl decl  -> lhsVars decl
    LoadData p _ _ -> foldMap lhsVars p
    _ -> mempty

declVars :: (HasVars a, BindsVars a) => [a] -> (Vars, Vars)
declVars [] = (mempty, mempty)
declVars (decl:rest) = (bvs <> bvsRest, fvs <> (fvsRest `envDiff` bvs))
  where
    (bvs, fvs) = (lhsVars decl, freeVars decl)
    (bvsRest, fvsRest) = declVars rest

stripSrcAnnot :: ExprP b -> ExprP b
stripSrcAnnot expr = case expr of
  Var _ _ _ -> expr
  Lit _   -> expr
  PrimOp op ts xs -> PrimOp op ts (map recur xs)
  Decl decl body  -> Decl (stripSrcAnnotDecl decl) (recur body)
  Lam l p body    -> Lam l p (recur body)
  App f arg    -> App (recur f) (recur arg)
  For b body   -> For b (recur body)
  Get e ie     -> Get (recur e) (recur ie)
  RecCon k r   -> RecCon k (fmap recur r)
  SrcAnnot e _ -> recur e
  Pack e t1 t2 -> Pack (recur e) t1 t2
  TabCon ty xs -> TabCon ty (fmap recur xs)
  IdxLit _ _   -> expr
  Annot e ty   -> Annot (recur e) ty
  where recur = stripSrcAnnot

stripSrcAnnotDecl :: DeclP b -> DeclP b
stripSrcAnnotDecl decl = case decl of
  LetMono p body -> LetMono p (stripSrcAnnot body)
  LetPoly b (TLam tbs body) -> LetPoly b (TLam tbs (stripSrcAnnot body))
  TyDef _ _ _ -> decl
  Unpack b v body -> Unpack b v (stripSrcAnnot body)

stripSrcAnnotTopDecl :: TopDeclP b -> TopDeclP b
stripSrcAnnotTopDecl (TopDecl ann decl) = TopDecl ann $ stripSrcAnnotDecl decl
stripSrcAnnotTopDecl (RuleDef ann b (TLam tbs body)) = RuleDef ann b (TLam tbs (stripSrcAnnot body))
stripSrcAnnotTopDecl (EvalCmd (Command cmd expr)) = EvalCmd (Command cmd (stripSrcAnnot expr))

instance RecTreeZip Type where
  recTreeZip (RecTree r) (RecType _ r') = RecTree $ recZipWith recTreeZip r r'
  recTreeZip (RecLeaf x) x' = RecLeaf (x, x')
  recTreeZip (RecTree _) _ = error "Bad zip"
