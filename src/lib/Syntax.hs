-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Syntax (Expr (..), Type (..), IdxSet, IdxSetVal, Builtin (..),
               ImpDecl (..), Decl (..), TopDecl (..), Command (..), Pat, SrcPos,
               CmdName (..), IdxExpr, TLam (..),
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
               Result (..), Result', freeVars, NLamExpr (..),
               Output (..), Nullable (..), SetVal (..), MonMap (..),
               Index, wrapDecls, builtinNames, commandNames, DataFormat (..),
               NExpr (..), NDecl (..), NAtom (..), SrcCtx,
               NTopDecl (..), NBinder, stripSrcAnnot, stripSrcAnnotTopDecl,
               SigmaType (..), asSigma, HasVars,
               SourceBlock (..), SourceBlock' (..), LitProg, ClassName (..),
               MonadicPrimitive (..), EffectTypeP (..), EffectType, NEffectType,
               RuleAnn (..), DeclAnn (..), CmpOp (..), catchIOExcept,
               LensPrimitive (..))  where

import Record
import Env

import qualified Data.Map.Strict as M

import Data.Tuple (swap)
import Data.Maybe (fromJust)
import Control.Monad.Except hiding (Except)
import Control.Exception  (Exception, catch)
import GHC.Generics
import Foreign.Ptr
import Data.Traversable
import Control.Applicative (liftA3)

-- === core IR ===

data Expr = Lit LitVal
          | Var Name Type [Type]
          | PrimOp Builtin [Type] [Expr]
          | Decl Decl Expr
          | Lam Type Pat Expr
          | App Expr Expr
          | For Pat Expr
          | Get Expr Expr
          | RecCon ProdKind (Record Expr)
          | TabCon Type [Expr]
          | IdxLit IdxSetVal Int
          | Annot Expr Type
          | SrcAnnot Expr SrcPos
          | Pack Expr Type Type
             deriving (Eq, Ord, Show, Generic)

data Decl = LetMono Pat Expr
          | LetPoly (BinderP SigmaType) TLam
          | DoBind Pat Expr
          | TyDef TyDefType Name [BinderP ()] Type
          | Unpack Binder Name Expr
            deriving (Eq, Ord, Show, Generic)

data TyDefType = TyAlias | NewType  deriving (Eq, Ord, Show, Generic)

type Pat = RecTree Binder

data ProdKind = Cart | Tens  deriving (Eq, Ord, Show, Generic)

data ClassName = Data | VSpace | IdxSet deriving (Eq, Ord, Show, Generic)
newtype Kind = Kind [ClassName]  deriving (Eq, Ord, Show, Generic)

data Type = BaseType BaseType
          | TypeVar Name
          | ArrType Lin Type Type
          | TabType IdxSet Type
          | RecType ProdKind (Record Type)
          | TypeApp Type [Type]
          | Monad EffectType Type
          | Lens Type Type
          | Exists Type
          | IdxSetLit IdxSetVal
          | Mult Multiplicity
          | BoundTVar Int
          | NoAnn
            deriving (Eq, Ord, Show, Generic)

type Lin = Type -- only TypeVar, BoundTVar and Mult constructors
data Multiplicity = Lin | NonLin  deriving (Eq, Ord, Show, Generic)

data EffectTypeP ty = Effect { readerEff :: ty
                             , writerEff :: ty
                             , stateEff  :: ty }  deriving (Eq, Ord, Show, Generic)
type EffectType = EffectTypeP Type

data SigmaType = Forall [Kind] Type  deriving (Eq, Ord, Show, Generic)
data TLam = TLam [TBinder] Expr  deriving (Eq, Ord, Show, Generic)

asSigma :: Type -> SigmaType
asSigma ty = Forall [] ty

type Binder  = BinderP Type

data TopDecl = TopDecl DeclAnn Decl
             | RuleDef RuleAnn SigmaType TLam
             | EvalCmd (Command Expr)  deriving (Show, Eq, Generic)

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
             | MemRef [ArrayRef] | MRun | MPrim MonadicPrimitive
             | LensPrim LensPrimitive | LensGet
               deriving (Eq, Ord, Generic)

data LensPrimitive = IdxAsLens | LensCompose | LensId
                       deriving (Eq, Ord, Generic)

data MonadicPrimitive = MAsk | MTell | MGet | MPut | MReturn
                          deriving (Eq, Ord, Generic)

data CmpOp = Less | Greater | Equal | LessEqual | GreaterEqual
               deriving (Eq, Ord, Show, Generic)

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
  ("newtypecast", NewtypeCast), ("select", Select),
  ("ask", MPrim MAsk), ("tell", MPrim MTell), ("get", MPrim MGet), ("put", MPrim MPut),
  ("return", MPrim MReturn), ("run", MRun),
  ("idxAsLens", LensPrim IdxAsLens),
  ("lensCompose", LensPrim LensCompose), ("lensId", LensPrim LensId),
  ("lensGet", LensGet)]

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

unitCon :: Expr
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
data SourceBlock' = UTopDecl TopDecl
                  | IncludeSourceFile String
                  | LoadData Pat DataFormat String
                  | ProseBlock String
                  | CommentLine
                  | EmptyLines
                  | UnParseable ReachedEOF String
                    deriving (Show, Eq, Generic)

-- === tuple-free ANF-ish normalized IR ===

data NExpr = NDecl NDecl NExpr
           | NScan NAtom NLamExpr
           | NPrimOp Builtin [Type] [NAtom]
           | NApp NAtom NAtom
           | NAtom NAtom
           | NRecGet NAtom RecField
           | NTabCon Type Type [NAtom]
             deriving (Show)

data NDecl = NLet NBinder NExpr
           | NUnpack NBinder Name NExpr
              deriving (Show)

data NAtom = NLit LitVal
           | NVar Name Type
           | NGet NAtom NAtom
           | NLam Type NLamExpr
           | NRecCon ProdKind (Record NAtom)
           -- Only used internally in the simplification pass as book-keeping
           -- for compile-time tables of functions etc.
           | NAtomicFor NBinder NExpr
           | NAtomicPrimOp Builtin [Type] [NAtom]
           | NDoBind NAtom NLamExpr
             deriving (Show)

data NLamExpr = NLamExpr [NBinder] NExpr  deriving (Show)

data NTopDecl = NTopDecl DeclAnn NDecl
              | NRuleDef RuleAnn Type NExpr
              | NEvalCmd (Command (Type, NExpr))
                 deriving (Show)

type NBinder = BinderP Type
type NEffectType = EffectTypeP Type

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
type Vars = FullEnv Type ()

wrapDecls :: [Decl] -> Expr -> Expr
wrapDecls [] expr = expr
wrapDecls (decl:decls) expr = Decl decl (wrapDecls decls expr)

-- === substitutions ===

class HasVars a where
  freeVars :: a -> Vars

instance HasVars Expr where
  freeVars expr = case expr of
    Var v ty ts -> v @> L ty <> freeVars ty <> foldMap freeVars ts
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
    TypeApp a b -> freeVars a <> foldMap freeVars b
    Exists body -> freeVars body
    Monad eff a -> foldMap freeVars eff <> freeVars a
    Lens a b    -> freeVars a <> freeVars b
    IdxSetLit _ -> mempty
    BoundTVar _ -> mempty
    Mult      _ -> mempty
    NoAnn       -> mempty

instance HasVars SigmaType where
  freeVars (Forall _ body) = freeVars body

instance HasVars b => HasVars (BinderP b) where
  freeVars (_ :> b) = freeVars b

instance HasVars () where
  freeVars () = mempty

instance HasVars Decl where
   freeVars (LetMono p expr) = foldMap freeVars p <> freeVars expr
   freeVars (LetPoly b tlam) = freeVars b <> freeVars tlam
   freeVars (DoBind  p expr) = foldMap freeVars p <> freeVars expr
   freeVars (Unpack b _ expr) = freeVars b <> freeVars expr
   freeVars (TyDef _ _ bs ty) = freeVars ty `envDiff` bindFold bs

instance HasVars TopDecl where
  freeVars (TopDecl _ decl) = freeVars decl
  freeVars (RuleDef ann ty body) = freeVars ann <> freeVars ty <> freeVars body
  freeVars (EvalCmd (Command _ expr)) = freeVars expr

instance HasVars RuleAnn where
  freeVars (LinearizationDef v) = v @> L unitTy

instance HasVars TLam where
  freeVars (TLam tbs expr) = freeVars expr `envDiff` foldMap bind tbs

instance (HasVars a, HasVars b) => HasVars (LorT a b) where
  freeVars (L x) = freeVars x
  freeVars (T x) = freeVars x

instance HasVars SourceBlock where
  freeVars block = case sbContents block of
    UTopDecl decl -> freeVars decl
    _ -> mempty

instance HasVars NExpr where
  freeVars expr = case expr of
    NDecl decl body -> freeVars decl <> (freeVars body `envDiff` bvs)
      where bvs = case decl of NLet b _       -> lhsVars b
                               NUnpack b tv _ -> lhsVars b <> tv @> ()
    NPrimOp _ ts xs -> foldMap freeVars ts <> foldMap freeVars xs
    NApp f x -> freeVars f <> freeVars x
    NAtom x  -> freeVars x
    NScan x lam -> freeVars x <> freeVars lam
    NRecGet x _ -> freeVars x
    NTabCon n ty xs -> freeVars n <> freeVars ty <> foldMap freeVars xs

instance HasVars NLamExpr where
  freeVars (NLamExpr bs body) =  foldMap freeVars bs
                               <> (freeVars body `envDiff` foldMap lhsVars bs)

instance HasVars NAtom where
  freeVars atom = case atom of
    NLit _ -> mempty
    NVar v ty -> v @> L ty <> freeVars ty
    NGet e i -> freeVars e <> freeVars i
    NLam _ lam -> freeVars lam
    NRecCon _ r -> foldMap freeVars r
    NAtomicFor b body ->  freeVars b <> (freeVars body `envDiff` lhsVars b)
    NAtomicPrimOp _ ts xs -> foldMap freeVars ts <> foldMap freeVars xs
    NDoBind m f -> freeVars m <> freeVars f

instance HasVars NDecl where
  freeVars (NLet bs expr) = foldMap freeVars bs <> freeVars expr
  freeVars (NUnpack bs _ expr) = foldMap freeVars bs <> freeVars expr

class BindsVars a where
  lhsVars :: a -> Env ()

instance BindsVars Binder where
  lhsVars (v:>_) = v @> ()

instance BindsVars Decl where
  lhsVars (LetMono p _  ) = foldMap lhsVars p
  lhsVars (LetPoly (v:>_) _) = v @> ()
  lhsVars (Unpack b tv _) = lhsVars b <> tv @> ()
  lhsVars (TyDef _ v _ _) = v @> ()
  lhsVars (DoBind  p _  ) = foldMap lhsVars p

instance BindsVars TopDecl where
  lhsVars (TopDecl _ decl) = lhsVars decl
  lhsVars _ = mempty

instance BindsVars SourceBlock where
  lhsVars block = case sbContents block of
    UTopDecl decl  -> lhsVars decl
    LoadData p _ _ -> foldMap lhsVars p
    _ -> mempty

declVars :: (HasVars a, BindsVars a) => [a] -> (Env (), Vars)
declVars [] = (mempty, mempty)
declVars (decl:rest) = (bvs <> bvsRest, fvs <> (fvsRest `envDiff` bvs))
  where
    (bvs, fvs) = (lhsVars decl, freeVars decl)
    (bvsRest, fvsRest) = declVars rest

stripSrcAnnot :: Expr -> Expr
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

stripSrcAnnotDecl :: Decl -> Decl
stripSrcAnnotDecl decl = case decl of
  LetMono p body -> LetMono p (stripSrcAnnot body)
  LetPoly b (TLam tbs body) -> LetPoly b (TLam tbs (stripSrcAnnot body))
  DoBind p body -> DoBind p (stripSrcAnnot body)
  TyDef _ _ _ _ -> decl
  Unpack b v body -> Unpack b v (stripSrcAnnot body)

stripSrcAnnotTopDecl :: TopDecl -> TopDecl
stripSrcAnnotTopDecl (TopDecl ann decl) = TopDecl ann $ stripSrcAnnotDecl decl
stripSrcAnnotTopDecl (RuleDef ann b (TLam tbs body)) = RuleDef ann b (TLam tbs (stripSrcAnnot body))
stripSrcAnnotTopDecl (EvalCmd (Command cmd expr)) = EvalCmd (Command cmd (stripSrcAnnot expr))

instance RecTreeZip Type where
  recTreeZip (RecTree r) (RecType _ r') = RecTree $ recZipWith recTreeZip r r'
  recTreeZip (RecLeaf x) x' = RecLeaf (x, x')
  recTreeZip (RecTree _) _ = error "Bad zip"

instance Functor EffectTypeP where
  fmap = fmapDefault

instance Foldable EffectTypeP where
  foldMap = foldMapDefault

instance Traversable EffectTypeP where
  traverse f (Effect r w s) = liftA3 Effect (f r) (f w) (f s)
