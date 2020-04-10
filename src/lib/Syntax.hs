-- Copyright 2019 Google LL
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StrictData #-}

module Syntax (
    Type (..), BaseType (..), Effect, EffectiveType, Mult,
    Kind (..), ClassName (..), TyQual (..),
    FExpr (..), FLamExpr (..), SrcPos, Pat, FDecl (..), Var, Dep,
    TVar, FTLam (..), Expr (..), Decl (..), CExpr, Con, Atom (..), LamExpr (..),
    PrimExpr (..), PrimCon (..), LitVal (..), PrimEffect (..), PrimOp (..),
    VSpaceOp (..), ScalarBinOp (..), ScalarUnOp (..), CmpOp (..), SourceBlock (..),
    ReachedEOF, SourceBlock' (..), TypeEnv, SubstEnv, Scope,
    RuleAnn (..), CmdName (..), Val, TopEnv (..),
    ModuleP (..), ModuleType, Module, ModBody (..),
    FModBody (..), FModule, ImpModBody (..), ImpModule,
    Array (..), ImpProg (..), ImpStatement, ImpInstr (..), IExpr (..), IVal, IPrimOp,
    IVar, IType (..), ArrayType, SetVal (..), MonMap (..), LitProg,
    SrcCtx, Result (..), Output (..), OutFormat (..), DataFormat (..),
    Err (..), ErrType (..), Except, throw, throwIf, modifyErr, addContext,
    addSrcContext, catchIOExcept, (-->), (--@), (==>), LorT (..),
    fromL, fromT, FullEnv, unitTy, sourceBlockBoundVars, PassName (..), parsePassName,
    TraversableExpr, traverseExpr, fmapExpr, freeVars, HasVars, declBoundVars,
    strToName, nameToStr, unzipExpr, declAsModule, exprAsModule, lbind, tbind,
    noEffect, isPure, EffectName (..), EffectRow,
    traverseType, monMapSingle, monMapLookup, PiType (..), makePi, applyPi)
  where

import Data.Tuple (swap)
import qualified Data.Map.Strict as M
import Control.Applicative
import Control.Monad.Identity
import Control.Monad.Writer
import Control.Monad.Except hiding (Except)
import Control.Exception  (Exception, catch)
import GHC.Generics
import Foreign.Ptr
import Data.Foldable (fold)
import Data.Traversable
import Control.Applicative (liftA3)

import Record
import Env

-- === types ===

data Type = TypeVar TVar
          | BaseType BaseType
          | ArrowType Mult PiType
          | IdxSetLit Int
          | Range Type Type
          | TabType Type Type
          | ArrayType [Int] BaseType
          | RecType (Record Type)
          | Ref Type
          | Forall [TVar] [TyQual] Type
          | TypeAlias [TVar] Type
          | TypeApp Type [Type]
          | Dep Var
          | DepLit Int
          | NoDep
          | Lin
          | NonLin
          | Effect (EffectRow Type) (Maybe Type)
          | NoAnn
            deriving (Show, Eq, Generic)

data Kind = TyKind
          | ArrowKind [Kind] Kind
          | MultKind
          | EffectKind
          | DepKind
          | NoKindAnn
            deriving (Eq, Show, Ord, Generic)

type EffectRow a = Env (EffectName, a)

data EffectName = Reader | Writer | State  deriving (Eq, Show)

data PiType = Pi Type EffectiveType  deriving (Eq, Show)

data  TyQual = TyQual TVar ClassName  deriving (Eq, Show)

data BaseType = IntType | BoolType | RealType | StrType
                deriving (Show, Eq, Generic)
type TVar = VarP Kind
type Mult   = Type
type Dep    = Type
type Effect = Type
type EffectiveType = (Effect, Type)

data ClassName = Data | VSpace | IdxSet  deriving (Show, Eq, Generic)

data TopEnv = TopEnv { topTypeEnv  :: TypeEnv
                     , topSubstEnv :: SubstEnv
                     , linRules    :: Env Atom }  deriving (Show, Eq, Generic)

type TypeEnv  = FullEnv Type Kind
type SubstEnv = FullEnv Atom Type

type Scope = Env ()

noEffect :: Effect
noEffect = Effect mempty Nothing

isPure :: Effect -> Bool
isPure (Effect eff Nothing) | eff == mempty = True
isPure _ = False

type ModuleType = (TypeEnv, TypeEnv)
data ModuleP body = Module ModuleType body  deriving (Show, Eq)

-- === front-end language AST ===

data FExpr = FDecl FDecl FExpr
           | FVar Var
           | FPrimExpr (PrimExpr Type FExpr FLamExpr)
           | Annot FExpr Type
           | SrcAnnot FExpr SrcPos -- TODO: make mandatory?
             deriving (Eq, Show, Generic)

type Pat = RecTree Var
data FLamExpr = FLamExpr Pat FExpr  deriving (Show, Eq, Generic)
type SrcPos = (Int, Int)

data FDecl = LetMono Pat FExpr
           | LetPoly Var FTLam
           | TyDef TVar Type
           | FRuleDef RuleAnn Type FTLam
             deriving (Show, Eq, Generic)

type Var  = VarP Type
data FTLam = FTLam [TVar] [TyQual] FExpr  deriving (Show, Eq, Generic)

data FModBody = FModBody [FDecl] (Env Type)  deriving (Show, Eq, Generic)
type FModule = ModuleP FModBody

data RuleAnn = LinearizationDef Name    deriving (Show, Eq, Generic)

-- === normalized core IR ===

data Expr = Decl Decl Expr
          | CExpr CExpr
          | Atom Atom
            deriving (Show, Eq, Generic)

data Decl = Let Var CExpr  deriving (Show, Eq, Generic)

type CExpr = PrimOp  Type Atom LamExpr
type Con   = PrimCon Type Atom LamExpr

data Atom = Var Var
          | TLam [TVar] [TyQual] Expr
          | Con Con
            deriving (Show, Eq, Generic)

data LamExpr = LamExpr Var Expr  deriving (Show, Eq, Generic)

data ModBody = ModBody [Decl] TopEnv  deriving (Show, Eq, Generic)
type Module = ModuleP ModBody
type Val = Atom

-- === primitive constructors and operators ===

data PrimExpr ty e lam = OpExpr  (PrimOp ty e lam)
                       | ConExpr (PrimCon ty e lam)
                         deriving (Show, Eq, Generic)

data PrimCon ty e lam =
        Lit LitVal
      | Lam ty ty lam
      | RecCon (Record e)
      | AsIdx ty e        -- Construct an index from an expression
                          -- NOTE: the indices are expected to be zero-based!
                          -- This means that even though the index space might
                          -- contain all integers between 5 and 10 (exclusive),
                          -- the only integers that are valid to be cast to such
                          -- indices fall into the range of [0, 5).
      | AFor ty e
      | AGet e
      | ArrayRef Array
      | Todo ty
        deriving (Show, Eq, Generic)

data LitVal = IntLit  Int
            | RealLit Double
            | BoolLit Bool
            | StrLit  String
              deriving (Show, Eq, Generic)

data Array = Array [Int] BaseType (Ptr ())  deriving (Show, Eq)

data PrimOp ty e lam =
        App ty ty e e
      | TApp e [ty]
      | For lam
      | TabGet e e
      | RecGet e RecField
      | ArrayGep e e
      | LoadScalar e
      | TabCon ty ty [e]
      | ScalarBinOp ScalarBinOp e e | ScalarUnOp ScalarUnOp e
      | VSpaceOp ty (VSpaceOp e) | Cmp CmpOp ty e e | Select ty e e e
      | PrimEffect ty e (PrimEffect e)
      | RunReader e  lam
      | RunWriter    lam
      | RunState  e  lam
      | IndexEff EffectName ty e e lam
      | Linearize lam | Transpose lam
      | IntAsIndex ty e | IdxSetSize ty
      | FFICall String [ty] ty [e]
      | NewtypeCast ty e
        deriving (Show, Eq, Generic)

data PrimEffect e = MAsk | MTell e | MGet | MPut e  deriving (Show, Eq, Generic)

data VSpaceOp e = VZero | VAdd e e deriving (Show, Eq, Generic)
data ScalarBinOp = IAdd | ISub | IMul | ICmp CmpOp | Pow
                 | FAdd | FSub | FMul | FCmp CmpOp | FDiv
                 | And | Or | Rem
                   deriving (Show, Eq, Generic)

data ScalarUnOp = Not | FNeg | IntToReal | BoolToInt | IndexAsInt
                  deriving (Show, Eq, Generic)

data CmpOp = Less | Greater | Equal | LessEqual | GreaterEqual
             deriving (Show, Eq, Generic)

type PrimName = PrimExpr () () ()

builtinNames :: M.Map String PrimName
builtinNames = M.fromList
  [ ("iadd", binOp IAdd), ("isub", binOp ISub), ("imul", binOp IMul)
  , ("fadd", binOp FAdd), ("fsub", binOp FSub), ("fmul", binOp FMul)
  , ("fdiv", binOp FDiv), ("pow" , binOp Pow ), ("rem" , binOp Rem )
  , ("and" , binOp And ), ("or"  , binOp Or  ), ("not" , unOp  Not )
  , ("fneg", unOp  FNeg)
  , ("inttoreal", unOp IntToReal)
  , ("booltoint", unOp BoolToInt)
  , ("asint"    , unOp IndexAsInt)
  , ("idxSetSize"      , OpExpr $ IdxSetSize ())
  , ("linearize"       , OpExpr $ Linearize ())
  , ("linearTranspose" , OpExpr $ Transpose ())
  , ("asidx"           , OpExpr $ IntAsIndex () ())
  , ("vzero"           , OpExpr $ VSpaceOp () $ VZero)
  , ("vadd"            , OpExpr $ VSpaceOp () $ VAdd () ())
  , ("newtypecast"     , OpExpr $ NewtypeCast () ())
  , ("select"          , OpExpr $ Select () () () ())
  , ("runReader"       , OpExpr $ RunReader () ())
  , ("runWriter"       , OpExpr $ RunWriter    ())
  , ("runState"        , OpExpr $ RunState  () ())
  , ("indexReader"     , OpExpr $ IndexEff Reader () () () ())
  , ("indexWriter"     , OpExpr $ IndexEff Writer () () () ())
  , ("indexState"      , OpExpr $ IndexEff State  () () () ())
  , ("todo"       , ConExpr $ Todo ())
  , ("ask"        , OpExpr $ PrimEffect () () $ MAsk)
  , ("tell"       , OpExpr $ PrimEffect () () $ MTell ())
  , ("get"        , OpExpr $ PrimEffect () () $ MGet)
  , ("put"        , OpExpr $ PrimEffect () () $ MPut  ()) ]
  where
    binOp op = OpExpr $ ScalarBinOp op () ()
    unOp  op = OpExpr $ ScalarUnOp  op ()

strToName :: String -> Maybe PrimName
strToName s = M.lookup s builtinNames

nameToStr :: PrimName -> String
nameToStr prim = case lookup prim $ map swap $ M.toList builtinNames of
  Just s  -> s
  Nothing -> show prim

-- === top-level constructs ===

data SourceBlock = SourceBlock
  { sbLine     :: Int
  , sbOffset   :: Int
  , sbText     :: String
  , sbContents :: SourceBlock' }  deriving (Show)

type ReachedEOF = Bool
data SourceBlock' = RunModule FModule
                  | Command CmdName (Var, FModule)
                  | GetNameType Var
                  | IncludeSourceFile String
                  | LoadData Pat DataFormat String
                  | ProseBlock String
                  | CommentLine
                  | EmptyLines
                  | UnParseable ReachedEOF String
                    deriving (Show, Eq, Generic)

data CmdName = GetType | ShowPasses | ShowPass PassName
             | TimeIt | EvalExpr OutFormat | Dump DataFormat String
                deriving  (Show, Eq, Generic)

declAsModule :: FDecl -> FModule
declAsModule decl = Module (freeVars decl, fDeclBoundVars decl) (FModBody [decl] mempty)

exprAsModule :: FExpr -> (Var, FModule)
exprAsModule expr = (v, Module (freeVars expr, lbind v) (FModBody body mempty))
  where v = "*ans*" :> NoAnn
        body = [LetMono (RecLeaf v) expr]

-- === imperative IR ===

data ImpModBody = ImpModBody [IVar] ImpProg TopEnv
type ImpModule = ModuleP ImpModBody

newtype ImpProg = ImpProg [ImpStatement]  deriving (Show, Semigroup, Monoid)
type ImpStatement = (Maybe IVar, ImpInstr)

data ImpInstr = Load  IExpr
              | Store IExpr IExpr  -- destination first
              | Copy  IExpr IExpr  -- destination first
              | Alloc ArrayType
              | Free IVar
              | Loop IVar Size ImpProg
              | IPrimOp IPrimOp
                deriving (Show)

data IExpr = ILit LitVal
           | IRef Array
           | IVar IVar
           | IGet IExpr Index
               deriving (Show, Eq)

type IPrimOp = PrimOp BaseType IExpr ()
type IVal = IExpr  -- only ILit and IRef constructors
type IVar = VarP IType
data IType = IValType BaseType
           | IRefType ArrayType
              deriving (Show, Eq)

type ArrayType = (BaseType, [Size])

type Size  = IExpr
type Index = IExpr

-- === some handy monoids ===

data SetVal a = Set a | NotSet
newtype MonMap k v = MonMap (M.Map k v)  deriving (Show, Eq)

instance Semigroup (SetVal a) where
  x <> NotSet = x
  _ <> Set x  = Set x

instance Monoid (SetVal a) where
  mempty = NotSet

instance (Ord k, Semigroup v) => Semigroup (MonMap k v) where
  MonMap m <> MonMap m' = MonMap $ M.unionWith (<>) m m'

instance (Ord k, Semigroup v) => Monoid (MonMap k v) where
  mempty = MonMap mempty

monMapSingle :: k -> v -> MonMap k v
monMapSingle k v = MonMap (M.singleton k v)

monMapLookup :: (Monoid v, Ord k) => MonMap k v -> k -> v
monMapLookup (MonMap m) k = case M.lookup k m of Nothing -> mempty
                                                 Just v  -> v

-- === passes ===

data PassName = Parse | TypePass | NormPass | SimpPass | ImpPass | JitPass
              | Flops | LLVMOpt | AsmPass
                deriving (Ord, Eq, Bounded, Enum)

passNameMap :: M.Map String PassName
passNameMap = buildNameMap

parsePassName :: String -> Maybe PassName
parsePassName s = M.lookup s passNameMap

instance Show PassName where
  show p = case p of
    Parse    -> "parse" ; TypePass -> "typed"   ; NormPass -> "norm"
    SimpPass -> "simp"  ; ImpPass  -> "imp"     ; JitPass  -> "llvm"
    Flops    -> "flops" ; LLVMOpt  -> "llvmopt" ; AsmPass  -> "asm"

-- TODO: consider using this for builtins too
buildNameMap :: (Show a, Enum a, Bounded a) => M.Map String a
buildNameMap = M.fromList [(show x, x) | x <- [minBound..maxBound]]

-- === outputs ===

type LitProg = [(SourceBlock, Result)]
type SrcCtx = Maybe SrcPos
data Result = Result [Output] (Except ())  deriving (Show, Eq)

data Output = TextOut String
            | HeatmapOut Int Int [Double]
            | ScatterOut [Double] [Double]
            | PassInfo PassName String String
              deriving (Show, Eq, Generic)

data OutFormat = Printed | Heatmap | Scatter   deriving (Show, Eq, Generic)
data DataFormat = DexObject | DexBinaryObject  deriving (Show, Eq, Generic)

data Err = Err ErrType SrcCtx String  deriving (Show, Eq)
instance Exception Err

data ErrType = NoErr
             | ParseErr
             | TypeErr
             | KindErr
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
addContext s m = modifyErr m $ \(Err e p s') -> Err e p (s' ++ s)

addSrcContext :: MonadError Err m => SrcCtx -> m a -> m a
addSrcContext ctx m = modifyErr m updateErr
  where
    updateErr :: Err -> Err
    updateErr (Err e ctx' s) = case ctx' of Nothing -> Err e ctx  s
                                            Just _  -> Err e ctx' s

catchIOExcept :: (MonadIO m , MonadError Err m) => IO a -> m a
catchIOExcept m = do
  ans <- liftIO $ catch (liftM Right m) $ \e -> return (Left (e::Err))
  liftEither ans

-- === misc ===

infixr 1 -->
infixr 1 --@
infixr 2 ==>

(-->) :: Type -> Type -> Type
a --> b = ArrowType NonLin $ Pi a (noEffect, b)

(--@) :: Type -> Type -> Type
a --@ b = ArrowType Lin $ Pi a (noEffect, b)

(==>) :: Type -> Type -> Type
(==>) = TabType

data LorT a b = L a | T b  deriving (Show, Eq)

fromL :: LorT a b -> a
fromL (L x) = x
fromL _ = error "Not a let-bound thing"

fromT :: LorT a b -> b
fromT (T x) = x
fromT _ = error "Not a type-ish thing"

unitTy :: Type
unitTy = RecType (Tup [])

type FullEnv v t = Env (LorT v t)

-- === substitutions ===

type Vars = TypeEnv

lbind :: Var -> Vars
lbind v@(_:>ty) = v @> L ty

tbind :: TVar -> Vars
tbind v@(_:>k) = v @> T k

class HasVars a where
  freeVars :: a -> Vars

instance HasVars FExpr where
  freeVars expr = case expr of
    FDecl decl body -> freeVars decl <> (freeVars body `envDiff` fDeclBoundVars decl)
    FVar v@(_:>ty) -> v@>L ty <> freeVars ty
    FPrimExpr e  -> freeVars e
    Annot e ty   -> freeVars e <> freeVars ty
    SrcAnnot e _ -> freeVars e

fDeclBoundVars :: FDecl -> Vars
fDeclBoundVars decl = case decl of
  LetMono p _    -> foldMap lbind p
  LetPoly v _    -> lbind v
  FRuleDef _ _ _ -> mempty
  TyDef v _      -> tbind v

sourceBlockBoundVars :: SourceBlock -> Vars
sourceBlockBoundVars block = case sbContents block of
  RunModule (Module (_,vs) _) -> vs
  LoadData p _ _           -> foldMap lbind p
  _                        -> mempty

instance HasVars FLamExpr where
  freeVars (FLamExpr p body) =
    foldMap freeVars p <> (freeVars body `envDiff` foldMap lbind p)

instance HasVars Type where
  freeVars ty = case ty of
    ArrowType l p -> freeVars l <> freeVars p
    TypeVar v  -> tbind v
    Forall    tbs _ body -> freeVars body `envDiff` foldMap tbind tbs
    TypeAlias tbs   body -> freeVars body `envDiff` foldMap tbind tbs
    Dep (DeBruijn _:>_) -> mempty
    Dep v -> lbind v
    Effect row tailVar ->  foldMap freeVarsEffect (envPairs row)
                        <> foldMap freeVars tailVar
    _ -> execWriter $ flip traverseType ty $ \_ t -> t <$ tell (freeVars t)

freeVarsEffect :: (Name, (EffectName, Type)) -> Vars
freeVarsEffect (DeBruijn _, (_, ty)) =              freeVars ty
freeVarsEffect (v,          (_, ty)) = (v:>()) @> L ty <> freeVars ty

instance HasVars PiType where
  freeVars (Pi a (eff, b)) = freeVars a <> freeVars eff <> freeVars b

instance HasVars b => HasVars (VarP b) where
  freeVars (_ :> b) = freeVars b

instance HasVars () where
  freeVars () = mempty

instance HasVars FDecl where
   freeVars (LetMono p expr)   = foldMap freeVars p <> freeVars expr
   freeVars (LetPoly b tlam)   = freeVars b <> freeVars tlam
   freeVars (TyDef _ ty)       = freeVars ty
   freeVars (FRuleDef ann ty body) = freeVars ann <> freeVars ty <> freeVars body

instance HasVars RuleAnn where
  freeVars (LinearizationDef v) = (v:>()) @> L unitTy

instance HasVars FTLam where
  freeVars (FTLam tbs _ expr) = freeVars expr `envDiff` foldMap tbind tbs

instance (HasVars a, HasVars b) => HasVars (LorT a b) where
  freeVars (L x) = freeVars x
  freeVars (T x) = freeVars x

instance (HasVars a, HasVars b) => HasVars (a, b) where
  freeVars (x, y) = freeVars x <> freeVars y

instance HasVars SourceBlock where
  freeVars block = case sbContents block of
    RunModule (Module (vs, _) _)    -> vs
    Command _ (_, Module (vs, _) _) -> vs
    GetNameType v                   -> v @> L (varAnn v)
    _ -> mempty

instance HasVars Expr where
  freeVars expr = case expr of
    Decl decl body -> freeVars decl <> (freeVars body `envDiff` declBoundVars decl)
    CExpr primop   -> freeVars primop
    Atom atom      -> freeVars atom

declBoundVars :: Decl -> Env ()
declBoundVars (Let b _) = b@>()

instance HasVars LamExpr where
  freeVars (LamExpr b body) = freeVars b <> (freeVars body `envDiff` (b@>()))

instance HasVars Atom where
  freeVars atom = case atom of
    Var v@(_:>ty) -> v @> L ty <> freeVars ty
    TLam tvs _ body -> freeVars body `envDiff` foldMap (@>()) tvs
    Con con   -> freeVars con

instance HasVars Kind where
  freeVars _ = mempty

instance HasVars Decl where
  freeVars (Let bs expr) = foldMap freeVars bs <> freeVars expr

instance HasVars a => HasVars (Env a) where
  freeVars env = foldMap freeVars env

instance HasVars TopEnv where
  freeVars (TopEnv e1 e2 e3) = freeVars e1 <> freeVars e2 <> freeVars e3

instance (HasVars a, HasVars b) => HasVars (Either a b)where
  freeVars (Left  x) = freeVars x
  freeVars (Right x) = freeVars x

instance HasVars ModBody where
  freeVars (ModBody (decl:decls) results) =
    freeVars decl <> (freeVars (ModBody decls results) `envDiff` declBoundVars decl)
  freeVars (ModBody [] results) = freeVars results

fmapExpr :: TraversableExpr expr
         => expr ty e lam
         -> (ty  -> ty')
         -> (e   -> e')
         -> (lam -> lam')
         -> expr ty' e' lam'
fmapExpr e fT fE fL =
  runIdentity $ traverseExpr e (return . fT) (return . fE) (return . fL)

class TraversableExpr expr where
  traverseExpr :: Applicative f
               => expr ty e lam
               -> (ty  -> f ty')
               -> (e   -> f e')
               -> (lam -> f lam')
               -> f (expr ty' e' lam')

instance TraversableExpr PrimExpr where
  traverseExpr (OpExpr  e) fT fE fL = liftA OpExpr  $ traverseExpr e fT fE fL
  traverseExpr (ConExpr e) fT fE fL = liftA ConExpr $ traverseExpr e fT fE fL

instance TraversableExpr PrimOp where
  traverseExpr primop fT fE fL = case primop of
    App l d e1 e2        -> liftA4 App (fT l) (fT d) (fE e1) (fE e2)
    TApp e tys           -> liftA2 TApp (fE e) (traverse fT tys)
    For lam              -> liftA  For (fL lam)
    TabCon n ty xs       -> liftA3 TabCon (fT n) (fT ty) (traverse fE xs)
    TabGet e i           -> liftA2 TabGet (fE e) (fE i)
    RecGet e i           -> liftA2 RecGet (fE e) (pure i)
    ArrayGep e i         -> liftA2 ArrayGep (fE e) (fE i)
    LoadScalar e         -> liftA  LoadScalar (fE e)
    ScalarBinOp op e1 e2 -> liftA2 (ScalarBinOp op) (fE e1) (fE e2)
    ScalarUnOp  op e     -> liftA  (ScalarUnOp  op) (fE e)
    VSpaceOp ty VZero    -> liftA2 VSpaceOp (fT ty) (pure VZero)
    VSpaceOp ty (VAdd e1 e2) -> liftA2 VSpaceOp (fT ty) (liftA2 VAdd (fE e1) (fE e2))
    Cmp op ty e1 e2      -> liftA3 (Cmp op) (fT ty) (fE e1) (fE e2)
    Select ty p x y      -> liftA3 Select (fT ty) (fE p) (fE x) <*> fE y
    PrimEffect d ref m   -> liftA3 PrimEffect (fT d) (fE ref) $ case m of
       MAsk    -> pure  MAsk
       MTell e -> liftA MTell (fE e)
       MGet    -> pure  MGet
       MPut  e -> liftA MPut  (fE e)
    RunReader r  lam    -> liftA2 RunReader (fE r ) (fL lam)
    RunWriter    lam    -> liftA  RunWriter         (fL lam)
    RunState  s  lam    -> liftA2 RunState  (fE s ) (fL lam)
    IndexEff eff d ref i lam -> liftA4 (IndexEff eff) (fT d) (fE ref) (fE i) (fL lam)
    Linearize lam        -> liftA  Linearize (fL lam)
    Transpose lam        -> liftA  Transpose (fL lam)
    IntAsIndex ty e      -> liftA2 IntAsIndex (fT ty) (fE e)
    IdxSetSize ty        -> liftA  IdxSetSize (fT ty)
    NewtypeCast ty e     -> liftA2 NewtypeCast (fT ty) (fE e)
    FFICall s argTys ansTy args ->
      liftA3 (FFICall s) (traverse fT argTys) (fT ansTy) (traverse fE args)

instance TraversableExpr PrimCon where
  traverseExpr op fT fE fL = case op of
    Lit l       -> pure   (Lit l)
    Lam lin eff lam -> liftA3 Lam (fT lin) (fT eff) (fL lam)
    AFor n e    -> liftA2 AFor (fT n) (fE e)
    AGet e      -> liftA  AGet (fE e)
    AsIdx n e   -> liftA2 AsIdx (fT n) (fE e)
    RecCon r    -> liftA  RecCon (traverse fE r)
    Todo ty             -> liftA  Todo (fT ty)
    ArrayRef ref        -> pure $ ArrayRef ref

instance (TraversableExpr expr, HasVars ty, HasVars e, HasVars lam)
         => HasVars (expr ty e lam) where
  freeVars expr = execWriter $
    traverseExpr expr (tell . freeVars) (tell . freeVars) (tell . freeVars)

liftA4 :: Applicative f => (a -> b -> c -> d -> e) -> f a -> f b -> f c -> f d -> f e
liftA4 f a b c d = f <$> a <*> b <*> c <*> d

unzipExpr :: TraversableExpr expr
          => expr ty e lam -> (expr () () (), ([ty], [e], [lam]))
unzipExpr expr = (blankExpr, xs)
  where
    blankExpr = fmapExpr expr (const ()) (const ()) (const ())
    xs = execWriter $ traverseExpr expr
            (\ty  -> tell ([ty], [] , []   ))
            (\e   -> tell ([]  , [e], []   ))
            (\lam -> tell ([]  , [] , [lam]))

instance RecTreeZip Type where
  recTreeZip (RecTree r) (RecType r') = RecTree $ recZipWith recTreeZip r r'
  recTreeZip (RecLeaf x) x' = RecLeaf (x, x')
  recTreeZip (RecTree _) _ = error "Bad zip"

instance Semigroup TopEnv where
  TopEnv e1 e2 e3 <> TopEnv e1' e2' e3' = TopEnv (e1 <> e1') (e2 <> e2') (e3 <> e3')

instance Monoid TopEnv where
  mempty = TopEnv mempty mempty mempty

instance Eq SourceBlock where
  x == y = sbText x == sbText y

instance Ord SourceBlock where
  compare x y = compare (sbText x) (sbText y)

instance Functor PrimEffect where
  fmap = fmapDefault

instance Foldable PrimEffect where
  foldMap = foldMapDefault

instance Traversable PrimEffect where
  traverse f prim = case prim of
    MAsk    -> pure  MAsk
    MTell x -> liftA MTell (f x)
    MGet    -> pure  MGet
    MPut  x -> liftA MPut (f x)

traverseType :: Applicative m => (Kind -> Type -> m Type) -> Type -> m Type
traverseType f ty = case ty of
  BaseType _           -> pure ty
  IdxSetLit _          -> pure ty
  Range a b            -> liftA2 Range (f DepKind a) (f DepKind b)
  TabType a b          -> liftA2 TabType (f TyKind a) (f TyKind b)
  ArrayType _ _        -> pure ty
  RecType r            -> liftA RecType $ traverse (f TyKind) r
  Ref t                -> liftA Ref (f TyKind t)
  TypeApp t xs         -> liftA2 TypeApp (f TyKind t) (traverse (f TyKind) xs)
  DepLit n             -> pure (DepLit n)
  NoDep                -> pure NoDep
  Lin                  -> pure Lin
  NonLin               -> pure NonLin
  NoAnn                -> pure NoAnn
  _ -> error $ "Shouldn't be handled generically: " ++ show ty

makePi :: Var -> EffectiveType -> PiType
makePi (v:>a) (eff, b) = Pi a ( abstractType v 0 eff
                              , abstractType v 0 b)

applyPi :: PiType -> Type -> EffectiveType
applyPi (Pi _ (eff, b)) (Dep (v:>_)) = ( instantiateType 0 v eff
                                       , instantiateType 0 v b)
applyPi (Pi _ b) _ = b

instantiateType :: Int -> Name -> Type -> Type
instantiateType d name ty = case ty of
 Dep (v:>ann) -> Dep $ lookupDBVar v :> recur ann
 TypeVar _ -> ty
 ArrowType m (Pi a (e, b)) -> ArrowType (recur m) $
   Pi (recur a) (instantiateType (d+1) name e, instantiateType (d+1) name b)
 Forall tbs cs body -> Forall tbs cs $ recur body
 Effect row tailVar -> Effect row' tailVar
   where row' = fold [ (lookupDBVar v :>()) @> (eff, recur ann)
                     | (v, (eff, ann)) <- envPairs row]
 _ -> runIdentity $ flip traverseType ty $ (const (return . recur))
 where
   recur ::Type -> Type
   recur = instantiateType d name

   lookupDBVar :: Name -> Name
   lookupDBVar v = case v of DeBruijn i | i == d -> name
                             _                   -> v

abstractType :: Name -> Int -> Type -> Type
abstractType v d ty = case ty of
  Dep (v':>ann) -> Dep (substWithDBVar v' :> recur ann)
  TypeVar _ -> ty
  ArrowType m (Pi a (e, b)) -> ArrowType (recur m) $
    Pi (recur a) (abstractType v (d+1) e, abstractType v (d+1) b)
  Forall tbs cs body -> Forall tbs cs $ recur body
  Effect row tailVar -> Effect row' tailVar
    where row' = fold [ (substWithDBVar v' :>()) @> (eff, recur ann)
                     | (v', (eff, ann)) <- envPairs row]
  _ -> runIdentity $ flip traverseType ty $ (const (return . recur))
  where
    recur ::Type -> Type
    recur = abstractType v d

    substWithDBVar :: Name -> Name
    substWithDBVar v' | v == v'   = DeBruijn d
                      | otherwise = v'
