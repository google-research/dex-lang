-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE PatternSynonyms #-}

module Syntax (
    Type, Kind, BaseType (..), Effects, Effect, EffectName (..),
    ClassName (..), TyQual (..), SrcPos, Var, Binder, Block (..), Decl (..),
    Expr (..), Atom (..), ArrowP (..), Arrow, PrimTC (..), PrimEff (..), Abs (..),
    PrimExpr (..), PrimCon (..), LitVal (..), PrimEffect (..), PrimOp (..),
    PrimHof (..), LamExpr, PiType, WithSrc (..), srcPos,
    ScalarBinOp (..), ScalarUnOp (..), CmpOp (..), SourceBlock (..),
    ReachedEOF, SourceBlock' (..), TypeEnv, SubstEnv, Scope, RuleEnv,
    CmdName (..), Val, TopInfEnv, TopSimpEnv, TopEnv (..), Op, Con, Hof, TC, Eff,
    Module (..), ImpFunction (..),
    ImpProg (..), ImpStatement, ImpInstr (..), IExpr (..), IVal, IPrimOp,
    IVar, IType (..), ArrayType, IArrayType, SetVal (..), MonMap (..), LitProg,
    SrcCtx, Result (..), Output (..), OutFormat (..), DataFormat (..),
    Err (..), ErrType (..), Except, throw, throwIf, modifyErr, addContext,
    addSrcContext, catchIOExcept, liftEitherIO, (-->), (--@), (==>),
    sourceBlockBoundVars, PassName (..), parsePassName,
    freeVars, freeUVars, HasVars, strToName, nameToStr, showPrimName, Vars,
    monMapSingle, monMapLookup, newEnv, Direction (..), ArrayRef, Array, Limit (..),
    UExpr, UExpr' (..), UType, UEffects (..), UBinder, UPiBinder, UVar,
    UPat, UPat', PatP, PatP' (..), UModule (..), UDecl (..), ULamArrow, UPiArrow, arrowEff,
    subst, deShadow, scopelessSubst, absArgType, applyAbs, makeAbs, freshSkolemVar,
    pattern IntVal, pattern UnitTy, pattern PairTy, pattern TupTy,
    pattern FixedIntRange, pattern RefTy, pattern BoolTy, pattern IntTy, pattern RealTy,
    pattern RecTy, pattern SumTy, pattern ArrayTy, pattern BaseTy, pattern UnitVal,
    pattern PairVal, pattern TupVal, pattern RecVal, pattern SumVal, pattern PureArrow,
    pattern RealVal, pattern BoolVal, pattern TyKind, pattern TabTy, isTabTy,
    pattern Pure, pattern BinaryFunTy, pattern BinaryFunVal, pattern UPure)
  where

import qualified Data.Map.Strict as M
import Control.Exception hiding (throw)
import Control.Monad.Fail
import Control.Monad.Identity
import Control.Monad.Writer
import Control.Monad.Except hiding (Except)
import qualified Data.Vector.Unboxed as V
import Data.Foldable (fold)
import Data.Tuple (swap)
import GHC.Generics

import Cat
import Record
import Env
import Array

-- === core IR ===

data Atom = Var Var
          | Lam LamExpr
          | Pi  PiType
          | Con Con
          | TC  TC
          | Eff Eff
            deriving (Show, Eq, Generic)

data Expr = App Atom Atom
          | Atom Atom
          | Op  Op
          | Hof Hof
            deriving (Show, Eq, Generic)

data Decl  = Let Binder Expr    deriving (Show, Eq, Generic)
data Block = Block [Decl] Expr  deriving (Show, Eq, Generic)

type Var    = VarP Type
type Binder = VarP Type

data Abs a = Abs Binder a  deriving (Show, Generic)
type LamExpr = Abs (Arrow, Block)
type PiType  = Abs (Arrow, Type)

type Arrow = ArrowP Effects
data ArrowP eff = PlainArrow eff
                | ImplicitArrow
                | TabArrow
                | LinArrow
                  deriving (Show, Eq, Generic, Functor, Foldable, Traversable)

type Val  = Atom
type Type = Atom
type Kind = Type
type Effects = Atom

type TC  = PrimTC  Atom
type Con = PrimCon Atom
type Op  = PrimOp  Atom
type Eff = PrimEff Atom
type Hof = PrimHof Atom

data TopEnv = TopEnv TopInfEnv TopSimpEnv RuleEnv
              deriving (Show, Eq, Generic)

type TypeEnv    = Env Type
type TopInfEnv  = (TypeEnv, Env Type)
type TopSimpEnv = SubstEnv
type RuleEnv    = Env Atom

data Module = Module (Maybe BlockId) [Var] [Var] Block  deriving (Show, Eq)

-- === front-end language AST ===

type UExpr = WithSrc UExpr'
data UExpr' = UVar UVar
            | ULam UBinder   ULamArrow UExpr
            | UPi  UPiBinder UPiArrow  UType
            | UApp ULamArrow UExpr UExpr
            | UDecl UDecl UExpr
            | UFor Direction UBinder UExpr
            | UTabCon [UExpr] (Maybe UExpr)
            | UPrimExpr (PrimExpr Name)
              deriving (Show, Eq, Generic)

data UDecl = ULet UBinder UExpr  deriving (Show, Eq, Generic)

type UType = UExpr
type ULamArrow = ArrowP ()
type UPiArrow  = ArrowP UEffects
type UVar      = VarP ()

type UPat    = PatP  UVar
type UPat'   = PatP' UVar
type UBinder   = (UPat, Maybe UType)
type UPiBinder = (UPat, UType)

data UEffects = UEffects [(EffectName, UExpr)] (Maybe UExpr)  deriving (Show, Eq)
data UModule = UModule [Name] [Name] [UDecl]  deriving (Show, Eq)
type SrcPos = (Int, Int)

type PatP  a = WithSrc (PatP' a)
data PatP' a = PatBind a
             | PatPair (PatP a) (PatP a)
             | PatUnit  deriving (Show, Eq, Functor, Foldable, Traversable)

data WithSrc a = WithSrc SrcPos a
                 deriving (Show, Eq, Functor, Foldable, Traversable)

srcPos :: WithSrc a -> SrcPos
srcPos (WithSrc pos _) = pos

-- === primitive constructors and operators ===

data PrimExpr e =
        TCExpr  (PrimTC  e)
      | EffExpr (PrimEff e)
      | ConExpr (PrimCon e)
      | OpExpr  (PrimOp  e)
      | HofExpr (PrimHof e)
        deriving (Show, Eq, Generic, Functor, Foldable, Traversable)

data PrimTC e =
        BaseType BaseType
      | IntRange e e
      | IndexRange e (Limit e) (Limit e)
      | ArrayType ArrayType
      | PairType e e
      | UnitType
      | RecType (Record e)
      | SumType (e, e)
      | RefType e e
      | TypeKind
      | EffectsKind
        deriving (Show, Eq, Generic, Functor, Foldable, Traversable)

data PrimEff e = PureEff | ExtendEff (Effect e) e
                 deriving (Show, Eq, Generic, Functor, Foldable, Traversable)
type Effect e = (EffectName, e)
data EffectName = Reader | Writer | State  deriving (Show, Eq, Generic)

data PrimCon e =
        Lit LitVal
      | ArrayLit Array
      | AnyValue e        -- Produces an arbitrary value of a given type
      | SumCon e e e      -- (bool constructor tag (True is Left), left value, right value)
      | PairCon e e
      | UnitCon
      | RefCon e e
      | RecCon (Record e)
      | AsIdx e e         -- Construct an index from its ordinal index (zero-based int)
      | AFor e e
      | AGet e
      | Todo e
        deriving (Show, Eq, Generic, Functor, Foldable, Traversable)

data PrimOp e =
        RecGet e RecField
      | Fst e | Snd e
      | SumGet e Bool
      | SumTag e
      | ArrayGep e e
      | LoadScalar e
      | TabCon e [e]                 -- table type, element type, elements
      | ScalarBinOp ScalarBinOp e e
      | ScalarUnOp ScalarUnOp e
      | Select e e e                 -- predicate, val-if-true, val-if-false
      | PrimEffect e (PrimEffect e)
      | FFICall String BaseType [e]
      | Inject e
      -- Typeclass operations
      -- Eq and Ord (should get eliminated during simplification)
      | Cmp CmpOp e e e  -- type, left, right
      -- Idx (survives simplification, because we allow it to be backend-dependent)
      | IntAsIndex e e   -- index set, ordinal index
      | IndexAsInt e
      | IdxSetSize e
        deriving (Show, Eq, Generic, Functor, Foldable, Traversable)

data PrimHof e =
        For Direction e
      | SumCase e e e
      | RunReader e e
      | RunWriter e
      | RunState  e e
      | Linearize e
      | Transpose e
        deriving (Show, Eq, Generic, Functor, Foldable, Traversable)

data PrimEffect e = MAsk | MTell e | MGet | MPut e
    deriving (Show, Eq, Generic, Functor, Foldable, Traversable)

data ScalarBinOp = IAdd | ISub | IMul | IDiv | ICmp CmpOp
                 | FAdd | FSub | FMul | FDiv | FCmp CmpOp | Pow
                 | And | Or | Rem
                   deriving (Show, Eq, Generic)

data ScalarUnOp = Not | FNeg | IntToReal | BoolToInt | UnsafeIntToBool
                  deriving (Show, Eq, Generic)

data CmpOp = Less | Greater | Equal | LessEqual | GreaterEqual
             deriving (Show, Eq, Generic)

data Direction = Fwd | Rev  deriving (Show, Eq, Generic)

data Limit a = InclusiveLim a
             | ExclusiveLim a
             | Unlimited
               deriving (Show, Eq, Generic, Functor, Foldable, Traversable)

data ClassName = Data | VSpace | IdxSet | Eq | Ord deriving (Show, Eq, Generic)

data TyQual = TyQual Var ClassName  deriving (Show, Eq, Generic)

type PrimName = PrimExpr ()

strToName :: String -> Maybe PrimName
strToName s = M.lookup s builtinNames

nameToStr :: PrimName -> String
nameToStr prim = case lookup prim $ map swap $ M.toList builtinNames of
  Just s  -> s
  Nothing -> show prim

showPrimName :: PrimExpr e -> String
showPrimName prim = nameToStr $ fmap (const ()) prim

-- === top-level constructs ===

data SourceBlock = SourceBlock
  { sbLine     :: Int
  , sbOffset   :: Int
  , sbText     :: String
  , sbContents :: SourceBlock'
  , sbId       :: Maybe BlockId }  deriving (Show)

type BlockId = Int
type ReachedEOF = Bool
data SourceBlock' = RunModule UModule
                  | Command CmdName (Name, UModule)
                  | GetNameType Var
                  | IncludeSourceFile String
                  | LoadData UBinder DataFormat String
                  | ProseBlock String
                  | CommentLine
                  | EmptyLines
                  | UnParseable ReachedEOF String
                    deriving (Show, Eq, Generic)

data CmdName = GetType | ShowPasses | ShowPass PassName
             | TimeIt | EvalExpr OutFormat | Dump DataFormat String
                deriving  (Show, Eq, Generic)

-- === imperative IR ===

-- TODO: add args
data ImpFunction = ImpFunction [IVar] [IVar] ImpProg  -- destinations first
                   deriving (Show, Eq)
newtype ImpProg = ImpProg [ImpStatement]
                  deriving (Show, Eq, Generic, Semigroup, Monoid)
type ImpStatement = (Maybe IVar, ImpInstr)

data ImpInstr = Load  IExpr
              | Store IExpr IExpr  -- destination first
              | Copy  IExpr IExpr  -- destination first
              | Alloc IArrayType
              | Free IVar
              | IGet IExpr Index
              | Loop Direction IVar Size ImpProg
              | IPrimOp IPrimOp
                deriving (Show, Eq)

data IExpr = ILit LitVal
           | IVar IVar
             deriving (Show, Eq)

type IPrimOp = PrimOp IExpr
type IVal = IExpr  -- only ILit and IRef constructors
type IVar = VarP IType
data IType = IValType BaseType
           | IRefType IArrayType
              deriving (Show, Eq)

type IArrayType = (BaseType, [Size])

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
              | Flops | LLVMOpt | AsmPass | JAXPass | JAXSimpPass | LLVMEval
              | JaxprAndHLO
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
    JAXPass  -> "jax"   ; JAXSimpPass -> "jsimp";
    LLVMEval -> "llvmeval" ; JaxprAndHLO -> "jaxprhlo";

-- TODO: consider using this for builtins too
buildNameMap :: (Show a, Enum a, Bounded a) => M.Map String a
buildNameMap = M.fromList [(show x, x) | x <- [minBound..maxBound]]

-- === outputs ===

type LitProg = [(SourceBlock, Result)]
type SrcCtx = Maybe SrcPos
data Result = Result [Output] (Except ())  deriving (Show, Eq)

data Output = TextOut String
            | HeatmapOut Int Int (V.Vector Double)
            | ScatterOut (V.Vector Double) (V.Vector Double)
            | PassInfo PassName String
            | MiscLog String
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

type Except = Either Err

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
catchIOExcept m = (liftIO >=> liftEither) $ (liftM Right m) `catches`
  [ Handler $ \(e::Err)           -> return $ Left e
  , Handler $ \(e::IOError)       -> return $ Left $ Err DataIOErr   Nothing $ show e
  , Handler $ \(e::SomeException) -> return $ Left $ Err CompilerErr Nothing $ show e
  ]

liftEitherIO :: (Exception e, MonadIO m) => Either e a -> m a
liftEitherIO (Left err) = liftIO $ throwIO err
liftEitherIO (Right x ) = return x

instance MonadFail (Either Err) where
  fail s = Left $ Err CompilerErr Nothing s

-- === UExpr free variables ===

type UVars = Env ()

class HasUVars a where
  freeUVars :: a -> UVars

instance HasUVars a => HasUVars (WithSrc a) where
  freeUVars (WithSrc _ e) = freeUVars e

instance HasUVars UExpr' where
  freeUVars expr = case expr of
    UVar v -> v@>()
    ULam b _ body -> uAbsFreeVars b body
    UPi (WithSrc _ pat, argTy) arr ty ->
      freeUVars argTy <>
      ((freeUVars arr <> freeUVars ty) `envDiff` foldMap (@>()) pat)
    -- TODO: maybe distinguish table arrow application
    -- (otherwise `x.i` and `x i` are the same)
    UApp _ f x -> freeUVars f <> freeUVars x
    UDecl (ULet b rhs) body -> freeUVars rhs <> uAbsFreeVars b body
    UFor _ b body -> uAbsFreeVars b body
    UTabCon xs n -> foldMap freeUVars xs <> foldMap freeUVars n
    UPrimExpr _ -> mempty

instance HasUVars UDecl where
  freeUVars (ULet p expr) = uBinderFreeVars p <> freeUVars expr

instance HasUVars SourceBlock where
  freeUVars block = case sbContents block of
    RunModule (   UModule vs _ _) -> foldMap nameAsEnv vs
    Command _ (_, UModule vs _ _) -> foldMap nameAsEnv vs
    GetNameType v                 -> v @> ()
    _ -> mempty

instance HasUVars UEffects where
  freeUVars (UEffects effs tailVar) =
    foldMap (freeUVars . snd) effs <> foldMap freeUVars tailVar

instance HasUVars eff => HasUVars (ArrowP eff) where
  freeUVars (PlainArrow eff) = freeUVars eff
  freeUVars _ = mempty

uAbsFreeVars :: UBinder -> UExpr -> UVars
uAbsFreeVars (WithSrc _ pat, ann) body =
  foldMap freeUVars ann <> (freeUVars body `envDiff` foldMap (@>()) pat)

uBinderFreeVars :: UBinder -> UVars
uBinderFreeVars (_, ann) = foldMap freeUVars ann

sourceBlockBoundVars :: SourceBlock -> UVars
sourceBlockBoundVars block = case sbContents block of
  RunModule (UModule _ vs _)    -> foldMap nameAsEnv vs
  LoadData (WithSrc _ p, _) _ _ -> foldMap (@>()) p
  _                             -> mempty

nameAsEnv :: Name -> UVars
nameAsEnv v = (v:>())@>()

-- === Expr free variables and substitutions ===

type Vars = TypeEnv
type SubstEnv = Env Atom
type Scope    = Env (Maybe Expr)
type ScopedSubstEnv = (SubstEnv, Scope)

scopelessSubst :: HasVars a => SubstEnv -> a -> a
scopelessSubst env x = subst (env, scope) x
  where scope = fmap (const Nothing) $
          foldMap freeVars env <> (freeVars x `envDiff` env)

class HasVars a where
  freeVars :: a -> Vars
  subst :: ScopedSubstEnv -> a -> a

instance (HasVars a, Eq a) => Eq (Abs a) where
  Abs (NoName:>a) b == Abs (NoName:>a') b' = a == a' && b == b'
  ab@(Abs (_:>a) _) == ab'@(Abs (_:>a') _) =
    a == a' && applyAbs ab v == applyAbs ab' v
    where v = Var $ freshSkolemVar (ab, ab') a

freshSkolemVar :: HasVars a => a -> Type -> Var
freshSkolemVar x ty = rename (rawName Skolem "x" :> ty) (freeVars x)

-- NOTE: We don't have an instance for VarP, because it's used to represent
--       both binders and regular variables, but each requires different treatment
freeBinderTypeVars :: Var -> Vars
freeBinderTypeVars (_ :> t) = freeVars t

applyAbs :: HasVars a => Abs a -> Atom -> a
applyAbs (Abs v body) x = scopelessSubst (v@>x) body

makeAbs :: HasVars a => Var -> a -> Abs a
makeAbs v body | v `isin` freeVars body = Abs v body
               | otherwise              = Abs (NoName:> varAnn v) body

absArgType :: Abs a -> Type
absArgType (Abs (_:>ty) _) = ty

varFreeVars :: Var -> Vars
varFreeVars v@(_ :> t) = bind v <> freeVars t

bind :: VarP a -> Env a
bind v@(_:>ty) = v @> ty

newEnv :: [VarP ann] -> [a] -> Env a
newEnv vs xs = fold $ zipWith (@>) vs xs

instance HasVars Arrow where
  freeVars arrow = case arrow of
    PlainArrow eff -> freeVars eff
    _ -> mempty

  subst env arrow = case arrow of
    PlainArrow eff -> PlainArrow $ subst env eff
    _ -> arrow

arrowEff :: Arrow -> Effects
arrowEff (PlainArrow eff) = eff
arrowEff _ = Pure

substVar :: (SubstEnv, Scope) -> Var -> Atom
substVar env@(sub, scope) v = case envLookup sub v of
  Nothing -> Var $ fmap (subst env) v
  Just x' -> deShadow x' scope

deShadow :: HasVars a => a -> Scope -> a
deShadow x scope = subst (mempty, scope) x

instance HasVars Expr where
  freeVars expr = case expr of
    App f x -> freeVars f <> freeVars x
    Atom x  -> freeVars x
    Op  e   -> foldMap freeVars e
    Hof e   -> foldMap freeVars e

  subst env expr = case expr of
    App f x -> App (subst env f) (subst env x)
    Atom x  -> Atom $ subst env x
    Op  e   -> Op  $ fmap (subst env) e
    Hof e   -> Hof $ fmap (subst env) e

instance HasVars Decl where
  freeVars (Let bs expr) = foldMap freeVars bs <> freeVars expr
  subst env (Let (v:>ty) bound) = Let (v:> subst env ty) (subst env bound)

instance HasVars Block where
  freeVars (Block [] result) = freeVars result
  freeVars (Block (decl@(Let b _):decls) result) =
    freeVars decl <> (freeVars body `envDiff` (b@>()))
    where body = Block decls result

  subst env (Block decls result) = do
    let (decls', env') = catMap substDecl env decls
    let result' = subst (env <> env') result
    Block decls' result'

instance HasVars Atom where
  freeVars atom = case atom of
    Var v   -> varFreeVars v
    Lam lam -> freeVars lam
    Pi  ty  -> freeVars ty
    Con con -> foldMap freeVars con
    TC  tc  -> foldMap freeVars tc
    Eff eff -> foldMap freeVars eff

  subst env atom = case atom of
    Var v   -> substVar env v
    Lam lam -> Lam $ subst env lam
    Pi  ty  -> Pi  $ subst env ty
    TC  tc  -> TC  $ fmap (subst env) tc
    Con con -> Con $ fmap (subst env) con
    Eff eff -> Eff $ fmap (subst env) eff

instance HasVars a => HasVars (Abs a) where
  freeVars (Abs b body) =
    freeBinderTypeVars b <> (freeVars body `envDiff` (b@>()))

  subst env (Abs (v:>ty) body) = Abs b body'
    where (b, env') = refreshBinder env (v:> subst env ty)
          body' = subst (env <> env') body

substDecl :: ScopedSubstEnv -> Decl -> (Decl, ScopedSubstEnv)
substDecl env (Let (v:>ty) bound) = (Let b (subst env bound), env')
  where (b, env') = refreshBinder env (v:> subst env ty)

refreshBinder :: ScopedSubstEnv -> Var -> (Var, ScopedSubstEnv)
refreshBinder (_, scope) b = (b', env')
  where b' = rename b scope
        env' = (b@>Var b', b'@>Nothing)

instance HasVars TopEnv where
  freeVars (TopEnv e1 e2 e3) = freeVars e1 <> freeVars e2 <> freeVars e3
  subst = error "not implemented"

instance HasVars () where
  freeVars () = mempty
  subst _ () = ()

instance (HasVars a, HasVars b) => HasVars (a, b) where
  freeVars (x, y) = freeVars x <> freeVars y
  subst env (x, y) = (subst env x, subst env y)

instance (HasVars a, HasVars b) => HasVars (Either a b)where
  freeVars (Left  x) = freeVars x
  freeVars (Right x) = freeVars x
  subst = error "not implemented"

instance HasVars a => HasVars (Env a) where
  freeVars x = foldMap freeVars x
  subst env x = fmap (subst env) x

instance HasVars a => HasVars (RecTree a) where
  freeVars x = foldMap freeVars x
  subst env x = fmap (subst env) x

instance HasVars a => HasVars [a] where
  freeVars x = foldMap freeVars x
  subst env x = fmap (subst env) x

instance RecTreeZip Type where
  recTreeZip (RecTree r) (TC (RecType r')) = RecTree $ recZipWith recTreeZip r r'
  recTreeZip (RecLeaf x) x' = RecLeaf (x, x')
  recTreeZip (RecTree _) _ = error "Bad zip"

instance Semigroup TopEnv where
  TopEnv e1 e2 e3 <> TopEnv e1' e2' e3'=
    TopEnv (e1 <> e1') (e2 <> e2') (e3 <> e3')

instance Monoid TopEnv where
  mempty = TopEnv mempty mempty mempty

instance Eq SourceBlock where
  x == y = sbText x == sbText y

instance Ord SourceBlock where
  compare x y = compare (sbText x) (sbText y)

-- === Synonyms ===

infixr 1 -->
infixr 1 --@
infixr 2 ==>

(-->) :: Type -> Type -> Type
a --> b = Pi (Abs (NoName:>a) (PureArrow, b))

(--@) :: Type -> Type -> Type
a --@ b = Pi (Abs (NoName:>a) (LinArrow, b))

(==>) :: Type -> Type -> Type
a ==> b = Pi (Abs (NoName:>a) (TabArrow, b))

pattern IntVal :: Int -> Atom
pattern IntVal x = Con (Lit (IntLit x))

pattern RealVal :: Double -> Atom
pattern RealVal x = Con (Lit (RealLit x))

pattern BoolVal :: Bool -> Atom
pattern BoolVal x = Con (Lit (BoolLit x))

pattern RecVal :: Record Atom -> Atom
pattern RecVal r = Con (RecCon r)

pattern SumVal :: Atom -> Atom -> Atom -> Atom
pattern SumVal t l r = Con (SumCon t l r)

pattern TupVal :: [Atom] -> Atom
pattern TupVal xs = RecVal (Tup xs)

pattern PairVal :: Atom -> Atom -> Atom
pattern PairVal x y = Con (PairCon x y)

pattern PairTy :: Type -> Type -> Type
pattern PairTy x y = TC (PairType x y)

pattern TupTy :: [Type] -> Type
pattern TupTy xs = TC (RecType (Tup xs))

pattern UnitVal :: Atom
pattern UnitVal = Con UnitCon

pattern UnitTy :: Type
pattern UnitTy = TC UnitType

pattern ArrayTy :: [Int] -> BaseType -> Type
pattern ArrayTy shape b = TC (ArrayType (shape, b))

pattern BaseTy :: BaseType -> Type
pattern BaseTy b = TC (BaseType b)

pattern RecTy :: Record Type -> Type
pattern RecTy a = TC (RecType a)

pattern SumTy :: Type -> Type -> Type
pattern SumTy l r = TC (SumType (l, r))

pattern RefTy :: Atom -> Type -> Type
pattern RefTy r a = TC (RefType r a)

pattern IntTy :: Type
pattern IntTy = TC (BaseType IntType)

pattern BoolTy :: Type
pattern BoolTy = TC (BaseType BoolType)

pattern RealTy :: Type
pattern RealTy = TC (BaseType RealType)

pattern TyKind :: Kind
pattern TyKind = TC TypeKind

pattern FixedIntRange :: Int -> Int -> Type
pattern FixedIntRange low high = TC (IntRange (IntVal low) (IntVal high))

pattern Pure :: Effects
pattern Pure = Eff PureEff

pattern PureArrow :: Arrow
pattern PureArrow = PlainArrow Pure

pattern UPure :: UEffects
pattern UPure = UEffects [] Nothing

pattern TabTy :: Type -> Type -> Type
pattern TabTy xs i = Pi (Abs (NoName:>xs) (TabArrow, i))

isTabTy :: Type -> Bool
isTabTy (TabTy _ _) = True
isTabTy _ = False

pattern BinaryFunTy :: Binder -> Binder -> Effects -> Type -> Type
pattern BinaryFunTy b1 b2 eff bodyTy =
          Pi (Abs b1 (PureArrow,
          Pi (Abs b2 (PlainArrow eff, bodyTy))))

pattern BinaryFunVal :: Binder -> Binder -> Effects -> Block -> Type
pattern BinaryFunVal b1 b2 eff body =
          Lam (Abs b1 (PureArrow, Block [] (Atom (
          Lam (Abs b2 (PlainArrow eff, body))))))

-- TODO: Enable once https://gitlab.haskell.org//ghc/ghc/issues/13363 is fixed...
-- {-# COMPLETE TypeVar, ArrowType, TabTy, Forall, TypeAlias, Effect, NoAnn, TC #-}

-- TODO: Can we derive these generically? Or use Show/Read?
--       (These prelude-only names don't have to be pretty.)
builtinNames :: M.Map String PrimName
builtinNames = M.fromList
  [ ("iadd", binOp IAdd), ("isub", binOp ISub)
  , ("imul", binOp IMul), ("fdiv", binOp FDiv)
  , ("fadd", binOp FAdd), ("fsub", binOp FSub)
  , ("fmul", binOp FMul), ("idiv", binOp IDiv)
  , ("pow" , binOp Pow ), ("rem" , binOp Rem )
  , ("and" , binOp And ), ("or"  , binOp Or  ), ("not" , unOp  Not )
  , ("fneg", unOp  FNeg)
  , ("True" , ConExpr $ Lit $ BoolLit True)
  , ("False", ConExpr $ Lit $ BoolLit False)
  , ("inttoreal", unOp IntToReal)
  , ("booltoint", unOp BoolToInt)
  , ("asint"       , OpExpr $ IndexAsInt ())
  , ("idxSetSize"  , OpExpr $ IdxSetSize ())
  , ("asidx"       , OpExpr $ IntAsIndex () ())
  , ("select"      , OpExpr $ Select () () ())
  , ("todo"       , ConExpr $ Todo ())
  , ("ask"        , OpExpr $ PrimEffect () $ MAsk)
  , ("tell"       , OpExpr $ PrimEffect () $ MTell ())
  , ("get"        , OpExpr $ PrimEffect () $ MGet)
  , ("put"        , OpExpr $ PrimEffect () $ MPut  ())
  , ("inject"     , OpExpr $ Inject ())
  , ("linearize"       , HofExpr $ Linearize ())
  , ("linearTranspose" , HofExpr $ Transpose ())
  , ("runReader"       , HofExpr $ RunReader () ())
  , ("runWriter"       , HofExpr $ RunWriter    ())
  , ("runState"        , HofExpr $ RunState  () ())
  , ("Int"     , TCExpr $ BaseType IntType)
  , ("Real"    , TCExpr $ BaseType RealType)
  , ("Bool"    , TCExpr $ BaseType BoolType)
  , ("TyKind"  , TCExpr $ TypeKind)
  , ("IntRange", TCExpr $ IntRange () ())
  , ("Ref"     , TCExpr $ RefType () ())
  , ("PairType", TCExpr $ PairType () ())
  , ("UnitType", TCExpr $ UnitType)
  , ("pair", ConExpr $ PairCon () ())
  , ("fst", OpExpr $ Fst ())
  , ("snd", OpExpr $ Snd ())
  ]
  where
    binOp op = OpExpr $ ScalarBinOp op () ()
    unOp  op = OpExpr $ ScalarUnOp  op ()
