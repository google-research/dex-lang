{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Syntax (Expr (..), Type (..), IdxSet, Builtin (..), Var,
               UExpr (..), UDecl (..), ImpDecl (..), Decl (..), Command (..),
               CmdName (..), IdxExpr, Kind (..),
               LitVal (..), BaseType (..), Pat, UPat, Binder, TBinder,
               Except, Err (..), ErrType (..), err, throw,
               FullEnv (..), setLEnv, setTEnv,
               (-->), (==>), newFullEnv, freeLVars,
               instantiateTVs, abstractTVs, subFreeTVs, HasTypeVars,
               freeTyVars, maybeSub, Size, Statement (..), unitTy,
               ImpProgram (..), IExpr (..), IType (..), IBinder,
               Value (..), Vec (..), Result (..), freeVars, lhsVars, Output,
               Nullable (..), SetVal (..), EvalStatus (..), MonMap (..),
               resultSource, resultText, resultErr, resultComplete
              ) where

import Record
import Env
import Fresh

import Data.Foldable (toList)
import Data.List (elemIndex, nub)
import qualified Data.Map.Strict as M

import Data.Foldable (fold)
import Data.Functor.Identity (runIdentity)
import Control.Monad.Except (MonadError, throwError)
import Control.Monad.Reader
import Control.Monad.State (State, execState, modify)
import Control.Applicative (liftA, liftA2, liftA3)

-- === core system-F-like IR ===

data Expr = Lit LitVal
          | Var Var
          | Builtin Builtin
          | Let Pat Expr Expr
          | Lam Pat Expr
          | App Expr Expr
          | For Binder Expr
          | Get Expr IdxExpr
          | Unpack Binder Var Expr Expr
          | TLam [TBinder] Expr
          | TApp Expr [Type]
          | RecCon (Record Expr)
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

type Var = Name

data Kind = IdxSetKind | TyKind  deriving (Show, Eq, Ord)

data Decl = TopLet    Binder     Expr
          | TopUnpack Binder Var Expr
          | EvalCmd (Command Expr)

data Command expr = Command CmdName expr | NoOp

type Binder = (Var, Type)
type TBinder = (Var, Kind)
type Pat  = RecTree Binder
type IdxSet = Type
type IdxExpr = Var
type IdxSetVal = Int

data LitVal = IntLit  Int
            | RealLit Double
            | StrLit  String
                deriving (Eq, Ord, Show)

data BaseType = IntType | BoolType | RealType | StrType
                   deriving (Eq, Ord, Show)

data Builtin = Add | Sub | Mul | FAdd | FSub | FMul | FDiv
             | Pow | Exp | Log | Sqrt | Sin | Cos | Tan
             | Hash | Rand | Randint | IntToReal
             | Iota | Fold
                deriving (Eq, Ord, Show)

data CmdName = GetType | Passes | TimeIt
             | EvalExpr | Plot | PlotMat
                deriving  (Show, Eq)


data Value = Value Type (RecTree Vec)  deriving (Show)
data Vec = IntVec [Int] | RealVec [Double]  deriving (Show)

unitTy = RecType (Tup [])

-- === untyped AST ===

data UExpr = ULit LitVal
           | UVar Var
           | UBuiltin Builtin
           | ULet UPat UExpr UExpr
           | ULam UPat UExpr
           | UApp UExpr UExpr
           | UFor Var UExpr
           | UGet UExpr IdxExpr
           | UUnpack Var UExpr UExpr
           | URecCon (Record UExpr)
           | UAnnot UExpr Type
               deriving (Show, Eq)

data UDecl = UTopLet    Var UExpr
           | UTopUnpack Var UExpr
           | UEvalCmd (Command UExpr)

type UPat = RecTree Var

-- === imperative IR ===

data ImpProgram = ImpProgram [Statement] [IExpr] deriving (Show)
data Statement = Update Var [Index] IExpr
               | ImpLet IBinder IExpr
               | Loop Index Size [Statement]
               | Alloc Var IType -- mutable
                   deriving (Show)

data IExpr = ILit LitVal
           | IVar  Var
           | IGet IExpr Index
           | IBuiltinApp Builtin [IExpr]
               deriving (Show, Eq)

data ImpDecl = ImpTopLet [IBinder] ImpProgram
             | ImpEvalCmd Type (Command ImpProgram)

type IBinder = (Var, IType)
data IType = IType BaseType [Size]  deriving (Show, Eq)
type Size = Var
type Index = Var

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
type Output = String
data Result = Result (SetVal Source) (SetVal EvalStatus) Output

resultSource s = Result (Set s) mempty mempty
resultText   s = Result mempty mempty s
resultErr    e = Result mempty (Set (Failed e)) mempty
resultComplete = Result mempty (Set Complete)   mempty

newtype Err = Err [(ErrType, String)]
  deriving (Eq, Ord, Show, Semigroup, Monoid)

data ErrType = NoErr
             | ParseErr
             | TypeErr
             | UnboundVarErr
             | CompilerErr
             | NotImplementedErr
             | UpstreamErr
             | OtherErr
  deriving (Eq, Ord, Show)

err :: ErrType -> String -> Err
err ty str = Err [(ty, str)]

type Except a = Either Err a

throw :: MonadError Err m => ErrType -> String -> m a
throw e s = throwError $ err e s

instance Semigroup Result where
  Result x y z <> Result x' y' z' = Result (x<>x') (y<>y') (z<>z')

instance Monoid Result where
  mempty = Result mempty mempty mempty

-- === misc ===

infixr 1 -->
infixr 2 ==>
(-->) = ArrType
(==>) = TabType

data FullEnv v t = FullEnv { lEnv :: Env v
                           , tEnv :: Env t }  deriving (Show, Eq)

newFullEnv :: [(Var, a)] -> [(Var, b)] -> FullEnv a b
newFullEnv lvars tvars = FullEnv (newEnv lvars) (newEnv tvars)

-- these should just be lenses
setLEnv :: (Env a -> Env b) -> FullEnv a t -> FullEnv b t
setLEnv update env = env {lEnv = update (lEnv env)}

setTEnv :: (Env a -> Env b) -> FullEnv v a -> FullEnv v b
setTEnv update env = env {tEnv = update (tEnv env)}

instance Semigroup (FullEnv v t) where
  FullEnv x y <> FullEnv x' y' = FullEnv (x<>x') (y<>y')

instance Monoid (FullEnv v t) where
  mempty = FullEnv mempty mempty
  mappend = (<>)

instantiateTVs :: [Type] -> Type -> Type
instantiateTVs vs x = subAtDepth 0 sub x
  where sub depth tvar = case tvar of
                        Left v -> TypeVar v
                        Right i | i >= depth -> vs !! i
                                | otherwise -> BoundTVar i

abstractTVs :: [Var] -> Type -> Type
abstractTVs vs x = subAtDepth 0 sub x
  where sub depth tvar = case tvar of
                           Left v -> case elemIndex v vs of
                                       Nothing -> TypeVar v
                                       Just i  -> BoundTVar (depth + i)
                           Right i -> BoundTVar i

subAtDepth :: Int -> (Int -> Either Var Int -> Type) -> Type -> Type
subAtDepth d f ty = case ty of
    BaseType _    -> ty
    TypeVar v     -> f d (Left v)
    ArrType a b   -> ArrType (recur a) (recur b)
    TabType a b   -> TabType (recur a) (recur b)
    RecType r     -> RecType (fmap recur r)
    Exists body   -> Exists (recurWith 1 body)
    Forall kinds body -> (Forall kinds) (recurWith (length kinds) body)
    IdxSetLit _   -> ty
    BoundTVar n   -> f d (Right n)
  where recur        = subAtDepth d f
        recurWith d' = subAtDepth (d + d') f

freeTyVars :: HasTypeVars a => a -> [Var]
freeTyVars x = execState (subFreeTVs collectVars x) []
  where collectVars :: Var -> State [Var] Type
        collectVars v = modify (v :) >> return (TypeVar v)

maybeSub :: (Var -> Maybe Type) -> Type -> Type
maybeSub f ty = runIdentity $ subFreeTVs (return . sub) ty
  where sub v = case f v of Just t -> t
                            Nothing -> TypeVar v

subFreeTVs :: (HasTypeVars a,  Applicative f) => (Var -> f Type) -> a -> f a
subFreeTVs = subFreeTVsBVs []

class HasTypeVars a where
  subFreeTVsBVs :: Applicative f => [Var] -> (Var -> f Type) -> a -> f a

instance (HasTypeVars a, HasTypeVars b) => HasTypeVars (a,b) where
  subFreeTVsBVs bvs f (x, y) = liftA2 (,) (subFreeTVsBVs bvs f x)
                                          (subFreeTVsBVs bvs f y)

instance HasTypeVars Type where
  subFreeTVsBVs bvs f ty = case ty of
      BaseType _    -> pure ty
      TypeVar v | v `elem` bvs -> pure ty
                | otherwise    -> f v
      ArrType a b   -> liftA2 ArrType (recur a) (recur b)
      TabType a b   -> liftA2 TabType (recur a) (recur b)
      RecType r     -> liftA RecType (traverse recur r)
      Exists body   -> liftA Exists (recur body)
      Forall kinds body -> liftA (Forall kinds) (recur body)
      IdxSetLit _   -> pure ty
      BoundTVar _   -> pure ty
    where recur = subFreeTVsBVs bvs f

instance HasTypeVars Expr where
  subFreeTVsBVs bvs f expr = case expr of
      Lit c -> pure $ Lit c
      Var v -> pure $ Var v
      Builtin b -> pure $ Builtin b
      Let p bound body -> liftA3 Let (traverse recurB p) (recur bound) (recur body)
      Lam p body       -> liftA2 Lam (traverse recurB p) (recur body)
      App fexpr arg    -> liftA2 App (recur fexpr) (recur arg)
      For b body       -> liftA2 For (recurB b) (recur body)
      Get e ie         -> liftA2 Get (recur e) (pure ie)
      RecCon r         -> liftA  RecCon (traverse recur r)
      Unpack b tv bound body -> liftA3 (\x y z -> Unpack x tv y z)
               (recurWithB [tv] b) (recur bound) (recurWith [tv] body)
      TLam bs expr      -> liftA  (TLam bs) (recurWith (map fst bs) expr)
      TApp expr ts      -> liftA2 TApp (recur expr) (traverse recurTy ts)
    where recur   = subFreeTVsBVs bvs f
          recurTy = subFreeTVsBVs bvs f
          recurB (v,ty) = liftA ((,) v) (recurTy ty)
          recurWith   vs = subFreeTVsBVs (vs ++ bvs) f
          recurWithTy vs = subFreeTVsBVs (vs ++ bvs) f
          recurWithB  vs (v,ty) = liftA ((,) v) (recurWithTy vs ty)


freeLVars :: Expr -> [Var]
freeLVars = freeLVarsEnv mempty

freeLVarsEnv :: Env Type -> Expr -> [Var]
freeLVarsEnv env expr = case expr of
  Lit _ -> []
  Var v -> [v]
  Builtin _ -> []
  Let p bound body -> recur bound ++ recurWith p body
  Lam p body       -> recurWith p body
  App fexpr arg    -> recur fexpr ++ recur arg
  For b body       -> recurWith [b] body
  Get e ie         -> recur e ++ [ie]
  RecCon r         -> concat $ toList $ fmap recur r
  Unpack b _ bound body -> recur bound ++ recurWith [b] body
  TLam _ expr      -> recur expr
  TApp expr _      -> recur expr

  where recur = freeLVarsEnv env
        recurWith b = freeLVarsEnv (addVs b env)

freeVars :: UDecl -> [Var]
freeVars decl = case decl of
  UTopLet    _ expr -> freeVarsUExpr' expr
  UTopUnpack _ expr -> freeVarsUExpr' expr
  UEvalCmd (Command _ expr) -> freeVarsUExpr' expr
  UEvalCmd NoOp -> []

freeVarsUExpr' :: UExpr -> [Var]
freeVarsUExpr' expr = nub $ runReader (freeVarsUExpr expr) mempty

freeVarsUExpr :: UExpr -> Reader (Env ()) [Var]
freeVarsUExpr expr = case expr of
  ULit _         -> return []
  UVar v         -> do isbound <- asks $ isin v
                       return $ if isbound then [] else [v]
  UBuiltin _     -> return []
  ULet p e body  -> liftM2 (<>) (recur e) (recurWith p body)
  ULam p body    -> recurWith p body
  UApp fexpr arg -> liftM2 (<>) (recur fexpr) (recur arg)
  UFor v body    -> recurWith [v] body
  UGet e ie      -> liftM2 (<>) (recur e) (recur (UVar ie))
  URecCon r      -> liftM fold (traverse recur r)
  UUnpack v e body -> liftM2 (<>) (recur e) (recurWith [v] body)
  UAnnot e ty    -> recur e  -- Annotation is irrelevant for free term variables
  where
    recur = freeVarsUExpr
    recurWith p expr = local (addVs (fmap (\v -> (v,())) p)) (recur expr)

lhsVars :: UDecl -> [Var]
lhsVars decl = case decl of
  UTopLet    v _ -> [v]
  UTopUnpack v _ -> [v]
  UEvalCmd     _ -> []
