{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Syntax (ExprP (..), Expr, Type (..), IdxSet, IdxSetVal, Builtin (..), Var,
               UExpr (..), UTopDecl (..), UDecl (..), ImpDecl (..), TopDeclP (..),
               DeclP (..), Decl, TopDecl, Command (..), Pat, SrcPos,
               CmdName (..), IdxExpr, Kind (..), UBinder (..),
               LitVal (..), BaseType (..), Binder, TBinder, lbind, tbind,
               Except, Err (..), ErrType (..),
               throw, addContext, addErrSource, addErrSourcePos,
               FullEnv (..), (-->), (==>), freeLVars, LorT (..), fromL, fromT,
               instantiateTVs, abstractTVs, subFreeTVs, HasTypeVars,
               freeTyVars, maybeSub, Size, unitTy, unitCon,
               ImpProg (..), Statement (..), IExpr (..), IType (..), IBinder,
               Value (..), Vec (..), Result (..), freeVars,
               lhsVars, Output, Nullable (..), SetVal (..), EvalStatus (..),
               MonMap (..), resultSource, resultText, resultErr, resultComplete,
               Index, wrapDecls, subExpr, Subst, strToBuiltin, idxSetKind,
               preludeNames, preludeApp, naryApp, tApp
               ) where

import Fresh
import Record
import Env
import Cat
import Util

import Data.List (elemIndex, nub)
import qualified Data.Map.Strict as M

import Data.Foldable (fold)
import Data.Tuple (swap)
import Data.Maybe (fromJust)
import Data.Functor.Identity (runIdentity)
import Control.Monad.Except hiding (Except)
import Control.Monad.Writer
import Control.Monad.Reader
import Control.Monad.State (State, execState, modify)
import Control.Applicative (liftA, liftA2, liftA3)

-- === core IR ===

data ExprP b = Lit LitVal
          | Var Var
          | PrimOp Builtin [Type] [ExprP b]
          | Decls [DeclP b] (ExprP b)
          | Lam (BinderP b) (ExprP b)
          | App (ExprP b) (ExprP b)
          | For (BinderP b) (ExprP b)
          | Get (ExprP b) (ExprP b)
          | TLam [TBinder] (ExprP b)
          | TApp (ExprP b) [Type]
          | RecCon (Record (ExprP b))
          | RecGet (ExprP b) RecField
          | TabCon IdxSetVal Type [ExprP b]
          | Annot (ExprP b) Type
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

type Var = Name

-- TODO: figure out how to treat index set kinds
-- data Kind = idxSetKind | TyKind  deriving (Show, Eq, Ord)
data Kind = TyKind  deriving (Show, Eq, Ord)
idxSetKind = TyKind

data DeclP b = Let    (BinderP b)     (ExprP b)
             | Unpack (BinderP b) Var (ExprP b)
               deriving (Eq, Ord, Show)

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
             | FLT | FGT | ILT | IGT
             | Pow | Exp | Log | Sqrt | Sin | Cos | Tan
             | Hash | Rand | Randint | IntToReal
             | Range | Scan | Copy | Deriv | Transpose
             | VZero | VAdd | VSingle | VSum | IndexAsInt
                deriving (Eq, Ord)

builtinNames = M.fromList [
  ("iadd", IAdd), ("isub", ISub), ("imul", IMul),
  ("fadd", FAdd), ("fsub", FSub), ("fmul", FMul),
  ("fdiv", FDiv), ("pow", Pow), ("exp", Exp),
  ("fgt", FLT), ("flt", FGT), ("igt", ILT), ("ilt", IGT),
  ("log", Log), ("sqrt", Sqrt), ("sin", Sin), ("cos", Cos), ("tan", Tan),
  ("scan", Scan), ("range", Range), ("inttoreal", IntToReal),
  ("hash", Hash), ("rand", Rand), ("randint", Randint), ("deriv", Deriv),
  ("transpose", Transpose), ("copy", Copy), ("asint", IndexAsInt),
  ("vzero", VZero), ("vadd", VAdd), ("vsingle", VSingle), ("vsum", VSum)]

builtinStrs = M.fromList $ map swap (M.toList builtinNames)

strToBuiltin :: String -> Maybe Builtin
strToBuiltin name = M.lookup name builtinNames

instance Show Builtin where
  show b = "%" ++ fromJust (M.lookup b builtinStrs)

data CmdName = GetType | Passes | LLVM | Asm | TimeIt
             | EvalExpr | Plot | PlotMat | Flops
                deriving  (Show, Eq)


data Value = Value Type (RecTree Vec)  deriving (Show)
data Vec = IntVec [Int] | RealVec [Double]  deriving (Show)

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
           | ULam Pat UExpr
           | UApp UExpr UExpr
           | UFor UBinder UExpr
           | UGet UExpr UExpr
           | URecCon (Record UExpr)
           | UTabCon [UExpr]
           | UAnnot UExpr Type
           | USrcAnnot UExpr SrcPos
                deriving (Show, Eq)

data UBinder = UBind (BinderP (Maybe Type)) | IgnoreBind  deriving (Show, Eq)
data UDecl = ULet Pat UExpr
           | UTAlias Var Type
           | UUnpack UBinder Var UExpr  deriving (Show, Eq)

data UTopDecl = UTopDecl UDecl
              | UEvalCmd (Command UExpr)  deriving (Show)

type Pat = RecTree UBinder

-- === imperative IR ===

newtype ImpProg = ImpProg [Statement]  deriving (Show, Semigroup, Monoid)

data Statement = Alloc IBinder ImpProg
               | Update Var [Index] Builtin [IExpr]
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
type Output = String
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

type FullEnv v t = Env (LorT v t)

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
      PrimOp b ts xs -> liftA2 (PrimOp b) (traverse recurTy ts)
                                                  (traverse recur xs)
      Decls [] final -> recur final
      Decls (decl:decls) final -> case decl of
        Let b bound ->
          liftA3 (\b' bound' body' -> wrapDecls [Let b' bound'] body')
                 (recurB b) (recur bound) (recur body)
        Unpack b tv bound ->
          liftA3 (\b' bound' body' -> wrapDecls [Unpack b' tv bound'] body')
                 (recurWithB [tv] b) (recur bound) (recurWith [tv] body)
        where body = Decls decls final
      Lam b body       -> liftA2 Lam (recurB b) (recur body)
      App fexpr arg    -> liftA2 App (recur fexpr) (recur arg)
      For b body       -> liftA2 For (recurB b) (recur body)
      Get e ie         -> liftA2 Get (recur e) (pure ie)
      RecCon r         -> liftA  RecCon (traverse recur r)
      RecGet e field   -> liftA (flip RecGet field) (recur e)
      TabCon n ty xs   -> liftA2 (TabCon n) (recurTy ty) (traverse recur xs)
      TLam bs expr      -> liftA  (TLam bs) (recurWith [v | v:>_ <- bs] expr)
      TApp expr ts      -> liftA2 TApp (recur expr) (traverse recurTy ts)
    where recur   = subFreeTVsBVs bvs f
          recurTy = subFreeTVsBVs bvs f
          recurB b = traverse recurTy b
          recurWith   vs = subFreeTVsBVs (vs ++ bvs) f
          recurWithTy vs = subFreeTVsBVs (vs ++ bvs) f
          recurWithB  vs b = traverse (recurWithTy vs) b

instance HasTypeVars Binder where
  subFreeTVsBVs bvs f b = traverse (subFreeTVsBVs bvs f) b

freeLVars :: Expr -> Env ()
freeLVars expr = snd $ runWriter (freeLVarsW expr)

freeLVarsW :: Expr -> Writer (Env ()) ()
freeLVarsW expr = case expr of
  Var v     -> tell (v @> ())
  Lit     _ -> return ()
  PrimOp _ _ xs -> mapM_ recur xs
  Decls [] body -> recur body
  Decls (decl:decls) final -> case decl of
    Let    b   bound -> recur bound >> unfree b body
    Unpack b _ bound -> recur bound >> unfree b body
    where body = Decls decls final
  Lam b body       -> unfree b body
  App fexpr arg    -> recur fexpr >> recur arg
  For b body       -> unfree b body
  Get e ie         -> recur e >> recur ie
  RecCon r         -> mapM_ recur r
  RecGet e _       -> recur e
  TLam _ expr      -> recur expr
  TApp expr _      -> recur expr
  where recur = freeLVarsW
        unfree (v:>_) expr = censor (envDelete v) (recur expr)
-- TODO: include type variables, since they're now lexcially scoped

freeVars :: UTopDecl -> [Var]
freeVars decl = case decl of
  UTopDecl (ULet    _   expr) -> freeVarsUExpr' expr
  UTopDecl (UUnpack _ _ expr) -> freeVarsUExpr' expr
  UEvalCmd (Command _ expr) -> freeVarsUExpr' expr
  UEvalCmd NoOp -> []

freeVarsUExpr' :: UExpr -> [Var]
freeVarsUExpr' expr = nub $ runReader (freeVarsUExpr expr) mempty

freeVarsUExpr :: UExpr -> Reader (Env (Maybe Type)) [Var]
freeVarsUExpr expr = case expr of
  ULit _         -> return []
  UVar v         -> do isbound <- asks $ isin v
                       return $ if isbound then [] else [v]
  UPrimOp _ args -> liftM fold (traverse recur args)
  UDecls [] body -> recur body
  UDecls (decl:decls) final -> case decl of
    ULet    p   e -> liftM2 (<>) (recur e) (recurWith p body)
    UUnpack b _ e -> liftM2 (<>) (recur e) (recurWith [b] body)
    where body = UDecls decls final
  ULam p body    -> recurWith p body
  UApp fexpr arg -> liftM2 (<>) (recur fexpr) (recur arg)
  UFor v body    -> recurWith [v] body
  UGet e ie      -> liftM2 (<>) (recur e) (recur ie)
  URecCon r      -> liftM fold (traverse recur r)
  UAnnot e _    -> recur e  -- Annotation is irrelevant for free term variables
  where
    recur = freeVarsUExpr
    recurWith p expr = local (foldMap ubind p <>) (recur expr)
    ubind b = case b of UBind b' -> bind b'
                        IgnoreBind -> mempty

lhsVars :: UTopDecl -> [Var]
lhsVars decl = case decl of
  UTopDecl (ULet (RecLeaf (UBind (v:>_))) _ ) -> [v]
  UTopDecl (UUnpack       (UBind (v:>_)) _ _) -> [v]
  _ -> []

wrapDecls :: [DeclP b] -> ExprP b -> ExprP b
wrapDecls [] expr = expr
wrapDecls decls expr = case expr of
  Decls decls' body -> Decls (decls ++ decls') body
  _ -> Decls decls expr

type Subst = FullEnv Expr Type
type Scope = Env ()

subExpr :: Subst -> Scope -> Expr -> Expr
subExpr sub scope expr = runReader (subExprR expr) (sub, scope)

subExprR :: Expr -> Reader (Subst, Scope) Expr
subExprR expr = case expr of
  Var v     -> lookup v
  Lit     _ -> return expr
  PrimOp b ts xs -> liftM2 (PrimOp b) (traverse subTy ts)
                                              (traverse recur xs)
  Decls [] body -> recur body
  Decls (decl:decls) final -> case decl of
    Let b bound -> do
      bound' <- recur bound
      refreshBinder b $ \b' -> do
        body' <- recur body
        return $ wrapDecls [Let b' bound'] body'
    Unpack b tv bound -> do
      bound' <- recur bound
      refreshTBinders [tv:>idxSetKind] $ \[tv':>_] ->
        refreshBinder b $ \b' -> do
          body' <- recur body
          return $ wrapDecls [Unpack b' tv' bound'] body'
    where body = Decls decls final
  Lam b body -> refreshBinder b $ \b' -> do
                   body' <- recur body
                   return $ Lam b' body'
  App fexpr arg -> liftM2 App (recur fexpr) (recur arg)
  For b body -> refreshBinder b $ \b' -> do
                  body' <- recur body
                  return $ For b' body'
  Get e ie -> liftM2 Get (recur e) (recur ie)
  RecCon r -> liftM RecCon $ traverse recur r
  RecGet e field -> liftM (flip RecGet field) (recur e)
  TLam ts expr -> refreshTBinders ts $ \ts' ->
                    liftM (TLam ts') (recur expr)

  TApp expr ts -> liftM2 TApp (recur expr) (traverse subTy ts)
  where
    recur = subExprR

    lookup :: Name -> Reader (Subst, Scope) Expr
    lookup v = do
      mval <- asks $ fmap fromL . flip envLookup v . fst
      case mval of
        Nothing -> return $ Var v
        Just e -> local (\(_, scope) -> (mempty, scope)) (subExprR e)

subTy :: Type -> Reader (Subst, Scope) Type
subTy ty = do env <- asks fst
              return $ maybeSub (fmap fromT . envLookup env) ty

refreshBinder :: Binder -> (Binder -> Reader (Subst, Scope) a)
                                   -> Reader (Subst, Scope) a
refreshBinder (v:>ty) cont = do
  ty' <- subTy ty
  v' <- asks $ rename v . snd
  local (<> (v @> L (Var v'), v'@>())) $
    cont (v':>ty')

refreshTBinders :: [TBinder] -> ([TBinder] -> Reader (Subst, Scope) a)
                                           -> Reader (Subst, Scope) a
refreshTBinders bs cont = do
  env <- ask
  let (bs', env') = runCat (traverse freshen bs) env
  local (<> env') (cont bs')
  where
    freshen :: TBinder -> Cat (Subst, Scope) TBinder
    freshen (v:>k) = do
      v' <- looks $ rename v . snd
      extend $ (v @> T (TypeVar v'), v'@>())
      return (v':>k)

lbind :: BinderP a -> FullEnv a b
lbind (v:>x) = v @> L x

tbind :: BinderP b -> FullEnv a b
tbind (v:>x) = v @> T x
