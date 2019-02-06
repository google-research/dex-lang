module Syntax (Expr (..), Type (..), UExpr (..), TopDecl (..), Command (..),
               DeclInstr (..), CmdName (..), IdxExpr, Kind (..),
               LitVal (..), BaseType (..), MetaVar (..),
               Var, TVar, IdxSet, Except, Err (..),
               SigmaType, Vars, FullEnv (..), setLEnv, setTEnv,
               fvsUExpr, (-->), (==>), exprTypes, tyMetaVars, subTy,
               subExprDepth, subTyDepth, bindMetaTy, bindMetaExpr) where

import Util
import Record
import Env
import Data.Semigroup
import Data.Traversable
import Data.List (intercalate, elemIndex)

import Control.Applicative (liftA, liftA2, liftA3)
import Control.Lens.Traversal (Traversal')

data Expr = Lit LitVal
          | Var Var
          | Let Type Expr Expr
          | Lam Type Expr
          | App Expr Expr
          | For IdxSet Expr
          | Get Expr IdxExpr
          | Unpack Type Expr Expr
          | TLam [Kind] Expr
          | TApp Expr [Type]
              deriving (Eq, Ord)

data Type = BaseType BaseType
          | TypeVar TVar
          | MetaTypeVar MetaVar
          | ArrType Type Type
          | TabType IdxSet Type
          | Forall [Kind] Type
          | Exists Type
              deriving (Eq, Ord)

data Kind = IdxSetKind | TyKind  deriving (Show, Eq, Ord)

type IdxSet = Type -- Constructed with MetaTypeVar or TypeVar
type SigmaType = Type  -- Constructed with Forall

data UExpr = ULit LitVal
           | UVar Var
           | ULet VarName UExpr UExpr
           | ULam VarName UExpr
           | UApp UExpr UExpr
           | UFor VarName UExpr
           | UGet UExpr IdxExpr
           | UUnpack VarName UExpr UExpr
           | URecCon (Record UExpr)
           | UAnnot UExpr Type
               deriving (Show, Eq)

type IdxExpr = Var

data LitVal = IntLit  Int
            | RealLit Float
            | StrLit  String
                 deriving (Eq, Ord)

data BaseType = IntType | BoolType | RealType | StrType
                   deriving (Eq, Ord)

data MetaVar = MetaVar Kind Int  deriving (Eq, Show, Ord)

infixr 1 -->
infixr 2 ==>
(-->) = ArrType
(==>) = TabType

data LetUniq  = LetUniq  deriving (Show, Eq)
data TypeUniq = TypeUniq deriving (Show, Eq)

type Var  = GVar LetUniq
type TVar = GVar TypeUniq
data FullEnv v t = FullEnv { lEnv :: Env Var  v
                           , tEnv :: Env TVar t }

-- these should just be lenses
setLEnv :: (Env Var v -> Env Var v) -> FullEnv v t -> FullEnv v t
setLEnv update env = env {lEnv = update (lEnv env)}

setTEnv :: (Env TVar t -> Env TVar t) -> FullEnv v t -> FullEnv v t
setTEnv update env = env {tEnv = update (tEnv env)}

type Vars = FullEnv () ()

type Source = String
data TopDecl expr = TopDecl Source Vars (DeclInstr expr)
data DeclInstr expr = TopAssign VarName expr
                    | EvalCmd (Command expr)  deriving (Show, Eq)

data Command expr = Command CmdName expr
                  | CmdResult String
                  | CmdErr Err  deriving (Show, Eq)

data CmdName = EvalExpr | GetType | GetTyped | GetParse
             | GetLLVM  | EvalJit   deriving  (Show, Eq)

data Err = ParseErr String
         | UnificationErr Type Type
         | TypeErr String
         | InfiniteTypeErr
         | UnboundVarErr VarName
         | RepVarPatternErr VarName
         | CompilerErr String
         | PrintErr String
         | NotImplementedErr String
  deriving (Eq)

type Except a = Either Err a

instance Traversable TopDecl where
  traverse f (TopDecl s fvs instr) = fmap (TopDecl s fvs) $ traverse f instr

instance Traversable DeclInstr where
  traverse f (TopAssign v expr) = fmap (TopAssign v) (f expr)
  traverse f (EvalCmd cmd) = fmap EvalCmd $ traverse f cmd

instance Traversable Command where
  traverse f (Command cmd expr) = fmap (Command cmd) (f expr)
  traverse f (CmdResult s) = pure $ CmdResult s

instance Show Err where
  show e = case e of
    ParseErr s -> s
    UnificationErr t1 t2 -> ("Type error: can't unify "
                             ++ show t1 ++ " and " ++ show t2)
    TypeErr s -> "Type error: " ++ s
    InfiniteTypeErr -> "Infinite type"
    UnboundVarErr v -> "Unbound variable: " ++ show v
    RepVarPatternErr v -> "Repeated variable in pattern: " ++ show v
    CompilerErr s -> "Compiler bug! " ++ s
    NotImplementedErr s -> "Not implemented: " ++ s
    PrintErr s -> "Print error: " ++ s

instance Semigroup (FullEnv v t) where
  FullEnv x y <> FullEnv x' y' = FullEnv (x<>x') (y<>y')

instance Monoid (FullEnv v t) where
  mempty = FullEnv mempty mempty
  mappend = (<>)

instance Functor TopDecl where
  fmap = fmapDefault

instance Foldable TopDecl where
  foldMap = foldMapDefault

instance Functor DeclInstr where
  fmap = fmapDefault

instance Foldable DeclInstr where
  foldMap = foldMapDefault

instance Functor Command where
  fmap = fmapDefault

instance Foldable Command where
  foldMap = foldMapDefault

type Updater i = (Env (GVar i) () -> Env (GVar i) ()) -> Vars -> Vars

fvsVar :: Updater i -> GVar i -> Vars
fvsVar updater v = case v of FV name -> updater (addFVar name ()) mempty
                             BV _ -> mempty

fvsUExpr :: UExpr -> Vars
fvsUExpr expr = case expr of
  ULit _         -> mempty
  UVar v         -> fvsVar setLEnv v
  ULet _ e body  -> fvsUExpr e <> fvsUExpr body
  ULam _ body    -> fvsUExpr body
  UApp fexpr arg -> fvsUExpr fexpr <> fvsUExpr arg
  UFor _ body    -> fvsUExpr body
  UGet e ie      -> fvsUExpr e <> fvsVar setLEnv ie
  URecCon r      -> foldMap fvsUExpr r
  UAnnot e t     -> fvsUExpr e <> fvsType t
  UUnpack _ e body -> fvsUExpr e <> fvsUExpr body

fvsType :: Type -> Vars
fvsType ty = case ty of
  BaseType _    -> mempty
  TypeVar v     -> fvsVar setTEnv v
  ArrType t1 t2 -> fvsType t1 <> fvsType t2
  MetaTypeVar _ -> mempty

paren :: String -> String
paren s = "(" ++ s ++ ")"

varNames :: [Char] -> [VarName]
varNames prefixes = map ithName [0..]
  where n = length prefixes
        ithName i | i < n     = [prefixes !! i]
                  | otherwise = ithName (mod i n) ++ show (div i n)

instance Show BaseType where
  show t = case t of
    IntType  -> "Int"
    BoolType -> "Bool"
    RealType -> "Real"
    StrType  -> "Str"

lVarNames = varNames ['x'..'z']
tVarNames = varNames ['a'..'c']

-- TODO: use these based on kind information
-- iVarNames = varNames ['i'..'k']
-- sVarNames = varNames ['i'..'k']

instance Show LitVal where
  show (IntLit x ) = show x
  show (RealLit x) = show x
  show (StrLit x ) = show x

instance Show Expr where
  show = showExpr (0, [])

instance Show Type where
  show = showType []

showType :: [Kind] -> Type -> String
showType env t = case t of
  BaseType b  -> show b
  TypeVar v   -> getName tVarNames depth v
  ArrType a b -> paren $ recur a ++ " -> " ++ recur b
  TabType a b -> recur a ++ "=>" ++ recur b
  MetaTypeVar (MetaVar kind v) -> "mv" ++ show v ++ "[" ++ show kind ++ "]"
  Forall kinds t -> "A " ++ spaceSep (take (length kinds) tVarNames) ++ ". "
                          ++ showType (kinds ++ env) t
  Exists body -> "E " ++ tVarNames !! depth ++ ". " ++
                 showType (IdxSetKind : env) body
  where recur = showType env
        depth = length env

spaceSep :: [String] -> String
spaceSep = intercalate " "

showExpr :: (Int, [Kind]) -> Expr -> String
showExpr env@(depth, kinds) expr = case expr of
  Lit val      -> show val
  Var v        -> name v
  Let t e1 e2  -> paren $    "let " ++ showBinder t ++ " = " ++ recur e1
                          ++ " in " ++ recurWith e2
  Lam t e      -> paren $ "lam " ++ showBinder t ++ ": " ++ recurWith e
  App e1 e2    -> paren $ recur e1 ++ " " ++ recur e2
  For t e      -> paren $ "for " ++ showBinder t ++ ": " ++ recurWith e
  Get e ie     -> recur e ++ "." ++ name ie
  Unpack ty e1 e2 -> paren $ "unpack {" ++ lVarNames !! depth ++ "::"
                             ++ showType (IdxSetKind:kinds) ty
                             ++ ", " ++ tVarNames !! (length kinds)
                             ++ "} = " ++ recur e1
                             ++ " in " ++ showExpr (depth+1, IdxSetKind:kinds) e2
  TLam kinds' expr ->
    "LAM " ++ spaceSep (zipWith (\k v -> v ++ "::" ++ show k)
                        kinds' tVarNames) ++ ": "
           ++ showExpr (depth, kinds' ++ kinds) expr

  TApp expr ts -> recur expr ++ "[" ++ spaceSep (map (showType kinds) ts) ++ "]"
  where recur = showExpr env
        recurWith = showExpr (depth + 1, kinds)
        showBinder ty = lVarNames !! depth ++ "::" ++ showType kinds ty
        name = getName lVarNames depth

getName :: [VarName] -> Int -> GVar i -> String
getName names depth v = case v of
  FV name -> name
  BV i -> let i' = depth - i - 1
          in if i' >= 0
             then names !! i'
             else "<BV " ++ show i ++ ">"

exprTypes :: Traversal' Expr Type
exprTypes f expr = case expr of
  Let t bound body -> liftA3 Let (f t) (recur bound) (recur body)
  Lam t body       -> liftA2 Lam (f t) (recur body)
  App fexpr arg    -> liftA2 App (recur fexpr) (recur arg)
  For t body       -> liftA2 For (f t) (recur body)
  Get e ie         -> liftA2 Get (recur e) (pure ie)
  Unpack t bound body -> liftA3 Unpack (f t) (recur bound) (recur body)
  TLam kinds expr     -> liftA  (TLam kinds) (recur expr)
  TApp expr ts        -> liftA2 TApp (recur expr) (traverse f ts)
  _ -> pure expr
  where recur = exprTypes f

tyMetaVars :: Traversal' Type MetaVar
tyMetaVars f ty = case ty of
  ArrType a b     -> liftA2 ArrType (recur a) (recur b)
  MetaTypeVar v   -> liftA MetaTypeVar (f v)
  TabType a b     -> liftA2 TabType (recur a) (recur b)
  Forall kinds body -> liftA (Forall kinds) (recur body)
  Exists body     -> liftA  Exists (recur body)
  _               -> pure ty
  where recur = tyMetaVars f

type MetaVarFun = Int -> MetaVar -> Maybe Type

subTyDepth :: Int -> MetaVarFun -> Type -> Type
subTyDepth d f t = case t of
  ArrType a b   -> ArrType (recur a) (recur b)
  TabType a b   -> TabType (recur a) (recur b)
  MetaTypeVar v -> case f d v of Just t' -> t'
                                 Nothing -> t
  Exists body -> Exists (recurWith 1 body)
  Forall kinds body -> Forall kinds (recurWith (length kinds) body)
  _ -> t
  where recur = subTyDepth d f
        recurWith d' = subTyDepth (d + d') f

subTy :: (MetaVar -> Maybe Type) -> Type -> Type
subTy f t = subTyDepth 0 (const f) t

subExprDepth ::  Int -> MetaVarFun -> Expr -> Expr
subExprDepth d f expr = case expr of
  Let t bound body -> Let (recurTy t) (recur bound) (recur body)
  Lam t body       -> Lam (recurTy t) (recur body)
  App fexpr arg    -> App (recur fexpr) (recur arg)
  For t body       -> For (recurTy t) (recur body)
  Get e ie         -> Get (recur e) ie
  Unpack t bound body -> Unpack (recurTy t) (recur bound) (recurWith 1 body)
  TLam kinds expr     -> TLam kinds (recurWith (length kinds) expr)
  TApp expr ts        -> TApp (recur expr) (map recurTy ts)
  _ -> expr
  where recur = subExprDepth d f
        recurWith d' = subExprDepth (d + d') f
        recurTy = subTyDepth d f

bindMetaTy :: [MetaVar] -> Type -> Type
bindMetaTy vs = subTyDepth 0 sub
  where sub d v = case elemIndex v vs of
                    Just i  -> Just $ TypeVar (BV (d + i))
                    Nothing -> Nothing

bindMetaExpr :: [MetaVar] -> Expr -> Expr
bindMetaExpr vs = subExprDepth 0 sub
  where sub d v = case elemIndex v vs of
                    Just i  -> Just $ TypeVar (BV (d + i))
                    Nothing -> Nothing
