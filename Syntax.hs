module Syntax (Expr (..), Type (..), UExpr (..), TopDecl (..), Command (..),
               DeclInstr (..), CmdName (..), GPat (..), Pat, IPat, UPat, UIPat,
               IdxExpr (..), LitVal (..), BaseType (..), MetaVar (..), IMetaVar
               (..), Var, IVar, TVar, SVar, ISet (..), Except, Err (..),
               SigmaType, Vars, FullEnv (..), setLEnv, setIEnv, setTEnv,
               setSEnv, fvsUExpr, (-->), (==>), unitTy) where

import Util
import Record
import Env
import Data.Semigroup
import Data.Traversable
import Data.List (intercalate)

data Expr = Lit LitVal
          | Var Var
          | Let Pat Expr Expr
          | Lam Pat Expr
          | App Expr Expr
          | For IPat Expr
          | Get Expr IdxExpr
          | Unpack Type Expr Expr
          | TLam Int Int Expr
          | TApp Expr [Type]
          -- | Pack ISet Expr Type
          -- | NamedTLam [VarName] Expr
          -- | RecCon (Record Expr)
              deriving (Eq, Ord)

data Type = BaseType BaseType
          | TypeVar TVar
          | ArrType Type Type
          | MetaTypeVar MetaVar
          | TabType ISet Type
          | Forall Int Int Type
          | Exists Type
          -- | RecType (Record Type)
          -- | Forall Int Type
          -- | NamedForall [VarName] Type
          -- | NamedExists VarName Type
              deriving (Eq, Ord)

type SigmaType = Type  -- type constructed with Forall

data ISet = ISet SVar
          | IMetaTypeVar IMetaVar  deriving (Eq, Ord, Show)

data UExpr = ULit LitVal
           | UVar Var
           | ULet UPat UExpr UExpr
           | ULam UPat UExpr
           | UApp UExpr UExpr
           | UFor UIPat UExpr
           | UGet UExpr IdxExpr
           | UUnpack VarName UExpr UExpr
           | URecCon (Record UExpr)
           | UAnnot UExpr Type
               deriving (Show, Eq)

data LitVal = IntLit  Int
            | RealLit Float
            | StrLit  String
                 deriving (Eq, Ord)

data BaseType = IntType | BoolType | RealType | StrType
                   deriving (Eq, Ord)

infixr 1 -->
infixr 2 ==>
(-->) = ArrType
(==>) = TabType


newtype MetaVar = MetaVar Int  deriving (Eq, Show, Ord)
newtype IMetaVar = IMetaVar Int  deriving (Eq, Show, Ord)

unitTy = BaseType IntType -- TODO: use the empty tuple when we reintroduce records

type IdxExpr = RecTree IVar

data GPat a = VarPat a
            | RecPat (Record (GPat a))  deriving (Show, Eq, Ord)

data LetUniq  = LetUniq  deriving (Show, Eq)
data IdxUniq  = IdxUniq  deriving (Show, Eq)
data TypeUniq = TypeUniq deriving (Show, Eq)
data ISetUniq = ISetUniq deriving (Show, Eq)

type IPat = GPat ISet
type Pat  = GPat Type

type UBinder = (String, Maybe Type)
type UIPat = GPat UBinder
type UPat  = GPat UBinder

type Var  = GVar LetUniq
type IVar = GVar IdxUniq
type TVar = GVar TypeUniq
type SVar = GVar ISetUniq

data FullEnv v i t s = FullEnv { lEnv :: Env Var  v
                               , iEnv :: Env IVar i
                               , tEnv :: Env TVar t
                               , sEnv :: Env SVar s }

type Vars = FullEnv () () () ()

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
         | InfiniteTypeErr
         | UnboundVarErr VarName
         | RepVarPatternErr VarName
         | CompilerErr String
         | PrintErr String
  deriving (Eq)

type Except a = Either Err a

instance Traversable GPat where
  traverse f (VarPat x) = fmap VarPat $ f x
  traverse f (RecPat r) = fmap RecPat $ traverse (traverse f) r

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
    InfiniteTypeErr -> "Infinite type"
    UnboundVarErr v -> "Unbound variable: " ++ show v
    RepVarPatternErr v -> "Repeated variable in pattern: " ++ show v
    CompilerErr s -> "Compiler bug! " ++ s
    PrintErr s -> "Print error: " ++ s

instance Semigroup (FullEnv v i t s) where
  FullEnv x y z w <> FullEnv x' y' z' w' = FullEnv (x<>x') (y<>y') (z<>z') (w<>w')

instance Monoid (FullEnv v i t s) where
  mempty = FullEnv mempty mempty mempty mempty
  mappend = (<>)

setLEnv :: (Env Var v -> Env Var v) -> FullEnv v i t s -> FullEnv v i t s
setLEnv update env = env {lEnv = update (lEnv env)}

setIEnv :: (Env IVar i -> Env IVar i) -> FullEnv v i t s -> FullEnv v i t s
setIEnv update env = env {iEnv = update (iEnv env)}

setTEnv :: (Env TVar t -> Env TVar t) -> FullEnv v i t s -> FullEnv v i t s
setTEnv update env = env {tEnv = update (tEnv env)}

setSEnv :: (Env SVar s -> Env SVar s) -> FullEnv v i t s -> FullEnv v i t s
setSEnv update env = env {sEnv = update (sEnv env)}

instance Functor GPat where
  fmap = fmapDefault

instance Foldable GPat where
  foldMap = foldMapDefault

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
  UGet e ie      -> fvsUExpr e <> foldMap (fvsVar setIEnv) ie
  URecCon r      -> foldMap fvsUExpr r
  UAnnot e t     -> fvsUExpr e <> fvsType t
  UUnpack _ e body -> fvsUExpr e <> fvsUExpr body


fvsType :: Type -> Vars
fvsType ty = case ty of
  BaseType _    -> mempty
  TypeVar v     -> fvsVar setTEnv v
  ArrType t1 t2 -> fvsType t1 <> fvsType t2
  -- TabType t1 t2 -> fvsType t1 <> fvsType t2
  -- RecType r     -> foldMap fvsType r
  -- Forall _ t    -> fvsType t
  -- Exists t      -> fvsType t
  MetaTypeVar _ -> mempty
  -- NamedForall _ t -> fvsType t
  -- NamedExists _ t -> fvsType t

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
iVarNames = varNames ['i'..'k']
tVarNames = varNames ['a'..'c']
sVarNames = varNames ['i'..'k']

instance Show LitVal where
  show (IntLit x ) = show x
  show (RealLit x) = show x
  show (StrLit x ) = show x

instance Show Expr where
  show = showExpr (0, 0, 0, 0)

instance Show Type where
  show = showType (0, 0)

showType :: (Int, Int) -> Type -> String
showType env@(depthT, depthS) t = case t of
  BaseType b  -> show b
  TypeVar v   -> getName tVarNames depthT v
  ArrType a b -> paren $ recur a ++ " -> " ++ recur b
  TabType i b -> showISet depthS i ++ "=>" ++ recur b
  MetaTypeVar (MetaVar v) -> "mv" ++ show v
  Forall nt ns t -> showType (nt, ns) t
  Exists body -> "E " ++ sVarNames !! depthS ++ ". " ++
                 showType (depthT, depthS + 1) body

  -- RecType r   -> printRecord recur typeRecPrintSpec r
  where recur = showType env

showISet :: Int -> ISet -> String
showISet depth s = case s of ISet v -> getName sVarNames depth v
                             IMetaTypeVar v -> "mv" ++ show v

spaceSep :: [String] -> String
spaceSep = intercalate " "

showExpr :: (Int, Int, Int, Int) -> Expr -> String
showExpr env@(l,i,t,s) expr = case expr of
  Lit val      -> show val
  Var v        -> getName lVarNames l v
  Let p e1 e2  -> paren $ "let " ++ showPat p ++ " = " ++ recur e1
                            ++ " in " ++ recurL e2
  Lam p e      -> paren $ "lam " ++ showPat p ++ ": " ++ recurL e
  App e1 e2    -> paren $ recur e1 ++ " " ++ recur e2
  For p e      -> paren $ "for " ++ showIPat p ++ ": " ++ recurI e
  Get e ie     -> recur e ++ "." ++ showIdxExpr ie
  Unpack ty e1 e2 -> paren $ "unpack {" ++ lVarNames !! l ++ "::"
                             ++ showType (t,s+1) ty
                             ++ ", " ++ sVarNames !! s
                             ++ "} = " ++ recur e1
                             ++ " in " ++ showExpr (l+1,i,t,s+1) e2
  TLam t s expr -> "LAM " ++ spaceSep (take t tVarNames) ++ " , "
                          ++ spaceSep (take s sVarNames) ++ ": "
                          ++ showExpr (0, 0, t, s) expr
  TApp expr ts -> recur expr ++ "[" ++ spaceSep (map (showType (t,s)) ts) ++ "]"
  where recur = showExpr env
        recurL = showExpr (l+1,i,t,s)
        recurI = showExpr (l,i+1,t,s)
        showPat p  = case p of VarPat ty   -> lVarNames !! l ++ "::" ++ showType (t,s) ty
        showIPat p = case p of VarPat iSet -> iVarNames !! i ++ "::" ++ showISet s iSet
        showIdxExpr e = case e of RecLeaf v -> getName iVarNames i v

getName :: [VarName] -> Int -> GVar i -> String
getName names depth v = case v of
  FV name -> name
  BV i -> let i' = depth - i - 1
          in if i' >= 0
             then names !! i'
             else "<unbound: " ++ show i ++ "/" ++ show depth ++ " >"
