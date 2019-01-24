module Syntax (Expr (..), Type (..), UExpr (..), TopDecl (..), Command (..),
               DeclInstr (..), CmdName (..), GPat (..), Pat, IPat, UPat, UIPat,
               IdxExpr (..), LitVal (..), BaseType (..), MetaVar (..), IType,
               Var, IVar, TVar, Except, Err (..), SigmaType, TauType,
               IdxType, Vars, FullEnv (..), setLEnv, setIEnv, setTEnv, fvsUExpr,
               (-->), (==>)) where
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
          | RecCon (Record Expr)
          | TLam Int Expr
          | TApp Expr [Type]
          | Unpack Expr
          | Pack IType Expr Type

          | NamedTLam [VarName] Expr
              deriving (Show, Eq, Ord)

data Type = BaseType BaseType
          | TypeVar TVar
          | ArrType Type Type
          | TabType IType Type
          | RecType (Record Type)
          | Forall Int Type
          | Exists Type

          | MetaTypeVar MetaVar
          | NamedForall [VarName] Type
          | NamedExists VarName Type
              deriving (Eq, Ord)

data UExpr = ULit LitVal
           | UVar Var
           | ULet UPat UExpr UExpr
           | ULam UPat UExpr
           | UApp UExpr UExpr
           | UFor UIPat UExpr
           | UGet UExpr IdxExpr
           | URecCon (Record UExpr)
           | UAnnot UExpr Type
               deriving (Show, Eq)

data LitVal = IntLit  Int
            | RealLit Float
            | StrLit  String
                 deriving (Show, Eq, Ord)

data BaseType = IntType | BoolType | RealType | StrType
                   deriving (Eq, Ord)

infixr 1 -->
infixr 2 ==>
(-->) = ArrType
(==>) = TabType

type IType     = Type
type SigmaType = Type  -- may have top-level forall
type TauType   = Type  -- doesn't have any foralls
type IdxType   = Type
newtype MetaVar = MetaVar Int  deriving (Eq, Show, Ord)

type IdxExpr = RecTree IVar

data GPat a = VarPat a
            | RecPat (Record (GPat a))  deriving (Show, Eq, Ord)

data LetUniq  = LetUniq  deriving (Show, Eq)
data IdxUniq  = IdxUniq  deriving (Show, Eq)
data TypeUniq = TypeUniq deriving (Show, Eq)

type IPat = GPat Type
type Pat  = GPat Type

type UBinder = (String, Maybe Type)
type UIPat = GPat UBinder
type UPat  = GPat UBinder

type Var  = GVar LetUniq
type IVar = GVar IdxUniq
type TVar = GVar TypeUniq

data FullEnv v i t = FullEnv { lEnv :: Env Var  v
                             , iEnv :: Env IVar i
                             , tEnv :: Env TVar t }

type Vars = FullEnv () () ()

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

instance Semigroup (FullEnv v i t) where
  FullEnv x y z <> FullEnv x' y' z' = FullEnv (x<>x') (y<>y') (z<>z')

instance Monoid (FullEnv v i t) where
  mempty = FullEnv mempty mempty mempty
  mappend = (<>)

setLEnv :: (Env Var v -> Env Var v) -> FullEnv v i t -> FullEnv v i t
setLEnv update env = env {lEnv = update (lEnv env)}

setIEnv :: (Env IVar i -> Env IVar i) -> FullEnv v i t -> FullEnv v i t
setIEnv update env = env {iEnv = update (iEnv env)}

setTEnv :: (Env TVar t -> Env TVar t) -> FullEnv v i t -> FullEnv v i t
setTEnv update env = env {tEnv = update (tEnv env)}

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

fvsType :: Type -> Vars
fvsType ty = case ty of
  BaseType _    -> mempty
  TypeVar v     -> fvsVar setTEnv v
  ArrType t1 t2 -> fvsType t1 <> fvsType t2
  TabType t1 t2 -> fvsType t1 <> fvsType t2
  RecType r     -> foldMap fvsType r
  Forall _ t    -> fvsType t
  Exists t      -> fvsType t
  MetaTypeVar _ -> mempty
  NamedForall _ t -> fvsType t
  NamedExists _ t -> fvsType t

paren :: String -> String
paren s = "(" ++ s ++ ")"

varNames :: [Char] -> [VarName]
varNames prefixes = map nthName [0..]
  where nthName n | n < 26    = [prefixes !! n]
                  | otherwise = nthName (mod n 26) ++ show (div n 26)

instance Show BaseType where
  show t = case t of
    IntType  -> "Int"
    BoolType -> "Bool"
    RealType -> "Real"
    StrType  -> "Str"

instance Show Type where
  show t = showType (varNames ['a'..'c']) 0 t

showType :: [VarName] -> Int -> Type -> String
showType names depth t = case t of
  BaseType b  -> show b
  TypeVar v   -> getName v
  ArrType a b -> paren $ recur a ++ " -> " ++ recur b
  TabType a b -> paren $ recur a ++ " => " ++ recur b
  RecType r   -> printRecord recur typeRecPrintSpec r
  Forall n t -> let vs' = slice depth (depth + n) names
                in "A " ++ intercalate " " vs' ++ ". " ++ recurDeeper n t
  Exists t  -> "<exists>"
  MetaTypeVar (MetaVar v) -> "mv" ++ show v
  where slice start stop = take (stop - start) . drop start
        recur = showType names depth
        recurDeeper n = showType names (depth + n)
        getName v = case v of FV name -> name
                              BV i -> names !! (depth - i - 1)
