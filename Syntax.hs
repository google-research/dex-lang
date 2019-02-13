module Syntax (GenExpr (..), GenType (..), GenIdxSet,
               Expr, Type, IdxSet, Builtin (..),
               UExpr (..), TopDecl (..), Command (..),
               DeclInstr (..), CmdName (..), IdxExpr, Kind (..),
               LitVal (..), BaseType (..),
               Var, TVar, Except, Err (..),
               Vars, FullEnv (..), setLEnv, setTEnv,
               fvsUExpr, (-->), (==>), Pass (..), strToBuiltin,
               subTy, subExpr, bindMetaTy, bindMetaExpr,
               noLeaves, checkNoLeaves, liftExcept, liftErrIO, assertEq,
               instantiateType, instantiateBody, joinType) where

import Util
import Record
import Env
import Data.Semigroup
import Data.Traversable
import Data.List (intercalate, elemIndex)
import qualified Data.Map as M

import System.Console.Haskeline (throwIO, Interrupt (..))
import Control.Monad.Except (MonadError, throwError)
import Control.Applicative (liftA, liftA2, liftA3)

data GenExpr a = Lit LitVal
               | Var Var
               | Builtin Builtin
               | Let (GenType a) (GenExpr a) (GenExpr a)
               | Lam (GenType a) (GenExpr a)
               | App (GenExpr a) (GenExpr a)
               | For (GenIdxSet a) (GenExpr a)
               | Get (GenExpr a) IdxExpr
               | Unpack (GenExpr a) (GenExpr a)
               | TLam [Kind] (GenExpr a)
               | TApp (GenExpr a) [(GenType a)]
                   deriving (Eq, Ord)

data GenType a = Meta a
               | BaseType BaseType
               | TypeVar TVar
               | ArrType (GenType a) (GenType a)
               | TabType (GenIdxSet a) (GenType a)
               | Forall [Kind] (GenType a)
               | Exists (GenType a)
                  deriving (Eq, Ord)

type GenIdxSet a = GenType a -- Constructed with Meta or TypeVar

type Type   = GenType   ()
type Expr   = GenExpr   ()
type IdxSet = GenIdxSet ()

data Kind = IdxSetKind | TyKind  deriving (Show, Eq, Ord)

data UExpr = ULit LitVal
           | UVar Var
           | UBuiltin Builtin
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
            | RealLit Double
            | StrLit  String
                 deriving (Eq, Ord)

data BaseType = IntType | BoolType | RealType | StrType
                   deriving (Eq, Ord)

data Builtin = Add | Sub | Mul | Pow | Exp | Log | Sqrt
             | Sin | Cos | Tan | Reduce | Iota | Sum' | Doubleit
             | Hash | Rand | Randint  deriving (Eq, Ord, Show)

builtinNames = M.fromList [
  ("add", Add), ("sub", Sub), ("mul", Mul), ("pow", Pow), ("exp", Exp),
  ("log", Log), ("sqrt", Sqrt), ("sin", Sin), ("cos", Cos), ("tan", Tan),
  ("reduce", Reduce), ("iota", Iota), ("sum", Sum'), ("doubleit", Doubleit),
  ("hash", Hash), ("rand", Rand), ("randint", Randint)]

strToBuiltin :: String -> Maybe Builtin
strToBuiltin name = M.lookup name builtinNames

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

data Pass a b v t = Pass
  { lowerExpr   ::            a -> FullEnv v t -> IO (v, b),
    lowerUnpack :: VarName -> a -> FullEnv v t -> IO (v, t, b),
    lowerCmd    ::    Command a -> FullEnv v t -> IO (Command b) }

-- these should just be lenses
setLEnv :: (Env Var v -> Env Var v) -> FullEnv v t -> FullEnv v t
setLEnv update env = env {lEnv = update (lEnv env)}

setTEnv :: (Env TVar t -> Env TVar t) -> FullEnv v t -> FullEnv v t
setTEnv update env = env {tEnv = update (tEnv env)}

type Vars = FullEnv () ()

type Source = String
data TopDecl expr = TopDecl Source Vars (DeclInstr expr)
data DeclInstr expr = TopAssign VarName expr
                    | TopUnpack VarName expr
                    | EvalCmd (Command expr)  deriving (Show, Eq)

data Command expr = Command CmdName expr
                  | CmdResult String
                  | CmdErr Err  deriving (Show, Eq)

data CmdName = EvalExpr | GetType | GetTyped | GetParse
             | GetLLVM  | EvalJit | TimeIt  deriving  (Show, Eq)

data Err = ParseErr String
         | UnificationErr String String
         | TypeErr String
         | InfiniteTypeErr
         | UnboundVarErr VarName
         | RepVarPatternErr VarName
         | CompilerErr String
         | PrintErr String
         | NotImplementedErr String
  deriving (Eq)

type Except a = Either Err a

liftExcept :: (MonadError e m) => Either e a -> m a
liftExcept = either throwError return

liftErrIO :: Except a -> IO a
liftErrIO = either (\e -> print e >> throwIO Interrupt) return

assertEq :: (Show a, Eq a) => a -> a -> String -> Except ()
assertEq x y s = if x == y then return () else Left (CompilerErr msg)
  where msg = s ++ ": " ++ show x ++ " != " ++ show y

instance Traversable TopDecl where
  traverse f (TopDecl s fvs instr) = fmap (TopDecl s fvs) $ traverse f instr

instance Traversable DeclInstr where
  traverse f (TopAssign v expr) = fmap (TopAssign v) (f expr)
  traverse f (TopUnpack v expr) = fmap (TopUnpack v) (f expr)
  traverse f (EvalCmd cmd) = fmap EvalCmd $ traverse f cmd

instance Traversable Command where
  traverse f (Command cmd expr) = fmap (Command cmd) (f expr)
  traverse f (CmdResult s) = pure $ CmdResult s

instance Show Err where
  show e = case e of
    ParseErr s -> s
    UnificationErr t1 t2 -> ("Type error: can't unify "
                             ++ t1 ++ " and " ++ t2)
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
  UBuiltin _     -> mempty
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
  Meta _ -> mempty

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

instance Show a => Show (GenExpr a) where
  show = showExpr (0, [])

instance Show a => Show (GenType a) where
  show = showType []

showType :: Show a => [Kind] -> GenType a -> String
showType env t = case t of
  Meta v -> show v
  BaseType b  -> show b
  TypeVar v   -> getName tVarNames depth v
  ArrType a b -> paren $ recur a ++ " -> " ++ recur b
  TabType a b -> recur a ++ "=>" ++ recur b
  Forall kinds t -> "A " ++ spaceSep (take (length kinds) tVarNames) ++ ". "
                          ++ showType (kinds ++ env) t
  Exists body -> "E " ++ tVarNames !! depth ++ ". " ++
                 showType (IdxSetKind : env) body
  where recur = showType env
        depth = length env

spaceSep :: [String] -> String
spaceSep = intercalate " "

showExpr :: Show a => (Int, [Kind]) -> GenExpr a -> String
showExpr env@(depth, kinds) expr = case expr of
  Lit val      -> show val
  Var v        -> name v
  Let t e1 e2  -> paren $    "let " ++ showBinder t ++ " = " ++ recur e1
                          ++ " in " ++ recurWith e2
  Lam t e      -> paren $ "lam " ++ showBinder t ++ ": " ++ recurWith e
  App e1 e2    -> paren $ recur e1 ++ " " ++ recur e2
  For t e      -> paren $ "for " ++ showBinder t ++ ": " ++ recurWith e
  Get e ie     -> recur e ++ "." ++ name ie
  Unpack e1 e2 -> paren $ "unpack {" ++ lVarNames !! depth
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

instance Functor GenExpr where
  fmap = fmapDefault

instance Foldable GenExpr where
  foldMap = foldMapDefault

instance Traversable GenExpr where
  traverse f expr = case expr of
    Lit c -> pure $ Lit c
    Var v -> pure $ Var v
    Builtin b -> pure $ Builtin b
    Let t bound body  -> liftA3 Let (recurTy t) (recur bound) (recur body)
    Lam t body        -> liftA2 Lam (recurTy t) (recur body)
    App fexpr arg     -> liftA2 App (recur fexpr) (recur arg)
    For t body        -> liftA2 For (recurTy t) (recur body)
    Get e ie          -> liftA2 Get (recur e) (pure ie)
    Unpack bound body -> liftA2 Unpack (recur bound) (recur body)
    TLam kinds expr   -> liftA  (TLam kinds) (recur expr)
    TApp expr ts      -> liftA2 TApp (recur expr) (traverse recurTy ts)
    where recur = traverse f
          recurTy = traverse f

instance Functor GenType where
  fmap = fmapDefault

instance Foldable GenType where
  foldMap = foldMapDefault

instance Traversable GenType where
  traverse f ty = case ty of
    Meta v            -> liftA Meta (f v)
    BaseType b        -> pure $ BaseType b
    TypeVar v         -> pure $ TypeVar v
    ArrType a b       -> liftA2 ArrType (recur a) (recur b)
    TabType a b       -> liftA2 TabType (recur a) (recur b)
    Forall kinds body -> liftA  (Forall kinds) (recur body)
    Exists body       -> liftA  Exists (recur body)
    where recur = traverse f

bindMetaTy :: Eq a => [a] -> GenType a -> GenType a
bindMetaTy vs = subTyDepth 0 (deBruijnSub vs)
  where sub d v = case elemIndex v vs of
                    Just i  -> TypeVar (BV (d + i))
                    Nothing -> Meta v

bindMetaExpr :: Eq a => [a] -> GenExpr a -> GenExpr a
bindMetaExpr vs = subExprDepth 0 (deBruijnSub vs)

joinType :: GenType (GenType a) -> GenType a
joinType = subTy id

subTy :: Sub a b -> GenType a -> GenType b
subTy f t = subTyDepth 0 (const f) t

subExpr :: Sub a b -> GenExpr a -> GenExpr b
subExpr f t = subExprDepth 0 (const f) t

type Sub a b = a -> GenType b

deBruijnSub :: Eq a => [a] -> (Int -> Sub a a)
deBruijnSub vs d v = case elemIndex v vs of
                       Just i  -> TypeVar (BV (d + i))
                       Nothing -> Meta v

subTyDepth :: Int -> (Int -> Sub a b) -> GenType a -> GenType b
subTyDepth d f t = case t of
  Meta v        -> f d v
  BaseType b    -> BaseType b
  TypeVar  v    -> TypeVar v
  ArrType a b   -> ArrType (recur a) (recur b)
  TabType a b   -> TabType (recur a) (recur b)
  Exists body -> Exists (recurWith 1 body)
  Forall kinds body -> Forall kinds (recurWith (length kinds) body)
  where recur = subTyDepth d f
        recurWith d' = subTyDepth (d + d') f

subExprDepth ::  Int -> (Int -> Sub a b) -> GenExpr a -> GenExpr b
subExprDepth d f expr = case expr of
  Lit c -> Lit c
  Var v -> Var v
  Builtin b -> Builtin b
  Let t bound body -> Let (recurTy t) (recur bound) (recur body)
  Lam t body       -> Lam (recurTy t) (recur body)
  App fexpr arg    -> App (recur fexpr) (recur arg)
  For t body       -> For (recurTy t) (recur body)
  Get e ie         -> Get (recur e) ie
  Unpack bound body -> Unpack (recur bound) (recurWith 1 body)
  TLam kinds expr     -> TLam kinds (recurWith (length kinds) expr)
  TApp expr ts        -> TApp (recur expr) (map recurTy ts)

  where recur = subExprDepth d f
        recurWith d' = subExprDepth (d + d') f
        recurTy = subTyDepth d f

checkNoLeaves :: Traversable f => f a -> Except (f b)
checkNoLeaves = traverse check
  where check _ = Left $ CompilerErr "Found metavariable"

noLeaves :: Traversable f => f a -> f b
noLeaves x = case checkNoLeaves x of Right x' -> x'
                                     Left e -> error $ show e

instantiateType :: [GenType a] -> GenType a -> GenType a
instantiateType ts t = case t of
  Forall kinds body | nt == length kinds -> instantiateBody ts' body
  Exists       body | nt == 1            -> instantiateBody ts' body
  ty -> case ts of [] -> ty
  where nt = length ts
        ts' = map Just ts

instantiateBody :: [Maybe (GenType a)] -> GenType a -> GenType a
instantiateBody env t = case t of
  BaseType _  -> t
  TypeVar (BV v) -> case env !! v of
                      Just t' -> t'
                      Nothing -> TypeVar (BV v)
  ArrType a b -> ArrType (recur a) (recur b)
  TabType a b -> TabType (recur a) (recur b)
  Forall kinds body -> let env' = map (const Nothing) kinds ++ env
                       in Forall kinds $ instantiateBody env' body
  Meta _ -> t
  where recur = instantiateBody env
