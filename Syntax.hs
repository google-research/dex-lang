module Syntax (Expr (..), Type (..), IdxSet, Builtin (..),
               UExpr (..), TopDecl (..), Command (..), CommandOutput (..),
               DeclInstr (..), CmdName (..), IdxExpr, Kind (..),
               LitVal (..), BaseType (..), Pat, UPat, Var, TVar, Except, Err (..),
               Vars, FullEnv (..), setLEnv, setTEnv, arity, numArgs, numTyArgs,
               (-->), (==>), Pass (..), strToBuiltin,
               raiseIOExcept, liftExcept, liftErrIO, assertEq, ignoreExcept,
               instantiateTVs, abstractTVs, subFreeTVs, HasTypeVars,
               fvsUExpr, freeTyVars,
              ) where

import Util
import Record
import Env
import Data.Semigroup
import Data.Foldable (toList)
import Data.Traversable
import Data.List (intercalate, elemIndex, nub)
import qualified Data.Map as M

import System.Console.Haskeline (throwIO, Interrupt (..))
import Data.Functor.Identity (Identity, runIdentity)
import Control.Monad.Except (MonadError, throwError)
import Control.Monad.State (State, execState, modify)
import Control.Applicative (liftA, liftA2, liftA3)

data Expr = Lit LitVal
          | Var Var
          | Builtin Builtin
          | Let Pat Expr Expr
          | Lam Pat Expr
          | App Expr Expr
          | For IdxSet Expr
          | Get Expr IdxExpr
          | Unpack Type Expr Expr
          | TLam [Kind] Expr
          | TApp Expr [Type]
          | RecCon (Record Expr)
          | BuiltinApp Builtin [Type] [Expr]
              deriving (Eq, Ord)

data Type = BaseType BaseType
          | TypeVar TVar
          | ArrType Type Type
          | TabType IdxSet Type
          | RecType (Record Type)
          | Forall [Kind] Type
          | Exists Type
             deriving (Eq, Ord)

type IdxSet = Type

data Kind = IdxSetKind | TyKind  deriving (Show, Eq, Ord)

data UExpr = ULit LitVal
           | UVar Var
           | UBuiltin Builtin
           | ULet UPat UExpr UExpr
           | ULam UPat UExpr
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
             | Sin | Cos | Tan | Iota | Doubleit
             | Hash | Rand | Randint
             | Fold | FoldDeFunc
               deriving (Eq, Ord, Show)

data ImpProgram = ImpProgram [Statement]

data Statement = VarAlloc VarName BaseType [Size]
               | VarFree  VarName
               | Assignment VarName [Index] ImpBuiltin [Size] [ImpOperand]
               | Loop Index Size [Statement]

data ImpOperand = ImpLit
                | ImpVar VarName [Index]

type Index = VarName
data Size = ConstSize Int | KnownSize VarName

type ImpBuiltin = Builtin

type UPat = RecTree VarName
type Pat  = RecTree Type

builtinNames = M.fromList [
  ("add", Add), ("sub", Sub), ("mul", Mul), ("pow", Pow), ("exp", Exp),
  ("log", Log), ("sqrt", Sqrt), ("sin", Sin), ("cos", Cos), ("tan", Tan),
  ("fold", Fold), ("iota", Iota), ("doubleit", Doubleit),
  ("hash", Hash), ("rand", Rand), ("randint", Randint)]

arity :: Builtin -> (Int, Int)
arity b = case b of
  Add      -> (0, 2)
  Mul      -> (0, 2)
  Sub      -> (0, 2)
  Iota     -> (0, 1)
  Fold     -> (3, 3)
  Doubleit -> (0, 1)
  Hash     -> (0, 2)
  Rand     -> (0, 1)
  Randint  -> (0, 2)

numArgs   = snd . arity
numTyArgs = fst . arity

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
                           , tEnv :: Env TVar t }  deriving (Show, Eq)

data Pass a b v t = Pass
  { lowerExpr   ::            a -> FullEnv v t -> IO (v, b),
    lowerUnpack :: VarName -> a -> FullEnv v t -> IO (v, t, b),
    lowerCmd    ::    Command a -> FullEnv v t -> IO (Command b) }

-- these should just be lenses
setLEnv :: (Env Var a -> Env Var b) -> FullEnv a t -> FullEnv b t
setLEnv update env = env {lEnv = update (lEnv env)}

setTEnv :: (Env TVar a -> Env TVar b) -> FullEnv v a -> FullEnv v b
setTEnv update env = env {tEnv = update (tEnv env)}
type Vars = FullEnv () ()

type Source = String
data TopDecl expr = TopDecl Source Vars (DeclInstr expr)
data DeclInstr expr = TopAssign VarName expr
                    | TopUnpack VarName expr
                    | EvalCmd (Command expr)  deriving (Show, Eq)

data CommandOutput = TextOut String
                   | PlotOut [Float] [Float]
                   | PlotMatOut [[Float]]
                       deriving (Show, Eq)

data Command expr = Command CmdName expr
                  | CmdResult CommandOutput
                  | CmdErr Err  deriving (Show, Eq)

data CmdName = EvalExpr | GetType | GetTyped | GetParse | DeFunc
             | GetLLVM  | EvalJit | TimeIt | ShowPersistVal
             | Plot | PlotMat
               deriving  (Show, Eq)


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
liftErrIO = either raiseIOExcept return

raiseIOExcept :: Err -> IO a
raiseIOExcept e =print e >> throwIO Interrupt

assertEq :: (Show a, Eq a) => a -> a -> String -> Except ()
assertEq x y s = if x == y then return () else Left (CompilerErr msg)
  where msg = s ++ ": " ++ show x ++ " != " ++ show y

ignoreExcept :: Except a -> a
ignoreExcept (Left e) = error $ show e
ignoreExcept (Right x) = x

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
  -- UAnnot e t     -> fvsUExpr e <> fvsType t
  UUnpack _ e body -> fvsUExpr e <> fvsUExpr body

paren :: String -> String
paren s = "(" ++ s ++ ")"

varNames :: [Char] -> [String]
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
  RecType r   -> printRecord recur typeRecPrintSpec r
  Forall kinds t -> "A " ++ spaceSep (take (length kinds) tVarNames) ++ ". "
                          ++ showType (kinds ++ env) t
  Exists body -> "E " ++ tVarNames !! depth ++ ". " ++
                 showType (IdxSetKind : env) body
  where recur = showType env
        depth = length env

spaceSep :: [String] -> String
spaceSep = intercalate " "

-- TODO: fix printing of pattern binders
showExpr :: (Int, [Kind]) -> Expr -> String
showExpr env@(depth, kinds) expr = case expr of
  Lit val      -> show val
  Var v        -> name v
  Builtin b    -> show b
  Let p e1 e2  -> paren $    "let " ++ printPat p ++ " = " ++ recur e1
                          ++ " in " ++ recurWith (length (toList p)) e2
  Lam p e      -> paren $ "lam " ++ printPat p ++ ": "
                                 ++ recurWith (length (toList p)) e
  App e1 e2    -> paren $ recur e1 ++ " " ++ recur e2
  For t e      -> paren $ "for " ++ showBinder depth kinds t ++ ": " ++ recurWith 1 e
  Get e ie     -> recur e ++ "." ++ name ie
  RecCon r     -> printRecord recur defaultRecPrintSpec r
  BuiltinApp b ts exprs -> paren $ show b ++ "[" ++ showTypes ts ++ "]"
                                         ++ paren (spaceSep (map recur exprs))
  Unpack t e1 e2 -> paren $ "unpack {" ++ showBinder depth (IdxSetKind:kinds) t
                             ++ ", " ++ tVarNames !! (length kinds)
                             ++ "} = " ++ recur e1
                             ++ " in " ++ showExpr (depth+1, IdxSetKind:kinds) e2
  TLam kinds' expr ->
    "LAM " ++ spaceSep (zipWith (\k v -> v ++ "::" ++ show k)
                        kinds' tVarNames) ++ ": "
           ++ showExpr (depth, kinds' ++ kinds) expr

  TApp expr ts -> recur expr ++ "[" ++ showTypes ts ++ "]"
  where recur = showExpr env
        showTypes ts = spaceSep (map (showType kinds) ts)
        recurWith n = showExpr (depth + n, kinds)
        showBinder i kinds ty = lVarNames !! i ++ "::" ++ showType kinds ty
        name = getName lVarNames depth
        printPat p = let depth' = depth + length (toList p) - 1
                         show' (i, ty) = showBinder (depth' - i) kinds ty
                     in printRecTree show' (enumerate p)

getName :: [String] -> Int -> GVar i -> String
getName names depth v = case v of
  FV (NamedVar name) -> name
  FV (TempVar i) -> "<tmp-" ++ show i ++ ">"
  BV i -> let i' = depth - i - 1
          in if i' >= 0
             then names !! i'
             else "<BV " ++ show i ++ ">"

type TempVar = Int

freeTyVars :: HasTypeVars a => a -> [VarName]
freeTyVars x = nub $ execState (subAtDepth 0 collectVars x) []
  where collectVars :: Int -> TVar -> State [VarName] Type
        collectVars _ v = do case v of BV _ -> return ()
                                       FV v' -> modify (v':)
                             return (TypeVar v)

instantiateTVs :: HasTypeVars a => [Type] -> a -> a
instantiateTVs vs x = runIdentity $ subAtDepth 0 sub x
  where sub depth v = return $ case v of
                        BV i | i >= depth -> vs !! i
                        _ -> TypeVar v

abstractTVs :: HasTypeVars a => [VarName] -> a -> a
abstractTVs vs x = runIdentity $ subAtDepth 0 sub x
  where sub depth v = return $ TypeVar $ case v of
                        BV _  -> v
                        FV v' -> case elemIndex v' vs of
                                   Nothing -> v
                                   Just i  -> BV (depth + i)

subFreeTVs :: (HasTypeVars a, Applicative f) => (VarName -> f Type) -> a -> f a
subFreeTVs f expr = subAtDepth 0 f' expr
  where f' _ v = case v of BV _  -> pure (TypeVar v)
                           FV v' -> f v'

class HasTypeVars a where
  subAtDepth :: Applicative f => Int -> (Int -> TVar -> f Type) -> a -> f a

instance (HasTypeVars a, HasTypeVars b) => HasTypeVars (a,b) where
  subAtDepth d f (x, y) = liftA2 (,) (subAtDepth d f x) (subAtDepth d f y)

instance HasTypeVars Type where
  subAtDepth d f ty = case ty of
      BaseType b    -> pure ty
      TypeVar v     -> f d v
      ArrType a b   -> liftA2 ArrType (recur a) (recur b)
      TabType a b   -> liftA2 TabType (recur a) (recur b)
      RecType r     -> liftA RecType (traverse recur r)
      Exists body   -> liftA Exists (recurWith 1 body)
      Forall kinds body -> liftA (Forall kinds) (recurWith (length kinds) body)
    where recur = subAtDepth d f
          recurWith d' = subAtDepth (d + d') f

instance HasTypeVars Expr where
  subAtDepth d f expr = case expr of
      Lit c -> pure $ Lit c
      Var v -> pure $ Var v
      Builtin b -> pure $ Builtin b
      Let p bound body -> liftA3 Let (traverse recurTy p) (recur bound) (recur body)
      Lam p body       -> liftA2 Lam (traverse recurTy p) (recur body)
      App fexpr arg    -> liftA2 App (recur fexpr) (recur arg)
      For t body       -> liftA2 For (recurTy t) (recur body)
      Get e ie         -> liftA2 Get (recur e) (pure ie)
      RecCon r         -> liftA  RecCon (traverse recur r)
      Unpack t bound body -> liftA3 Unpack (recurWithTy 1 t) (recur bound) (recurWith 1 body)
      TLam kinds expr   -> liftA  (TLam kinds) (recurWith (length kinds) expr)
      TApp expr ts      -> liftA2 TApp (recur expr) (traverse recurTy ts)
      BuiltinApp b ts v -> liftA2 (BuiltinApp b) (traverse recurTy ts) (traverse recur v)
    where recur   = subAtDepth d f
          recurTy = subAtDepth d f
          recurWith   d' = subAtDepth (d + d') f
          recurWithTy d' = subAtDepth (d + d') f
