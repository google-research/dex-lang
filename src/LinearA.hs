module LinearA where

import Prelude hiding (lookup)
import Control.Monad
import Control.Monad.Except
import Data.Foldable
import Data.List (intercalate)
import Data.Functor.Identity
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.Map.Strict ((!))

type Var = String
data MixedType = MixedType [Type] [Type]
                 deriving Eq
data Type = FloatType | TupleType [Type]
            deriving Eq
data Expr = Ret [Var] [Var]
          | LetMixed     [Var] [Var] Expr Expr
          | LetUnpack    [Var]       Var  Expr
          | LetUnpackLin [Var]       Var  Expr
          | App FuncName [Var] [Var]
          -- Additional non-linear expressions
          | Var Var
          | Lit Float
          | Tuple [Expr]
          | UnOp  UnOp  Expr
          | BinOp BinOp Expr Expr
          -- Additional linear expressions
          | LVar Var
          | LTuple [Expr]
          | LAdd   Expr Expr
          | LScale Expr Expr
          | LZero  [Var]
          | Dup  Expr
          | Drop Expr
data UnOp  = Sin | Cos | Exp
data BinOp = Add | Mul

type FuncName = String
data FuncDef = FuncDef [(Var, Type)] [(Var, Type)] MixedType Expr
data Program = Program (M.Map FuncName FuncDef)

data Value = FloatVal Float | TupleVal [Value]
             deriving Eq
data Result = Result [Value] [Value]
              deriving Eq

instance Show Value where
  show (FloatVal f) = show f
  show (TupleVal vs) = "(" ++ intercalate ", " (show <$> vs) ++ ")"
instance Show Result where
  show (Result vs linVs) = "(" ++ intercalate ", " (show <$> vs) ++ "; "
                               ++ intercalate ", " (show <$> linVs) ++ ")"

-------------------- Evaluation --------------------

type EvalEnv = M.Map Var Value
eval :: Program -> EvalEnv -> Expr -> Result
eval prog@(Program defs) env expr = case expr of
  Ret nonlin lin -> Result ((env !) <$> nonlin) ((env !) <$> lin)
  LetMixed vs linVs e1 e2 -> do
    let Result vals linVals = eval prog env e1
    let env' = envExt env (vs ++ linVs) (vals ++ linVals)
    eval prog env' e2
  LetUnpack vs v e -> do
    let TupleVal vals = env ! v
    let env' = envExt env vs vals
    eval prog env' e
  LetUnpackLin vs v e -> do
    let TupleVal vals = env ! v
    let env' = envExt env vs vals
    eval prog env' e
  App funcName args linArgs -> do
    let FuncDef formals linFormals _ funcExpr = defs ! funcName
    let argVals = (env !) <$> args
    let linArgVals = (env !) <$> linArgs
    let appEnv = envExt mempty (fst <$> (formals ++ linFormals)) (argVals ++ linArgVals)
    eval prog appEnv funcExpr
  -- Nonlinear expressions
  Var v     -> result $ env ! v
  Lit f     -> result $ FloatVal f
  Tuple es  -> result $ TupleVal $ fromResult . eval prog env <$> es
  UnOp op e -> do
    let Result [FloatVal x] [] = eval prog env e
    result $ FloatVal $ f x
    where
      f = case op of
        Sin -> sin
        Cos -> cos
        Exp -> exp
  BinOp op le re -> do
    let Result [FloatVal lv] [] = eval prog env le
    let Result [FloatVal rv] [] = eval prog env re
    result $ FloatVal $ f lv rv
    where
      f = case op of
        Add -> (+)
        Mul -> (*)
  -- Linear expressions
  LVar v -> linResult $ env ! v
  LTuple es -> linResult $ TupleVal $ fromLinResult . eval prog env <$> es
  LAdd le re -> do
    let Result [] [FloatVal lv] = eval prog env le
    let Result [] [FloatVal rv] = eval prog env re
    linResult $ FloatVal $ lv + rv
  LScale se le -> do
    let Result [FloatVal sv] [] = eval prog env se
    let Result [] [FloatVal lv] = eval prog env le
    linResult $ FloatVal $ sv * lv
  LZero _ -> linResult $ FloatVal 0
  Dup   e -> do
    let Result [] [v] = eval prog env e
    Result [] [v, v]
  Drop  _ -> Result [] []
  where
    result :: Value -> Result
    result v = Result [v] []

    fromResult :: Result -> Value
    fromResult (Result [v] []) = v
    fromResult _ = error "Unexpected result type"

    linResult :: Value -> Result
    linResult v = Result [] [v]

    fromLinResult :: Result -> Value
    fromLinResult (Result [] [v]) = v
    fromLinResult _ = error "Unexpected result type"

-------------------- Free variable querying --------------------

data FreeVars = FV (S.Set Var) (S.Set Var)
instance Semigroup FreeVars where
  (FV v lv) <> (FV v' lv') = FV (v <> v') (lv <> lv')
instance Monoid FreeVars where
  mempty = FV mempty mempty

freeVars :: Expr -> FreeVars
freeVars expr = case expr of
  Ret vs linVs -> FV (S.fromList vs) (S.fromList linVs)
  LetMixed vs linVs e1 e2 -> FV
    (freeE1    `S.union` (freeE2    `S.difference` S.fromList vs   ))
    (freeLinE1 `S.union` (freeLinE2 `S.difference` S.fromList linVs))
    where
      FV freeE1 freeLinE1 = freeVars e1
      FV freeE2 freeLinE2 = freeVars e2
  Lit _  -> mempty
  Var v  -> FV (S.singleton v) mempty
  LVar v -> FV mempty (S.singleton v)
  LetUnpack vs v e -> FV (S.singleton v <> (free `S.difference` S.fromList vs)) freeLin
    where FV free freeLin = freeVars e
  LetUnpackLin vs v e -> FV free (S.singleton v <> (freeLin `S.difference` S.fromList vs))
    where FV free freeLin = freeVars e
  App _ vs linVs -> FV (S.fromList vs) (S.fromList linVs)
  Tuple es       -> foldMap freeVars es
  UnOp  _ e      -> freeVars e
  BinOp _ le re  -> freeVars le <> freeVars re
  LTuple es      -> foldMap freeVars es
  LAdd    le re  -> freeVars le <> freeVars re
  LScale  se le  -> freeVars se <> freeVars le
  LZero   vs     -> FV mempty $ S.fromList vs
  Dup  e -> freeVars e
  Drop e -> freeVars e

-------------------- Type checking --------------------

type TypeEnv = (M.Map Var Type, M.Map Var Type)
typecheck :: Program -> TypeEnv -> Expr -> Either String MixedType
typecheck prog@(Program progMap) tenv@(env, linEnv) expr = case expr of
  Ret vs linVs -> do
    check "Ret non-linear environment mismatched" $ S.fromList vs == M.keysSet env
    check "Repeated linear returns" $ unique linVs
    check "Ret linear environment mismatched" $ S.fromList linVs == M.keysSet linEnv
    return $ MixedType ((env !) <$> vs) ((linEnv !) <$> linVs)
  LetMixed vs linVs e1 e2 -> do
    let FV freeE1 freeLinE1 = freeVars e1
    let FV freeE2 freeLinE2 = freeVars e2
    check "shadowing in binders" $ unique (vs ++ linVs)
    check "LetMixed: non-linear environment mismatched" $
      S.union freeE1 (freeE2 `S.difference` S.fromList vs) == M.keysSet env
    check "LetMixed: linear variable consumed twice" $
      S.disjoint freeLinE1 (freeLinE2 `S.difference` S.fromList linVs)
    check "LetMixed: linear environment mismatched" $
      S.union freeLinE1 (freeLinE2 `S.difference` S.fromList linVs) == M.keysSet linEnv
    let e1Env = (env `M.restrictKeys` freeE1, linEnv `M.restrictKeys` freeLinE1)
    MixedType vTys linVTys <- typecheck prog e1Env e1
    let e2Env = ( envExt (env `M.restrictKeys` freeE2) vs vTys
                , envExt (linEnv `M.restrictKeys` freeLinE2) linVs linVTys)
    typecheck prog e2Env e2
  Lit f -> do
    check "Lit: non-empty environments" $ null env && null linEnv
    return $ MixedType [FloatType] []
  Var v -> do
    check "Var: non-empty linear env" $ null linEnv
    check "Var: non-singleton env" $ (S.singleton v == M.keysSet env)
    return $ MixedType [env ! v] []
  LVar v -> do
    check "LVar: non-empty env" $ null env
    check "LVar: non-singleton linear env" $ S.singleton v == M.keysSet linEnv
    return $ MixedType [] [linEnv ! v]
  App f args linArgs -> do
    let FuncDef formals linFormals resTy _ = progMap ! f
    -- Use (L)Tuple checking rules to verify that references to args are valid
    typecheck prog (env, mempty)    $ Tuple  $ Var  <$> args
    typecheck prog (mempty, linEnv) $ LTuple $ LVar <$> linArgs
    return $ resTy
  Tuple es -> do
    let (free, freeLin) = unzip $ ((\(FV a b) -> (a, b)) . freeVars) <$> es
    check "Tuple: non-linear environment mismatched" $ fold free == M.keysSet env
    check "Tuple: linear variable consumed twice" $ S.size (fold freeLin) == sum (S.size <$> freeLin)
    check "Tuple: linear environment mismatched" $ fold freeLin == M.keysSet linEnv
    tys <- forM (zip3 free freeLin es) $ \(f, fl, e) -> do
      let eEnv = (env `M.restrictKeys` f, linEnv `M.restrictKeys` fl)
      eTy <- typecheck prog eEnv e
      case eTy of
        MixedType [ty] [] -> return ty
        _ -> throwError "Tuple: unexpected element type"
    return $ MixedType [TupleType tys] []
  _ -> undefined
  -- TODO:
  -- LetUnpack    [Var]       Var  Expr
  -- LetUnpackLin [Var]       Var  Expr
  -- UnOp  UnOp  Expr
  -- BinOp BinOp Expr Expr
  -- LTuple [Expr]
  -- LAdd   Expr Expr
  -- LScale Expr Expr
  -- LZero  [Var]
  -- Dup  Expr
  -- Drop Expr

isFuncTypeCorrect :: Program -> FuncName -> Bool
isFuncTypeCorrect prog@(Program funcMap) name = case typecheck prog env body of
  Left  _  -> False
  Right ty -> ty == resultType
  where
    FuncDef formals linFormals resultType body = funcMap ! name
    env = (M.fromList formals, M.fromList linFormals)

isProgramTypeCorrect :: Program -> Bool
isProgramTypeCorrect prog@(Program progMap) = foldl (&&) True $ isFuncTypeCorrect prog <$> M.keys progMap

-------------------- Helpers --------------------

unique :: Foldable f => f Var -> Bool
unique vs = S.size (S.fromList $ toList vs) == length vs

envExt :: Ord k => M.Map k v -> [k] -> [v] -> M.Map k v
envExt env vs vals = foldl (\env (k, v) -> M.insert k v env) env $ zip vs vals

check :: MonadError e m => e -> Bool -> m ()
check err cond = unless cond $ throwError err
