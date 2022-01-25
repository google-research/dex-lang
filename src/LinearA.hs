module LinearA where

import Prelude hiding (lookup)
import Control.Monad
import Control.Monad.Except
import Data.Foldable
import Data.List (intercalate)
import Data.Functor ((<&>))
import Data.String (IsString(..))
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import GHC.Stack
import Prettyprinter

data Var = MkVar String Int
         deriving (Eq, Ord)

data MixedType = MixedType [Type] [Type]
                 deriving (Eq, Show)
data Type = FloatType | TupleType [Type]
            deriving (Eq, Show)
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
          | LZero
          | Dup  Expr
          | Drop Expr
          deriving Show
data UnOp  = Sin | Cos | Exp deriving Show
data BinOp = Add | Mul deriving Show

type FuncName = String
data FuncDef = FuncDef [(Var, Type)] [(Var, Type)] MixedType Expr
               deriving Show
data Program = Program (M.Map FuncName FuncDef)
               deriving Show

data Value = FloatVal Float | TupleVal [Value]
             deriving Eq
data Result = Result [Value] [Value]
              deriving Eq

instance IsString Var where
  fromString s = MkVar s 0

instance Show Var where
  show (MkVar s 0) = s
  show (MkVar s n) = s ++ "#" ++ show n
instance Show Value where
  show (FloatVal f) = show f
  show (TupleVal vs) = "(" ++ intercalate ", " (show <$> vs) ++ ")"
instance Show Result where
  show (Result vs linVs) = "(" ++ intercalate ", " (show <$> vs) ++ "; "
                               ++ intercalate ", " (show <$> linVs) ++ ")"

-------------------- Pretty printing --------------------

instance Pretty Program where
  pretty (Program progMap) = vcat $ M.toList progMap <&> \(fname, def) -> "def" <+> pretty fname <+> pretty def
instance Pretty FuncDef where
  pretty (FuncDef vs vs' (MixedType rtys rtys') body) =
    parens (prettyFormals vs <> " ;" <+> prettyFormals vs') <+> (nest 2 $
      softline' <> "->" <+> encloseSep "(" "" ", " (pretty <$> rtys) <>
      "; " <> encloseSep "" ")" ", " (pretty <$> rtys') <+> "=" <> hardline <> pretty body)
    where
      prettyFormals vs = cat $ punctuate ", " $ vs <&> \(v, ty) -> pretty v <> ":" <> pretty ty
instance Pretty Var where
  pretty v = fromString $ show v
instance Pretty Type where
  pretty = \case
    FloatType     -> "Float"
    TupleType tys -> tupled $ pretty <$> tys
instance Pretty Expr where
  pretty = \case
    Ret vs vs' -> prettyMixedVars vs vs'
    LetMixed vs vs' e1 e2 -> "let" <+> prettyMixedVars vs vs' <+> "=" <> (nest 2 $ group $ line <> pretty e1) <> hardline <> pretty e2
    LetUnpack vs v e -> "explode" <+> prettyMixedVars vs [] <+> "=" <+> pretty v <> hardline <> pretty e
    LetUnpackLin vs' v e -> "explode" <+> prettyMixedVars [] vs' <+> "=" <+> pretty v <> hardline <> pretty e
    App funcName vs vs' -> pretty funcName <> prettyMixedVars vs vs'
    Var v -> pretty v
    Lit v -> pretty v
    Tuple es -> tupled $ pretty <$> es
    UnOp Sin e -> "sin" <+> parens (pretty e)
    UnOp Cos e -> "cos" <+> parens (pretty e)
    UnOp Exp e -> "exp" <+> parens (pretty e)
    BinOp Add e1 e2 -> parens (pretty e1) <+> "+" <+> parens (pretty e2)
    BinOp Mul e1 e2 -> parens (pretty e1) <+> "*" <+> parens (pretty e2)
    LVar v -> pretty v
    LTuple es -> tupled $ pretty <$> es
    LAdd e1 e2 -> pretty $ BinOp Add e1 e2
    LScale es el -> pretty $ BinOp Mul es el
    LZero -> "zero"
    Dup e -> "dup" <+> parens (pretty e)
    Drop e -> "drop" <+> parens (pretty e)
    where
      prettyMixedVars :: [Var] -> [Var] -> Doc ann
      prettyMixedVars vs vs' = group $ "(" <> fillSep (pretty <$> vs) <> line' <> "; " <> fillSep (pretty <$> vs') <> ")"

-------------------- Evaluation --------------------

type EvalEnv = M.Map Var Value
evalFunc :: Program -> FuncName -> [Value] -> [Value] -> Result
evalFunc prog@(Program defs) funcName vals vals' = do
  let FuncDef formals linFormals _ funcExpr = defs ! funcName
  let appEnv = envExt mempty (fst <$> (formals ++ linFormals)) (vals ++ vals')
  eval prog appEnv funcExpr

eval :: Program -> EvalEnv -> Expr -> Result
eval prog env expr = case expr of
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
  App funcName args linArgs ->
    evalFunc prog funcName ((env !) <$> args) ((env !) <$> linArgs)
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
  LZero -> linResult $ FloatVal 0
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

data FreeVars = FV { getFree :: (S.Set Var), getFreeLin :: (S.Set Var) }
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
  LZero          -> mempty
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
  LetUnpack vs v e -> do
    let FV free freeLin = freeVars e
    check "shadowing in binders" $ unique vs
    check "LetUnpack: non-linear environment mismatched" $
      M.keysSet env == S.insert v (free `S.difference` S.fromList vs)
    check "LetUnpack: linear environment mismatched" $
      M.keysSet linEnv == freeLin
    case env ! v of
      TupleType tys -> do
        check "" $ length tys == length vs
        typecheck prog (envExt (env `M.restrictKeys` free) vs tys, linEnv) e
      _ -> throwError "Unpacking a non-tuple type"
  LetUnpackLin vs v e -> do
    let FV free freeLin = freeVars e
    check "shadowing in binders" $ unique vs
    check "LetUnpackLin: non-linear environment mismatched" $
      M.keysSet env == free
    check "LetUnpackLin: linear environment mismatched" $
       (M.keysSet linEnv `S.difference` S.singleton v) `S.union` (S.fromList vs) == freeLin
    case linEnv ! v of
      TupleType tys -> do
        check "" $ length tys == length vs
        typecheck prog (env, envExt (M.delete v linEnv) vs tys) e
      _ -> throwError "Unpacking a non-tuple type"
  Lit _ -> do
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
    let FuncDef _ _ resTy _ = progMap ! f
    -- Use (L)Tuple checking rules to verify that references to args are valid
    void $ typecheck prog (env, mempty)    $ Tuple  $ Var  <$> args
    void $ typecheck prog (mempty, linEnv) $ LTuple $ LVar <$> linArgs
    return $ resTy
  Tuple exprs -> do
    envs <- splitEnv exprs
    tys <- forM (zip envs exprs) $ \(env, expr) -> do
      eTy <- typecheck prog env expr
      case eTy of
        MixedType [ty] [] -> return ty
        _ -> throwError "Tuple: unexpected element type"
    return $ MixedType [TupleType tys] []
  UnOp _ e -> do
    typecheckEq tenv e $ MixedType [FloatType] []
    return $ MixedType [FloatType] []
  BinOp _ le re -> do
    ~[lenv, renv] <- splitEnv [le, re]
    typecheckEq lenv le $ MixedType [FloatType] []
    typecheckEq renv re $ MixedType [FloatType] []
    return $ MixedType [FloatType] []
  LTuple exprs -> do
    envs <- splitEnv exprs
    tys <- forM (zip envs exprs) $ \(env, expr) -> do
      eTy <- typecheck prog env expr
      case eTy of
        MixedType [] [ty] -> return ty
        _ -> throwError "Tuple: unexpected element type"
    return $ MixedType [] [TupleType tys]
  LAdd le re -> do
    ~[lenv, renv] <- splitEnv [le, re]
    typecheckEq lenv le $ MixedType [] [FloatType]
    typecheckEq renv re $ MixedType [] [FloatType]
    return $ MixedType [] [FloatType]
  LScale se le -> do
    ~[senv, lenv] <- splitEnv [se, le]
    typecheckEq senv se $ MixedType [FloatType] []
    typecheckEq lenv le $ MixedType [] [FloatType]
    return $ MixedType [] [FloatType]
  LZero -> do
    check "LZero: non-empty environment" $ null env && null linEnv
    return $ MixedType [] [FloatType]
  Dup e -> do
    ty <- typecheck prog tenv e
    case ty of
      MixedType [] [lty] -> return $ MixedType [] [lty, lty]
      _ -> throwError "Incorrect type in Dup"
  Drop e -> do
    _ <- typecheck prog tenv e
    return $ MixedType [] []
  where
    splitEnv :: [Expr] -> Either String [TypeEnv]
    splitEnv exprs = do
      let (free, freeLin) = unzip $ ((\(FV a b) -> (a, b)) . freeVars) <$> exprs
      check "unbound or unconsumed non-linear variable found" $ fold free == M.keysSet env
      check "linear variable consumed twice" $ S.size (fold freeLin) == sum (S.size <$> freeLin)
      check "unbound or unconsumed linear variable found" $ fold freeLin == M.keysSet linEnv
      return $ zip free freeLin <&> \(f, fl) ->
        (env `M.restrictKeys` f, linEnv `M.restrictKeys` fl)

    typecheckEq :: TypeEnv -> Expr -> MixedType -> Either String ()
    typecheckEq te expr ty = do
      ty' <- typecheck prog te expr
      check ("expected " ++ show ty ++ ", got " ++ show ty') $ ty == ty'

typecheckFunc :: Program -> FuncName -> Either String ()
typecheckFunc prog@(Program funcMap) name = case typecheck prog env body of
  Left  err -> Left err
  Right ty  -> case ty == resultType of
    True  -> Right ()
    False -> Left "Return type mismatch"
  where
    FuncDef formals linFormals resultType body = funcMap ! name
    env = (M.fromList formals, M.fromList linFormals)

typecheckProgram :: Program -> Either String ()
typecheckProgram prog@(Program progMap) = sequence_ $ typecheckFunc prog <$> M.keys progMap

-------------------- JVP --------------------

freshVar :: Scope -> Var
freshVar s = case S.lookupMax s of
  Nothing          -> MkVar "v" 0
  Just (MkVar n i) -> MkVar n (i + 1)

freshVars :: Scope -> [Var]
freshVars s = x : freshVars (S.insert x s)
  where x = freshVar s

type Scope      = S.Set Var
type Subst      = M.Map Var Var
type TangentMap = M.Map Var Var
type JVPFuncMap = M.Map FuncName FuncName

-- TODO: Assert uniqeness
scopeExt :: Scope -> [Var] -> Scope
scopeExt sub vs = sub <> S.fromList vs

jvpProgram :: Program -> Program
jvpProgram (Program progMap) = Program $ jvpFunc jvpFuncMap <$> progMap
  where jvpFuncMap = M.mapWithKey const progMap  -- identity name map

jvpFunc :: JVPFuncMap -> FuncDef -> FuncDef
jvpFunc funcEnv (FuncDef formalsWithTypes linFormals resultType body) =
  case (linFormals, resultType) of
    ([], MixedType tys []) ->
      FuncDef formalsWithTypes (zip formals' formalTypes) (MixedType tys tys) $
        jvp funcEnv
         (scopeExt formalsScope formals')
         (M.fromList $ zip formals formals)
         (M.fromList $ zip formals formals')
         body
      where
        (formals, formalTypes) = unzip formalsWithTypes
        formalsScope = scopeExt mempty formals
        formals' = take (length formals) $ freshVars formalsScope
    _  -> error "Non-linear"

splitTangents :: Scope -> TangentMap -> [Expr] -> (Expr -> Expr, Scope, [TangentMap])
splitTangents scope env es = go scope env (freeVars <$> es)
  where
    go scope _   [] = (id, scope, [])
    go scope env (FV fvs fvs':tfvs) = case null fvs' of
      False -> error "Linear variables in a JVPed expression"
      True  -> case commonFvs of
        [] -> (subcontext, subscope, (M.restrictKeys env fvs):submaps)
          where (subcontext, subscope, submaps) = go scope (M.withoutKeys env fvs) tfvs
        _  -> (context . subcontext, subscope, (M.fromList $ zip commonFvs dvs2'):submaps)
          where
            allFresh@(vst':vst2':allDvs') = take (2 + 2 * length commonFvs) $ freshVars scope
            (dvs', dvs2') = splitAt (length commonFvs) allDvs'
            (subcontext, subscope, submaps) =
              go (scopeExt scope allFresh)
                (envExt (M.withoutKeys env fvs) commonFvs dvs') tfvs
            context = LetMixed [] [vst', vst2'] (Dup (LTuple $ LVar . (env !) <$> commonFvs)) .
                      LetUnpackLin dvs'  vst' .
                      LetUnpackLin dvs2' vst2'
      where
        commonFvsS = fvs `S.intersection` getFree (fold tfvs)
        commonFvs  = toList commonFvsS

jvp :: JVPFuncMap -> Scope -> Subst -> TangentMap -> Expr -> Expr
jvp funcEnv scope subst env e = case e of
  Ret vs_ [] -> ctx $ Ret ((subst !) <$> vs_) (zipWith (!) envs vs_)
    where (ctx, _, envs) = splitTangents scope env (Var <$> vs_)
  Ret _ _  -> expectNonLinear
  LetMixed vs_ [] e1 e2 ->
    ctx $ LetMixed vs vs' (rec ctxScope subst env1 e1) $
      rec ctxScope (envExt subst vs_ vs) (envExt env2 vs_ vs') e2
    where
      allFresh  = take (2 * length vs_) $ freshVars scope
      (vs, vs') = splitAt (length vs_) allFresh
      (ctx, ctxScope, [env1, env2]) = splitTangents (scopeExt scope allFresh) (envExt env vs_ vs') [e1, e2]
  LetMixed _ _ _ _ -> expectNonLinear
  LetUnpack _ _ _ -> undefined
  -- TODO: Split envs
  --LetUnpack vs v e ->
    --LetMixed [t] [t'] (rec scope env $ Var v) $
    --LetUnpack vs t $
    --LetUnpackLin vs' t' $
      --rec (scope <> S.fromList allFresh) (envExt env vs vs') e
    --where allFresh@(t : t' : vs') = take (length vs + 2) $ freshVars scope
  Tuple _ -> undefined
  -- TODO: Is the scoping correct here?
  --Tuple xs -> ctx $ shuffle ctxScope $ zipWith (uncurry $ rec ctxScope subst) envs xs
    --where (ctx, ctxScope, envs) = splitTangents scope env xs
  App f vs_ [] -> ctx $ App (funcEnv ! f) ((subst !) <$> vs_) (zipWith (!) envs vs_)
    where (ctx, _, envs) = splitTangents scope env (Var <$> vs_)
  App _ _ _  -> expectNonLinear
  Var v -> Ret [subst ! v] [env ! v]
  Lit v -> retExprs scope (Lit v) LZero
  UnOp Sin e -> jvpUnOp e Sin $ UnOp Cos . Var
  UnOp Cos e -> jvpUnOp e Cos $ \v -> BinOp Mul (UnOp Sin (Var v)) (Lit (-1))
  UnOp Exp e -> jvpUnOp e Exp $ UnOp Exp . Var
  BinOp Add e1 e2 -> ctx $
    LetMixed [v1] [v1'] (rec ctxScope subst env1 e1) $
    LetMixed [v2] [v2'] (rec (ctxScope <> S.fromList [v1, v1']) subst env2 e2) $
    retExprs (ctxScope <> S.fromList [v1, v1', v2, v2'])
      (BinOp Add (Var v1) (Var v2)) (LAdd (LVar v1') (LVar v2'))
    where
      (ctx, ctxScope, [env1, env2]) = splitTangents scope env [e1, e2]
      v1:v1':v2:v2':_ = freshVars ctxScope
  BinOp Mul e1 e2 -> ctx $
    LetMixed [v1] [v1'] (rec ctxScope subst env1 e1) $
    LetMixed [v2] [v2'] (rec (ctxScope <> S.fromList [v1, v1']) subst env2 e2) $
    retExprs (ctxScope <> S.fromList [v1, v1', v2, v2'])
      (BinOp Mul (Var v1) (Var v2))
      (LAdd (LScale (Var v2) (LVar v1'))
            (LScale (Var v1) (LVar v2')))
    where
      (ctx, ctxScope, [env1, env2]) = splitTangents scope env [e1, e2]
      v1:v1':v2:v2':_ = freshVars ctxScope
  Drop e -> Drop $ rec scope subst env e
  Dup _              -> expectNonLinear
  LTuple _           -> expectNonLinear
  LetUnpackLin _ _ _ -> expectNonLinear
  LVar _             -> expectNonLinear
  LAdd _ _           -> expectNonLinear
  LScale _ _         -> expectNonLinear
  LZero              -> expectNonLinear
  where
    rec = jvp funcEnv
    expectNonLinear = error "JVP only applies to completely non-linear computations"

    jvpUnOp :: Expr -> UnOp -> (Var -> Expr) -> Expr
    jvpUnOp e primOp tanCoef =
      LetMixed [v] [v'] (rec scope subst env e) $
      retExprs (scope <> S.fromList [v, v'])
        (UnOp primOp (Var v)) (LScale (tanCoef v) (LVar v'))
      where v : v' : _ = freshVars scope

retExprs :: Scope -> Expr -> Expr -> Expr
retExprs scope e1 e2 =
  LetMixed [v] []   e1 $
  LetMixed []  [v'] e2 $
  Ret [v] [v']
  where v : v' : _ = freshVars scope

-- | Take a bunch of expressions that produce mixed pairs and
-- convert them into an expr that returns a mixed pair containing
-- a tuple of their non-linear components and another with linear
-- components.
shuffle :: Scope -> [Expr] -> Expr
shuffle scope es = go [] [] (freshVars scope) es
  where
    go :: [Expr] -> [Expr] -> [Var] -> [Expr] -> Expr
    go n l (v:v':_)  []    =
      LetMixed [v] []   (Tuple  n) $
      LetMixed []  [v'] (LTuple l) $
        Ret [v] [v']
    go n l (v:v':vt) (e:t) = LetMixed [v] [v'] e $ go (Var v:n) (LVar v':l) vt t
    go _ _ _ _ = error "Impossible"

-------------------- Unzip --------------------

unzipProgram :: Program -> Program
unzipProgram orig@(Program funcMap) = new where
  new = Program $ flip M.foldMapWithKey funcMap $ \name def -> do
    -- Tying the knot by passing `new` here does assume that laziness
    -- will figure out a sensible order in which to actually perform
    -- the unzipping so that the type of every unzipped callee is
    -- available for its unzipped caller.
    let (udef, udef') = unzipFunc orig new def
    M.fromList [(name ++ ".nonlin", udef), (name ++ ".lin", udef')]

-- The nonlinear returned function packages the tape in the _last_ returned value
unzipFunc :: Program -> Program -> FuncDef -> (FuncDef, FuncDef)
unzipFunc orig new def =
  ( FuncDef formalsWithTys [] nonlinFuncTy nonlinBody
  , FuncDef [(resVar, residualTupleTy)]
      linFormalsWithTys (MixedType [] linRetTys) linBody
  )
  where
    (FuncDef formalsWithTys linFormalsWithTys (MixedType retTys linRetTys) body) = def
    (formals, _) = unzip formalsWithTys
    (linFormals, _) = unzip linFormalsWithTys
    formalsScope = scopeExt (scopeExt mempty formals) linFormals
    formalsSubst = envExt (envExt mempty formals formals) linFormals linFormals
    ((ctx, ctxScope), ubody, ubody') = unzipExpr orig formalsScope formalsSubst body
    residualVars = toList $ getFree (freeVars ubody') `S.difference` (scopeExt mempty linFormals)
    resVar:retVars = take (1 + length retTys) $ freshVars ctxScope
    nonlinBody = ctx $
      LetMixed retVars [] ubody $
      LetMixed [resVar] [] (Tuple $ Var <$> residualVars) $
      Ret (retVars ++ [resVar]) []
    linBody = LetUnpack residualVars resVar $ ubody'
    nonlinFuncTy@(MixedType nonlinRetTys []) = case
      typecheck new (M.fromList formalsWithTys, mempty) nonlinBody of
        Right res -> res
        Left err -> error $ err ++ " in\n" ++ show (pretty nonlinBody)
          ++ "\nwith env\n" ++ show (pretty formalsWithTys)
    residualTupleTy = last nonlinRetTys

nonLinRetTys :: Program -> FuncName -> [Type]
nonLinRetTys (Program funcMap) name = rets where
  (Just (FuncDef _ _ (MixedType rets _) _)) = M.lookup name funcMap

-- The Scope is the set of variables used by the generated body so far
-- (with respect to which new variables must be fresh).
-- The Subst is the remapping of old variable names to new ones.
-- The return is
-- - The binding list, represented as an Expr -> Expr function
-- - The Scope in that context
-- - The non-linear result expression
-- - The linear result expression
unzipExpr :: Program -> Scope -> Subst -> Expr -> ((Expr -> Expr, Scope), Expr, Expr)
unzipExpr orig scope subst expr = case expr of
  Ret vs vs' -> ((id, scope), Ret ((subst !) <$> vs) [], Ret [] ((subst !) <$> vs'))
  LetMixed vs vs' e1 e2 ->
      ( (ctx1 . LetMixed uvs [] ue1 . ctx2, scopeCtx2)
      , ue2
      , LetMixed [] uvs' ue1' ue2'
      )
    where
      ((ctx1, scopeCtx1), ue1, ue1') = rec scope subst e1
      (uvs, uvs') = splitAt (length vs) $ take (length vs + length vs') $ freshVars scopeCtx1
      e2Subst = envExt (envExt subst vs uvs) vs' uvs'
      e2Scope = scopeExt (scopeExt scope uvs) uvs'
      ((ctx2, scopeCtx2), ue2, ue2') = rec e2Scope e2Subst e2
  App name vs vs' ->
      ( (LetMixed (retVars ++ [tapeVar]) [] (App (name ++ ".nonlin") uvs []), scope2)
      , Ret retVars []
      , App (name ++ ".lin") [tapeVar] uvs'
      )
    where
      uvs = (subst !) <$> vs
      uvs' = (subst !) <$> vs'
      retTys = nonLinRetTys orig name
      tapeVar:retVars = take (1 + length retTys) $ freshVars scope
      scope2 = scopeExt scope $ tapeVar:retVars
  Var  v -> ((id, scope), Var (subst ! v), Ret [] [])
  LVar v -> ((id, scope), Ret [] [], LVar (subst ! v))
  UnOp op e -> ((ctx, ctxScope), UnOp op ue, ue')
    where ((ctx, ctxScope), ue, ue') = rec scope subst e
  BinOp op e1 e2 -> ((ctx1 . ctx2, ctxScope2), BinOp op ue1 ue2, ue')
    where
      ((ctx1, ctxScope1), ue1, ue1') = rec scope subst e1
      ((ctx2, ctxScope2), ue2, ue2') = rec ctxScope1 subst e2
      ue' = LetMixed [] [] ue1' ue2'
  LAdd e1 e2 -> ((ctx1 . ctx2, ctxScope2), ue, LAdd ue1' ue2')
    where
      ((ctx1, ctxScope1), ue1, ue1') = rec scope subst e1
      ((ctx2, ctxScope2), ue2, ue2') = rec ctxScope1 subst e2
      ue = LetMixed [] [] ue1 ue2
  LScale s e ->
    ( (sCtx . eCtx, eCtxScope)
    , LetMixed [] [] ue  $ Ret [] []
    , LetMixed [] [] us' $ LScale us ue'
    )
    where
      ((sCtx, sCtxScope), us, us') = rec scope     subst s
      ((eCtx, eCtxScope), ue, ue') = rec sCtxScope subst e
  Dup e -> ((ctx, ctxScope), ue, Dup ue')
    where
      ((ctx, ctxScope), ue, ue') = rec scope subst e
  _ -> error $ "Unzip not implemented: " ++ show (pretty expr)
  where
    rec = unzipExpr orig

-------------------- Transposition --------------------

-- expr : free vars -> unnamed outputs
-- transpose expr : (cotangent per) unnamed outputs -> (cotangents of) free vars

type CotangentMap = M.Map Var Var

transposeProgram :: Program -> Program
transposeProgram (Program funcMap) = Program $ funcMap <&> \def -> case def of
  FuncDef _ _ (MixedType [] _) _ -> transposeFunc def
  _ -> def

transposeFunc :: FuncDef -> FuncDef
transposeFunc (FuncDef formalsWithTys linFormalsWithTys (MixedType retTys linRetTys) body) =
  case retTys of
    [] -> FuncDef formalsWithTys ctFormalsWithTys (MixedType [] linTys) tbody
      where
        (formals   , _     ) = unzip formalsWithTys
        (linFormals, linTys) = unzip linFormalsWithTys
        formalsScope = scopeExt mempty formals
        ctFormals = take (length linRetTys) $ freshVars formalsScope
        ctFormalsWithTys = zip ctFormals linRetTys
        (ctx, _, ctMap) = transposeExpr (scopeExt formalsScope ctFormals) body ctFormals
        tbody = ctx $ Ret [] ((ctMap !) <$> linFormals)
    _ -> error "Transposing a function with non-linear results!"

-- An alternative would be to return (Expr, [Var]) with the second argument
-- mapping the linear outputs of the expr to variables in a primal program.
transposeExpr :: Scope -> Expr -> [Var] -> (Expr -> Expr, Scope, CotangentMap)
transposeExpr scope expr cts = case expr of
  Ret vs vs' -> case vs of
    [] -> (id, scope, M.fromList $ zip vs' cts)
    -- TODO: Relax?
    _ -> error "Returning non-linear values in transposition!"
  LetMixed vs vs' e1 e2 -> case vs of
    [] ->
      ( e2Ctx . e1Ctx
      , e1Scope
      , e1Map <> (e2Map `M.withoutKeys` (S.fromList vs'))
      )
      where
        (e2Ctx, e2Scope, e2Map) = transposeExpr scope   e2 cts
        (e1Ctx, e1Scope, e1Map) = transposeExpr e2Scope e1 ((e2Map !) <$> vs')
    -- TODO: Relax
    _ -> error "Binding non-linear values in transposition!"
  -- TODO(axch): Cover this with a test case and uncomment it
  -- LetUnpackLin vs v body ->
  --   ( bCtx . LetMixed [] [v'] (Tuple $ map Var vs') . vCtx
  --   , vScope
  --   , vMap <> (bMap `M.withoutKeys` (S.fromList vs))
  --   )
  --   where
  --     (bCtx, bScope, bMap) = transposeExpr scope body cts
  --     vs' = (bMap !) <$> vs
  --     v':_ = freshVars bScope
  --     (vCtx, vScope, vMap) = transposeExpr (scopeExt bScope [v']) (Var v) [v']
  LetUnpack vs v body -> (LetUnpack vs v . bCtx, bScope, bMap)
    where
      (bCtx, bScope, bMap) = transposeExpr scope body cts
  App name vs vs' ->
    ( LetMixed [] cts' (App name vs cts)
    , scope'
    , M.fromList $ zip vs' cts'
    )
    where
      cts' = take (length vs') $ freshVars scope
      scope' = scopeExt scope cts'
  LAdd x y ->
    ( LetMixed [] [ct1, ct2] (Dup (LVar ct)) . xtCtx . ytCtx
    , yScope
    , xMap <> yMap
    )
    where
      ct1:ct2:_ = freshVars scope
      [ct] = cts
      (xtCtx, xScope, xMap) = transposeExpr (scopeExt scope [ct1, ct2]) x [ct1]
      (ytCtx, yScope, yMap) = transposeExpr xScope y [ct2]
  LVar v -> (id, scope, M.singleton v ct)
    where [ct] = cts
  _ -> error $ "Transpose not implemented: " ++ show (pretty expr)


-- It would be nice to make this the signature of transpose
--   (Decls, CotangentMap) -> (Decls, CotangentMap)
-- but the language would have to look more like this:
--   Block (Nest Decl) [Var]
-- where Decls are in ANF.
-- This works because:
--   Block Decls [Var] + [CotangentExprs] === (Decls, M.fromList (zip vars cotangentExprs))

-------------------- Helpers --------------------

unique :: Foldable f => f Var -> Bool
unique vs = S.size (S.fromList $ toList vs) == length vs

envExt :: Ord k => M.Map k v -> [k] -> [v] -> M.Map k v
envExt env vs vals = foldl (\env (k, v) -> M.insert k v env) env $ zip vs vals

check :: MonadError e m => e -> Bool -> m ()
check err cond = unless cond $ throwError err

(!) :: (HasCallStack, Ord k, Show k, Show v) => M.Map k v -> k -> v
m ! k = case M.lookup k m of
  Just v -> v
  Nothing -> error $ "Missing key: " ++ show k ++ " in " ++ show m
