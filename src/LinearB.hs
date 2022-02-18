module LinearB (module LinearB, module LinearA) where

import Control.Monad.Except
import Data.Functor
import Data.Foldable
import qualified Data.Set as S
import qualified Data.Map.Strict as M

import LinearA (Var, FuncName, Subst,
                FreeVars (..), freeVar, freeLinVar,
                freshVar,
                UnOp (..), BinOp (..),
                (!), check, envExt, unique)

data MixedDepType = MixedDepType [(Maybe Var, Type)] [Type]
                    deriving (Show, Eq)

data Type = FloatType
          | TupleType [Type]
          | SumType   [Type]
          | SumDepType ProjExpr Var [Type]
          deriving (Show, Eq)

data ProjExpr = ProjHere Var
              | ProjThere ProjExpr Int
              deriving (Show, Eq)

data Expr
       -- LinearA parts that are not included in LinearB
       -- = Ret [Var] [Var]
       -- | LetMixed     [Var] [Var] Expr Expr
       -- | LetUnpack    [Var]       Var  Expr
       -- | LetUnpackLin [Var]       Var  Expr
          = App FuncName [Var] [Var]
          -- Additional non-linear expressions
          | Var Var
          | Lit Float
          | Tuple [Var]
          | UnOp  UnOp  Expr
          | BinOp BinOp Expr Expr
          -- Additional linear expressions
          | LVar Var
          | LTuple [Var]
          | LAdd   Expr Expr
          | LScale Expr Expr
          | LZero
          | Dup  Expr
          | Drop Expr
          -- LinearB extensions
          | RetDep [Var] [Var] MixedDepType  -- Notice the explicit type annotation!
          | LetDepMixed    [Var] [Var] Expr    Expr
          | LetUnpackMixed [Var] [Var] Var Var Expr
          | Case Var Var [Expr]
          | Inject Int Var [Type]
          deriving Show

data FuncDef = FuncDef [(Var, Type)] [(Var, Type)] MixedDepType Expr
               deriving Show
data Program = Program (M.Map FuncName FuncDef)
               deriving Show

freeVars :: Expr -> FreeVars
freeVars e = case e of
  Lit _  -> mempty
  Var v  -> freeVar v
  LVar v -> freeLinVar v
  App _ vs linVs -> FV (S.fromList vs) (S.fromList linVs)
  Tuple vs       -> FV (S.fromList vs) mempty
  UnOp  _ e      -> freeVars e
  BinOp _ le re  -> freeVars le <> freeVars re
  LTuple vs      -> FV mempty (S.fromList vs)
  LAdd    le re  -> freeVars le <> freeVars re
  LScale  se le  -> freeVars se <> freeVars le
  LZero          -> mempty
  Dup  e -> freeVars e
  Drop e -> freeVars e
  RetDep vs linVs ty -> (FV (S.fromList vs) (S.fromList linVs)) <> freeVarsMixedType ty
  LetDepMixed vs linVs e1 e2 -> FV
    (freeE1    `S.union` (freeE2    `S.difference` S.fromList vs   ))
    (freeLinE1 `S.union` (freeLinE2 `S.difference` S.fromList linVs))
    where
      FV freeE1 freeLinE1 = freeVars e1
      FV freeE2 freeLinE2 = freeVars e2
  LetUnpackMixed vs vs' v v' e -> FV (S.singleton v  <> (free    `S.difference` S.fromList vs ))
                                     (S.singleton v' <> (freeLin `S.difference` S.fromList vs'))
    where FV free freeLin = freeVars e
  Case v b exprs -> freeVar v <> (FV fe' fel')
    where
      FV fe fel' = foldMap freeVars exprs
      fe' = fe `S.difference` S.singleton b
  Inject _ v tys -> freeVar v <> FV (foldMap freeVarsType tys) mempty

freeVarsMixedType :: MixedDepType -> FreeVars
freeVarsMixedType (MixedDepType tysBs linTys) =
    FV (foldMap freeVarsType tys <> (foldMap freeVarsType linTys `S.difference` bsFree)) mempty
  where
    (bs, tys) = unzip tysBs
    bsFree = flip foldMap bs $ \b -> case b of Nothing -> mempty; Just v -> S.singleton v

freeVarsType :: Type -> S.Set Var
freeVarsType ty = case ty of
  FloatType         -> mempty
  TupleType tys     -> foldMap freeVarsType tys
  SumType   tys     -> foldMap freeVarsType tys
  SumDepType p v ty -> freeVarsProj p <> (foldMap freeVarsType ty `S.difference` S.singleton v)

freeVarsProj :: ProjExpr -> S.Set Var
freeVarsProj p = case p of
  ProjHere v     -> S.singleton v
  ProjThere p' _ -> freeVarsProj p'

substType :: Subst -> Type -> Type
substType s ty = case ty of
  FloatType     -> FloatType
  TupleType tys -> TupleType (substType s <$> tys)
  SumType   tys -> SumType   (substType s <$> tys)
  SumDepType p v ty -> SumDepType (substProj s p) v' (substType (s <> M.singleton v v') <$> ty)
  where v' = freshVar $ S.fromList $ toList s

substProj :: Subst -> ProjExpr -> ProjExpr
substProj s p = case p of
  ProjHere v     -> ProjHere $ case M.lookup v s of Nothing -> v; Just v' -> v'
  ProjThere p' i -> ProjThere (substProj s p') i


-------------------- Type checking --------------------

type TypeEnv = (M.Map Var Type, M.Map Var Type)
typecheck :: Program -> TypeEnv -> Expr -> Either String MixedDepType
typecheck prog@(Program progMap) tenv@(env, linEnv) expr = case expr of
  RetDep vs linVs ty@(MixedDepType tysBs linTys) -> do
    check "RetDep non-linear environment mismatched" $ S.fromList vs == M.keysSet env
    check "Repeated linear returns" $ unique linVs
    check "RetDep linear environment mismatched" $ S.fromList linVs == M.keysSet linEnv
    check "RetDep non-linear type annotation invalid length" $ length vs == length tysBs
    check "RetDep linear type annotation invalid length" $ length linVs == length linTys
    forM_ (zip vs tysBs) $ \(v, (_, t)) ->
      check "RetDep non-linear type annotation mismatched" $ (env ! v) == t
    let s = M.fromList $ concat $ zip tysBs vs <&> \((b, _), v) -> case b of Nothing -> []; Just b' -> [(b', v)]
    -- TODO: Is this a sensible restriction? It's necessary for substType below to succeed.
    check "Non-closed RetDep type" $
      getFree (freeVarsMixedType $ MixedDepType [] linTys) `S.isSubsetOf` M.keysSet s
    forM_ (zip linVs linTys) $ \(v, t) ->
      checkTypeEq (linEnv ! v) (substType s t)
    return ty
  LetDepMixed vs linVs e1 e2 -> do
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
    MixedDepType vTysBs linVTys' <- typecheck prog e1Env e1
    let (vBs, vTys) = unzip vTysBs
    let s = M.fromList $ concat $ zip vBs vs <&> \(b, v) -> case b of Nothing -> []; Just b' -> [(b', v)]
    let linVTys = substType s <$> linVTys'
    let e2Env = ( envExt (env `M.restrictKeys` freeE2) vs vTys
                , envExt (linEnv `M.restrictKeys` freeLinE2) linVs linVTys)
    typecheck prog e2Env e2
  Case v b es -> do
    case env ! v of
      SumType tys -> do
        check "Mismatched case count" $ length tys == length es
        eTys <- forM (zip3 [0..] tys es) $ \(i, ty, e) -> do
          let eEnv = case S.member v (getFree $ freeVars e) of
                       True  -> env
                       False -> M.delete v env
          typecheck prog (envExt eEnv [b] [ty], refineConstructor v b i linEnv) e
        check "Case of empty sum type not supported" $ not $ null eTys
        let rTy = head eTys
        forM_ eTys $ \eTy -> check "Cases return different types" $ eTy == rTy
        return rTy
      _ -> throwError "Case on a non-sum type"
  Inject con v tys -> do
    check "Invalid constructor index" $ 0 <= con && con < length tys
    check "Inject type mismatch" $ env ! v == tys !! con
    return $ MixedDepType [(Nothing, SumType tys)] []
  LetUnpackMixed vs vs' v v' e -> do
    let FV free freeLin = freeVars e
    check "LetUnpackMixed shadowing in non-linear binders" $ unique vs
    check "LetUnpackMixed shadowing in linear binders" $ unique vs'
    check "LetUnpack: non-linear environment mismatched" $
      M.keysSet env == S.insert v (free `S.difference` S.fromList vs)
    check "LetUnpackMixed: linear environment mismatched" $
       (M.keysSet linEnv `S.difference` S.singleton v') `S.union` (S.fromList vs') == freeLin
    case (env ! v, linEnv ! v') of
      (TupleType tys, TupleType tys') -> do
        check "" $ length tys == length vs
        check "" $ length tys' == length vs'
        typecheck prog (envExt (env `M.restrictKeys` free) vs tys,
                        envExt (M.delete v' linEnv) vs' tys') e
      _ -> throwError "Unpacking a non-tuple type"
  Lit _ -> do
    check "Lit: non-empty environments" $ null env && null linEnv
    return $ MixedDepType [(Nothing, FloatType)] []
  Var v -> do
    check "Var: non-empty linear env" $ null linEnv
    check "Var: non-singleton env" $ (S.singleton v == M.keysSet env)
    return $ MixedDepType [(Nothing, env ! v)] []
  LVar v -> do
    check "LVar: non-empty env" $ null env
    check "LVar: non-singleton linear env" $ S.singleton v == M.keysSet linEnv
    return $ MixedDepType [] [linEnv ! v]
  App f args linArgs -> do
    let FuncDef _ _ resTy _ = progMap ! f
    -- Use (L)Tuple checking rules to verify that references to args are valid
    void $ typecheck prog (env, mempty)    $ Tuple  args
    void $ typecheck prog (mempty, linEnv) $ LTuple linArgs
    return $ resTy
  Tuple vars -> do
    envs <- splitFV $ freeVar <$> vars
    tys <- forM (zip envs vars) $ \(env, var) -> do
      eTy <- typecheck prog env $ Var var
      case eTy of
        MixedDepType [(_, ty)] [] -> return ty
        _ -> throwError "Tuple: unexpected element type"
    return $ MixedDepType [(Nothing, TupleType tys)] []
  UnOp _ e -> do
    checkFloat tenv e
    return $ MixedDepType [(Nothing, FloatType)] []
  BinOp _ le re -> do
    ~[lenv, renv] <- splitEnv [le, re]
    checkFloat lenv le
    checkFloat renv re
    return $ MixedDepType [(Nothing, FloatType)] []
  LTuple vars -> do
    envs <- splitFV $ freeLinVar <$> vars
    tys <- forM (zip envs vars) $ \(env, var) -> do
      eTy <- typecheck prog env $ LVar var
      case eTy of
        MixedDepType [] [ty] -> return ty
        _ -> throwError "Tuple: unexpected element type"
    return $ MixedDepType [] [TupleType tys]
  LAdd le re -> do
    ~[lenv, renv] <- splitEnv [le, re]
    lty <- typecheck prog lenv le
    rty <- typecheck prog renv re
    check ("expected " ++ show lty ++ ", got " ++ show rty) $ lty == rty
    return lty
  LScale se le -> do
    ~[senv, lenv] <- splitEnv [se, le]
    checkFloat senv se
    typecheck prog lenv le
  LZero -> do
    check "LZero: non-empty environment" $ null env && null linEnv
    return $ MixedDepType [] [FloatType]
  Dup e -> do
    ty <- typecheck prog tenv e
    case ty of
      MixedDepType [] [lty] -> return $ MixedDepType [] [lty, lty]
      _ -> throwError "Incorrect type in Dup"
  Drop e -> do
    _ <- typecheck prog tenv e
    return $ MixedDepType [] []
  where
    splitEnv :: [Expr] -> Either String [TypeEnv]
    splitEnv exprs = splitFV $ freeVars <$> exprs

    splitFV :: [FreeVars] -> Either String [TypeEnv]
    splitFV fvs = do
      let (free, freeLin) = unzip $ (\(FV a b) -> (a, b)) <$> fvs
      check "unbound or unconsumed non-linear variable found" $ fold free == M.keysSet env
      check "linear variable consumed twice" $ S.size (fold freeLin) == sum (S.size <$> freeLin)
      check "unbound or unconsumed linear variable found" $ fold freeLin == M.keysSet linEnv
      return $ zip free freeLin <&> \(f, fl) ->
        (env `M.restrictKeys` f, linEnv `M.restrictKeys` fl)

    checkFloat :: TypeEnv -> Expr -> Either String ()
    checkFloat te expr = do
      ty <- typecheck prog te expr
      case ty of
        MixedDepType [(_, FloatType)] [] -> return ()
        _ -> throwError $ "expected Float, got " ++ show ty

    checkTypeEq :: Type -> Type -> Either String ()
    checkTypeEq a b = check ("expected " ++ show a ++ " and " ++ show b ++ " to be equal") $ a == b

    refineConstructor :: Var -> Var -> Int -> M.Map Var Type -> M.Map Var Type
    refineConstructor v vb cons env = env <&> go
      where
        go ty = case ty of
          FloatType     -> FloatType
          TupleType tys -> TupleType $ go <$> tys
          SumType   tys -> SumType   $ go <$> tys
          SumDepType v' b tys -> case v' == ProjHere v of
            True  -> substType (M.singleton b vb) (go $ tys !! cons)
            False -> case b == vb of  -- TODO: Refresh
              False -> SumDepType v' b (go <$> tys)
              True  -> error "Not implemented"


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
