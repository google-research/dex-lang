module LinearB (module LinearB, module LinearA) where

import Control.Monad.Except
import Data.Functor
import Data.Foldable
import Data.Hashable
import Control.Exception
import qualified Data.Set as S
import qualified Data.HashSet as HS
import qualified Data.Map.Strict as M
import GHC.Generics
import Prettyprinter

import LinearA (Var (..), FuncName, Subst,
                FreeVars (..), freeVar, freeLinVar,
                Scope, scopeExt, freshVar, freshVars,
                JVPFuncMap, TangentMap,
                UnOp (..), BinOp (..),
                (!), check, envExt, unique)


data TypeEqEvidence = InjEvidence  Int Var  -- ith injection of var
                    | ProjEvidence [Var]    -- unpacked into vars
                    deriving (Eq, Generic, Show)
instance Hashable TypeEqEvidence

data MixedDepType = MixedDepType [(Maybe Var, Type)] [Type]
                    deriving Show

data Type = FloatType
          | TupleType [Type]
          | SumType   [Type]
          | SumDepType ProjExpr Var [Type]
          deriving (Show, Eq, Generic)
instance Hashable Type

data ProjExpr = Proj Var [Int]
                deriving (Show, Eq, Generic)
instance Hashable ProjExpr

appendProj :: ProjExpr -> Int -> ProjExpr
appendProj (Proj v ps) p = Proj v (ps ++ [p])

data Expr
       -- LinearA parts that are not included in LinearB
       -- = Ret [Var] [Var]
       -- | LetMixed     [Var] [Var] Expr Expr
          = LetUnpack    [Var]        Var  Expr
          | LetUnpackLin [Var] [Type] Var  Expr
          | App FuncName [Var] [Var]
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
          | RetDep         [Var] [Var] MixedDepType
          | LetDepMixed    [Var] [Var] Expr    Expr
          | Case Var Var MixedDepType [Expr]  -- scrutinee, binder, result type, expression
          | Inject Int Var [Type]
          deriving Show

data FuncDef = FuncDef [(Var, Type)] [(Var, Type)] MixedDepType Expr
               deriving Show
data Program = Program (M.Map FuncName FuncDef)
               deriving Show

-------------------- Pretty printing --------------------

instance Pretty Program where
  pretty (Program progMap) = vcat $ M.toList progMap <&> \(fname, def) -> "def" <+> pretty fname <+> pretty def
instance Pretty FuncDef where
  pretty (FuncDef vs vs' (MixedDepType rtys rtys') body) =
    parens (prettyFormals vs <> " ;" <+> prettyFormals vs') <+> (nest 2 $
      softline' <> "->" <+> encloseSep "(" "" ", " (pretty <$> rtys) <>
      "; " <> encloseSep "" ")" ", " (pretty <$> rtys') <+> "=" <> hardline <> pretty body)
    where
      prettyFormals vs = cat $ punctuate ", " $ vs <&> \(v, ty) -> pretty v <> ":" <> pretty ty
instance Pretty Type where
  pretty = \case
    FloatType     -> "Float"
    TupleType tys -> tupled $ pretty <$> tys
    SumType   tys -> encloseSep "{" "}" "|" $ pretty <$> tys
    SumDepType p v tys -> "tcase" <+> pretty p <+> "of" <+> pretty v <+> encloseSep "{" "}" "|" (pretty <$> tys)
instance Pretty MixedDepType where
  pretty (MixedDepType tysBs linTys) =
    group $ parens $ fillSep (tysBs <&> prettyBinder) <> line' <> "; " <>
                     fillSep (pretty <$> linTys)
    where
      prettyBinder (b, ty) = case b of
        Nothing -> "_:" <> pretty ty
        Just n  -> pretty n <> ":" <> pretty ty
instance Pretty ProjExpr where
  pretty (Proj v ps) = pretty v <> (flip foldMap ps $ \p -> "." <> pretty p)
instance Pretty Expr where
  pretty = \case
    RetDep vs vs' ty -> prettyMixedVars vs vs' <> "@" <> pretty ty
    LetDepMixed vs vs' e1 e2 -> "let" <+> prettyMixedVars vs vs' <+> "=" <> (nest 2 $ group $ line <> pretty e1) <> hardline <> pretty e2
    LetUnpack vs v e -> "explodeN" <+> prettyMixedVars vs [] <+> "=" <+> pretty v <> hardline <> pretty e
    LetUnpackLin vs' _ v e -> "explodeL" <+> prettyMixedVars [] vs' <+> "=" <+> pretty v <> hardline <> pretty e
    App funcName vs vs' -> pretty funcName <> prettyMixedVars vs vs'
    Var v -> pretty v
    Lit v -> pretty v
    Tuple es -> "tupN" <+> (tupled $ pretty <$> es)
    UnOp Sin e -> "sin" <+> parens (pretty e)
    UnOp Cos e -> "cos" <+> parens (pretty e)
    UnOp Exp e -> "exp" <+> parens (pretty e)
    BinOp Add e1 e2 -> parens (pretty e1) <+> "+" <+> parens (pretty e2)
    BinOp Mul e1 e2 -> parens (pretty e1) <+> "*" <+> parens (pretty e2)
    LVar v -> pretty v
    LTuple es -> "tupL" <+> (tupled $ pretty <$> es)
    LAdd e1 e2 -> pretty $ BinOp Add e1 e2
    LScale es el -> pretty $ BinOp Mul es el
    LZero -> "zero"
    Dup e -> "dup" <+> parens (pretty e)
    Drop e -> "drop" <+> parens (pretty e)
    Case v b ty es -> "case" <+> pretty v <+> "@" <+> pretty ty <+> "of" <+> pretty b <+> (nest 2 $ flip foldMap es $ \e -> hardline <> "->" <+> nest 3 (pretty e))
    Inject con v tys -> "inject" <+> pretty con <+> pretty v <+> "@" <+> pretty (SumType tys)
    where
      prettyMixedVars :: [Var] -> [Var] -> Doc ann
      prettyMixedVars vs vs' = group $ "(" <> fillSep (pretty <$> vs) <> line' <> "; " <> fillSep (pretty <$> vs') <> ")"

-------------------- Free variable querying --------------------

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
  LetUnpack vs v e -> freeVar v <> (freeVars e `hiding` FV (S.fromList vs) mempty)
  LetUnpackLin vs tys v e -> assertClosedTys tys $ freeLinVar v <> (freeVars e `hiding` FV mempty (S.fromList vs))
  Case v b ty exprs -> freeVar v <> FV fe' fel' <> freeVarsMixedType ty
    where
      FV fe fel' = foldMap freeVars exprs
      fe' = fe `S.difference` S.singleton b
  Inject _ v tys -> assertClosedTys tys $ freeVar v
  where
    assertClosedTys :: [Type] -> a -> a
    assertClosedTys tys = assert (null $ foldMap freeVarsType tys)
    (FV a b) `hiding` (FV a' b') = FV (a `S.difference` a') (b `S.difference` b')

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
freeVarsProj (Proj v _) = S.singleton v

substType :: Subst -> Type -> Type
substType s ty = case ty of
  FloatType     -> FloatType
  TupleType tys -> TupleType (substType s <$> tys)
  SumType   tys -> SumType   (substType s <$> tys)
  SumDepType p v ty -> SumDepType (substProj s p) v' (substType (s <> M.singleton v v') <$> ty)
  where v' = freshVar $ S.fromList $ toList s

substProj :: Subst -> ProjExpr -> ProjExpr
substProj s (Proj v ps) = case M.lookup v s of
  Nothing -> Proj v  ps
  Just v' -> Proj v' ps


-------------------- Type checking --------------------

type TypeEqEvidenceEnv = M.Map Var (HS.HashSet TypeEqEvidence)
type TypeEnv = (TypeEqEvidenceEnv, M.Map Var Type, M.Map Var Type)

typecheck :: Program -> TypeEnv -> Expr -> Either String MixedDepType
typecheck prog@(Program progMap) tenv@(evid, env, linEnv) expr = case expr of
  RetDep vs linVs ty -> do
    check "RetDep non-linear environment mismatched" $ S.fromList vs == M.keysSet env
    check "Repeated linear returns" $ unique linVs
    check "RetDep linear environment mismatched" $ S.fromList linVs == M.keysSet linEnv
    let inferredType = MixedDepType (zip (Just <$> vs) ((env !) <$> vs)) ((linEnv !) <$> linVs)
    check "RetDep type annotation" $ mixedTypeEqualGiven scope evid ty inferredType
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
    let e1Env = (evid, env `M.restrictKeys` freeE1, linEnv `M.restrictKeys` freeLinE1)
    MixedDepType vTysBs linVTys' <- typecheck prog e1Env e1
    let (vBs, vTys) = unzip vTysBs
    let s = M.fromList $ concat $ zip vBs vs <&> \(b, v) -> case b of Nothing -> []; Just b' -> [(b', v)]
    let linVTys = substType s <$> linVTys'
    let e2Evid = case (vs, e1) of
                   ([b], Tuple vs      ) -> addEvidence evid b $ ProjEvidence vs
                   ([b], Inject con v _) -> addEvidence evid b $ InjEvidence con v
                   _ -> evid
    let e2Env = ( e2Evid
                , envExt (env `M.restrictKeys` freeE2) vs vTys
                , envExt (linEnv `M.restrictKeys` freeLinE2) linVs linVTys)
    typecheck prog e2Env e2
  Case v b ty es -> do
    case env ! v of
      SumType tys -> do
        check "Mismatched case count" $ length tys == length es
        forM_ (zip3 [0..] tys es) $ \(con, bty, e) -> do
          let eEnv = case S.member v (getFree $ freeVars e) of
                       True  -> env
                       False -> M.delete v env
          let eEvid = addEvidence evid v $ InjEvidence con b
          eTy <- typecheck prog (eEvid, envExt eEnv [b] [bty], linEnv) e
          check ("Cases return different types: expected " ++ show ty ++ ", got " ++ show eTy) $
            mixedTypeEqualGiven scope eEvid eTy ty
        return ty
      _ -> throwError "Case on a non-sum type"
  Inject con v tys -> do
    check "Invalid constructor index" $ 0 <= con && con < length tys
    check "Inject type mismatch" $ env ! v == tys !! con
    return $ MixedDepType [(Nothing, SumType tys)] []
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
        typecheck prog (addEvidence evid v $ ProjEvidence vs, envExt (env `M.restrictKeys` free) vs tys, linEnv) e
      _ -> throwError "Unpacking a non-tuple type"
  LetUnpackLin vs tys v e -> do
    let FV free freeLin = freeVars e
    check "shadowing in binders" $ unique vs
    check "LetUnpackLin: non-linear environment mismatched" $
      M.keysSet env == free
    check "LetUnpackLin: linear environment mismatched" $
       (M.keysSet linEnv `S.difference` S.singleton v) `S.union` (S.fromList vs) == freeLin
    check "LetUnpackLin: annotations mismatched" $
      typeEqualGiven scope evid (linEnv ! v) (TupleType tys)
    typecheck prog (evid, env, envExt (M.delete v linEnv) vs tys) e
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
    -- TODO: Check that args are aligned with what f expects!
    void $ typecheck prog (evid, env, mempty)    $ Tuple  args
    void $ typecheck prog (evid, mempty, linEnv) $ LTuple linArgs
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
    lmty <- typecheck prog lenv le
    rmty <- typecheck prog renv re
    -- TODO: Check that both types are VSpaces
    case (lmty, rmty) of
      (MixedDepType [] [lty], MixedDepType [] [rty]) -> checkTypeEq lty rty
      _ -> throwError "Expected one linear value on each side of LAdd"
    return lmty
  LScale se le -> do
    ~[senv, lenv] <- splitEnv [se, le]
    checkFloat senv se
    -- TODO: Check that the type is a vspace
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
        (evid, env `M.restrictKeys` f, linEnv `M.restrictKeys` fl)

    checkFloat :: TypeEnv -> Expr -> Either String ()
    checkFloat te expr = do
      ty <- typecheck prog te expr
      case ty of
        MixedDepType [(_, ty)] [] -> checkTypeEq ty FloatType
        _ -> throwError $ "expected Float, got " ++ show ty

    checkTypeEq :: Type -> Type -> Either String ()
    checkTypeEq a b = check ("expected " ++ show a ++ " and " ++ show b ++ " to be equal") $ typeEqualGiven scope evid a b

    addEvidence :: TypeEqEvidenceEnv -> Var -> TypeEqEvidence -> TypeEqEvidenceEnv
    addEvidence env v e = M.insertWith (<>) v (HS.singleton e) env

    scope = M.keysSet env <> M.keysSet linEnv

typecheckFunc :: Program -> FuncName -> Either String ()
typecheckFunc prog@(Program funcMap) name = case typecheck prog env body of
  Left  err -> Left err
  Right ty  -> case mixedTypeEqualGiven mempty mempty ty resultType of
    True  -> Right ()
    False -> Left "Return type mismatch"
  where
    FuncDef formals linFormals resultType body = funcMap ! name
    env = (mempty, M.fromList formals, M.fromList linFormals)

typecheckProgram :: Program -> Either String ()
typecheckProgram prog@(Program progMap) = sequence_ $ typecheckFunc prog <$> M.keys progMap

typeEqualGiven :: Scope -> TypeEqEvidenceEnv -> Type -> Type -> Bool
typeEqualGiven scope evidence at bt =
    not $ null $ (saturate (alphaNormalize at)) `HS.intersection` (saturate (alphaNormalize bt))
  where
    alphaNormalize :: Type -> Type
    alphaNormalize t = go scope mempty t
      where
        go scope subst t = case t of
          FloatType         -> FloatType
          TupleType ts      -> TupleType $ go scope subst <$> ts
          SumType   ts      -> SumType   $ go scope subst <$> ts
          SumDepType p b ts ->
            SumDepType (substProj subst p) b' $
              go (scopeExt scope [b']) (envExt subst [b] [b']) <$> ts
            where b' = freshVar scope

    saturate :: Type -> HS.HashSet Type
    saturate t = case t of
      FloatType         -> HS.singleton FloatType
      TupleType ts      -> TupleType `HS.map` (join $ saturate <$> ts)
      SumType   ts      -> SumType   `HS.map` (join $ saturate <$> ts)
      SumDepType p@(Proj v ps) b ts ->
        (SumDepType p b `HS.map` (join $ saturate <$> ts)) <>
        (case ps of
          []      -> flip foldMap ev $ \e -> case e of
            InjEvidence con v' -> saturate $ substType (M.singleton b v') (ts !! con)
            _                  -> mempty
          (hp:tp) -> flip foldMap ev $ \e -> case e of
            ProjEvidence vs -> saturate $ SumDepType (Proj (vs !! hp) tp) b ts
            _               -> mempty)
        where
          ev = case M.lookup v evidence of
            Nothing  -> mempty
            Just ev' -> ev'

    join :: (Hashable a, Eq a) => [HS.HashSet a] -> HS.HashSet [a]
    join []    = HS.singleton []
    join (h:t) = foldMap (\v -> HS.map (v:) ft) h
      where ft = join t

mixedTypeEqualGiven :: Scope -> TypeEqEvidenceEnv -> MixedDepType -> MixedDepType -> Bool
mixedTypeEqualGiven topScope evidence (MixedDepType tysBs tysLin) (MixedDepType tysBs' tysLin') =
    go topScope mempty tysBs tysBs'
  where
    go scope subst tbs tbs' = case (tbs, tbs') of
      ([]     , []        ) ->
        all (uncurry $ typeEqualGiven scope evidence) $
          zip tysLin (substType subst <$> tysLin')
      ((b,t):r, (b',t'):r') -> typeEqualGiven topScope evidence t t' && restEqual
        where
          restEqual = case (b, b') of
            (Nothing, Nothing) -> go scope subst r r'
            (Nothing, Just v') -> not (v' `S.member` foldMap freeVarsType tysLin') &&
                                  go scope subst r r'
            (Just v , Nothing) -> not (v  `S.member` foldMap freeVarsType tysLin ) &&
                                  go scope subst r r'
            (Just v , Just v') -> go (scopeExt scope [v]) (envExt subst [v'] [v]) r r'
      _ -> False

-------------------- Smart constructors --------------------

-- That do ANF on demand

retDepPair :: Scope -> Expr -> Expr -> Type -> Expr
retDepPair scope e1 e2 ty =
  LetDepMixed [v] []   e1 $
  LetDepMixed []  [v'] e2 $
  RetDep [v] [v'] (MixedDepType [(Just v, ty)] [tangentType v ty])
  where v : v' : _ = freshVars scope

-------------------- JVP --------------------

jvpProgram :: Program -> Program
jvpProgram (Program progMap) = Program $ jvpFunc jvpFuncMap <$> progMap
  where jvpFuncMap = M.mapWithKey const progMap  -- identity name map

jvpFunc :: JVPFuncMap -> FuncDef -> FuncDef
jvpFunc funcEnv (FuncDef formalsWithTypes linFormals resultType body) =
  case (linFormals, resultType) of
    ([], MixedDepType tys []) ->
      FuncDef formalsWithTypes (zip formals' tangentTypes)
        (MixedDepType (zip (Just <$> resultNames) (snd <$> tys)) resTys') $
        jvp funcEnv
         (M.fromList formalsWithTypes)
         (scopeExt formalsScope formals')
         (M.fromList $ zip formals formals)
         (M.fromList $ zip formals formals')
         body
      where
        (formals, formalTypes) = unzip formalsWithTypes
        formalsScope = scopeExt mempty formals
        formals' = take (length formals) $ freshVars formalsScope
        tangentTypes = uncurry tangentType <$> zip formals formalTypes
        resultNames = MkVar "r" <$> [1..]
        resTys' = uncurry tangentType <$> zip resultNames (snd <$> tys)
    _  -> error "Non-linear"

tangentType :: Var -> Type -> Type
tangentType v vTy = go (Proj v [], vTy)
  where
    go (p, ty) = case ty of
      FloatType     -> FloatType
      TupleType tys -> TupleType $ go <$> zip (appendProj p <$> [0..]) tys
      SumType   tys -> SumDepType p "v" $ tys <&> \t -> go (Proj "v" [], t)
      SumDepType _ _ _ -> error "unsupported"

splitTangents :: M.Map Var Type -> Scope -> TangentMap -> [Expr] -> (Expr -> Expr, Scope, [TangentMap])
splitTangents typeEnv scope env es = go scope env (freeVars <$> es)
  where
    go scope _   [] = (id, scope, [])
    go scope env (FV fvs fvs':tfvs) = case null fvs' of
      False -> error "Linear variables in a JVPed expression"
      True  -> case commonFvs of
        [] -> (subcontext, subscope, (M.restrictKeys env fvs):submaps)
          where (subcontext, subscope, submaps) = go scope (M.withoutKeys env fvs) tfvs
        _  -> (context . subcontext, subscope, emap:submaps)
          where
            allFresh@(vst':vst2':allDvs') = take (2 + 2 * length commonFvs) $ freshVars scope
            (dvs', dvs2') = splitAt (length commonFvs) allDvs'
            (subcontext, subscope, submaps) =
              go (scopeExt scope allFresh)
                (envExt (M.withoutKeys env fvs) commonFvs dvs') tfvs
            emap = envExt (M.withoutKeys env subfvs) commonFvs dvs2'
            context = LetDepMixed [] [vst', vst2'] (Dup (LTuple $ (env !) <$> commonFvs)) .
                      LetUnpackLin dvs'  tanTys vst' .
                      LetUnpackLin dvs2' tanTys vst2'
      where
        subfvs = getFree (fold tfvs)
        commonFvsS = fvs `S.intersection` subfvs
        commonFvs  = toList commonFvsS
        tanTys = commonFvs <&> \v -> tangentType v (typeEnv ! v)

jvp :: JVPFuncMap -> M.Map Var Type -> Scope -> Subst -> TangentMap -> Expr -> Expr
jvp funcEnv typeEnv scope subst env e = case e of
  App f vs_ [] -> ctx $ App (funcEnv ! f) ((subst !) <$> vs_) (zipWith (!) envs vs_)
    where (ctx, _, envs) = splitTangents typeEnv scope env (Var <$> vs_)
  App _ _ _  -> expectNonLinear
  Var v -> RetDep [subst ! v] [env ! v] $ MixedDepType [(Just v, typeEnv ! v)] [tangentType v (typeEnv ! v)]
  Lit v -> retDepPair scope (Lit v) LZero FloatType
  Tuple vs_ ->
    ctx $ retDepPair scope'
      (Tuple $ (subst !) <$> vs_) (LTuple $ zipWith (!) envs vs_)
      (TupleType $ (typeEnv !) <$> vs_)
    where
      (ctx, scope', envs) = splitTangents typeEnv scope env (Var <$> vs_)
  UnOp Sin e -> jvpUnOp e Sin $ UnOp Cos . Var
  UnOp Cos e -> jvpUnOp e Cos $ \v -> BinOp Mul (UnOp Sin (Var v)) (Lit (-1))
  UnOp Exp e -> jvpUnOp e Exp $ UnOp Exp . Var
  BinOp Add e1 e2 -> ctx $
    LetDepMixed [v1] [v1'] (rec typeEnv ctxScope subst env1 e1) $
    LetDepMixed [v2] [v2'] (rec typeEnv (ctxScope <> S.fromList [v1, v1']) subst env2 e2) $
    retDepPair (ctxScope <> S.fromList [v1, v1', v2, v2'])
      (BinOp Add (Var v1) (Var v2)) (LAdd (LVar v1') (LVar v2')) FloatType
    where
      (ctx, ctxScope, [env1, env2]) = splitTangents typeEnv scope env [e1, e2]
      v1:v1':v2:v2':_ = freshVars ctxScope
  BinOp Mul e1 e2 -> ctx $
    LetDepMixed [v1] [v1'] (rec typeEnv ctxScope subst env1 e1) $
    LetDepMixed [v2] [v2'] (rec typeEnv (ctxScope <> S.fromList [v1, v1']) subst env2 e2) $
    retDepPair (ctxScope <> S.fromList [v1, v1', v2, v2'])
      (BinOp Mul (Var v1) (Var v2))
      (LAdd (LScale (Var v2) (LVar v1'))
            (LScale (Var v1) (LVar v2')))
      FloatType
    where
      (ctx, ctxScope, [env1, env2]) = splitTangents typeEnv scope env [e1, e2]
      v1:v1':v2:v2':_ = freshVars ctxScope
  LVar _     -> expectNonLinear
  LTuple _   -> expectNonLinear
  LAdd _ _   -> expectNonLinear
  LScale _ _ -> expectNonLinear
  LZero      -> expectNonLinear
  Dup _      -> expectNonLinear
  Drop e -> Drop $ rec typeEnv scope subst env e
  LetUnpack vs_ v_ e ->
    ctx $
      LetUnpack    vs         (subst ! v_) $
      LetUnpackLin vs' tanTys (envv ! v_) $
      rec typeEnv' (scopeExt ctxScope allFresh) subst' env' e
    where
      (ctx, ctxScope, [envv, enve]) = splitTangents typeEnv scope env [Var v_, e]
      allFresh = take (2 * length vs_) $ freshVars ctxScope
      (vs, vs') = splitAt (length vs_) allFresh
      subst' = envExt subst vs_ vs
      env' = envExt enve vs_ vs'
      typeEnv' = envExt typeEnv vs_ vsTys_
      TupleType vsTys_ = typeEnv ! v_
      tanTys = vs <&> \v -> tangentType v (typeEnv ! v)
  LetUnpackLin _ _ _ _ -> expectNonLinear
  RetDep vs_ [] (MixedDepType tysBs_ []) ->
    ctx $ RetDep vs (zipWith (!) envs vs_)
      (MixedDepType (zip (Just <$> vs_) tys_) (uncurry tangentType <$> zip vs_ tys_))
    where
      (ctx, _, envs) = splitTangents typeEnv scope env (Var <$> vs_)
      vs = (subst !) <$> vs_
      tys_ = snd <$> tysBs_
  RetDep _ _ _ -> expectNonLinear
  LetDepMixed vs_ [] e1 e2 ->
    ctx $ LetDepMixed vs vs' (rec typeEnv ctxScope subst env1 e1) $
      rec (envExt typeEnv vs vsTys) ctxScope (envExt subst vs_ vs) (envExt env2 vs_ vs') e2
    where
      allFresh  = take (2 * length vs_) $ freshVars scope
      (vs, vs') = splitAt (length vs_) allFresh
      -- TODO: This env extension is sketchy?
      (ctx, ctxScope, [env1, env2]) = splitTangents typeEnv (scopeExt scope allFresh) env [e1, e2]
      -- TODO: Carry the original function env!
      Right (MixedDepType vsTysBs []) = typecheck undefined (mempty, typeEnv, mempty) e1
      vsTys = snd <$> vsTysBs
  LetDepMixed _ _ _ _ -> expectNonLinear
  Case v_ b_ (MixedDepType tysBs_ []) es_ -> ctx $ Case (subst ! v_) b (MixedDepType tysBs tys') es
    where
      b = freshVar scope
      -- TODO: Empty case
      (ctx, ctxScope, [envv, enve]) = splitTangents typeEnv (scopeExt scope [b]) env [Var v_, head es_]
      SumType conTys = typeEnv ! v_
      es = zip [0..] es_ <&> \(con, e) ->
        rec (envExt typeEnv [b_] [conTys !! con]) ctxScope (envExt subst [b_] [b]) (envExt enve [b_] [envv ! v_]) e
      tys_ = snd <$> tysBs_
      tysVs = MkVar "r" <$> [1..]
      tysBs = zip (Just <$> tysVs) tys_  -- This assumes that primal types are closed!
      tys' = uncurry tangentType <$> zip tysVs tys_  -- This assumes that primal types are closed!
  Case _ _ _ _ -> expectNonLinear
  Inject con v_ tys ->
    LetDepMixed [b] [] (Inject con (subst ! v_) tys) $
      RetDep [b] [env ! v_] (MixedDepType [(Just b, SumType tys)] [tangentType b (SumType tys)])
    where b = freshVar scope
  where
    rec = jvp funcEnv
    expectNonLinear = error "JVP only applies to completely non-linear computations"

    jvpUnOp :: Expr -> UnOp -> (Var -> Expr) -> Expr
    jvpUnOp e primOp tanCoef =
      LetDepMixed [v] [v'] (rec typeEnv scope subst env e) $
      retDepPair (scope <> S.fromList [v, v'])
        (UnOp primOp (Var v)) (LScale (tanCoef v) (LVar v')) FloatType
      where v : v' : _ = freshVars scope
