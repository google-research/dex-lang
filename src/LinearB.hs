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
          = LetUnpack    [Var]       Var  Expr
          | LetUnpackLin [Var]       Var  Expr
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
          | Cast           Expr  MixedDepType
          | RetDep         [Var] [Var]
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
    Cast e ty -> parens (pretty e) <> "@" <> pretty ty
    RetDep vs vs' -> prettyMixedVars vs vs'
    LetDepMixed vs vs' e1 e2 -> "let" <+> prettyMixedVars vs vs' <+> "=" <> (nest 2 $ group $ line <> pretty e1) <> hardline <> pretty e2
    LetUnpack vs v e -> "explodeN" <+> prettyMixedVars vs [] <+> "=" <+> pretty v <> hardline <> pretty e
    LetUnpackLin vs' v e -> "explodeL" <+> prettyMixedVars [] vs' <+> "=" <+> pretty v <> hardline <> pretty e
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
  Cast e ty -> freeVars e <> freeVarsMixedType ty
  RetDep vs linVs -> FV (S.fromList vs) (S.fromList linVs)
  LetDepMixed vs linVs e1 e2 -> FV
    (freeE1    `S.union` (freeE2    `S.difference` S.fromList vs   ))
    (freeLinE1 `S.union` (freeLinE2 `S.difference` S.fromList linVs))
    where
      FV freeE1 freeLinE1 = freeVars e1
      FV freeE2 freeLinE2 = freeVars e2
  LetUnpack vs v e -> freeVar v <> (freeVars e `hiding` FV (S.fromList vs) mempty)
  LetUnpackLin vs v e -> freeLinVar v <> (freeVars e `hiding` FV mempty (S.fromList vs))
  Case v b ty exprs -> freeVar v <> FV fe' fel' <> freeVarsMixedType ty
    where
      FV fe fel' = foldMap freeVars exprs
      fe' = fe `S.difference` S.singleton b
  Inject _ v tys -> freeVar v <> FV (foldMap freeVarsType tys) mempty
  where
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
  SumDepType p v tys -> SumDepType (substProj s p) v' (substType (s <> M.singleton v v') <$> tys)
    where v' = freshVar $ S.fromList (toList s) <> foldMap freeVarsType tys

substProj :: Subst -> ProjExpr -> ProjExpr
substProj s (Proj v ps) = case M.lookup v s of
  Nothing -> Proj v  ps
  Just v' -> Proj v' ps


-------------------- Type checking --------------------

type TypeEqEvidenceEnv = M.Map Var (HS.HashSet TypeEqEvidence)
type TypeEnv = (TypeEqEvidenceEnv, M.Map Var Type, M.Map Var Type)

-- TODO: Should occurences of non-linear vars in types count
-- towards the "at least one use" rule? Right now they do!
typecheck :: Program -> TypeEnv -> Expr -> Either String MixedDepType
typecheck prog tenv@(evid, env, linEnv) expr = case expr of
  Cast e ty -> do
    let FV freeE _ = freeVars e
    let FV freeTy _ = freeVarsMixedType ty
    check "Cast: non-linear environment mismatched" $
      S.union freeE freeTy == M.keysSet env
    inferredTy <- typecheck prog (evid, env `M.restrictKeys` freeE, linEnv) e
    check "Cast: incompatible annotation" $ mixedTypeEqualGiven scope evid inferredTy ty
    return ty
  RetDep vs linVs -> do
    check "RetDep non-linear environment mismatched" $ S.fromList vs == M.keysSet env
    check "Repeated linear returns" $ unique linVs
    check "RetDep linear environment mismatched" $ S.fromList linVs == M.keysSet linEnv
    return $ MixedDepType (zip (Just <$> vs) ((env !) <$> vs)) ((linEnv !) <$> linVs)
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
        -- TODO: Delete ty free vars if necessary
        let eEnv = case es of
                     [] -> error "shouldn't be needed"
                     (he:_) -> case S.member v (getFree $ freeVars he) of
                       True  -> env
                       False -> M.delete v env
        forM_ (zip3 [0..] tys es) $ \(con, bty, e) -> do
          let eEvid = addEvidence evid v $ InjEvidence con b
          eTy <- typecheck prog (eEvid, envExt eEnv [b] [bty], linEnv) e
          check ("Cases return different types: expected " ++ show ty ++ ", got " ++ show eTy) $
            mixedTypeAlphaEqual scope eTy ty
        return ty
      _ -> throwError "Case on a non-sum type"
  Inject con v tys -> do
    check "Inject: non-linear env mismatch" $ S.insert v (foldMap freeVarsType tys) == M.keysSet env
    check "Inject: non-empty linear env" $ null linEnv
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
        typecheck prog (evid, env, envExt (M.delete v linEnv) vs tys) e
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
    let Program progMap = prog
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
    checkTypeEq a b = check ("expected " ++ show a ++ " and " ++ show b ++ " to be equal") $ typeAlphaEqual scope a b

    addEvidence :: TypeEqEvidenceEnv -> Var -> TypeEqEvidence -> TypeEqEvidenceEnv
    addEvidence env v e = M.insertWith (<>) v (HS.singleton e) env

    scope = M.keysSet env <> M.keysSet linEnv

typecheckFunc :: Program -> FuncName -> Either String ()
typecheckFunc prog@(Program funcMap) name = case typecheck prog env body of
  Left  err -> Left err
  Right ty  -> case mixedTypeAlphaEqual (S.fromList $ fst <$> formals) ty resultType of
    True  -> Right ()
    False -> Left "Return type mismatch"
  where
    FuncDef formals linFormals resultType body = funcMap ! name
    env = (mempty, M.fromList formals, M.fromList linFormals)

typecheckProgram :: Program -> Either String ()
typecheckProgram prog@(Program progMap) = sequence_ $ typecheckFunc prog <$> M.keys progMap

typeAlphaEqual :: Scope -> Type -> Type -> Bool
typeAlphaEqual s = typeEqualGiven s mempty

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

mixedTypeAlphaEqual :: Scope -> MixedDepType -> MixedDepType -> Bool
mixedTypeAlphaEqual s = mixedTypeEqualGiven s mempty

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

retDepPair :: Scope -> Expr -> Expr -> Expr
retDepPair scope e1 e2 =
  LetDepMixed [v] []   e1 $
  LetDepMixed []  [v'] e2 $
  RetDep [v] [v']
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
splitTangents _ scope env es = go scope env (freeVars <$> es)
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
                      LetUnpackLin dvs'  vst' .
                      LetUnpackLin dvs2' vst2'
      where
        subfvs = getFree (fold tfvs)
        commonFvsS = fvs `S.intersection` subfvs
        commonFvs  = toList commonFvsS

jvp :: JVPFuncMap -> M.Map Var Type -> Scope -> Subst -> TangentMap -> Expr -> Expr
jvp funcEnv typeEnv scope subst env e = case e of
  App f vs_ [] -> ctx $ App (funcEnv ! f) ((subst !) <$> vs_) (zipWith (!) envs vs_)
    where (ctx, _, envs) = splitTangents typeEnv scope env (Var <$> vs_)
  App _ _ _  -> expectNonLinear
  Var v -> RetDep [subst ! v] [env ! v]
  Lit v -> retDepPair scope (Lit v) LZero
  Tuple vs_ ->
    ctx $ retDepPair scope'
      (Tuple $ (subst !) <$> vs_)
      (Cast (LTuple $ zipWith (!) envs vs_)
            (MixedDepType [] [TupleType $ vs_ <&> \v_ -> tangentType v_ (typeEnv ! v_)]))
    where
      (ctx, scope', envs) = splitTangents typeEnv scope env (Var <$> vs_)
  UnOp Sin e -> jvpUnOp e Sin $ UnOp Cos . Var
  UnOp Cos e -> jvpUnOp e Cos $ \v -> BinOp Mul (UnOp Sin (Var v)) (Lit (-1))
  UnOp Exp e -> jvpUnOp e Exp $ UnOp Exp . Var
  BinOp Add e1 e2 -> ctx $
    LetDepMixed [v1] [v1'] (rec typeEnv ctxScope subst env1 e1) $
    LetDepMixed [v2] [v2'] (rec typeEnv (ctxScope <> S.fromList [v1, v1']) subst env2 e2) $
    retDepPair (ctxScope <> S.fromList [v1, v1', v2, v2'])
      (BinOp Add (Var v1) (Var v2)) (LAdd (LVar v1') (LVar v2'))
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
      LetUnpack    vs  (subst ! v_) $
      LetUnpackLin vs' (envv ! v_) $
      LetDepMixed  [] vs' (Cast (RetDep [] vs') (MixedDepType [] tanTys)) $
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
  LetUnpackLin _ _ _ -> expectNonLinear
  RetDep vs_ [] ->
    ctx $ RetDep vs (zipWith (!) envs vs_)
    where
      (ctx, _, envs) = splitTangents typeEnv scope env (Var <$> vs_)
      vs = (subst !) <$> vs_
  RetDep _ _ -> expectNonLinear
  LetDepMixed vs_ [] e1 e2 ->
    ctx $ LetDepMixed vs vs' (rec typeEnv ctxScope subst env1 e1) $
      rec (envExt typeEnv vs_ vsTys) ctxScope (envExt subst vs_ vs) (envExt env2 vs_ vs') e2
    where
      allFresh  = take (2 * length vs_) $ freshVars scope
      (vs, vs') = splitAt (length vs_) allFresh
      (ctx, ctxScope, [env1, env2]) = splitTangents typeEnv (scopeExt scope allFresh) env [e1, e2]
      -- TODO: Carry the original function env!
      Right (MixedDepType vsTysBs []) = typecheck undefined (mempty, typeEnv, mempty) e1
      vsTys = snd <$> vsTysBs
  LetDepMixed _ _ _ _ -> expectNonLinear
  Case v_ b_ (MixedDepType tysBs_ []) es_ -> ctx $ Case (subst ! v_) b (MixedDepType tysBs tys') es
    where
      allFresh@[b, b'] = take 2 $ freshVars scope
      -- TODO: Empty case
      (ctx, ctxScope, [envv, enve]) = splitTangents typeEnv (scopeExt scope allFresh) env [Var v_, head es_]
      SumType conTys = typeEnv ! v_
      es = zip [0..] es_ <&> \(con, e) ->
             LetDepMixed [] [b'] (Cast (LVar (envv ! v_)) (MixedDepType [] [tangentType b (conTys !! con)])) $
             rec (envExt typeEnv [b_] [conTys !! con])
                 ctxScope
                 (envExt subst [b_] [b])
                 (envExt enve [b_] [b'])
                 e
      tys_ = snd <$> tysBs_
      tysVs = MkVar "r" <$> [1..]
      tysBs = zip (Just <$> tysVs) tys_  -- This assumes that primal types are closed!
      tys' = uncurry tangentType <$> zip tysVs tys_  -- This assumes that primal types are closed!
  Case _ _ _ _ -> expectNonLinear
  Inject con v_ tys ->
    LetDepMixed [b] [] (Inject con (subst ! v_) tys) $
    LetDepMixed [] [bt] (Cast (LVar $ env ! v_) (MixedDepType [] [tangentType b (SumType tys)])) $
      RetDep [b] [bt]
    where b:bt:_ = freshVars scope
  -- Not very important, since we generally only emit it in jvp
  Cast _ _ -> undefined
  where
    rec = jvp funcEnv
    expectNonLinear = error "JVP only applies to completely non-linear computations"

    jvpUnOp :: Expr -> UnOp -> (Var -> Expr) -> Expr
    jvpUnOp e primOp tanCoef =
      LetDepMixed [v] [v'] (rec typeEnv scope subst env e) $
      retDepPair (scope <> S.fromList [v, v'])
        (UnOp primOp (Var v)) (LScale (tanCoef v) (LVar v'))
      where v : v' : _ = freshVars scope

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


-- TODO: How to transfer evidence between the non-linear and linear functions?
-- We need it for the tangent type casts to be valid.
-- (1) We could have a new type for "evidence witness" values (a'la GADTs).
--     The only problem is that those would have to be non-linear values dependent
--     on non-linear values, which we don't support.
-- (2) The pairing method (bundling linear cast with a non-linear op) doesn't work
--     with unzipping at all, so that's not a solution either.

-- The nonlinear returned function packages the tape in the _last_ returned value
unzipFunc :: Program -> Program -> FuncDef -> (FuncDef, FuncDef)
unzipFunc orig new def = assert implLimitationsOk $
  ( FuncDef formalsWithTys [] nonlinFuncTy nonlinBody
  -- TOOD: We could bundle formalsWithTys into residuals, but we'd need to
  -- adjust linRetTys to use projections from residuals instead of formal vars.
  -- TODO: We have to take retTys, or else linRetTys are not well scoped.
  -- TODO: Take in formals or else linRetTys might not be well scoped.
  , FuncDef (retFormalsWithTys ++ [(resVar, residualTupleTy)])
      linFormalsWithTys (MixedDepType [] linRetTys) linBody
  )
  where
    (FuncDef formalsWithTys linFormalsWithTys (MixedDepType retTysBs linRetTys) body) = def
    (formals, _) = unzip formalsWithTys
    (linFormals, _) = unzip linFormalsWithTys
    formalsScope = scopeExt (scopeExt mempty formals) linFormals
    formalsSubst = envExt (envExt mempty formals formals) linFormals linFormals
    ((ctx, ctxScope), ubody, ubody') = unzipExpr orig formalsScope formalsSubst body

    resVar:retVarsHints = take (1 + length retTysBs) $ freshVars ctxScope
    retVars = zip retTysBs retVarsHints <&> \((mb, _), h) -> case mb of Nothing -> h; Just b -> b
    residualVars = toList $ getFree (freeVars ubody') `S.difference`
                            (scopeExt mempty $ linFormals)
    retFormalsWithTys = zip retVars (snd <$> retTysBs)

    resOnlyBody = ctx $ LetDepMixed [] [] (Drop ubody) $ Tuple residualVars
    MixedDepType [(_, residualTupleTy)] [] = case
      typecheck new (mempty, M.fromList formalsWithTys, mempty) resOnlyBody of
        Right res -> res
        Left err -> error $ err ++ " in\n" ++ show (pretty resOnlyBody)
          ++ "\nwith env\n" ++ show (pretty formalsWithTys)
    nonlinFuncTy = MixedDepType (retTysBs ++ [(Nothing, residualTupleTy)]) []
    nonlinBody = ctx $
      LetDepMixed retVars [] ubody $
      LetDepMixed [resVar] [] (Tuple residualVars) $
      RetDep (retVars ++ [resVar]) []

    -- TODO: Important! Can this drop mess up complexity results??
    linBody = LetDepMixed [] [] (Drop $ Tuple retVars) $
              LetUnpack residualVars resVar $
              ubody'

    -- TODO: Refresh the retTysBs to make sure they don't run into conflicts with other vars
    implLimitationsOk = (not $ any (`S.member` formalsScope) retVars) &&
                        (not $ any (== resVar) retVars)


-- The Scope is the set of variables used by the generated body so far
-- (with respect to which new variables must be fresh).
-- The Subst is the remapping of old variable names to new ones.
-- The return is
-- - The binding list, represented as an Expr -> Expr function
-- - The Scope in that context (scope argument is always contained in it)
-- - The non-linear result expression
-- - The linear result expression
unzipExpr :: Program -> Scope -> Subst -> Expr -> ((Expr -> Expr, Scope), Expr, Expr)
unzipExpr orig scope subst expr = case expr of
  RetDep vs vs' ->
    ( (id, scope)
    , RetDep ((subst !) <$> vs) []
    , RetDep [] ((subst !) <$> vs')
    )
  LetDepMixed vs vs' e1 e2 ->
      ( (ctx1 . LetDepMixed uvs [] ue1 . ctx2, scopeCtx2)
      , ue2
      , LetDepMixed [] uvs' ue1' ue2'
      )
    where
      ((ctx1, scopeCtx1), ue1, ue1') = rec scope subst e1
      (uvs, uvs') = splitAt (length vs) $ take (length vs + length vs') $ freshVars scopeCtx1
      e2Subst = envExt (envExt subst vs uvs) vs' uvs'
      e2Scope = scopeExt (scopeExt scope uvs) uvs'
      ((ctx2, scopeCtx2), ue2, ue2') = rec e2Scope e2Subst e2
  LetUnpack vs v e ->
      ((LetUnpack uvs (subst ! v) . ctx, ctxScope), ue, ue')
    where
      uvs = take (length vs) $ freshVars scope
      subst' = envExt subst vs uvs
      scope' = (scopeExt scope uvs)
      ((ctx, ctxScope), ue, ue') = rec scope' subst' e
  LetUnpackLin vs v e ->
      ( (ctx, ctxScope)
      , ue
      , LetUnpackLin uvs (subst ! v) ue'
      )
    where
      uvs = take (length vs) $ freshVars scope
      subst' = envExt subst vs uvs
      scope' = (scopeExt scope uvs)
      ((ctx, ctxScope), ue, ue') = rec scope' subst' e
  App _ _ _ -> undefined
  --App name vs vs' ->
      --( (LetMixed (retVars ++ [tapeVar]) [] (App (name ++ ".nonlin") uvs []), scope2)
      --, Ret retVars []
      --, App (name ++ ".lin") [tapeVar] uvs'
      --)
    --where
      --uvs = (subst !) <$> vs
      --uvs' = (subst !) <$> vs'
      --retTys = nonLinRetTys orig name
      --tapeVar:retVars = take (1 + length retTys) $ freshVars scope
      --scope2 = scopeExt scope $ tapeVar:retVars
  Var v -> ((id, scope), Var (subst ! v), trivial)
  Lit f -> ((id, scope), Lit f, trivial)
  Tuple vs -> ((id, scope), Tuple $ (subst !) <$> vs, trivial)
  UnOp op e -> ((ctx, ctxScope), UnOp op ue, ue')
    where ((ctx, ctxScope), ue, ue') = rec scope subst e
  BinOp op e1 e2 -> ((ctx1 . ctx2, ctxScope2), BinOp op ue1 ue2, ue')
    where
      ((ctx1, ctxScope1), ue1, ue1') = rec scope subst e1
      ((ctx2, ctxScope2), ue2, ue2') = rec ctxScope1 subst e2
      ue' = LetDepMixed [] [] ue1' ue2'
  LVar v -> ((id, scope), trivial, LVar (subst ! v))
  LTuple vs -> ((id, scope), trivial, LTuple $ (subst !) <$> vs)
  LAdd e1 e2 -> ((ctx1 . ctx2, ctxScope2), ue, LAdd ue1' ue2')
    where
      ((ctx1, ctxScope1), ue1, ue1') = rec scope subst e1
      ((ctx2, ctxScope2), ue2, ue2') = rec ctxScope1 subst e2
      ue = LetDepMixed [] [] ue1 ue2
  LScale s e ->
    ( (sCtx . eCtx, eCtxScope)
    , LetDepMixed [] [] ue  $ trivial
    , LetDepMixed [] [] us' $ LScale us ue'
    )
    where
      ((sCtx, sCtxScope), us, us') = rec scope     subst s
      ((eCtx, eCtxScope), ue, ue') = rec sCtxScope subst e
  LZero -> ((id, scope), trivial, LZero)
  Dup e -> ((ctx, ctxScope), ue, Dup ue')
    where ((ctx, ctxScope), ue, ue') = rec scope subst e
  Drop e -> ((ctx, ctxScope), Drop ue, Drop ue')
    where ((ctx, ctxScope), ue, ue') = rec scope subst e
  --Case v_ b_ (MixedDepType tysBs_ linTys_) es_ -> undefined
  Case _ _ _ _ -> undefined
  Inject con v_ tys -> ((id, scope), Inject con (subst ! v_) tys, trivial)
  where
    rec = unzipExpr orig
    trivial = RetDep [] []

