-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}

module Type (
  getType, checkType, HasType (..), Checkable (..), litType,
  isPure, exprEffs, blockEffs, extendEffect, binOpType, unOpType, isData,
  indexSetConcreteSize, checkNoShadow) where

import Prelude hiding (pi)
import Control.Monad
import Control.Monad.Except hiding (Except)
import Control.Monad.Reader
import Data.Functor
import Data.Text.Prettyprint.Doc
import GHC.Stack

import Array
import Syntax
import Env
import PPrint
import Cat

type TypeEnv = Bindings  -- Only care about type payload
type ClassEnv = MonMap Name [ClassName]

data OptionalEnv env = SkipChecks | CheckWith env  deriving Functor
type TypeCheckEnv = OptionalEnv (TypeEnv, EffectRow)
type TypeM = ReaderT TypeCheckEnv Except

class Pretty a => HasType a where
  typeCheck :: a -> TypeM Type

getType :: HasType a => a -> Type
getType x = ignoreExcept $ ctx $ runTypeCheck SkipChecks $ typeCheck x
  where ctx = addContext $ "Querying:\n" ++ pprint x

checkType :: HasType a => TypeEnv -> EffectRow -> a -> Except ()
checkType env eff x = void $ ctx $ runTypeCheck (CheckWith (env, eff)) $ typeCheck x
  where ctx = addContext $ "Checking:\n" ++ pprint x

runTypeCheck :: TypeCheckEnv -> TypeM a -> Except a
runTypeCheck env m = runReaderT m env

-- === Module interfaces ===

class Pretty a => Checkable a where
  checkValid :: a -> Except ()

instance Checkable Module where
  checkValid m@(Module ir decls bindings) =
    addContext ("Checking module:\n" ++ pprint m) $ asCompilerErr $ do
      let env = freeVars m
      forM_ (envNames env) $ \v -> when (not $ isGlobal $ v:>()) $
        throw CompilerErr $ "Non-global free variable in module: " ++ pprint v
      addContext "Checking IR variant" $ checkModuleVariant m
      addContext "Checking body types" $ do
        let block = Block decls $ Atom $ UnitVal
        void $ runTypeCheck (CheckWith (env, Pure)) (typeCheck block)
      addContext "Checking evaluated bindings" $ do
        checkBindings (env <> foldMap declAsScope decls) ir bindings

asCompilerErr :: Except a -> Except a
asCompilerErr (Left (Err _ c msg)) = Left $ Err CompilerErr c msg
asCompilerErr (Right x) = Right x

checkBindings :: TypeEnv -> IRVariant -> Bindings -> Except ()
checkBindings env ir bs = void $ runTypeCheck (CheckWith (env <> bs, Pure)) $
  mapM_ (checkBinding ir) $ envPairs bs

checkBinding :: IRVariant -> (Name, (Type, BinderInfo)) -> TypeM ()
checkBinding ir (GlobalName v, b@(ty, info)) =
  addContext ("binding: " ++ pprint (v, b)) $ do
    ty |: TyKind
    when (ir >= Evaluated && any (not . isGlobal) (envAsVars $ freeVars b)) $
      throw CompilerErr "Non-global name in a fully evaluated atom"
    case info of
      LetBound _ atom -> atom |: ty
      _ -> return ()
checkBinding _ _ = throw CompilerErr "Module bindings must have global names"

-- === Core IR ===

instance HasType Atom where
  typeCheck atom = case atom of
    Var v -> typeCheckVar v
    -- TODO: check arrowhead-specific effect constraints (both lam and arrow)
    Lam (Abs b (arr, body)) -> withBinder b $ do
      checkArrow arr
      bodyTy <- withAllowedEff (arrowEff arr) $ typeCheck body
      return $ Pi $ makeAbs b (arr, bodyTy)
    Pi (Abs b (arr, resultTy)) -> withBinder b $
      checkArrow arr >> resultTy|:TyKind $> TyKind
    Con con  -> typeCheckCon con
    TC tyCon -> typeCheckTyCon tyCon
    Eff eff  -> checkEffRow eff $> EffKind
    DataCon def@(DataDef _ paramBs cons) params con args -> do
      let (DataConDef _ argBs) = cons !! con
      let funTy = foldr
            (\(arr, b) body -> Pi (Abs b (arr, body)))
            (TypeCon def (map Var paramBs))
            (zip (repeat ImplicitArrow) paramBs ++ zip (repeat PureArrow) argBs)
      foldM checkApp funTy $ params ++ args
    TypeCon (DataDef _ bs _) params -> do
      let paramTys = map varType bs
      zipWithM_ (|:) params paramTys
      let paramTysRemaining = drop (length params) paramTys
      return $ foldr (-->) TyKind paramTysRemaining

typeCheckVar :: Var -> TypeM Type
typeCheckVar v@(name:>annTy) = do
  annTy |: TyKind
  when (annTy == EffKind) $
    throw CompilerErr "Effect variables should only occur in effect rows"
  checkWithEnv $ \(env, _) -> case envLookup env v of
    Nothing -> throw CompilerErr $ "Lookup failed: " ++ pprint v
    Just (ty, _) -> assertEq annTy ty $ "Annotation on var: " ++ pprint name
  return annTy

instance HasType Expr where
  typeCheck expr = case expr of
    App f x -> do
      fTy <- typeCheck f
      checkApp fTy x
    Atom x   -> typeCheck x
    Op   op  -> typeCheckOp op
    Hof  hof -> typeCheckHof hof
    Case e alts resultTy -> do
      checkWithEnv $ \_ -> do
        TypeCon def params <- typeCheck e
        let cons = applyDataDefParams def params
        checkEq  (length cons) (length alts)
        forM_ (zip cons alts) $ \((DataConDef _ bs'), (NAbs bs body)) -> do
          checkEq  (map varType bs') (map varType bs)
          resultTy' <- flip (foldr withBinder) bs $ typeCheck body
          checkEq resultTy resultTy'
      return resultTy

checkApp :: Type -> Atom -> TypeM Type
checkApp fTy x = do
  Pi piTy <- return fTy
  x |: absArgType piTy
  let (arr, resultTy) = applyAbs piTy x
  declareEffs $ arrowEff arr
  return resultTy

-- TODO: replace with something more precise (this is too cautious)
blockEffs :: Block -> EffectSummary
blockEffs (Block decls result) =
  foldMap (\(Let _ _ expr) -> exprEffs expr) decls <> exprEffs result

isPure :: Expr -> Bool
isPure expr = case exprEffs expr of
  NoEffects   -> True
  SomeEffects -> False

exprEffs :: Expr -> EffectSummary
exprEffs expr = case expr of
  Atom _ -> NoEffects
  App f _ -> functionEffs f
  Op op -> case op of
    PrimEffect _ _ -> SomeEffects
    _ -> NoEffects
  Hof hof -> case hof of
    For _ f -> functionEffs f
    SumCase _ l r -> functionEffs l <> functionEffs r
    While cond body -> functionEffs cond <> functionEffs body
    Linearize _ -> NoEffects
    Transpose _ -> NoEffects
    -- These are more convservative than necessary.
    -- TODO: make them more precise by de-duping with type checker
    RunReader _ _ -> SomeEffects
    RunWriter _   -> SomeEffects
    RunState _ _  -> SomeEffects

functionEffs :: Atom -> EffectSummary
functionEffs f = case getType f of
  Pi (Abs _ (arr, _)) | arrowEff arr == Pure -> NoEffects
  _ -> SomeEffects

instance HasType Block where
  typeCheck (Block decls result) = do
    checkingEnv <- ask
    case checkingEnv of
      SkipChecks -> typeCheck result
      CheckWith (env, _) -> do
        env' <- catFoldM checkDecl env decls
        withTypeEnv (env <> env') $ typeCheck result

checkDecl :: TypeEnv -> Decl -> TypeM TypeEnv
checkDecl env decl = withTypeEnv env $ addContext ctxStr $ case decl of
  Let _ b rhs -> do
    -- TODO: effects
    checkBinder b
    ty <- typeCheck rhs
    checkEq (varType b) ty
    return $ varBinding b
  Unpack bs rhs -> do
    mapM_ checkBinder bs
    TypeCon def params <- typeCheck rhs
    [DataConDef _ bs'] <- return $ applyDataDefParams def params
    assertEq (length bs) (length bs') ""
    zipWithM_ checkEq (map varType bs) (map varType bs')
    return $ foldMap varBinding bs
  where ctxStr = "checking decl:\n" ++ pprint decl

checkArrow :: Arrow -> TypeM ()
checkArrow arr = mapM_ checkEffRow arr

infixr 7 |:
(|:) :: HasType a => a -> Type -> TypeM ()
(|:) x reqTy = do
  ty <- typeCheck x
  checkEq reqTy ty

checkEq :: (Show a, Pretty a, Eq a) => a -> a -> TypeM ()
checkEq reqTy ty = checkWithEnv $ \_ -> assertEq reqTy ty ""

withBinder :: Binder -> TypeM a -> TypeM a
withBinder b m = checkBinder b >> extendTypeEnv (varBinding b) m

checkBinder :: Binder -> TypeM ()
checkBinder b@(_:>ty) = do
  checkWithEnv $ \(env, _) -> checkNoShadow env b
  ty |: TyKind

checkNoShadow :: (MonadError Err m, Pretty b) => Env a -> VarP b -> m ()
checkNoShadow env v = when (v `isin` env) $ throw CompilerErr $ pprint v ++ " shadowed"

-- === Core IR syntactic variants ===

type VariantM = ReaderT IRVariant Except

checkModuleVariant :: Module -> Except ()
checkModuleVariant (Module ir decls bindings) = do
  flip runReaderT ir $ mapM_ checkVariant decls
  flip runReaderT ir $ mapM_ (checkVariant . snd) bindings

class CoreVariant a where
  checkVariant :: a -> VariantM ()

instance CoreVariant Atom where
  checkVariant atom = addExpr atom $ case atom of
    Var v   -> checkVariantVar v
    Lam (Abs b (_, body)) -> checkVariantVar b >> checkVariant body
    Pi  (Abs b (arr, body)) -> do
      case arr of
        TabArrow -> alwaysAllowed
        _        -> goneBy Simp
      checkVariantVar b >> checkVariant body
    Con e -> checkVariant e >> forM_ e checkVariant
    TC  e -> checkVariant e >> forM_ e checkVariant
    Eff _ -> alwaysAllowed
    DataCon _ _ _ _ -> alwaysAllowed
    TypeCon _ _     -> alwaysAllowed

instance CoreVariant BinderInfo where
  checkVariant info = case info of
    DataBoundTypeCon _   -> alwaysAllowed
    DataBoundDataCon _ _ -> alwaysAllowed
    LetBound _ _     -> absentUntil Simp
    _                -> neverAllowed

instance CoreVariant Expr where
  checkVariant expr = addExpr expr $ case expr of
    App f x -> checkVariant f >> checkVariant x
    Atom x  -> checkVariant x
    Op  e   -> checkVariant e >> forM_ e checkVariant
    Hof e   -> checkVariant e >> forM_ e checkVariant
    Case e alts _ -> do
      checkVariant e
      forM_ alts $ \(NAbs _ body) -> checkVariant body

instance CoreVariant Decl where
  -- let annotation restrictions?
  checkVariant (Let _ b e) = checkVariantVar b >> checkVariant e
  checkVariant (Unpack bs e) = mapM checkVariantVar bs >> checkVariant e

instance CoreVariant Block where
  checkVariant (Block ds e) = mapM_ checkVariant ds >> checkVariant e

-- TODO: consider adding namespace restrictions
checkVariantVar :: Var ->  VariantM ()
checkVariantVar (_:>ty) = checkVariant ty

instance CoreVariant (PrimTC a) where
  checkVariant e = case e of
    -- TODO: only `TypeKind` past Simp is in the effect regions. We could make a
    -- distinct tyep for those, so we can rule out this case.
    TypeKind -> alwaysAllowed
    EffectRowKind  -> alwaysAllowed
    JArrayType _ _ -> neverAllowed
    _ -> alwaysAllowed

instance CoreVariant (PrimOp a) where
  checkVariant e = case e of
    Select _ _ _       -> alwaysAllowed  -- TODO: only scalar select after Simp
    _ -> alwaysAllowed

instance CoreVariant (PrimCon a) where
  checkVariant e = case e of
    ClassDictHole _ -> goneBy Core
    SumCon _ _ _    -> alwaysAllowed -- not sure what this should be
    RefCon _ _      -> neverAllowed
    _ -> alwaysAllowed

instance CoreVariant (PrimHof a) where
  checkVariant e = case e of
    For _ _       -> alwaysAllowed
    While _ _     -> alwaysAllowed
    SumCase _ _ _ -> goneBy Simp
    RunReader _ _ -> alwaysAllowed
    RunWriter _   -> alwaysAllowed
    RunState  _ _ -> alwaysAllowed
    Linearize _   -> goneBy Simp
    Transpose _   -> goneBy Simp
    Tile _ _ _    -> alwaysAllowed

-- TODO: namespace restrictions?
alwaysAllowed :: VariantM ()
alwaysAllowed = return ()

neverAllowed :: VariantM ()
neverAllowed = throw IRVariantErr $ "should never appear in finalized expression"

absentUntil :: IRVariant -> VariantM ()
absentUntil ir = do
  curIR <- ask
  when (curIR < ir) $ throw IRVariantErr $ "shouldn't appear until " ++ show ir

goneBy :: IRVariant -> VariantM ()
goneBy ir = do
  curIR <- ask
  when (curIR >= ir) $ throw IRVariantErr $ "shouldn't appear after " ++ show ir

addExpr :: (Pretty e, MonadError Err m) => e -> m a -> m a
addExpr x m = modifyErr m $ \e -> case e of
  Err IRVariantErr ctx s -> Err CompilerErr ctx (s ++ ": " ++ pprint x)
  _ -> e

-- === effects ===

checkEffRow :: EffectRow -> TypeM ()
checkEffRow (EffectRow effs effTail) = do
  forM_ effs $ \(_, v) -> Var (v:>TyKind) |: TyKind
  forM_ effTail $ \v -> do
    checkWithEnv $ \(env, _) -> case envLookup env (v:>()) of
      Nothing -> throw CompilerErr $ "Lookup failed: " ++ pprint v
      Just (ty, _) -> assertEq EffKind ty "Effect var"

declareEff :: Effect -> TypeM ()
declareEff (effName, h) = declareEffs $ EffectRow [(effName, h)] Nothing

declareEffs :: EffectRow -> TypeM ()
declareEffs effs = checkWithEnv $ \(_, allowedEffects) ->
  checkExtends allowedEffects effs

checkExtends :: MonadError Err m => EffectRow -> EffectRow -> m ()
checkExtends allowed (EffectRow effs effTail) = do
  let (EffectRow allowedEffs allowedEffTail) = allowed
  case effTail of
    Just _ -> assertEq allowedEffTail effTail ""
    Nothing -> return ()
  forM_ effs $ \eff -> unless (eff `elem` allowedEffs) $
    throw CompilerErr $ "Unexpected effect: " ++ pprint eff ++
                      "\nAllowed: " ++ pprint allowed

extendEffect :: Effect -> EffectRow -> EffectRow
extendEffect eff (EffectRow effs t) = EffectRow (eff:effs) t

-- === type checker monad combinators ===

checkWithEnv :: ((TypeEnv, EffectRow) -> TypeM ()) -> TypeM ()
checkWithEnv check = do
  optEnv <- ask
  case optEnv of
    SkipChecks -> return ()
    CheckWith env -> check env

updateTypeEnv :: (TypeEnv -> TypeEnv) -> TypeM a -> TypeM a
updateTypeEnv f m = flip local m $ fmap $ \(env, eff) -> (f env, eff)

extendTypeEnv :: TypeEnv -> TypeM a -> TypeM a
extendTypeEnv new m = updateTypeEnv (<> new) m

withTypeEnv :: TypeEnv -> TypeM a -> TypeM a
withTypeEnv new m = updateTypeEnv (const new) m

extendAllowedEffect :: Effect -> TypeM () -> TypeM ()
extendAllowedEffect eff m = updateAllowedEff (extendEffect eff) m

updateAllowedEff :: (EffectRow -> EffectRow) -> TypeM a -> TypeM a
updateAllowedEff f m = flip local m $ fmap $ \(env, eff) -> (env, f eff)

withAllowedEff :: EffectRow -> TypeM a -> TypeM a
withAllowedEff eff m = updateAllowedEff (const eff) m

-- === primitive ops and constructors ===

typeCheckTyCon :: TC -> TypeM Type
typeCheckTyCon tc = case tc of
  BaseType _       -> return TyKind
  ArrayType t      -> t|:TyKind >> return TyKind
  IntRange a b     -> a|:IntTy >> b|:IntTy >> return TyKind
  IndexRange t a b -> t|:TyKind >> mapM_ (|:t) a >> mapM_ (|:t) b >> return TyKind
  IndexSlice n l   -> n|:TyKind >> l|:TyKind >> return TyKind
  SumType  l r     -> l|:TyKind >> r|:TyKind >> return TyKind
  PairType a b     -> a|:TyKind >> b|:TyKind >> return TyKind
  UnitType         -> return TyKind
  RefType r a      -> r|:TyKind >> a|:TyKind >> return TyKind
  TypeKind         -> return TyKind
  EffectRowKind    -> return TyKind
  JArrayType _ _   -> undefined

typeCheckCon :: Con -> TypeM Type
typeCheckCon con = case con of
  Lit l -> return $ BaseTy $ litType l
  ArrayLit ty _ -> return $ ArrayTy ty
  AnyValue t -> t|:TyKind $> t
  SumCon _ l r -> SumTy <$> typeCheck l <*> typeCheck r
  PairCon x y -> PairTy <$> typeCheck x <*> typeCheck y
  UnitCon -> return UnitTy
  RefCon r x -> r|:TyKind >> RefTy r <$> typeCheck x
  Coerce t@(Var _) _ -> t |: TyKind $> t
  Coerce t e -> do
    sourceTy <- coercionSourceType t
    e |: sourceTy $> t
    where
      coercionSourceType :: Type -> TypeM Type
      coercionSourceType ty = case ty of
        TC (ArrayType  st   ) -> ArrayTy <$> coercionSourceType st
        TC (IntRange   _ _  ) -> return IntTy -- from ordinal
        TC (IndexRange _ _ _) -> return IntTy -- from ordinal
        TC (IndexSlice _ _  ) -> return IntTy -- from ordinal of the first slice element
        _ -> throw TypeErr $ "Unexpected coercion destination type: " ++ pprint t
  SumAsProd ty _ _ -> return ty  -- TODO: check!
  ClassDictHole ty -> ty |: TyKind >> return ty

typeCheckOp :: Op -> TypeM Type
typeCheckOp op = case op of
  TabCon ty xs -> do
    ty |: TyKind
    TabTy v a <- return ty
    -- TODO: Propagate the binder to support dependently typed dimensions?
    mapM_ (|:a) xs
    Just n <- return $ indexSetConcreteSize $ varType v
    assertEq n (length xs) "Index set size mismatch"
    return ty
  Fst p -> do { PairTy x _ <- typeCheck p; return x}
  Snd p -> do { PairTy _ y <- typeCheck p; return y}
  SumGet x isLeft -> do
    SumTy l r <- typeCheck x
    l|:TyKind >> r|:TyKind
    return $ if isLeft then l else r
  SumTag x -> do
    SumTy l r <- typeCheck x
    l|:TyKind >> r|:TyKind
    return $ TC $ BaseType $ Scalar BoolType
  ScalarBinOp binop x1 x2 ->
    x1 |: BaseTy (Scalar t1) >> x2 |: BaseTy (Scalar t2) $> BaseTy (Scalar tOut)
    where (t1, t2, tOut) = binOpType binop
  ScalarUnOp unop x -> x |: BaseTy (Scalar ty) $> BaseTy (Scalar outTy)
    where (ty, outTy) = unOpType unop
  Select p x y -> do
    p|:BoolTy
    ty <- typeCheck x
    y |:ty
    return ty
  IntAsIndex ty i -> ty|:TyKind >> i|:IntTy $> ty
  IndexAsInt i -> typeCheck i $> IntTy
  IdxSetSize i -> typeCheck i $> IntTy
  FFICall _ ansTy args -> do
    -- We have no signatures for FFI functions so we just assume that the types are ok
    mapM_ typeCheck args
    return $ BaseTy ansTy
  Inject i -> do
    TC (IndexRange ty _ _) <- typeCheck i
    return ty
  PrimEffect ref m -> do
    RefTy (Var (h:>TyKind)) s <- typeCheck ref
    case m of
      MGet    ->         declareEff (State , h) $> s
      MPut  x -> x|:s >> declareEff (State , h) $> UnitTy
      MAsk    ->         declareEff (Reader, h) $> s
      MTell x -> x|:s >> declareEff (Writer, h) $> UnitTy
  IndexRef ref i -> do
    RefTy h (TabTy v a) <- typeCheck ref
    i |: (varType v)
    return $ RefTy h a
  FstRef ref -> do
    RefTy h (PairTy a _) <- typeCheck ref
    return $ RefTy h a
  SndRef ref -> do
    RefTy h (PairTy _ b) <- typeCheck ref
    return $ RefTy h b
  ArrayOffset arr idx off -> do
    -- TODO: b should be applied!!
    ArrayTy (TabTyAbs a) <- typeCheck arr
    off |: IntTy
    idx |: absArgType a
    return $ ArrayTy $ snd $ applyAbs a idx
  ArrayLoad arr -> do
    ArrayTy (BaseTy b)  <- typeCheck arr
    return $ BaseTy b
  SliceOffset s i -> do
    TC (IndexSlice n l) <- typeCheck s
    l' <- typeCheck i
    checkEq l l'
    return n
  SliceCurry s i -> do
    TC (IndexSlice n (PairTy u v)) <- typeCheck s
    u' <- typeCheck i
    checkEq u u'
    return $ TC $ IndexSlice n v
  VectorBinOp binop x1 x2 ->
    x1 |: BaseTy (Vector t1) >> x2 |: BaseTy (Vector t2) $> BaseTy (Vector tOut)
    where (t1, t2, tOut) = binOpType binop
  VectorPack xs -> do
    unless (length xs == vectorWidth) $ throw TypeErr lengthMsg
    BaseTy (Scalar sb) <- typeCheck $ head xs
    mapM_ (|: (BaseTy (Scalar sb))) xs
    return $ BaseTy $ Vector sb
    where lengthMsg = "VectorBroadcast should have exactly " ++ show vectorWidth ++
                      " elements: " ++ pprint op
  VectorIndex x i -> do
    BaseTy (Vector sb) <- typeCheck x
    i |: TC (IntRange (IntVal 0) (IntVal vectorWidth))
    return $ BaseTy $ Scalar sb
  ThrowError ty -> ty|:TyKind $> ty

typeCheckHof :: Hof -> TypeM Type
typeCheckHof hof = case hof of
  For _ f -> do
    Pi (Abs n (arr, a)) <- typeCheck f
    -- TODO: check `n` isn't free in `eff`
    declareEffs $ arrowEff arr
    return $ Pi $ Abs n (TabArrow, a)
  Tile dim fT fS -> do
    FunTy tv eff  tr    <- typeCheck fT
    FunTy sv eff' sr    <- typeCheck fS
    TC (IndexSlice n l) <- return $ varType tv
    (dv, b, b')         <- zipExtractDim dim tr sr
    checkEq l (varType dv)
    checkEq n (varType sv)
    when (dv `isin` freeVars b ) $ throw TypeErr "Cannot tile dimensions that other dimensions depend on"
    when (sv `isin` freeVars b') $ throw TypeErr "Cannot tile dimensions that other dimensions depend on"
    checkEq b b'
    checkEq eff eff'
    -- TODO: check `tv` and `sv` isn't free in `eff`
    declareEffs eff
    return $ replaceDim dim tr n
    where
      zipExtractDim 0 (TabTy dv b) b' = return (dv, b, b')
      zipExtractDim d (TabTy dv b) (TabTy sv b') =
        if varType dv == varType sv
          then zipExtractDim (d-1) b b'
          else throw TypeErr $ "Result type of tiled and non-tiled bodies differ along " ++
                               "dimension " ++ show (dim - d + 1) ++ ": " ++
                               pprint b ++ " and " ++ pprint b'
      zipExtractDim d _ _ = throw TypeErr $
        "Tiling over dimension " ++ show dim ++ " has to produce a result with at least " ++
        show (dim + 1) ++ " dimensions, but it has only " ++ show (dim - d)

      replaceDim 0 (TabTy _ b) n  = TabTy (NoName:>n) b
      replaceDim d (TabTy dv b) n = TabTy dv $ replaceDim (d-1) b n
      replaceDim _ _ _ = error "This should be checked before"

  While cond body -> do
    Pi (Abs (NoName:>UnitTy) (arr , condTy)) <- typeCheck cond
    Pi (Abs (NoName:>UnitTy) (arr', bodyTy)) <- typeCheck body
    declareEffs $ arrowEff arr
    declareEffs $ arrowEff arr'
    checkEq BoolTy condTy
    checkEq UnitTy bodyTy
    return UnitTy
  SumCase st l r -> do
    Pi (Abs (NoName:>la) (PlainArrow Pure, lb)) <- typeCheck l
    Pi (Abs (NoName:>ra) (PlainArrow Pure, rb)) <- typeCheck r
    checkEq lb rb
    st |: SumTy la ra
    return lb
  Linearize f -> do
    Pi (Abs (NoName:>a) (PlainArrow Pure, b)) <- typeCheck f
    return $ a --> PairTy b (a --@ b)
  Transpose f -> do
    Pi (Abs (NoName:>a) (LinArrow, b)) <- typeCheck f
    return $ b --@ a
  RunReader r f -> do
    (resultTy, readTy) <- checkAction Reader f
    r |: readTy
    return resultTy
  RunWriter f -> uncurry PairTy <$> checkAction Writer f
  RunState s f -> do
    (resultTy, stateTy) <- checkAction State f
    s |: stateTy
    return $ PairTy resultTy stateTy

checkAction :: EffectName -> Atom -> TypeM (Type, Type)
checkAction effName f = do
  BinaryFunTy regionBinder refBinder eff resultTy <- typeCheck f
  regionName:>_ <- return regionBinder
  let region = Var regionBinder
  extendAllowedEffect (effName, regionName) $ declareEffs eff
  checkEq (varAnn regionBinder) TyKind
  RefTy region' referentTy <- return $ varAnn refBinder
  checkEq region' region
  return (resultTy, referentTy)

litType :: LitVal -> BaseType
litType v = case v of
  IntLit  _ -> Scalar IntType
  RealLit _ -> Scalar RealType
  StrLit  _ -> Scalar StrType
  BoolLit _ -> Scalar BoolType
  VecLit  l -> Vector sb
    where (Scalar sb) = litType $ head l

binOpType :: BinOp -> (ScalarBaseType, ScalarBaseType, ScalarBaseType)
binOpType op = case op of
  IAdd   -> (i, i, i);  ISub   -> (i, i, i)
  IMul   -> (i, i, i);  IDiv   -> (i, i, i)
  IRem   -> (i, i, i);  IPow   -> (i, i, i)
  ICmp _ -> (i, i, b)
  FAdd   -> (r, r, r);  FSub   -> (r, r, r)
  FMul   -> (r, r, r);  FDiv   -> (r, r, r);
  FPow   -> (r, r, r)
  FCmp _ -> (r, r, b)
  BAnd   -> (b, b, b);  BOr    -> (b, b, b)
  where b = BoolType
        i = IntType
        r = RealType

unOpType :: UnOp -> (ScalarBaseType, ScalarBaseType)
unOpType op = case op of
  IntToReal       -> (IntType , RealType)
  BoolToInt       -> (BoolType, IntType)
  UnsafeIntToBool -> (IntType , BoolType)
  Exp             -> (RealType, RealType)
  Exp2            -> (RealType, RealType)
  Log             -> (RealType, RealType)
  Log2            -> (RealType, RealType)
  Log10           -> (RealType, RealType)
  Sin             -> (RealType, RealType)
  Cos             -> (RealType, RealType)
  Tan             -> (RealType, RealType)
  Sqrt            -> (RealType, RealType)
  Floor           -> (RealType, IntType )
  Ceil            -> (RealType, IntType )
  Round           -> (RealType, IntType )
  FNeg            -> (RealType, RealType)
  BNot            -> (BoolType, BoolType)

indexSetConcreteSize :: Type -> Maybe Int
indexSetConcreteSize ty = case ty of
  FixedIntRange low high -> Just $ high - low
  BoolTy  -> Just 2
  _ -> Nothing

checkDataLike :: MonadError Err m => String -> Bindings -> Type -> m ()
checkDataLike msg env ty = case ty of
  Var v -> error "Not implemented"
  TabTy _ b -> recur b
  -- TODO: check that data constructor arguments are data-like, and so on
  TypeCon _ _ -> return ()
  TC con -> case con of
    BaseType _       -> return ()
    PairType a b     -> recur a >> recur b
    UnitType         -> return ()
    SumType l r      -> checkDataLike msg env l >> checkDataLike msg env r
    IntRange _ _     -> return ()
    IndexRange _ _ _ -> return ()
    _ -> throw TypeErr $ pprint ty ++ msg
  _   -> throw TypeErr $ pprint ty ++ msg
  where recur x = checkDataLike msg env x

checkData :: MonadError Err m => Bindings -> Type -> m ()
checkData = checkDataLike " is not serializable"

--TODO: Make this work even if the type has type variables!
isData :: Bindings -> Type -> Bool
isData bindings ty = case checkData bindings ty of
  Left  _ -> False
  Right _ -> True
