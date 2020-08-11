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
  isPure, exprEffs, blockEffs, extendEffect, isData, checkBinOp, checkUnOp,
  checkIntBaseType, checkFloatBaseType,
  indexSetConcreteSize, checkNoShadow) where

import Prelude hiding (pi)
import Control.Monad
import Control.Monad.Except hiding (Except)
import Control.Monad.Reader
import Data.Foldable (toList)
import Data.Functor
import qualified Data.Map.Strict as M
import Data.Text.Prettyprint.Doc

import Array
import Syntax
import Env
import PPrint
import Cat
import Util (bindM2)

type TypeEnv = Bindings  -- Only care about type payload

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
        checkBindings (env <> foldMap boundVars decls) ir bindings

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
      let paramVars = fmap (\(Bind v) -> v) paramBs
      let (DataConDef _ argBs) = cons !! con
      let funTy = foldr
            (\(arr, b) body -> Pi (Abs b (arr, body)))
            (TypeCon def (map Var $ toList paramVars))
            (   zip (repeat ImplicitArrow) (toList paramBs)
             ++ zip (repeat PureArrow    ) (toList argBs))
      foldM checkApp funTy $ params ++ args
    TypeCon (DataDef _ bs _) params -> do
      let paramTys = map binderType $ toList bs
      zipWithM_ (|:) params paramTys
      let paramTysRemaining = drop (length params) paramTys
      return $ foldr (-->) TyKind paramTysRemaining
    Record items -> do
      types <- mapM typeCheck items
      return $ RecordTy types
    RecordTy items -> do
      mapM_ (|: TyKind) items
      return TyKind
    Variant vtys@(LabeledItems types) label i value -> do
      value |: ((types M.! label) !! i)
      let ty = VariantTy vtys
      ty |: TyKind
      return ty
    VariantTy items -> do
      mapM_ (|: TyKind) items
      return TyKind

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
        ety <- typeCheck e
        case ety of
          TypeCon def params -> do
            let cons = applyDataDefParams def params
            checkEq  (length cons) (length alts)
            forM_ (zip cons alts) $ \((DataConDef _ bs'), (Abs bs body)) -> do
              checkEq bs' bs
              resultTy' <- flip (foldr withBinder) bs $ typeCheck body
              checkEq resultTy resultTy'
          VariantTy types -> do
            checkEq (length types) (length alts)
            forM_ (zip (toList types) alts) $ \(ty, (Abs bs body)) -> do
              [b] <- pure $ toList bs
              checkEq (getType b) ty
              resultTy' <- flip (foldr withBinder) bs $ typeCheck body
              checkEq resultTy resultTy'
          _ -> throw TypeErr $ "Case analysis only supported on ADTs and variants, not on " ++ pprint ety
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
    While cond body -> functionEffs cond <> functionEffs body
    Linearize _ -> NoEffects
    Transpose _ -> NoEffects
    -- These are more convservative than necessary.
    -- TODO: make them more precise by de-duping with type checker
    RunReader _ _ -> SomeEffects
    RunWriter _   -> SomeEffects
    RunState _ _  -> SomeEffects
    Tile _ _ _ -> error "not implemented"
  Case _ alts _ -> foldMap (\(Abs _ block) -> blockEffs block) alts

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

instance HasType Binder where
  typeCheck b = do
    checkWithEnv $ \(env, _) -> checkNoShadow env b
    let ty = binderType b
    ty |: TyKind
    return ty

checkDecl :: TypeEnv -> Decl -> TypeM TypeEnv
checkDecl env decl = withTypeEnv env $ addContext ctxStr $ case decl of
  Let _ b rhs -> do
    -- TODO: effects
    ty  <- typeCheck b
    ty' <- typeCheck rhs
    checkEq ty ty'
    return $ binderBinding b
  Unpack bs rhs -> do
    void $ checkNestedBinders bs
    ty <- typeCheck rhs
    bs' <- case ty of
      TypeCon def params -> do
        [DataConDef _ bs'] <- return $ applyDataDefParams def params
        return bs'
      RecordTy types -> return $ toNest $ map Ignore $ toList types
      _ -> throw TypeErr $ "Only single-member ADTs and record types can be unpacked in let bindings"
    checkEq bs bs'
    return $ foldMap binderBinding bs
  where ctxStr = "checking decl:\n" ++ pprint decl

checkNestedBinders :: Nest Binder -> TypeM (Nest Type)
checkNestedBinders Empty = return Empty
checkNestedBinders (Nest b bs) = do
  void $ typeCheck b
  extendTypeEnv (binderBinding b) $ checkNestedBinders bs

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
withBinder b m = typeCheck b >> extendTypeEnv (binderBinding b) m

checkNoShadow :: (MonadError Err m, Pretty b) => Env a -> BinderP b -> m ()
checkNoShadow env b = when (b `isin` env) $ throw CompilerErr $ pprint b ++ " shadowed"

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
    Var (_:>ty) -> checkVariant ty
    Lam (Abs b (_, body)) -> checkVariant b >> checkVariant body
    Pi  (Abs b (arr, body)) -> do
      case arr of
        TabArrow -> alwaysAllowed
        _        -> goneBy Simp
      checkVariant b >> checkVariant body
    Con e -> checkVariant e >> forM_ e checkVariant
    TC  e -> checkVariant e >> forM_ e checkVariant
    Eff _ -> alwaysAllowed
    DataCon _ _ _ _ -> alwaysAllowed
    TypeCon _ _     -> alwaysAllowed
    Record _ -> alwaysAllowed
    RecordTy _ -> alwaysAllowed
    Variant _ _ _ _ -> alwaysAllowed
    VariantTy _ -> alwaysAllowed

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
      forM_ alts $ \(Abs _ body) -> checkVariant body

instance CoreVariant Decl where
  -- let annotation restrictions?
  checkVariant (Let _ b e) = checkVariant b >> checkVariant e
  checkVariant (Unpack bs e) = mapM checkVariant bs >> checkVariant e

instance CoreVariant Block where
  checkVariant (Block ds e) = mapM_ checkVariant ds >> checkVariant e

instance CoreVariant Binder where
  checkVariant b = checkVariant (binderType b)

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
    ClassDictHole _ _ -> goneBy Core
    _ -> alwaysAllowed

instance CoreVariant (PrimHof a) where
  checkVariant e = case e of
    For _ _       -> alwaysAllowed
    While _ _     -> alwaysAllowed
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
  IntType          -> return TyKind
  CharType         -> return TyKind
  FloatType         -> return TyKind
  ArrayType t      -> t|:TyKind >> return TyKind
  IntRange a b     -> a|:IntTy >> b|:IntTy >> return TyKind
  IndexRange t a b -> t|:TyKind >> mapM_ (|:t) a >> mapM_ (|:t) b >> return TyKind
  IndexSlice n l   -> n|:TyKind >> l|:TyKind >> return TyKind
  PairType a b     -> a|:TyKind >> b|:TyKind >> return TyKind
  UnitType         -> return TyKind
  RefType r a      -> r|:TyKind >> a|:TyKind >> return TyKind
  TypeKind         -> return TyKind
  EffectRowKind    -> return TyKind
  JArrayType _ _   -> undefined

typeCheckCon :: Con -> TypeM Type
typeCheckCon con = case con of
  Lit l -> return $ BaseTy $ litType l
  CharCon v -> checkIntBaseType   False (getType v) $> CharTy
  IntCon  v -> checkIntBaseType   False (getType v) $> IntTy
  FloatCon v -> checkFloatBaseType False (getType v) $> FloatTy
  ArrayLit ty _ -> return $ ArrayTy ty
  AnyValue t -> t|:TyKind $> t
  PairCon x y -> PairTy <$> typeCheck x <*> typeCheck y
  UnitCon -> return UnitTy
  Coerce t@(Var _) _ -> t |: TyKind $> t
  Coerce destTy e -> do
    sourceTy <- typeCheck e
    destTy  |: TyKind
    checkValidCoercion sourceTy destTy
    return destTy
  SumAsProd ty _ _ -> return ty  -- TODO: check!
  ClassDictHole _ ty -> ty |: TyKind >> return ty

checkIntBaseType :: MonadError Err m => Bool -> Type -> m ()
checkIntBaseType allowVector t = case t of
  BaseTy (Scalar sbt)               -> checkSBT sbt
  BaseTy (Vector sbt) | allowVector -> checkSBT sbt
  _ -> notInt
  where
    checkSBT sbt = case sbt of
      Int64Type -> return ()
      Int32Type -> return ()
      Int8Type  -> return ()
      _         -> notInt
    notInt = throw TypeErr $ "Expected a fixed-width " ++ (if allowVector then "" else "scalar ") ++
                             "integer type, but found: " ++ pprint t

checkFloatBaseType :: MonadError Err m => Bool -> Type -> m ()
checkFloatBaseType allowVector t = case t of
  BaseTy (Scalar sbt)               -> checkSBT sbt
  BaseTy (Vector sbt) | allowVector -> checkSBT sbt
  _ -> notFloat
  where
    checkSBT sbt = case sbt of
      Float64Type -> return ()
      Float32Type -> return ()
      _           -> notFloat
    notFloat = throw TypeErr $ "Expected a fixed-width " ++ (if allowVector then "" else "scalar ") ++
                               "floating-point type, but found: " ++ pprint t

checkValidCoercion :: Type -> Type -> TypeM ()
checkValidCoercion sourceTy destTy = case (sourceTy, destTy) of
  (ArrayTy st, ArrayTy IntTy)    -> checkIntBaseType   False st
  (ArrayTy st, ArrayTy FloatTy)  -> checkFloatBaseType False st
  (ArrayTy st, ArrayTy CharTy)   -> checkIntBaseType   False st
  (ArrayTy st, ArrayTy dt)       -> checkValidCoercion st dt
  (IntTy, TC (IntRange   _ _  )) -> return () -- from ordinal
  (IntTy, TC (IndexRange _ _ _)) -> return () -- from ordinal
  (IntTy, TC (IndexSlice _ _  )) -> return () -- from ordinal of the first slice element
  _ -> throw TypeErr $ "Can't coerce " ++ pprint sourceTy ++ " to " ++ pprint destTy

checkValidCast :: Type -> Type -> TypeM ()
checkValidCast sourceTy destTy = checkScalarType sourceTy >> checkScalarType destTy
  where
    checkScalarType ty = case ty of
      BaseTy (Scalar Int64Type  ) -> return ()
      BaseTy (Scalar Int32Type  ) -> return ()
      BaseTy (Scalar Int8Type   ) -> return ()
      BaseTy (Scalar Float64Type) -> return ()
      BaseTy (Scalar Float32Type) -> return ()
      IntTy                       -> return ()
      FloatTy                     -> return ()
      _ -> throw TypeErr $ "Can't cast " ++ pprint sourceTy ++ " to " ++ pprint destTy

typeCheckOp :: Op -> TypeM Type
typeCheckOp op = case op of
  TabCon ty xs -> do
    ty |: TyKind
    TabTy b a <- return ty
    -- TODO: Propagate the binder to support dependently typed dimensions?
    mapM_ (|:a) xs
    Just n <- return $ indexSetConcreteSize $ binderType b
    assertEq n (length xs) "Index set size mismatch"
    return ty
  Fst p -> do { PairTy x _ <- typeCheck p; return x}
  Snd p -> do { PairTy _ y <- typeCheck p; return y}
  ScalarBinOp binop x y -> bindM2 (checkBinOp binop) (typeCheck x) (typeCheck y)
  ScalarUnOp  unop  x   -> checkUnOp unop =<< typeCheck x
  Select p x y -> do
    p |: (BaseTy $ Scalar Int8Type)
    ty <- typeCheck x
    y |: ty
    return ty
  IntAsIndex ty i -> ty|:TyKind >> i|:IntTy $> ty
  IndexAsInt i -> typeCheck i $> IntTy
  IdxSetSize i -> typeCheck i $> IntTy
  FFICall _ ansTy args -> do
    forM_ args $ \arg -> do
      argTy <- typeCheck arg
      case argTy of
        BaseTy _ -> return ()
        _        -> throw TypeErr $ "All arguments of FFI calls have to be " ++
                                    "fixed-width base types, but got: " ++ pprint argTy
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
    RefTy h (TabTy b a) <- typeCheck ref
    i |: (binderType b)
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
  VectorBinOp _ _ _ -> throw CompilerErr "Vector operations are not supported at the moment"
  VectorPack xs -> do
    unless (length xs == vectorWidth) $ throw TypeErr lengthMsg
    BaseTy (Scalar sb) <- typeCheck $ head xs
    mapM_ (|: (BaseTy (Scalar sb))) xs
    return $ BaseTy $ Vector sb
    where lengthMsg = "VectorBroadcast should have exactly " ++ show vectorWidth ++
                      " elements: " ++ pprint op
  VectorIndex x i -> do
    BaseTy (Vector sb) <- typeCheck x
    i |: TC (IntRange (asIntVal 0) (asIntVal vectorWidth))
    return $ BaseTy $ Scalar sb
  ThrowError ty -> ty|:TyKind $> ty
  CastOp t@(Var _) _ -> t |: TyKind $> t
  CastOp destTy e -> do
    sourceTy <- typeCheck e
    destTy  |: TyKind
    checkValidCast sourceTy destTy
    return destTy

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
    TC (IndexSlice n l) <- return $ binderType tv
    (dv, b, b')         <- zipExtractDim dim tr sr
    checkEq l (binderType dv)
    checkEq n (binderType sv)
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
        if binderType dv == binderType sv
          then zipExtractDim (d-1) b b'
          else throw TypeErr $ "Result type of tiled and non-tiled bodies differ along " ++
                               "dimension " ++ show (dim - d + 1) ++ ": " ++
                               pprint b ++ " and " ++ pprint b'
      zipExtractDim d _ _ = throw TypeErr $
        "Tiling over dimension " ++ show dim ++ " has to produce a result with at least " ++
        show (dim + 1) ++ " dimensions, but it has only " ++ show (dim - d)

      replaceDim 0 (TabTy _ b) n  = TabTy (Ignore n) b
      replaceDim d (TabTy dv b) n = TabTy dv $ replaceDim (d-1) b n
      replaceDim _ _ _ = error "This should be checked before"
  While cond body -> do
    Pi (Abs (Ignore UnitTy) (arr , condTy)) <- typeCheck cond
    Pi (Abs (Ignore UnitTy) (arr', bodyTy)) <- typeCheck body
    declareEffs $ arrowEff arr
    declareEffs $ arrowEff arr'
    checkEq (BaseTy $ Scalar Int8Type) condTy
    checkEq UnitTy bodyTy
    return UnitTy
  Linearize f -> do
    Pi (Abs (Ignore a) (PlainArrow Pure, b)) <- typeCheck f
    return $ a --> PairTy b (a --@ b)
  Transpose f -> do
    Pi (Abs (Ignore a) (LinArrow, b)) <- typeCheck f
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
  BinaryFunTy (Bind regionBinder) refBinder eff resultTy <- typeCheck f
  regionName:>_ <- return regionBinder
  let region = Var regionBinder
  extendAllowedEffect (effName, regionName) $ declareEffs eff
  checkEq (varAnn regionBinder) TyKind
  RefTy region' referentTy <- return $ binderAnn refBinder
  checkEq region' region
  return (resultTy, referentTy)

litType :: LitVal -> BaseType
litType v = case v of
  Int64Lit   _ -> Scalar Int64Type
  Int32Lit   _ -> Scalar Int32Type
  Int8Lit    _ -> Scalar Int8Type
  Float64Lit _ -> Scalar Float64Type
  Float32Lit _ -> Scalar Float32Type
  VecLit  l -> Vector sb
    where (Scalar sb) = litType $ head l

data ArgumentType = SomeFloatArg | SomeIntArg | Int8Arg
data ReturnType   = SameReturn | Int8Return

checkOpArgType :: MonadError Err m => ArgumentType -> Type -> m ()
checkOpArgType argTy x =
  case argTy of
    SomeIntArg   -> case x of
      IntTy   -> return ()
      _       -> checkIntBaseType   True x
    SomeFloatArg -> case x of
      FloatTy -> return ()
      _       -> checkFloatBaseType True x
    Int8Arg      -> case x of
      BaseTy (Scalar Int8Type) -> return ()
      BaseTy (Vector Int8Type) -> return ()
      _ -> throw TypeErr "Expected an Int8 argument"

checkBinOp :: MonadError Err m => BinOp -> Type -> Type -> m Type
checkBinOp op x y = do
  checkOpArgType argTy x
  assertEq x y ""
  return $ case retTy of
    SameReturn -> x
    Int8Return -> BaseTy $ Scalar Int8Type
  where
    (argTy, retTy) = case op of
      IAdd   -> (ia, sr);  ISub   -> (ia, sr)
      IMul   -> (ia, sr);  IDiv   -> (ia, sr)
      IRem   -> (ia, sr);  IPow   -> (ia, sr)
      ICmp _ -> (ia, br)
      FAdd   -> (fa, sr);  FSub   -> (fa, sr)
      FMul   -> (fa, sr);  FDiv   -> (fa, sr);
      FPow   -> (fa, sr)
      FCmp _ -> (fa, br)
      BAnd   -> (ba, br);  BOr    -> (ba, br)
      where
        ba = Int8Arg; ia = SomeIntArg; fa = SomeFloatArg
        br = Int8Return; sr = SameReturn

checkUnOp :: MonadError Err m => UnOp -> Type -> m Type
checkUnOp op x = do
  checkOpArgType argTy x
  return $ case retTy of
    SameReturn -> x
    Int8Return -> BaseTy $ Scalar Int8Type
  where
    (argTy, retTy) = case op of
      Exp              -> (f, sr)
      Exp2             -> (f, sr)
      Log              -> (f, sr)
      Log2             -> (f, sr)
      Log10            -> (f, sr)
      Sin              -> (f, sr)
      Cos              -> (f, sr)
      Tan              -> (f, sr)
      Sqrt             -> (f, sr)
      Floor            -> (f, sr)
      Ceil             -> (f, sr)
      Round            -> (f, sr)
      FNeg             -> (f, sr)
      BNot             -> (b, sr)
      where
        b = Int8Arg; f = SomeFloatArg; sr = SameReturn

indexSetConcreteSize :: Type -> Maybe Int
indexSetConcreteSize ty = case ty of
  FixedIntRange l h -> Just $ high - low
    where low = getIntLit l; high = getIntLit h
  _                 -> Nothing

checkDataLike :: MonadError Err m => String -> Bindings -> Type -> m ()
checkDataLike msg env ty = case ty of
  Var _ -> error "Not implemented"
  TabTy _ b -> recur b
  -- TODO: check that data constructor arguments are data-like, and so on
  TypeCon _ _ -> return ()
  TC con -> case con of
    BaseType _       -> return ()
    IntType          -> return ()
    FloatType        -> return ()
    CharType         -> return ()
    PairType a b     -> recur a >> recur b
    UnitType         -> return ()
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
