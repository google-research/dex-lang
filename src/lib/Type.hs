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
  getType, HasType (..), Checkable (..), litType, isPure, extendEffect,
  binOpType, unOpType, isData, indexSetConcreteSize, checkNoShadow) where

import Control.Monad
import Control.Monad.Except hiding (Except)
import Control.Monad.Reader
import Data.Functor
import Data.Text.Prettyprint.Doc

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
getType x = ignoreExcept $ ctx $ runTypeCheck SkipChecks (typeCheck x)
  where ctx = addContext $ "Querying:\n" ++ pprint x

runTypeCheck :: TypeCheckEnv -> TypeM a -> Except a
runTypeCheck env m = runReaderT m env

-- === Module interfaces ===

class Pretty a => Checkable a where
  checkValid :: a -> Except ()

instance Checkable Module where
  checkValid m@(Module _ decls bindings) =
    addContext ("Checking module:\n" ++ pprint m) $ asCompilerErr $ do
      let env = freeVars m
      addContext "Checking IR variant" $ checkModuleVariant m
      addContext "Checking body types" $ do
        let block = Block decls $ Atom $ UnitVal
        void $ runTypeCheck (CheckWith (env, Pure)) (typeCheck block)
      addContext "Checking evaluated bindings" $ do
        checkBindings (env <> foldMap declAsScope decls) bindings

asCompilerErr :: Except a -> Except a
asCompilerErr (Left (Err _ c msg)) = Left $ Err CompilerErr c msg
asCompilerErr (Right x) = Right x

checkBindings :: TypeEnv -> Bindings -> Except ()
checkBindings env bs = forM_ (envPairs bs) $ \binding -> do
  (GlobalName _, (ty, LetBound _ (Atom atom))) <- return binding
  void $ runTypeCheck (CheckWith (env <> bs, Pure)) $ atom |: ty

-- === Core IR ===

instance HasType Atom where
  typeCheck atom = case atom of
    Var v@(name:>annTy) -> do
      annTy |: TyKind
      when (annTy == EffKind) $
        throw CompilerErr "Effect variables should only occur in effect rows"
      checkWithEnv $ \(env, _) -> case envLookup env v of
        Nothing -> throw CompilerErr $ "Lookup failed: " ++ pprint v
        Just (ty, _) -> assertEq annTy ty $ "Annotation on var: " ++ pprint name
      return annTy
    -- TODO: check arrowhead-specific effect constraints (both lam and arrow)
    Lam (Abs b (arr, body)) -> withBinder b $ do
      checkArrow arr
      bodyTy <- withAllowedEff (arrowEff arr) $ typeCheck body
      return $ Pi $ makeAbs b (arr, bodyTy)
    Pi (Abs b (arr, resultTy)) -> withBinder b $
      checkArrow arr >> resultTy|:TyKind $> TyKind
    Con con  -> typeCheckCon con
    TC tyCon -> typeCheckTyCon tyCon $> TyKind
    Eff eff  -> checkEffRow eff $> EffKind

instance HasType Expr where
  typeCheck expr = case expr of
    App f x -> do
      Pi piTy <- typeCheck f
      x |: absArgType piTy
      let (arr, resultTy) = applyAbs piTy x
      declareEffs $ arrowEff arr
      return resultTy
    Atom x   -> typeCheck x
    Op   op  -> typeCheckOp op
    Hof  hof -> typeCheckHof hof

-- TODO: replace with something more precise (this is too cautious)
isPure :: Expr -> Bool
isPure expr = case expr of
  Atom _ -> True
  App f _ -> case getType f of
    Pi (Abs _ (arr, _)) -> arrowEff arr == Pure
    _ -> False
  _ -> False

instance HasType Block where
  typeCheck (Block decls result) = do
    checkingEnv <- ask
    case checkingEnv of
      SkipChecks -> typeCheck result
      CheckWith (env, _) -> do
        env' <- catFoldM checkDecl env decls
        withTypeEnv (env <> env') $ typeCheck result

checkDecl :: TypeEnv -> Decl -> TypeM TypeEnv
checkDecl env decl@(Let _ b rhs) =
  withTypeEnv env $ addContext ctxStr $ do
    -- TODO: effects
    checkBinder b
    ty <- typeCheck rhs
    checkEq (varType b) ty
    return $ b @> (ty, UnknownBinder)
  where ctxStr = "checking decl:\n" ++ pprint decl

checkArrow :: Arrow -> TypeM ()
checkArrow arr = mapM_ checkEffRow arr

infixr 7 |:
(|:) :: Atom -> Type -> TypeM ()
(|:) x reqTy = do
  ty <- typeCheck x
  checkEq reqTy ty

checkEq :: Type -> Type -> TypeM ()
checkEq reqTy ty = checkWithEnv $ \_ -> assertEq reqTy ty ""

withBinder :: Binder -> TypeM a -> TypeM a
withBinder b@(_:>ty) m = checkBinder b >> extendTypeEnv (b@>(ty, UnknownBinder)) m

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
  when (ir < Simp       && not (null bindings)) $ throw CompilerErr "unexpected bindings"
  when (ir == Evaluated && not (null decls))    $ throw CompilerErr "unexpected decls"
  flip runReaderT ir $ mapM_ checkVariant decls

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

instance CoreVariant Expr where
  checkVariant expr = addExpr expr $ case expr of
    App f x -> checkVariant f >> checkVariant x
    Atom x  -> checkVariant x
    Op  e   -> checkVariant e >> forM_ e checkVariant
    Hof e   -> checkVariant e >> forM_ e checkVariant

instance CoreVariant Decl where
  -- let annotation restrictions?
  checkVariant (Let _ b e) = checkVariantVar b >> checkVariant e

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
    NewtypeApp _ _ -> goneBy Simp
    _ -> alwaysAllowed

instance CoreVariant (PrimOp a) where
  checkVariant e = case e of
    FromNewtypeCon _ _ -> goneBy Simp
    Select _ _ _       -> alwaysAllowed  -- TODO: only scalar select after Simp
    _ -> alwaysAllowed

instance CoreVariant (PrimCon a) where
  checkVariant e = case e of
    ClassDictHole _ -> goneBy Core
    NewtypeCon _ _  -> goneBy Simp
    SumCon _ _ _    -> alwaysAllowed -- not sure what this should be
    RefCon _ _      -> neverAllowed
    Todo _          -> goneBy Simp
    _ -> alwaysAllowed

instance CoreVariant (PrimHof a) where
  checkVariant e = case e of
    For _ _       -> alwaysAllowed
    SumCase _ _ _ -> goneBy Simp
    RunReader _ _ -> alwaysAllowed
    RunWriter _   -> alwaysAllowed
    RunState  _ _ -> alwaysAllowed
    Linearize _   -> goneBy Simp
    Transpose _   -> goneBy Simp

-- TODO: namespace restrictions?
alwaysAllowed :: VariantM ()
alwaysAllowed = return ()

neverAllowed :: VariantM ()
neverAllowed = throw IRVariantErr $ "should never appear in finalized expression"

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

typeCheckTyCon :: TC -> TypeM ()
typeCheckTyCon tc = case tc of
  BaseType _       -> return ()
  ArrayType t      -> t|:TyKind
  IntRange a b     -> a|:IntTy >> b|:IntTy
  IndexRange t a b -> t|:TyKind >> mapM_ (|:t) a >> mapM_ (|:t) b
  SumType  l r     -> l|:TyKind >> r|:TyKind
  PairType a b     -> a|:TyKind >> b|:TyKind
  UnitType         -> return ()
  RefType r a      -> r|:TyKind >> a|:TyKind
  TypeKind         -> return ()
  EffectRowKind    -> return ()
  JArrayType _ _   -> undefined
  NewtypeApp _ _ -> return () -- TODO!

typeCheckCon :: Con -> TypeM Type
typeCheckCon con = case con of
  Lit l -> return $ BaseTy $ litType l
  ArrayLit ty _ -> return $ ArrayTy ty
  AnyValue t -> t|:TyKind $> t
  SumCon _ l r -> SumTy <$> typeCheck l <*> typeCheck r
  PairCon x y -> PairTy <$> typeCheck x <*> typeCheck y
  UnitCon -> return UnitTy
  RefCon r x -> r|:TyKind >> RefTy r <$> typeCheck x
  AsIdx n e -> n|:TyKind >> e|:IntTy $> n
  NewtypeCon toTy x -> toTy|:TyKind >> typeCheck x $> toTy
  ClassDictHole ty -> ty |: TyKind >> return ty
  Todo ty -> ty|:TyKind $> ty

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
    return $ TC $ BaseType BoolType
  ScalarBinOp binop x1 x2 ->
    x1 |: BaseTy t1 >> x2 |: BaseTy t2 $> BaseTy tOut
    where (t1, t2, tOut) = binOpType binop
  -- TODO: check index set constraint
  ScalarUnOp unop x -> x |: BaseTy ty $> BaseTy outTy
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
  FromNewtypeCon toTy x -> toTy|:TyKind >> typeCheck x $> toTy
  ArrayOffset arr idx off -> do
    -- TODO: b should be applied!!
    ArrayTy (TabTyAbs a) <- typeCheck arr
    off |: IntTy
    idx |: absArgType a
    return $ ArrayTy $ snd $ applyAbs a idx
  ArrayLoad arr -> do
    ArrayTy (BaseTy b)  <- typeCheck arr
    return $ BaseTy b

typeCheckHof :: Hof -> TypeM Type
typeCheckHof hof = case hof of
  For _ f -> do
    Pi (Abs n (arr, a)) <- typeCheck f
    -- TODO: check `n` isn't free in `eff`
    declareEffs $ arrowEff arr
    return $ Pi $ Abs n (TabArrow, a)
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
  IntLit  _ -> IntType
  RealLit _ -> RealType
  StrLit  _ -> StrType
  BoolLit _ -> BoolType

binOpType :: ScalarBinOp -> (BaseType, BaseType, BaseType)
binOpType op = case op of
  IAdd   -> (i, i, i);  ISub   -> (i, i, i)
  IMul   -> (i, i, i);  ICmp _ -> (i, i, b)
  IDiv   -> (i, i, i)
  Pow    -> (i, i, i);  Rem    -> (i, i, i)
  FAdd   -> (r, r, r);  FSub   -> (r, r, r)
  FMul   -> (r, r, r);  FCmp _ -> (r, r, b)
  FDiv   -> (r, r, r);  And    -> (b, b, b)
  Or     -> (b, b, b)
  where b = BoolType
        i = IntType
        r = RealType

unOpType :: ScalarUnOp -> (BaseType, BaseType)
unOpType op = case op of
  Not             -> (BoolType, BoolType)
  FNeg            -> (RealType, RealType)
  IntToReal       -> (IntType, RealType)
  BoolToInt       -> (BoolType, IntType)
  UnsafeIntToBool -> (IntType, BoolType)

indexSetConcreteSize :: Type -> Maybe Int
indexSetConcreteSize ty = case ty of
  FixedIntRange low high -> Just $ high - low
  BoolTy  -> Just 2
  _ -> Nothing

checkDataLike :: MonadError Err m => String -> ClassEnv -> Type -> m ()
checkDataLike msg env ty = case ty of
  -- This is an implicit `instance IdxSet a => Data a`
  Var v -> checkVarClass env IdxSet v `catchError`
             const (checkVarClass env Data v)
  TabTy _ b -> recur b
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

checkData :: MonadError Err m => ClassEnv -> Type -> m ()
checkData = checkDataLike " is not serializable"

--TODO: Make this work even if the type has type variables!
isData :: Type -> Bool
isData ty = case checkData mempty ty of Left _ -> False
                                        Right _ -> True

checkVarClass :: MonadError Err m => ClassEnv -> ClassName -> Var -> m ()
checkVarClass env c (v:>k) = do
  unless (k == TyKind) $ throw KindErr $ " Only types can belong to type classes"
  unless (c `elem` cs) $ throw TypeErr $
              " Type variable \"" ++ pprint v ++ "\" not in class: " ++ pprint c
  where cs = monMapLookup env v
