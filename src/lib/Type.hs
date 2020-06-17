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

type ClassEnv = MonMap Name [ClassName]

data OptionalEnv env = SkipChecks | CheckWith env  deriving Functor
type TypeCheckEnv = OptionalEnv (TypeEnv, EffectRow)
type TypeM = ReaderT TypeCheckEnv Except

class Pretty a => HasType a where
  typeCheck :: a -> TypeM Type

getType :: HasType a => a -> Type
getType x = ignoreExcept $ runTypeCheck SkipChecks x

runTypeCheck :: HasType a => TypeCheckEnv -> a -> Except Type
runTypeCheck env x = addContext ctxStr $ runReaderT (typeCheck x) env
  where ctxStr = "\nChecking:\n" ++ pprint x

-- === Module interfaces ===

class Pretty a => Checkable a where
  checkValid :: a -> Except ()

instance Checkable Module where
  checkValid m@(Module _ imports exports block) =
    asCompilerErr $ do
      let env = (foldMap varAsEnv imports, Pure)
      outTys <- fromConsListTy =<< runTypeCheck (CheckWith env) block
      assertEq (map varAnn exports) outTys "export types"
    where ctxStr = "\nChecking:\n" ++ pprint m

asCompilerErr :: Except a -> Except a
asCompilerErr (Left (Err _ c msg)) = Left $ Err CompilerErr c msg
asCompilerErr (Right x) = Right x

-- === Normalized IR ===

instance HasType Atom where
  typeCheck atom = case atom of
    Var v@(_:>annTy) -> do
      annTy |: TyKind
      when (annTy == EffKind) $
        throw CompilerErr "Effect variables should only occur in effect rows"
      checkWithEnv $ \(env, _) -> case envLookup env v of
        Nothing -> throw CompilerErr $ "Lookup failed: " ++ pprint v
        Just ty -> assertEq annTy ty "Var annotation"
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
  App f x -> case getType f of
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
checkDecl env decl@(Let b@(_:>annTy) rhs) =
  withTypeEnv env $ addContext ctxStr $ do
    -- TODO: effects
    checkBinder b
    ty <- typeCheck rhs
    return $ b @> ty
  where ctxStr = "\nchecking decl: \n" ++ pprint decl

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
withBinder b@(_:>ty) m = checkBinder b >> extendTypeEnv (b@>ty) m

checkBinder :: Binder -> TypeM ()
checkBinder b@(_:>ty) = do
  env <- ask
  checkWithEnv $ \(env, _) -> checkNoShadow env b
  ty |: TyKind

checkNoShadow :: (MonadError Err m, Pretty b) => Env a -> VarP b -> m ()
checkNoShadow env v = when (v `isin` env) $ throw CompilerErr $ pprint v ++ " shadowed"

-- === effects ===

checkEffRow :: EffectRow -> TypeM ()
checkEffRow (EffectRow effs effTail) = do
  forM_ effs $ \(_, v) -> Var (v:>TyKind) |: TyKind
  forM_ effTail $ \v -> do
    checkWithEnv $ \(env, _) -> case envLookup env (v:>()) of
      Nothing -> throw CompilerErr $ "Lookup failed: " ++ pprint v
      Just ty -> assertEq EffKind ty "Effect var"

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

updateTypeEnv :: (Env Type -> Env Type) -> TypeM a -> TypeM a
updateTypeEnv f m = flip local m $ fmap $ \(env, eff) -> (f env, eff)

extendTypeEnv :: Env Type -> TypeM a -> TypeM a
extendTypeEnv new m = updateTypeEnv (<> new) m

withTypeEnv :: Env Type -> TypeM a -> TypeM a
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
  IntRange a b     -> a|:IntTy >> b|:IntTy
  IndexRange t a b -> t|:TyKind >> mapM_ (|:t) a >> mapM_ (|:t) b
  ArrayType _      -> return ()
  SumType  l r     -> l|:TyKind >> r|:TyKind
  PairType a b     -> a|:TyKind >> b|:TyKind
  UnitType         -> return ()
  RefType r a      -> r|:TyKind >> a|:TyKind
  TypeKind         -> return ()
  EffectRowKind    -> return ()

typeCheckCon :: Con -> TypeM Type
typeCheckCon con = case con of
  Lit l -> return $ BaseTy $ litType l
  ArrayLit ty _ -> return $ ty
  AnyValue t -> t|:TyKind $> t
  SumCon _ l r -> SumTy <$> typeCheck l <*> typeCheck r
  PairCon x y -> PairTy <$> typeCheck x <*> typeCheck y
  UnitCon -> return UnitTy
  RefCon r x -> r|:TyKind >> RefTy r <$> typeCheck x
  AFor n a -> n|:TyKind >> TabTy n <$> typeCheck a
  AGet st -> (BaseTy . scalarTableBaseType) <$> typeCheck st
  AsIdx n e -> n|:TyKind >> e|:IntTy $> n
  Todo ty -> ty|:TyKind $> ty

typeCheckOp :: Op -> TypeM Type
typeCheckOp op = case op of
  TabCon ty xs -> do
    ty |: TyKind
    TabTy n a <- return ty
    mapM_ (|:a) xs
    Just n' <- return $ indexSetConcreteSize n
    assertEq n' (length xs) "Index set size mismatch"
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
  Cmp _ x y -> do
    ty <- typeCheck x
    y |: ty
    return BoolTy
  Select p x y -> do
    p|:BoolTy
    ty <- typeCheck x
    y |:ty
    return ty
  IntAsIndex ty i -> ty|:TyKind >> i|:IntTy $> ty
  IndexAsInt i -> typeCheck i $> IntTy
  IdxSetSize i -> typeCheck i $> IntTy
  FFICall _ ansTy args -> do
    argTys <- mapM typeCheck args
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
    RefTy h (TabTy n a) <- typeCheck ref
    i|:n
    return $ RefTy h a

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

pureNonDepAbsBlock :: Abs Block -> TypeM (Type, Type)
pureNonDepAbsBlock (Abs b body) = withBinder b $ withAllowedEff Pure $ do
  resultTy <- typeCheck body
  case makeAbs b resultTy of
    Abs (NoName:>a) b -> return (a, b)
    _ -> throw CompilerErr "Unexpectedly dependent function"

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

-- === Built-in typeclasses (CURRENTLY NOT USED) ===

checkClassConstraint :: ClassName -> Type -> TypeM ()
checkClassConstraint c ty = do
  env <- error "currently broken" -- lift ask
  case c of
    VSpace -> checkVSpace env ty
    IdxSet -> checkIdxSet env ty
    Data   -> checkData   env ty
    Eq     -> checkInEq   env ty
    Ord    -> checkOrd    env ty

checkVSpace :: MonadError Err m => ClassEnv -> Type -> m ()
checkVSpace env ty = case ty of
  Var v     -> checkVarClass env VSpace v
  RealTy    -> return ()
  _ -> throw TypeErr $ " Not a vector space: " ++ pprint ty

checkIdxSet :: MonadError Err m => ClassEnv -> Type -> m ()
checkIdxSet env ty = case ty of
  Var v                 -> checkVarClass env IdxSet v
  SumTy l r             -> recur l >> recur r
  BoolTy                -> return ()
  TC (IntRange _ _)     -> return ()
  TC (IndexRange _ _ _) -> return ()
  _ -> throw TypeErr $ " Not a valid index set: " ++ pprint ty
  where recur = checkIdxSet env

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

checkInEq :: MonadError Err m => ClassEnv -> Type -> m ()
checkInEq = checkDataLike " is not equatable"

checkOrd :: MonadError Err m => ClassEnv -> Type -> m ()
checkOrd env ty = case ty of
  Var v                 -> checkVarClass env Ord v
  IntTy                 -> return ()
  RealTy                -> return ()
  TC (IntRange _ _ )    -> return ()
  TC (IndexRange _ _ _) -> return ()
  _ -> throw TypeErr $ pprint ty ++ " doesn't define an ordering"

-- TODO: Make this work even if the type has type variables!
isData :: Type -> Bool
isData ty = case checkData mempty ty of Left _ -> False
                                        Right _ -> True

checkVarClass :: MonadError Err m => ClassEnv -> ClassName -> Var -> m ()
checkVarClass env c (v:>k) = do
  unless (k == TyKind) $ throw KindErr $ " Only types can belong to type classes"
  unless (c `elem` cs) $ throw TypeErr $
              " Type variable \"" ++ pprint v ++ "\" not in class: " ++ pprint c
  where cs = monMapLookup env v
