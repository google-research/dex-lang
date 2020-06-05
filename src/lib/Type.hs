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
  getType, HasType (..), Checkable (..), litType, isPure, forbiddenEffects,
  binOpType, unOpType, isData, indexSetConcreteSize, checkNoShadow) where

import Control.Monad
import Control.Monad.Except hiding (Except)
import Control.Monad.Reader
import Control.Monad.Writer
import Data.Foldable
import Data.Functor
import qualified Data.Map.Strict as M
import Data.Text.Prettyprint.Doc
import GHC.Stack

import Array
import Syntax
import Env
import Record
import PPrint
import Cat

type ClassEnv = MonMap Name [ClassName]

data OptionalEnv env = SkipChecks | CheckWith env  deriving Functor
type TypeCheckEnv = OptionalEnv (TypeEnv, Effects)
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
      TupTy outTys <- runTypeCheck (CheckWith env) block
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
      env <- ask
      case env of
        SkipChecks -> return ()
        CheckWith (tyEnv, _) -> case envLookup tyEnv v of
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
    Eff eff  -> typeCheckEff eff $> TC EffectsKind

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
checkArrow arr = mapM_ (|: TC EffectsKind) arr

infixr 7 |:
(|:) :: Atom -> Type -> TypeM ()
(|:) x reqTy = do
  ty <- typeCheck x
  checkEq reqTy ty

-- TODO: consider skipping the checks if the env is Nothing
checkEq :: Type -> Type -> TypeM ()
checkEq reqTy ty = assertEq reqTy ty ""

withBinder :: Binder -> TypeM a -> TypeM a
withBinder b@(_:>ty) m = checkBinder b >> extendTypeEnv (b@>ty) m

checkBinder :: Binder -> TypeM ()
checkBinder b@(_:>ty) = do
  env <- ask
  checkWithEnv $ \(env, _) -> checkNoShadow env b
  ty |: TyKind

checkNoShadow :: (MonadError Err m, Pretty b) => Env a -> VarP b -> m ()
checkNoShadow env v = when (v `isin` env) $ throw CompilerErr $ pprint v ++ " shadowed"

declareEff :: Effect Atom -> TypeM ()
declareEff eff = declareEffs $ Eff $ ExtendEff eff Pure

declareEffs :: Effects -> TypeM ()
declareEffs effs = checkWithEnv $ \(_, allowedEffects) ->
  case forbiddenEffects allowedEffects effs of
    Pure -> return ()
    extraEffs -> throw TypeErr $ "Unexpected effects: " ++ pprint extraEffs

forbiddenEffects :: Effects -> Effects -> Effects
forbiddenEffects allowed checked = wrapEffects extraConcrete extraTail
  where
    (effsAllowed, effTailAllowed) = flattenEffects allowed
    (effsChecked, effTailChecked) = flattenEffects checked
    extraConcrete = filter (\e -> not (e `elem` effsAllowed)) effsChecked
    extraTail = case effTailChecked of
      Pure -> Pure
      _ | effTailChecked  == effTailAllowed -> Pure
        | otherwise -> effTailChecked

removeEffect :: Effects -> Effect Atom -> Effects
removeEffect effects e = wrapEffects (filter (/= e) concreteEffs) effTail
  where (concreteEffs, effTail) = flattenEffects effects

flattenEffects :: Effects -> ([Effect Atom], Type)
flattenEffects (Eff (ExtendEff eff rest)) = (eff:effs, effTail)
  where (effs, effTail) = flattenEffects rest
flattenEffects effs = ([], effs)

wrapEffects :: [Effect Atom] -> Type -> Effects
wrapEffects [] effTail = effTail
wrapEffects (eff:rest) effTail = Eff $ ExtendEff eff $ wrapEffects rest effTail

-- === type checker monad combinators ===

checkWithEnv :: ((TypeEnv, Effects) -> TypeM ()) -> TypeM ()
checkWithEnv check = do
  optEnv <- ask
  case optEnv of
    SkipChecks -> return ()
    CheckWith env -> check env

updateAllowedEff :: (Effects -> Effects) -> TypeM a -> TypeM a
updateAllowedEff f m = flip local m $ fmap $ \(env, eff) -> (env, f eff)

withAllowedEff :: Effects -> TypeM a -> TypeM a
withAllowedEff eff m = updateAllowedEff (const eff) m

extendAllowedEff :: Effect Atom -> TypeM a -> TypeM a
extendAllowedEff newEff m = updateAllowedEff (Eff . ExtendEff newEff) m

updateTypeEnv :: (Env Type -> Env Type) -> TypeM a -> TypeM a
updateTypeEnv f m = flip local m $ fmap $ \(env, eff) -> (f env, eff)

extendTypeEnv :: Env Type -> TypeM a -> TypeM a
extendTypeEnv new m = updateTypeEnv (<> new) m

withTypeEnv :: Env Type -> TypeM a -> TypeM a
withTypeEnv new m = updateTypeEnv (const new) m

-- === primitive ops and constructors ===

typeCheckTyCon :: TC -> TypeM ()
typeCheckTyCon tc = case tc of
  BaseType _       -> return ()
  IntRange a b     -> a|:IntTy >> b|:IntTy
  IndexRange t a b -> t|:TyKind >> mapM_ (|:TyKind) a >> mapM_ (|:TyKind) b
  ArrayType _      -> return ()
  SumType (l, r)   -> l|:TyKind >> r|:TyKind
  PairType a b     -> a|:TyKind >> b|:TyKind
  UnitType         -> return ()
  RecType r        -> mapM_ (|:TyKind) r
  RefType r a      -> r|: TC RegionType >> a|:TyKind
  RegionType       -> return ()
  TypeKind         -> return ()

typeCheckEff :: Eff -> TypeM ()
typeCheckEff PureEff = return ()
typeCheckEff (ExtendEff (_, r) rest) = do
  r    |: TC RegionType
  rest |: TC EffectsKind

typeCheckCon :: Con -> TypeM Type
typeCheckCon con = case con of
  Lit l -> return $ BaseTy $ litType l
  ArrayLit (Array (shape, b) _) -> return $ ArrayTy shape b
  AnyValue t -> t|:TyKind $> t
  SumCon _ l r -> (TC . SumType) <$> ((,) <$> typeCheck l <*> typeCheck r)
  PairCon x y -> PairTy <$> typeCheck x <*> typeCheck y
  RecCon r -> RecTy <$> mapM typeCheck r
  RefCon r x -> r|:(TC RegionType) >> RefTy r <$> typeCheck x
  AFor n a -> TabTy <$> typeCheck n <*> typeCheck a
  AGet x -> do
    -- TODO: check shape matches AFor scope
    ArrayTy _ b <- typeCheck x
    return $ BaseTy b
  AsIdx n e -> n|:TyKind >> e|:IntTy $> n
  Todo ty -> ty|:TyKind $> ty

typeCheckOp :: Op -> TypeM Type
typeCheckOp op = case op of
  TabCon n ty xs -> do
    n|:TyKind >> ty|:TyKind >> mapM_ (|:ty) xs
    Just n' <- return $ indexSetConcreteSize n
    assertEq n' (length xs) "Index set size mismatch"
    return (n==>ty)
  Fst p -> do { PairTy x _ <- typeCheck p; return x}
  Snd p -> do { PairTy _ y <- typeCheck p; return y}
  RecGet x i -> do
    RecTy r <- typeCheck x
    return $ recGet r i  -- TODO: make a total version of recGet
  SumGet x isLeft -> do
    SumTy l r <- typeCheck x
    l|:TyKind >> r|:TyKind
    return $ if isLeft then l else r
  SumTag x -> do
    SumTy l r <- typeCheck x
    l|:TyKind >> r|:TyKind
    return $ TC $ BaseType BoolType
  ArrayGep x i -> do
    ArrayTy (_:shape) b <- typeCheck x
    i|:IntTy
    return $ ArrayTy shape b
  LoadScalar x -> do
    ArrayTy [] b <- typeCheck x
    return $ BaseTy b
  ScalarBinOp binop x1 x2 ->
    x1 |: BaseTy t1 >> x2 |: BaseTy t2 $> BaseTy tOut
    where (t1, t2, tOut) = binOpType binop
  -- TODO: check index set constraint
  ScalarUnOp unop x -> x |: BaseTy ty $> BaseTy outTy
    where (ty, outTy) = unOpType unop
  Cmp _ ty x y    -> ty|:TyKind >> x|:ty >> y|:ty $> BoolTy
  Select p x y -> do
    p|:BoolTy
    ty <- typeCheck x
    y |:ty
    return ty
  IntAsIndex ty i -> ty|:TyKind >> i|:ty $> ty
  IndexAsInt i -> typeCheck i $> IntTy
  IdxSetSize i -> typeCheck i $> IntTy
  FFICall _ argTys ansTy args -> do
    zipWithM_ (|:) args (map BaseTy argTys)
    return $ BaseTy ansTy
  Inject i -> do
    TC (IndexRange ty _ _) <- typeCheck i
    return ty
  PrimEffect ref m -> do
    RefTy r s <- typeCheck ref
    case m of
      MGet   ->           declareEff (State, r) $> s
      MPut x -> x |: s >> declareEff (State, r) $> UnitTy

typeCheckHof :: Hof -> TypeM Type
typeCheckHof hof = case hof of
  For _ f -> do
    Pi (Abs n (arr, a)) <- typeCheck f
    -- TODO: check `n` isn't free in `eff`
    declareEffs $ arrowEff arr
    return $ Pi $ Abs n (TabArrow, a)
  -- SumCase st l r -> do
  --   (la, lb) <- pureNonDepAbsBlock l
  --   (ra, rb) <- pureNonDepAbsBlock r
  --   checkEq lb rb
  --   st |: SumTy la ra
  --   return lb
  -- Linearize lam -> do
  --   (a, b) <- pureNonDepAbsBlock lam
  --   return $ a --> PairTy b (a --@ b)
  -- Transpose lam -> do
  --   (a, b) <- pureNonDepAbsBlock lam
  --   return $ b --@ a
  RunState s f -> do
    stateTy <- typeCheck s
    BinaryFunTy regionBinder refBinder eff resultTy <- typeCheck f
    let region = Var regionBinder
    declareEffs $ eff `removeEffect` (State, region)
    checkEq (varAnn regionBinder) (TC RegionType)
    checkEq (varAnn refBinder) $ RefTy region stateTy
    return $ PairTy resultTy stateTy

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
  RecTy r -> liftM product $ mapM indexSetConcreteSize $ toList r
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
  RecTy r   -> mapM_ recur r
  _ -> throw TypeErr $ " Not a vector space: " ++ pprint ty
  where recur = checkVSpace env

checkIdxSet :: MonadError Err m => ClassEnv -> Type -> m ()
checkIdxSet env ty = case ty of
  Var v                 -> checkVarClass env IdxSet v
  RecTy r               -> mapM_ recur r
  SumTy l r             -> recur l >> recur r
  BoolTy                -> return ()
  TC (IntRange _ _)     -> return ()
  TC (IndexRange _ _ _) -> return ()
  _ -> throw TypeErr $ " Not a valid index set: " ++ pprint ty
  where recur = checkIdxSet env

checkDataLike :: MonadError Err m => String -> ClassEnv -> Type -> m ()
checkDataLike msg env ty = case ty of
  -- This is an implicit `instance IdxSet a => Data a`
  Var v              -> checkVarClass env IdxSet v `catchError`
                           const (checkVarClass env Data v)
  TC con -> case con of
    BaseType _       -> return ()
    RecType r        -> mapM_ recur r
    SumType (l, r)   -> checkDataLike msg env l >> checkDataLike msg env r
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
