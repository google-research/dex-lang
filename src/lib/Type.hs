-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Type (
  getType, getEffType, checkEffType, HasType (..), Checkable (..), litType,
  binOpType, unOpType, isData, indexSetConcreteSize, maybeApplyPi, makePi,
  applyPi, pureType, checkNoShadow) where

import Control.Monad
import Control.Monad.Except hiding (Except)
import Control.Monad.Reader
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
import Subst

type ClassEnv = MonMap Name [ClassName]

data TypeCheckEnv = SkipChecks | CheckWith JointTypeEnv
-- TODO: put the effects in a writer/cat monad here
type TypeM = ReaderT TypeCheckEnv Except

getType :: HasType a => a -> Type
getType x = snd $ getEffType x

getEffType :: HasType a => a -> EffectiveType
getEffType x = ignoreExcept $ runTypeCheck SkipChecks x

checkEffType :: HasType a => TypeEnv -> a -> Except EffectiveType
checkEffType env x = runTypeCheck (CheckWith (fromNamedEnv env)) x

class Pretty a => HasType a where
  typeCheck :: a -> TypeM Type

runTypeCheck :: HasType a => TypeCheckEnv -> a -> Except EffectiveType
runTypeCheck env x = do
  ty <- addContext ctxStr $ runReaderT (typeCheck x) env
  return (noEffect, ty) -- TODO: effects!
  where ctxStr = "\nChecking:\n" ++ pprint x

-- === Module interfaces ===

class Pretty a => Checkable a where
  checkValid :: a -> Except ()

instance Checkable Module where
  checkValid m@(Module _ imports exports block) =
    asCompilerErr $ do
      let env = fromNamedEnv $ foldMap varAsEnv imports
      (eff, TupTy outTys) <- runTypeCheck (CheckWith env) block
      assertEq noEffect eff "module effect"
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
        CheckWith tyEnv -> case jointEnvLookup tyEnv v of
          Nothing -> throw CompilerErr $ "Lookup failed: " ++ pprint v
          Just ty -> assertEq annTy ty "Var annotation"
      return annTy
    Lam h lam -> Arrow h <$> typeCheckLamExpr lam
    -- TODO: check effect is empty unless arrowhead is PlainArrow
    Arrow _ piTy -> typeCheckPiType piTy $> TyKind
    Con con -> typeCheckCon con
    TC tyCon -> typeCheckTyCon tyCon $> TyKind

instance HasType Expr where
  typeCheck expr = case expr of
    App h f x -> do
      Arrow h' piTy@(Pi a _) <- typeCheck f
      x |: a
      assertEq h' h "arrow head mismatch"
      return $ snd $ applyPi piTy x
    For _ lam -> do
      Pi a (eff, b) <- typeCheckLamExpr lam
      -- TODO: check pi binder isn't free in `eff`
      return $ Arrow TabArrow $ Pi a (pureType b)
    Atom x -> typeCheck x
    Op op -> typeCheckOp op

instance HasType Block where
  typeCheck (Block decls result _) = do
    checkingEnv <- ask
    case checkingEnv of
      SkipChecks -> typeCheck result
      CheckWith (JointTypeEnv env _) -> do
        env' <- catFoldM checkDecl env decls
        withNamedEnv (env <> env') $ typeCheck result

checkDecl :: TypeEnv -> Decl -> TypeM TypeEnv
checkDecl env decl@(Let b@(_:>annTy) rhs) =
  withNamedEnv env $ addContext ctxStr $ do
    -- TODO: effects
    checkNoShadow env b
    annTy |: TyKind
    ty <- typeCheck rhs
    return $ b @> ty
  where ctxStr = "\nchecking decl: \n" ++ pprint decl

typeCheckLamExpr :: LamExpr -> TypeM (PiType EffectiveType)
typeCheckLamExpr (LamExpr b@(_:>a) body) = do
  bodyTy <- local (updateTypeCheckEnv (b @> a)) $ typeCheck body
  return $ makePi b (noEffect, bodyTy)

typeCheckPiType :: PiType EffectiveType -> TypeM ()
typeCheckPiType (Pi a b) = return () -- TODO!

withNamedEnv :: TypeEnv -> TypeM a -> TypeM a
withNamedEnv env m = local (const (CheckWith (fromNamedEnv env))) m

checkNoShadow :: (MonadError Err m, Pretty b) => Env a -> VarP b -> m ()
checkNoShadow env v = when (v `isin` env) $ throw CompilerErr $ pprint v ++ " shadowed"

addType :: Atom -> TypeM (Atom, Type)
addType x = do
  ty <- typeCheck x
  return (x, ty)

pureType :: Type -> EffectiveType
pureType ty = (noEffect, ty)

infixr 7 |:
(|:) :: Atom -> Type -> TypeM ()
(|:) x reqTy = do
  ty <- typeCheck x
  checkEq reqTy ty

-- TODO: consider skipping the checks if the env is Nothing
checkEq :: Type -> Type -> TypeM ()
checkEq reqTy ty = assertEq reqTy ty ""

updateTypeCheckEnv :: Env Type -> TypeCheckEnv -> TypeCheckEnv
updateTypeCheckEnv env tcEnv = case tcEnv of
  SkipChecks -> SkipChecks
  CheckWith prev -> CheckWith $ prev {namedEnv = namedEnv prev <> env}

-- === primitive ops and constructors ===

typeCheckTyCon :: TyCon Type Atom -> TypeM ()
typeCheckTyCon tc = case tc of
  BaseType _       -> return ()
  IntRange a b     -> a|:IntTy >> b|:IntTy
  IndexRange t a b -> t|:TyKind >> mapM_ (|:TyKind) a >> mapM_ (|:TyKind) b
  ArrayType _      -> return ()
  SumType (l, r)   -> l|:TyKind >> r|:TyKind
  RecType r        -> mapM_ (|:TyKind) r
  RefType a        -> a|:TyKind
  TypeKind         -> return ()

typeCheckCon :: Con -> TypeM Type
typeCheckCon con = case con of
  Lit l -> return $ BaseTy $ litType l
  ArrayLit (Array (shape, b) _) -> return $ ArrayTy shape b
  AnyValue t -> t|:TyKind $> t
  SumCon _ l r -> (TC . SumType) <$> ((,) <$> typeCheck l <*> typeCheck r)
  RecCon r -> RecTy <$> mapM typeCheck r
  AFor n a -> TabTy <$> typeCheck n <*> typeCheck a <*> return noEffect
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
  SumCase st l r -> do
    lp@(Pi la (leff, lb)) <- typeCheckLamExpr l
    rp@(Pi ra (reff, rb)) <- typeCheckLamExpr r
    when (any isDependentType [lp, rp]) $ throw TypeErr $
      "Return type of cases cannot depend on the matched value"
    checkEq leff noEffect
    checkEq reff noEffect
    checkEq lb rb
    st |: SumTy la ra
    return lb
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
  Select ty p x y -> ty|:TyKind >> p|:BoolTy >> x|:ty >> y|:ty $> ty
  IntAsIndex ty i -> ty|:TyKind >> i|:ty $> ty
  IndexAsInt i -> typeCheck i $> IntTy
  IdxSetSize i -> typeCheck i $> IntTy
  FFICall _ argTys ansTy args -> do
    mapM_ (|:TyKind) argTys >> ansTy|:TyKind
    zipWithM_ (|:) args argTys
    return ansTy
  Inject i -> do
    TC (IndexRange ty _ _) <- typeCheck i
    return ty
  Linearize lam -> do
    Pi a (eff, b) <- typeCheckLamExpr lam
    checkEq noEffect eff
    return $ a --> PairTy b (a --@ b)
  Transpose lam -> do
    Pi a (eff, b) <- typeCheckLamExpr lam
    checkEq noEffect eff
    return $ b --@ a
  _ -> error "not implemented"

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

-- === Pi types ===

maybeApplyPi :: (HasVars t, PiAbstractable t, MonadError Err m) => (PiType t) -> Maybe Atom -> m t
maybeApplyPi piTy maybeAtom
  | isDependentType piTy = do
      case maybeAtom of
        Just atom -> return $ applyPi piTy atom
        Nothing -> throw TypeErr $ "Dependent argument must be fully-reduced"
  | otherwise = return b  where (Pi _ b) = piTy


makePi :: PiAbstractable t => Var -> t -> PiType t
makePi v@(_:>a) b = Pi a $ abstractDepType v 0 b

applyPi :: PiAbstractable t => PiType t -> Atom -> t
applyPi (Pi _ b) x = instantiateDepType 0 x b

isDependentType :: (HasVars t, PiAbstractable t) => PiType t -> Bool
isDependentType (Pi _ b) = usesPiVar b
  where
    usesPiVar t = dummyVar `isin` freeVars (instantiateDepType 0 (Var dummyVar) t)
    dummyVar ="__dummy_type_variable_that_should_be_unused!" :> UnitTy

class PiAbstractable t where
  instantiateDepType :: Int -> Atom -> t -> t
  abstractDepType :: Var -> Int -> t -> t

instance PiAbstractable Type where
  instantiateDepType d x ty = case ty of
    Var v -> lookupDBVar v
    Arrow h (Pi a (e, b)) -> Arrow h $
      Pi (recur a) (instantiateDepType (d+1) x e, instantiateDepType (d+1) x b)
    Effect row tailVar -> Effect row' tailVar
      where row' = fold [ (lookupDBVarName v :>()) @> (eff, recur ann)
                        | (v, (eff, ann)) <- envPairs row]
    TC con -> TC $ fmapTyCon con recur (subst (env, mempty))
      where env = (DeBruijn d :>()) @> x
    _ -> error "Not a type"
    where
      recur ::Type -> Type
      recur = instantiateDepType d x

      lookupDBVarName :: Name -> Name
      lookupDBVarName v = case v of
        DeBruijn i | i == d -> v'  where (Var (v':>_)) = x
        _                   -> v

      lookupDBVar :: Var -> Type
      lookupDBVar (v:>ann) = case v of
        DeBruijn i | i == d -> x
        _                   -> Var $ v:>ann

  abstractDepType v d ty = case ty of
    Var (v':>ann) -> Var $ substWithDBVar v' :> ann
    Arrow h (Pi a (e, b)) -> Arrow h $
      Pi (recur a) (abstractDepType v (d+1) e, abstractDepType v (d+1) b)
    Effect row tailVar -> Effect row' tailVar
      where row' = fold [ (substWithDBVar v' :>()) @> (eff, recur ann)
                        | (v', (eff, ann)) <- envPairs row]
    TC con -> TC $ fmapTyCon con recur (subst (env, mempty))
      where env = v @> Var (DeBruijn d :> varAnn v)
    _ -> error "Not a type"
    where
      recur ::Type -> Type
      recur = abstractDepType v d

      substWithDBVar :: Name -> Name
      substWithDBVar v' | varName v == v' = DeBruijn d
                        | otherwise       = v'

instance PiAbstractable EffectiveType where
  instantiateDepType d x (eff, b) = ( instantiateDepType d x eff
                                    , instantiateDepType d x b)
  abstractDepType v d (eff, b) = ( abstractDepType v d eff
                                 , abstractDepType v d b)

-- === Effects (CURRENTLY NOT USED) ===

combineEffects :: MonadError Err m => Effect -> Effect -> m Effect
combineEffects ~eff@(Effect row t) ~eff'@(Effect row' t') = case (t, t') of
  (Nothing, Nothing) -> do
    row'' <- rowUnion row row'
    return $ Effect row'' Nothing
  (Just _ , Nothing) -> checkRowExtends row  row' >> return eff
  (Nothing, Just _ ) -> checkRowExtends row' row  >> return eff'
  (Just _ , Just _)
    | eff == eff' -> return eff
    | otherwise -> throw TypeErr $ "Effect mismatch "
                                 ++ pprint eff ++ " != " ++ pprint eff'

checkExtends :: MonadError Err m => Effect -> Effect -> m ()
checkExtends (Effect row _) (Effect row' Nothing) = checkRowExtends row row'
checkExtends eff eff' | eff == eff' = return ()
                      | otherwise   = throw TypeErr $ "Effect mismatch: "
                           ++ pprint eff ++ " doesn't extend " ++ pprint eff'

checkRowExtends :: MonadError Err m => EffectRow Type -> EffectRow Type -> m ()
checkRowExtends superRow row = do
  mapM_ (\(t,t') -> assertEq t t' "Effect type mismatch") $ rowMeet superRow row
  let extraEffects = rowJoin superRow row `envDiff` superRow
  when (extraEffects /= mempty) $
    throw TypeErr $ "Extra effects: " ++ pprint extraEffects

rowUnion :: MonadError Err m
         => EffectRow Type -> EffectRow Type -> m (EffectRow Type)
rowUnion (Env m) (Env m') = liftM Env $ sequence $
  M.unionWith consensusValsErr (fmap return m) (fmap return m')

consensusValsErr :: (Eq a, Pretty a, MonadError Err m) => m a -> m a -> m a
consensusValsErr x y = do
  x' <- x
  y' <- y
  assertEq x' y' "Map merge"
  return x'

rowMeet :: Env a -> Env b -> Env (a, b)
rowMeet (Env m) (Env m') = Env $ M.intersectionWith (,) m m'

rowJoin :: Env a -> Env b -> Env ()
rowJoin (Env m) (Env m') =
  Env $ M.unionWith (\() () -> ()) (fmap (const ()) m) (fmap (const ()) m')

popRow :: MonadError Err m
       => (a -> a -> m ())
       -> EffectRow a -> (EffectName, a) -> m (EffectRow a)
popRow eq env (eff, x) = case envLookup env (v:>()) of
  Nothing -> return env'
  Just (eff', x') -> do
    assertEq eff eff' "Effect"
    eq x x'
    return env'
  where v = DeBruijn 0
        env' = envDelete v env

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
