-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module SaferNames.Type (
  checkTypes, getType, litType) where

import Control.Monad
import Control.Monad.Except hiding (Except)
import Control.Monad.Identity
import Data.Foldable (toList)
import Data.Functor
import qualified Data.List.NonEmpty as NE
import qualified Data.Map.Strict as M
import qualified Data.Set        as S
import Data.Text.Prettyprint.Doc

import LabeledItems
import Err
import Type (litType)

import SaferNames.Syntax
import SaferNames.Name
import SaferNames.PPrint ()

-- === top-level API ===

checkTypes :: forall n m e. MonadErr m => CheckableE e => Scope n -> e n -> m ()
checkTypes scope e = liftEither $ runSubstReaderT scope (newEnv Rename) m
  where m = void (checkE e) :: CheckedTyperM n n ()

getType :: forall e n. HasType e => Scope n -> e n -> Type n
getType scope e =
  runIdentity $ runIgnoreChecks $ runSubstReaderT scope (newEnv Rename) doit
  where doit = getTypeE e :: UncheckedTyper n n (Type n)

-- === the type checking/querying monad ===

-- TODO: not clear why we need the explicit `Monad2` here since it should
-- already be a superclass, transitively, through both MonadErr2 and
-- MonadAtomSubst.
class (MonadFail2 m, Monad2 m, MonadErr2 m, SubstReader AtomSubstVal m)
     => Typer (m::MonadKind2)

-- This fakes MonadErr by just throwing a hard error using `error`. We use it
-- to skip the checks (via laziness) when we just querying types.
newtype IgnoreChecks e a = IgnoreChecks { runIgnoreChecks :: Identity a }
                           deriving (Functor, Applicative, Monad)

instance MonadFail (IgnoreChecks e) where
  fail = error "Monad fail!"

instance Pretty e => MonadError e (IgnoreChecks e) where
  throwError e = error $ pprint e
  catchError m _ = m

type CheckedTyperM = SubstReaderT Except AtomSubstVal  :: S -> S -> * -> *
instance Typer CheckedTyperM

type UncheckedTyper = SubstReaderT (IgnoreChecks Err) AtomSubstVal  :: S -> S -> * -> *
instance Typer UncheckedTyper

-- === typeable things ===

-- Minimal complete definition: getTypeE | getTypeAndSubstE
-- (Usually we just implement `getTypeE` but for big things like blocks it can
-- be worth implementing the specialized versions too, as optimizations.)
class SubstE AtomSubstVal e => HasType (e::E) where
  getTypeE   :: Typer m => e i -> m i o (Type o)
  getTypeE e = snd <$> getTypeAndSubstE e

  getTypeAndSubstE :: Typer m => e i -> m i o (e o, Type o)
  getTypeAndSubstE e = (,) <$> substE e <*> getTypeE e

  checkTypeE :: Typer m => Type o -> e i -> m i o (e o)
  checkTypeE reqTy e = do
    (e', ty) <- getTypeAndSubstE e
    checkAlphaEq reqTy ty
    return e'

class HasNamesE e => CheckableE (e::E) where
  checkE :: Typer m => e i -> m i o (e o)

class HasNamesB b => CheckableB (b::B) where
  checkB :: Typer m
         => b i i'
         -> (forall o'. b o o' -> m i' o' a)
         -> m i o a

-- === convenience functions ===

infixr 7 |:
(|:) :: (Typer m, HasType e) => e i -> Type o -> m i o ()
(|:) x reqTy = void $ checkTypeE reqTy x

checkEq :: (MonadErr m, Show a, Pretty a, Eq a) => a -> a -> m ()
checkEq reqTy ty = assertEq reqTy ty ""

-- === type checking core ===

instance HasType Atom where
  getTypeE atom = case atom of
    Var name -> do
      substVal <- lookupSubstM name
      case substVal of
        Rename name' -> do
          TypedBinderInfo ty _ <- lookupScopeM name'
          return ty
        SubstVal atom' -> dropSubst $ getTypeE atom'
    -- TODO: check arrowhead-specific effect constraints (both lam and arrow)
    Lam (Abs b@(LamBinder _ arr) body) -> substB b \(LamBinder b' arr') -> do
      checkArrow arr
      -- TODO: effects
      bodyTy <- getTypeE body
      return $ Pi $ Abs (PiBinder b' arr') bodyTy
    Pi (Abs b@(PiBinder _ arr) resultTy) -> substB b \_ ->
      checkArrow arr >> resultTy|:TyKind $> TyKind
    Con con  -> typeCheckPrimCon con
    TC tyCon -> typeCheckPrimTC  tyCon
    Eff eff  -> checkEffRow eff $> EffKind
    DataCon name params con args -> do
      def <- substE name >>= lookupScopeM
      let funTy = dataConFunType def con
      foldM checkApp funTy $ params ++ args
    TypeCon name params -> do
      def <- substE name >>= lookupScopeM
      let funTy = typeConFunType def
      foldM checkApp funTy $ params
    LabeledRow row -> checkLabeledRow row $> LabeledRowKind
    Record items -> do
      types <- mapM getTypeE items
      return $ RecordTy (NoExt types)
    RecordTy row -> checkLabeledRow row $> TyKind
    -- Variant vtys@(Ext (LabeledItems types) _) label i arg -> do
    --   let ty = VariantTy vtys
    --   let argTy = do
    --         labelTys <- M.lookup label types
    --         guard $ i < length labelTys
    --         return $ labelTys NE.!! i
    --   case argTy of
    --     Just argType -> arg |: argType
    --     Nothing -> throw TypeErr $ "Bad variant: " <> pprint atom
    --                                <> " with type " <> pprint ty
    --   ty |: TyKind
    --   return ty
    VariantTy row -> checkLabeledRow row $> TyKind
    ACase e alts resultTy -> checkCase e alts resultTy
    DataConRef defName params args -> do
      defName' <- substE defName
      def@(DataDef _ paramBs@(_:>>paramTys) [DataConDef _ argBs]) <- lookupScopeM defName'
      params' <- forMZipped paramTys params checkTypeE
      argBs' <- applyNaryAbs (Abs paramBs argBs) params'
      checkDataConRefBindings argBs' args
      return $ RawRefTy $ TypeCon defName' params'
    -- BoxedRef ptr numel (Abs b@(_:>annTy) body) -> do
    --   PtrTy (_, t) <- getTypeE ptr
    --   annTy |: TyKind
    --   annTy' <- substE annTy
    --   checkAlphaEq annTy' (BaseTy t)
    --   numel |: IdxRepTy
    --   scope <- askScope
    --   depTy <- substB b \b' -> do
    --     bodyTy <- getTypeE body
    --     return $ Abs b' bodyTy
    --   fromConstAbs depTy
    ProjectElt (i NE.:| is) v -> do
      ty <- getTypeE $ case NE.nonEmpty is of
              Nothing -> Var v
              Just is' -> ProjectElt is' v
      case ty of
        -- TypeCon def params -> do
        --   [DataConDef _ bs'] <- return $ applyDataDefParams def params
        --   -- Users might be accessing a value whose type depends on earlier
        --   -- projected values from this constructor. Rewrite them to also
        --   -- use projections.
        --   let go :: Int -> SubstEnv -> Nest Binder -> Type
        --       go j env (Nest b _) | i == j = scopelessSubst env $ binderAnn b
        --       go j env (Nest b rest) = go (j+1) (env <> (b @> proj)) rest
        --         where proj = ProjectElt (j NE.:| is) v
        --       go _ _ _ = error "Bad projection index"
        --   return $ go 0 mempty bs'
        RecordTy (NoExt types) -> return $ toList types !! i
        RecordTy _ -> throw CompilerErr "Can't project partially-known records"
        PairTy x _ | i == 0 -> return x
        PairTy _ y | i == 1 -> return y
        Var _ -> throw CompilerErr $ "Tried to project value of unreduced type " <> pprint ty
        _ -> throw TypeErr $
              "Only single-member ADTs and record types can be projected. Got " <> pprint ty <> "   " <> pprint v

instance HasType Expr where
  getTypeE expr = case expr of
    App f x -> do
      fTy <- getTypeE f
      checkApp fTy x
    Atom x   -> getTypeE x
    Op   op  -> typeCheckPrimOp op
    Hof  hof -> typeCheckPrimHof hof
    Case e alts resultTy -> checkCase e alts resultTy

instance HasType Block where
  getTypeE (Block ty decls expr) = do
    tyReq <- substE ty
    checkB decls \decls' -> do
      tyReq' <- injectNamesM decls' tyReq
      expr |: tyReq'
    return tyReq

instance CheckableB Decl where
  checkB (Let ann (b:>ty) expr) cont = do
    ty' <- checkTypeE TyKind ty
    expr' <- checkTypeE ty' expr
    let declInfo = TypedBinderInfo ty' $ LetBound ann expr'
    withFreshM b declInfo \b' ->
      cont $ Let ann (b':>ty') expr'

instance CheckableB b => CheckableB (Nest b) where
  checkB nest cont = case nest of
    Empty -> cont Empty
    Nest b rest -> checkB b \b' -> checkB rest \rest' -> cont $ Nest b' rest'

typeCheckPrimTC :: Typer m => PrimTC (Atom i) -> m i o (Type o)
typeCheckPrimTC tc = case tc of
  BaseType _       -> return TyKind
  IntRange a b     -> a|:IdxRepTy >> b|:IdxRepTy >> return TyKind
  IndexRange t a b -> do
    t' <- checkTypeE TyKind t
    mapM_ (|:t') a >> mapM_ (|:t') b >> return TyKind
  IndexSlice n l   -> n|:TyKind >> l|:TyKind >> return TyKind
  PairType a b     -> a|:TyKind >> b|:TyKind >> return TyKind
  UnitType         -> return TyKind
  RefType r a      -> mapM_ (|: TyKind) r >> a|:TyKind >> return TyKind
  TypeKind         -> return TyKind
  EffectRowKind    -> return TyKind
  LabeledRowKindTC -> return TyKind
  ParIndexRange t gtid nthr -> gtid|:IdxRepTy >> nthr|:IdxRepTy >> t|:TyKind >> return TyKind

typeCheckPrimCon :: Typer m => PrimCon (Atom i) -> m i o (Type o)
typeCheckPrimCon con = case con of
  Lit l -> return $ BaseTy $ litType l
  PairCon x y -> PairTy <$> getTypeE x <*> getTypeE y
  UnitCon -> return UnitTy
  SumAsProd ty tag _ -> tag |:TagRepTy >> substE ty  -- TODO: check!
  ClassDictHole _ ty  -> ty |:TyKind   >> substE ty
  IntRangeVal     l h i -> i|:IdxRepTy >> substE (TC $ IntRange     l h)
  IndexRangeVal t l h i -> i|:IdxRepTy >> substE (TC $ IndexRange t l h)
  IndexSliceVal _ _ _ -> error "not implemented"
  BaseTypeRef p -> do
    (PtrTy (_, b)) <- getTypeE p
    return $ RawRefTy $ BaseTy b
  TabRef tabTy -> do
    TabTy b (RawRefTy a) <- getTypeE tabTy
    return $ RawRefTy $ TabTy b a
  ConRef conRef -> case conRef of
    UnitCon -> return $ RawRefTy UnitTy
    PairCon x y ->
      RawRefTy <$> (PairTy <$> typeCheckRef x <*> typeCheckRef y)
    IntRangeVal     l h i -> do
      l' <- substE l
      h' <- substE h
      i|:(RawRefTy IdxRepTy) >> return (RawRefTy $ TC $ IntRange     l' h')
    IndexRangeVal t l h i -> do
      t' <- substE t
      l' <- mapM substE l
      h' <- mapM substE h
      i|:(RawRefTy IdxRepTy)
      return $ RawRefTy $ TC $ IndexRange t' l' h'
    SumAsProd ty tag _ -> do    -- TODO: check args!
      tag |:(RawRefTy TagRepTy)
      RawRefTy <$> substE ty
    _ -> error $ "Not a valid ref: " ++ pprint conRef
  ParIndexCon t v -> t|:TyKind >> v|:IdxRepTy >> substE t
  RecordRef _ -> error "Not implemented"

typeCheckPrimOp :: Typer m => PrimOp (Atom i) -> m i o (Type o)
typeCheckPrimOp op = case op of
  -- TabCon ty xs -> do
  --   ty |: TyKind
  --   ty'@(TabTyAbs a) <- substE ty
  --   let idxs = indicesNoIO $ absArgType a
  --   mapM_ (uncurry (|:)) $ zip xs (fmap (withoutArrow . scopelessApplyAbs a) idxs)
  --   assertEq (length idxs) (length xs) "Index set size mismatch"
  --   return ty'
  ScalarBinOp binop x y -> do
    xTy <- typeCheckBaseType x
    yTy <- typeCheckBaseType y
    TC <$> BaseType <$> checkBinOp binop xTy yTy
  ScalarUnOp  unop  x -> do
    xTy <- typeCheckBaseType x
    TC <$> BaseType <$> checkUnOp unop xTy
  Select p x y -> do
    p |: (BaseTy $ Scalar Word8Type)
    ty <- getTypeE x
    y |: ty
    return ty
  UnsafeFromOrdinal ty i -> ty|:TyKind >> i|:IdxRepTy >> substE ty
  ToOrdinal i -> getTypeE i $> IdxRepTy
  IdxSetSize i -> getTypeE i $> IdxRepTy
  FFICall _ ansTy args -> do
    forM_ args \arg -> do
      argTy <- getTypeE arg
      case argTy of
        BaseTy _ -> return ()
        _        -> throw TypeErr $ "All arguments of FFI calls have to be " ++
                                    "fixed-width base types, but got: " ++ pprint argTy
    declareEff IOEffect
    substE ansTy
  Inject i -> do
    TC tc <- getTypeE i
    case tc of
      IndexRange ty _ _ -> return ty
      ParIndexRange ty _ _ -> return ty
      _ -> throw TypeErr $ "Unsupported inject argument type: " ++ pprint (TC tc)
  PrimEffect ref m -> do
    TC (RefType ~(Just (Var h')) s) <- getTypeE ref
    case m of
      MGet      ->                 declareEff (RWSEffect State  h') $> s
      MPut  x   -> x|:s         >> declareEff (RWSEffect State  h') $> UnitTy
      MAsk      ->                 declareEff (RWSEffect Reader h') $> s
      MExtend x -> x|:(s --> s) >> declareEff (RWSEffect Writer h') $> UnitTy
  IndexRef ref i -> do
    RefTy h (TabTyAbs a) <- getTypeE ref
    i' <- checkTypeE (piArgType a) i
    eltTy <- applyAbs a i'
    return $ RefTy h eltTy
  FstRef ref -> do
    RefTy h (PairTy a _) <- getTypeE ref
    return $ RefTy h a
  SndRef ref -> do
    RefTy h (PairTy _ b) <- getTypeE ref
    return $ RefTy h b
  IOAlloc t n -> do
    n |: IdxRepTy
    declareEff IOEffect
    return $ PtrTy (Heap CPU, t)
  IOFree ptr -> do
    PtrTy _ <- getTypeE ptr
    declareEff IOEffect
    return UnitTy
  PtrOffset arr off -> do
    PtrTy (a, b) <- getTypeE arr
    off |: IdxRepTy
    return $ PtrTy (a, b)
  PtrLoad ptr -> do
    PtrTy (_, t) <- getTypeE ptr
    declareEff IOEffect
    return $ BaseTy t
  PtrStore ptr val -> do
    PtrTy (_, t)  <- getTypeE ptr
    val |: BaseTy t
    declareEff IOEffect
    return $ UnitTy
  SliceOffset s i -> do
    TC (IndexSlice n l) <- getTypeE s
    l' <- getTypeE i
    checkAlphaEq l l'
    return n
  SliceCurry s i -> do
    TC (IndexSlice n (PairTy u v)) <- getTypeE s
    u' <- getTypeE i
    checkAlphaEq u u'
    return $ TC $ IndexSlice n v
  VectorBinOp _ _ _ -> throw CompilerErr "Vector operations are not supported at the moment"
  VectorPack xs -> do
    unless (length xs == vectorWidth) $ throw TypeErr lengthMsg
    BaseTy (Scalar sb) <- getTypeE $ head xs
    mapM_ (|: (BaseTy (Scalar sb))) xs
    return $ BaseTy $ Vector sb
    where lengthMsg = "VectorBroadcast should have exactly " ++ show vectorWidth ++
                      " elements: " ++ pprint op
  VectorIndex x i -> do
    BaseTy (Vector sb) <- getTypeE x
    i |: TC (IntRange (IdxRepVal 0) (IdxRepVal $ fromIntegral vectorWidth))
    return $ BaseTy $ Scalar sb
  ThrowError ty -> ty|:TyKind >> substE ty
  ThrowException ty -> do
    declareEff ExceptionEffect
    ty|:TyKind >> substE ty
  CastOp t@(Var _) _ -> t |: TyKind >> substE t
  CastOp destTy e -> do
    sourceTy <- typeCheckBaseType e
    destTy  |: TyKind
    (TC (BaseType destTy')) <- substE destTy
    checkValidCast sourceTy destTy'
    return $ TC $ BaseType $ destTy'
  RecordCons items record -> do
    types <- mapM getTypeE items
    rty <- getTypeE record
    rest <- case rty of
      RecordTy rest -> return rest
      _ -> throw TypeErr $ "Can't add fields to a non-record object "
                        <> pprint record <> " (of type " <> pprint rty <> ")"
    return $ RecordTy $ prefixExtLabeledItems types rest
  RecordSplit types record -> do
    mapM_ (|: TyKind) types
    types' <- mapM substE types
    fullty <- getTypeE record
    full <- case fullty of
      RecordTy full -> return full
      _ -> throw TypeErr $ "Can't split a non-record object " <> pprint record
                        <> " (of type " <> pprint fullty <> ")"
    diff <- labeledRowDifference full (NoExt types')
    return $ RecordTy $ NoExt $
      Unlabeled [ RecordTy $ NoExt types', RecordTy diff ]
  VariantLift types variant -> do
    mapM_ (|: TyKind) types
    types' <- mapM substE types
    rty <- getTypeE variant
    rest <- case rty of
      VariantTy rest -> return rest
      _ -> throw TypeErr $ "Can't add alternatives to a non-variant object "
                        <> pprint variant <> " (of type " <> pprint rty <> ")"
    return $ VariantTy $ prefixExtLabeledItems types' rest
  VariantSplit types variant -> do
    mapM_ (|: TyKind) types
    types' <- mapM substE types
    fullty <- getTypeE variant
    full <- case fullty of
      VariantTy full -> return full
      _ -> throw TypeErr $ "Can't split a non-variant object "
                          <> pprint variant <> " (of type " <> pprint fullty
                          <> ")"
    diff <- labeledRowDifference full (NoExt types')
    return $ VariantTy $ NoExt $
      Unlabeled [ VariantTy $ NoExt types', VariantTy diff ]
  DataConTag x -> do
    (TypeCon _ _) <- getTypeE x
    return TagRepTy
  ToEnum t x -> do
    x |: Word8Ty
    TypeCon name [] <- checkTypeE TyKind t
    DataDef _ _ dataConDefs <- lookupScopeM name
    forM_ dataConDefs \(DataConDef _ (Abs binders _)) -> checkEmpty binders
    return $ TypeCon name []

typeCheckPrimHof :: Typer m => PrimHof (Atom i) -> m i o (Type o)
typeCheckPrimHof op = undefined

-- Having this as a separate helper function helps with "'b0' is untouchable" errors
-- from GADT+monad type inference.
checkEmpty :: MonadErr m => Nest b n l -> m ()
checkEmpty Empty = return ()
checkEmpty _  = throw TypeErr "Not empty"

dataConFunType :: DataDef n -> Int -> Type n
dataConFunType (DataDef _ (bs:>>paramTys) cons) con = undefined
  -- let DataConDef _ argBinders = cons !! con
  -- in foldr (\(arr, b) body -> Pi (Abs b (arr, body)))
  --     (TypeCon def (map Var $ toList paramVars))
  --     (      zip (repeat ImplicitArrow) (toList paramBs)
  --         ++ zip (repeat PureArrow    ) (toList argBs))

typeConFunType :: DataDef n -> Type n
typeConFunType (DataDef _ (_:>> paramTys) _) = foldr (?-->) TyKind paramTys

checkCase :: Typer m => HasType body => Atom i -> [AltP body i] -> Type i -> m i o (Type o)
checkCase e alts resultTy = do
  resultTy' <- substE resultTy
  ety <- getTypeE e
  case ety of
    TypeCon defName params -> do
      def <- lookupScopeM defName
      cons <- applyDataDefParams def params
      forMZipped_ cons alts \(DataConDef _ bs') alt ->
        checkAlt resultTy' bs' alt
    VariantTy (NoExt types) -> do
      let bs = map typeAsBinderNest $ toList types
      forMZipped_ bs alts $ checkAlt resultTy'
    VariantTy _ -> throw CompilerErr
      "Can't pattern-match partially-known variants"
    _ -> throw TypeErr $ "Case analysis only supported on ADTs and variants, not on " ++ pprint ety
  return resultTy'

checkDataConRefBindings :: Typer m
                        => EmptyAbs (Nest Binder) o
                        -> EmptyAbs (Nest DataConRefBinding) i
                        -> m i o ()
checkDataConRefBindings (Abs Empty UnitE) (Abs Empty UnitE) = return ()
-- checkDataConRefBindings (Nest b restBs) (Nest refBinding restRefs) = do
--   let DataConRefBinding b'@(Bind v) ref = refBinding
--   ref |: RawRefTy (binderAnn b)
--   checkEq (binderAnn b) (binderAnn b')
--   let restBs' = scopelessSubst (b@>Var v) restBs
--   withBinder b' $ checkDataConRefBindings restBs' restRefs
-- checkDataConRefBindings _ _ = throw CompilerErr $ "Mismatched args and binders"

typeAsBinderNest :: Type n -> Abs (Nest Binder) UnitE n
typeAsBinderNest ty = Abs (Nest (Ignore :> ty) Empty) UnitE

checkAlt :: HasType body => Typer m
         => Type o -> EmptyAbs (Nest Binder) o -> AltP body i -> m i o ()
checkAlt = undefined
-- checkAlt resultTyReq reqBs (Abs bs body) = do
--   bs' <- substE (EmptyAbs bs)
--   checkAlphaEq reqBs bs'
--   withFreshAtomBinder bs \ext _ -> do
--     resultTy <- getTypeE body
--     let resultTyReq' = injectNamesL ext resultTyReq
--     checkAlphaEq resultTyReq' resultTy

checkApp :: Typer m => Type o -> Atom i -> m i o (Type o)
checkApp fTy x = do
  Pi piTy <- return fTy
  x' <- checkTypeE (piArgType piTy) x
  applyAbs piTy x'

checkArrow :: Typer m => Arrow i -> m i o ()
checkArrow = mapM_ checkEffRow

typeCheckRef :: Typer m => HasType e => e i -> m i o (Type o)
typeCheckRef x = do
  TC (RefType _ a) <- getTypeE x
  return a

checkIntBaseType :: MonadError Err m => Bool -> BaseType -> m ()
checkIntBaseType allowVector t = case t of
  Scalar sbt               -> checkSBT sbt
  Vector sbt | allowVector -> checkSBT sbt
  _ -> notInt
  where
    checkSBT sbt = case sbt of
      Int64Type -> return ()
      Int32Type -> return ()
      Word8Type  -> return ()
      _         -> notInt
    notInt = throw TypeErr $ "Expected a fixed-width " ++ (if allowVector then "" else "scalar ") ++
                             "integer type, but found: " ++ pprint t

checkFloatBaseType :: MonadError Err m => Bool -> BaseType -> m ()
checkFloatBaseType allowVector t = case t of
  Scalar sbt               -> checkSBT sbt
  Vector sbt | allowVector -> checkSBT sbt
  _ -> notFloat
  where
    checkSBT sbt = case sbt of
      Float64Type -> return ()
      Float32Type -> return ()
      _           -> notFloat
    notFloat = throw TypeErr $ "Expected a fixed-width " ++ (if allowVector then "" else "scalar ") ++
                               "floating-point type, but found: " ++ pprint t

checkValidCast :: MonadErr m => BaseType -> BaseType -> m ()
checkValidCast (PtrType _) (PtrType _) = return ()
checkValidCast (PtrType _) (Scalar Int64Type) = return ()
checkValidCast (Scalar Int64Type) (PtrType _) = return ()
checkValidCast sourceTy destTy =
  checkScalarType sourceTy >> checkScalarType destTy
  where
    checkScalarType ty = case ty of
      Scalar Int64Type   -> return ()
      Scalar Int32Type   -> return ()
      Scalar Word8Type   -> return ()
      Scalar Float64Type -> return ()
      Scalar Float32Type -> return ()
      _ -> throw TypeErr $ "Can't cast " ++ pprint sourceTy ++ " to " ++ pprint destTy

typeCheckBaseType :: Typer m => HasType e => e i -> m i o BaseType
typeCheckBaseType e =
  getTypeE e >>= \case
    TC (BaseType b) -> return b
    ty -> throw TypeErr $ "Expected a base type. Got: " ++ pprint ty

data ArgumentType = SomeFloatArg | SomeIntArg | SomeUIntArg
data ReturnType   = SameReturn | Word8Return

checkOpArgType :: MonadError Err m => ArgumentType -> BaseType -> m ()
checkOpArgType argTy x =
  case argTy of
    SomeIntArg   -> checkIntBaseType   True x
    SomeUIntArg  -> assertEq x (Scalar Word8Type) ""
    SomeFloatArg -> checkFloatBaseType True x

checkBinOp :: MonadError Err m => BinOp -> BaseType -> BaseType -> m BaseType
checkBinOp op x y = do
  checkOpArgType argTy x
  assertEq x y ""
  return $ case retTy of
    SameReturn -> x
    Word8Return -> Scalar Word8Type
  where
    (argTy, retTy) = case op of
      IAdd   -> (ia, sr);  ISub   -> (ia, sr)
      IMul   -> (ia, sr);  IDiv   -> (ia, sr)
      IRem   -> (ia, sr);
      ICmp _ -> (ia, br)
      FAdd   -> (fa, sr);  FSub   -> (fa, sr)
      FMul   -> (fa, sr);  FDiv   -> (fa, sr);
      FPow   -> (fa, sr)
      FCmp _ -> (fa, br)
      BAnd   -> (ia, sr);  BOr    -> (ia, sr)
      BShL   -> (ia, sr);  BShR   -> (ia, sr)
      where
        ia = SomeIntArg; fa = SomeFloatArg
        br = Word8Return; sr = SameReturn

checkUnOp :: MonadError Err m => UnOp -> BaseType -> m BaseType
checkUnOp op x = do
  checkOpArgType argTy x
  return $ case retTy of
    SameReturn -> x
    Word8Return -> Scalar Word8Type
  where
    (argTy, retTy) = case op of
      Exp              -> (f, sr)
      Exp2             -> (f, sr)
      Log              -> (f, sr)
      Log2             -> (f, sr)
      Log10            -> (f, sr)
      Log1p            -> (f, sr)
      Sin              -> (f, sr)
      Cos              -> (f, sr)
      Tan              -> (f, sr)
      Sqrt             -> (f, sr)
      Floor            -> (f, sr)
      Ceil             -> (f, sr)
      Round            -> (f, sr)
      LGamma           -> (f, sr)
      FNeg             -> (f, sr)
      BNot             -> (u, sr)
      where
        u = SomeUIntArg; f = SomeFloatArg; sr = SameReturn

indexSetConcreteSize :: Type n -> Maybe Int
indexSetConcreteSize ty = case ty of
  FixedIntRange low high -> Just $ fromIntegral $ high - low
  _                      -> Nothing

-- === various helpers for querying types ===

getBaseMonoidType :: ScopeReader m => Type n -> m n (Type n)
getBaseMonoidType = undefined
-- getBaseMonoidType scope ty = case ty of
--   Pi ab -> ignoreExcept $ runScopeReader scope $ fromConstAbs ab
--   _     -> return ty

applyDataDefParams :: ScopeReader m => DataDef n -> [Type n] -> m n [DataConDef n]
applyDataDefParams = undefined
-- applyDataDefParams (DataDef _ bs cons) params
--   | length params == length (toList bs) = applyNaryAbs (Abs bs cons) params
--   | otherwise = error $ "Wrong number of parameters: " ++ show (length params)

piArgType :: PiType n -> Type n
piArgType (Abs (PiBinder (_:>ty) _) _) = ty

-- === effects ===

checkEffRow :: Typer m => EffectRow i -> m i o ()
checkEffRow _ = return ()
-- checkEffRow (EffectRow effs effTail) = do
--   forM_ effs \eff -> case eff of
--     RWSEffect _ v -> Var (v:>TyKind) |: TyKind
--     ExceptionEffect -> return ()
--     IOEffect        -> return ()
--   forM_ effTail \v -> do
--     checkWithEnv \(env, _) -> case envLookup env (v:>()) of
--       Nothing -> throw CompilerErr $ "Lookup failed: " ++ pprint v
--       Just (ty, _) -> assertEq EffKind ty "Effect var"

declareEff :: Typer m => Effect o -> m i o ()
declareEff eff = declareEffs $ oneEffect eff

declareEffs :: Typer m => EffectRow o -> m i o ()
declareEffs = undefined
-- declareEffs effs = checkWithEnv \(_, allowedEffects) ->
--   checkExtends allowedEffects effs

checkExtends :: MonadError Err m => EffectRow n -> EffectRow n -> m ()
checkExtends = undefined
-- checkExtends allowed (EffectRow effs effTail) = do
--   let (EffectRow allowedEffs allowedEffTail) = allowed
--   case effTail of
--     Just _ -> assertEq allowedEffTail effTail ""
--     Nothing -> return ()
--   forM_ effs \eff -> unless (eff `elem` allowedEffs) $
--     throw CompilerErr $ "Unexpected effect: " ++ pprint eff ++
--                       "\nAllowed: " ++ pprint allowed

extendEffect :: Effect n -> EffectRow n -> EffectRow n
extendEffect = undefined
-- extendEffect eff (EffectRow effs t) = EffectRow (S.insert eff effs) t

oneEffect :: Effect n -> EffectRow n
oneEffect eff = EffectRow (S.singleton eff) Nothing

-- === labeled row types ===

checkLabeledRow :: Typer m => ExtLabeledItems (Type i) (AtomName i) -> m i o ()
checkLabeledRow (Ext items rest) = do
  mapM_ (|: TyKind) items
  forM_ rest \v -> do
    substVal <- lookupSubstM v
    case substVal of
      Rename name' -> do
        TypedBinderInfo ty _ <- lookupScopeM name'
        checkAlphaEq LabeledRowKind ty
      SubstVal atom -> dropSubst $ atom |: LabeledRowKind

labeledRowDifference :: Typer m
                     => ExtLabeledItems (Type o) (AtomName o)
                     -> ExtLabeledItems (Type o) (AtomName o)
                     -> m i o (ExtLabeledItems (Type o) (AtomName o))
labeledRowDifference (Ext (LabeledItems items) rest)
                     (Ext (LabeledItems subitems) subrest) = do
  -- Check types in the right.
  _ <- flip M.traverseWithKey subitems \label subtypes ->
    case M.lookup label items of
      -- Just types -> assertEq subtypes
      --     (NE.fromList $ NE.take (length subtypes) types) $
      --     "Row types for label " ++ show label
      Nothing -> throw TypeErr $ "Extracting missing label " ++ show label
  -- Extract remaining types from the left.
  let
    neDiff xs ys = NE.nonEmpty $ NE.drop (length ys) xs
    diffitems = M.differenceWith neDiff items subitems
  -- Check tail.
  diffrest <- case (subrest, rest) of
    (Nothing, _) -> return rest
    (Just v, Just v') | v == v' -> return Nothing
    _ -> throw TypeErr $ "Row tail " ++ pprint subrest
      ++ " is not known to be a subset of " ++ pprint rest
  return $ Ext (LabeledItems diffitems) diffrest
