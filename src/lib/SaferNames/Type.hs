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
import qualified Data.Set as S
import Data.Text.Prettyprint.Doc

import LabeledItems
import Err
import Type (litType)

import SaferNames.Syntax
import SaferNames.Name
import SaferNames.PPrint ()

-- === top-level API ===

checkTypes :: MonadErr m => CheckableE e => Scope n -> e n -> m ()
checkTypes scope e = liftEither $ runSubstReaderT scope (idSubst scope) $ checkE e

getType :: HasType e => Scope n -> e n -> Type n
getType = undefined

-- === the type checking/querying monad ===

-- TODO: not clear why we need the explicit `MonadMP` here since it should
-- already be a superclass, transitively, through both MonadErrMP and
-- MonadAtomSubst.
class (MonadFail2 m, Monad2 m, MonadErr2 m, SubstReader AtomSubstVal m)
     => MonadTyper (m::MonadKind2)

-- This fakes MonadErr by just throwing a hard error using `error`. We use it
-- to skip the checks (via laziness) when we just querying types.
newtype IgnoreChecks e a = IgnoreChecks (Identity a)
                           deriving (Functor, Applicative, Monad)

instance MonadFail (IgnoreChecks e) where
  fail = undefined

instance Pretty e => MonadError e (IgnoreChecks e) where
  throwError = undefined
  catchError = undefined

type CheckedTyper = SubstReaderT Except AtomSubstVal  :: S -> S -> * -> *
instance MonadTyper CheckedTyper

type UncheckedTyper = SubstReaderT (IgnoreChecks Err) AtomSubstVal  :: S -> S -> * -> *
instance MonadTyper UncheckedTyper

-- === typeable things ===

-- alias for legacy reason. We should probably just use `getTypeE`.
typeCheck :: HasType e => MonadTyper m => e i -> m i o (Type o)
typeCheck = getTypeE

-- TODO: these should all return the substituted terms too, so we don't have to
-- traverse them twice (which might even bad asymptotics).
class HasNamesE e => CheckableE (e::E) where
  checkE :: MonadTyper m => e i -> m i o ()

class CheckableE e => HasType (e::E) where
  getTypeE :: MonadTyper m => e i -> m i o (Type o)

class HasNamesB b => CheckableB (b::B) where
  checkB :: MonadTyper m
         => b i i'
         -> (forall o'. b o o' -> m i' o' a)
         -> m i o a

-- === convenience functions ===

-- TODO: this should probably return the substituted term too,
-- because otherwise we end up traversing things twice
-- (usually just types though, not other terms).
infixr 7 |:
(|:) :: (MonadTyper m, HasType e) => e i -> Type o -> m i o ()
(|:) x reqTy = do
  ty <- typeCheck x
  checkAlphaEq reqTy ty

checkableFromHasType :: HasType e => MonadTyper m => e i -> m i o ()
checkableFromHasType e = void $ typeCheck e

checkEq :: (MonadErr m, Show a, Pretty a, Eq a) => a -> a -> m ()
checkEq reqTy ty = assertEq reqTy ty ""

-- === type checking core ===

dataConFunType :: DataDef n -> Int -> Type n
dataConFunType (DataDef _ (bs:>paramTys) cons) con = undefined
  -- let DataConDef _ argBinders = cons !! con
  -- in foldr (\(arr, b) body -> Pi (Abs b (arr, body)))
  --     (TypeCon def (map Var $ toList paramVars))
  --     (      zip (repeat ImplicitArrow) (toList paramBs)
  --         ++ zip (repeat PureArrow    ) (toList argBs))

typeConFunType :: DataDef n -> Type n
typeConFunType (DataDef _ (_:> ListE paramTys) _) = foldr (?-->) TyKind paramTys

instance CheckableE Atom where checkE = checkableFromHasType
instance HasType Atom where
  getTypeE atom = case atom of
    -- Var (AnnVar name annTy) -> do
    --   annTy |: TyKind
    --   annTy' <- substE annTy
    --   case annTy of
    --     EffKind -> throw CompilerErr "Effect variables should only occur in effect rows"
    --     _ -> return ()
    --   return annTy'
    -- TODO: check arrowhead-specific effect constraints (both lam and arrow)
    Lam (Abs b@(LamBinder _ arr) body) -> substB b \(LamBinder b' arr') -> do
      checkArrow arr
      -- TODO: effects
      bodyTy <- typeCheck body
      return $ Pi $ Abs (PiBinder b' arr') bodyTy
    Pi (Abs b@(PiBinder _ arr) resultTy) -> substB b \_ ->
      checkArrow arr >> resultTy|:TyKind $> TyKind
    Con con  -> typeCheckPrimCon con
    TC tyCon -> typeCheckPrimTC  tyCon
    Eff eff  -> checkEffRow eff $> EffKind
    -- DataCon (NamedDataDef _ def) params con args -> do
    --   def' <- substE def
    --   let funTy = dataConFunType def' con
    --   foldM checkApp funTy $ params ++ args
    -- TypeCon (NamedDataDef _ def) params -> do
    --   def' <- substE def
    --   let funTy = typeConFunType def'
    --   foldM checkApp funTy $ params
    LabeledRow row -> checkLabeledRow row $> LabeledRowKind
    Record items -> do
      types <- mapM typeCheck items
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
    -- VariantTy row -> checkLabeledRow row $> TyKind
    ACase e alts resultTy -> checkCase e alts resultTy
    -- DataConRef ~def@(DataDef _ paramBs [DataConDef _ argBs]) params args -> do
    --   checkEq (length paramBs) (length params)
    --   forM_ (zip (toList paramBs) (toList params)) \(b, param) ->
    --     param |: binderAnn b
    --   let argBs' = applyNaryAbs (Abs paramBs argBs) params
    --   checkDataConRefBindings argBs' args
    --   return $ RawRefTy $ TypeCon def params
    -- BoxedRef ptr numel (Abs b@(_:>annTy) body) -> do
    --   PtrTy (_, t) <- typeCheck ptr
    --   annTy |: TyKind
    --   annTy' <- substE annTy
    --   checkAlphaEq annTy' (BaseTy t)
    --   numel |: IdxRepTy
    --   scope <- askScope
    --   depTy <- substB b \b' -> do
    --     bodyTy <- typeCheck body
    --     return $ Abs b' bodyTy
    --   fromConstAbs depTy
    ProjectElt (i NE.:| is) v -> do
      ty <- typeCheck $ case NE.nonEmpty is of
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

instance CheckableE Expr where checkE = checkableFromHasType
instance HasType Expr where
  getTypeE expr = case expr of
    App f x -> do
      fTy <- typeCheck f
      checkApp fTy x
    Atom x   -> typeCheck x
    Op   op  -> typeCheckPrimOp op
    Hof  hof -> typeCheckPrimHof hof
    Case e alts resultTy -> checkCase e alts resultTy

instance CheckableE Block where checkE = checkableFromHasType
instance HasType Block where
  getTypeE = undefined
  -- getTypeE (Block ty decls expr) = do
  --   ty' <- substE ty
  --   checkBlockRec ty' (Abs decls expr)
  --   return ty'
  --   where
  --     checkBlockRec :: MonadTyper m => Type o -> Abs (Nest Decl) Expr i -> m i o ()
  --     checkBlockRec reqTy (Abs Empty result) = result |: reqTy
  --     checkBlockRec reqTy (Abs (Nest decl@(Let _ @(_:>tyAnn) rhs) rest) result) = do
  --       tyAnn' <- substE tyAnn
  --       rhs |: tyAnn'
  --       refreshBinders b \_ ->
  --         checkBlockRec (injectNamesL ext reqTy) $ Abs rest result

typeCheckPrimTC :: MonadTyper m => PrimTC (Atom i) -> m i o (Type o)
typeCheckPrimTC tc = case tc of
  BaseType _       -> return TyKind
  IntRange a b     -> a|:IdxRepTy >> b|:IdxRepTy >> return TyKind
  IndexRange t a b -> do
    t' <- substE t
    t|:TyKind >> mapM_ (|:t') a >> mapM_ (|:t') b >> return TyKind
  IndexSlice n l   -> n|:TyKind >> l|:TyKind >> return TyKind
  PairType a b     -> a|:TyKind >> b|:TyKind >> return TyKind
  UnitType         -> return TyKind
  RefType r a      -> mapM_ (|: TyKind) r >> a|:TyKind >> return TyKind
  TypeKind         -> return TyKind
  EffectRowKind    -> return TyKind
  LabeledRowKindTC -> return TyKind
  ParIndexRange t gtid nthr -> gtid|:IdxRepTy >> nthr|:IdxRepTy >> t|:TyKind >> return TyKind

typeCheckPrimCon :: MonadTyper m => PrimCon (Atom i) -> m i o (Type o)
typeCheckPrimCon con = case con of
  Lit l -> return $ BaseTy $ litType l
  PairCon x y -> PairTy <$> typeCheck x <*> typeCheck y
  UnitCon -> return UnitTy
  SumAsProd ty tag _ -> tag |:TagRepTy >> substE ty  -- TODO: check!
  ClassDictHole _ ty  -> ty |:TyKind   >> substE ty
  IntRangeVal     l h i -> i|:IdxRepTy >> substE (TC $ IntRange     l h)
  IndexRangeVal t l h i -> i|:IdxRepTy >> substE (TC $ IndexRange t l h)
  IndexSliceVal _ _ _ -> error "not implemented"
  BaseTypeRef p -> do
    (PtrTy (_, b)) <- typeCheck p
    return $ RawRefTy $ BaseTy b
  TabRef tabTy -> do
    TabTy b (RawRefTy a) <- typeCheck tabTy
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

typeCheckPrimOp :: MonadTyper m => PrimOp (Atom i) -> m i o (Type o)
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
    ty <- typeCheck x
    y |: ty
    return ty
  UnsafeFromOrdinal ty i -> ty|:TyKind >> i|:IdxRepTy >> substE ty
  ToOrdinal i -> typeCheck i $> IdxRepTy
  IdxSetSize i -> typeCheck i $> IdxRepTy
  FFICall _ ansTy args -> do
    forM_ args \arg -> do
      argTy <- typeCheck arg
      case argTy of
        BaseTy _ -> return ()
        _        -> throw TypeErr $ "All arguments of FFI calls have to be " ++
                                    "fixed-width base types, but got: " ++ pprint argTy
    declareEff IOEffect
    substE ansTy
  Inject i -> do
    TC tc <- typeCheck i
    case tc of
      IndexRange ty _ _ -> return ty
      ParIndexRange ty _ _ -> return ty
      _ -> throw TypeErr $ "Unsupported inject argument type: " ++ pprint (TC tc)
  -- PrimEffect ref m -> do
  --   TC (RefType ~(Just (Var (AnnVar h' TyKind))) s) <- typeCheck ref
  --   case m of
  --     MGet      ->                 declareEff (RWSEffect State  h') $> s
  --     MPut  x   -> x|:s         >> declareEff (RWSEffect State  h') $> UnitTy
  --     MAsk      ->                 declareEff (RWSEffect Reader h') $> s
  --     MExtend x -> x|:(s --> s) >> declareEff (RWSEffect Writer h') $> UnitTy
  -- IndexRef ref i -> do
  --   RefTy h (TabTyAbs a) <- typeCheck ref
  --   i |: absArgType a
  --   i' <- substE i
  --   eltTy <- applyAbsM a i'
  --   return $ RefTy h eltTy
  FstRef ref -> do
    RefTy h (PairTy a _) <- typeCheck ref
    return $ RefTy h a
  SndRef ref -> do
    RefTy h (PairTy _ b) <- typeCheck ref
    return $ RefTy h b
  IOAlloc t n -> do
    n |: IdxRepTy
    declareEff IOEffect
    return $ PtrTy (Heap CPU, t)
  IOFree ptr -> do
    PtrTy _ <- typeCheck ptr
    declareEff IOEffect
    return UnitTy
  PtrOffset arr off -> do
    PtrTy (a, b) <- typeCheck arr
    off |: IdxRepTy
    return $ PtrTy (a, b)
  PtrLoad ptr -> do
    PtrTy (_, t) <- typeCheck ptr
    declareEff IOEffect
    return $ BaseTy t
  PtrStore ptr val -> do
    PtrTy (_, t)  <- typeCheck ptr
    val |: BaseTy t
    declareEff IOEffect
    return $ UnitTy
  SliceOffset s i -> do
    TC (IndexSlice n l) <- typeCheck s
    l' <- typeCheck i
    checkAlphaEq l l'
    return n
  SliceCurry s i -> do
    TC (IndexSlice n (PairTy u v)) <- typeCheck s
    u' <- typeCheck i
    checkAlphaEq u u'
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
    types <- mapM typeCheck items
    rty <- typeCheck record
    rest <- case rty of
      RecordTy rest -> return rest
      _ -> throw TypeErr $ "Can't add fields to a non-record object "
                        <> pprint record <> " (of type " <> pprint rty <> ")"
    return $ RecordTy $ prefixExtLabeledItems types rest
  RecordSplit types record -> do
    mapM_ (|: TyKind) types
    types' <- mapM substE types
    fullty <- typeCheck record
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
    rty <- typeCheck variant
    rest <- case rty of
      VariantTy rest -> return rest
      _ -> throw TypeErr $ "Can't add alternatives to a non-variant object "
                        <> pprint variant <> " (of type " <> pprint rty <> ")"
    return $ VariantTy $ prefixExtLabeledItems types' rest
  VariantSplit types variant -> do
    mapM_ (|: TyKind) types
    types' <- mapM substE types
    fullty <- typeCheck variant
    full <- case fullty of
      VariantTy full -> return full
      _ -> throw TypeErr $ "Can't split a non-variant object "
                          <> pprint variant <> " (of type " <> pprint fullty
                          <> ")"
    diff <- labeledRowDifference full (NoExt types')
    return $ VariantTy $ NoExt $
      Unlabeled [ VariantTy $ NoExt types', VariantTy diff ]
  DataConTag x -> do
    (TypeCon _ _) <- typeCheck x
    return TagRepTy
  -- ToEnum t x -> do
  --   t |: TyKind
  --   x |: Word8Ty
  --   t' <- substE t
  --   TypeCon (NamedDataDef _ (DataDef _ _ dataConDefs)) _ <- return t'
  --   forM_ dataConDefs \(DataConDef _ (Abs binders _)) -> checkEmpty binders
  --   return t'
  _ -> undefined

typeCheckPrimHof :: MonadTyper m => PrimHof (Atom i) -> m i o (Type o)
typeCheckPrimHof op = undefined

-- Having this as a separate helper function helps with "'b0' is untouchable" errors
-- from GADT+monad type inference.
checkEmpty :: MonadErr m => Nest b n l -> m ()
checkEmpty Empty = return ()
checkEmpty _  = throw TypeErr "Not empty"

checkCase :: MonadTyper m => HasType body => Atom i -> [AltP body i] -> Type i -> m i o (Type o)
checkCase e alts resultTy = do
  resultTySubst <- substE resultTy
  ety <- typeCheck e
  case ety of
    -- TypeCon def params -> do
    --   let cons = applyDataDefParams def params
    --   checkEq  (length cons) (length alts)
    --   zipWithM_ cons alts \((DataConDef _ bs'), (Abs bs body)) -> do
    --     checkEq bs' bs
    --     resultTy' <- flip (foldr withBinder) bs $ typeCheck body
    -- --     checkEq resultTySubst resultTy'
    VariantTy (NoExt types) -> do
      checkEq (length types) (length alts)
      let bs = map typeAsBinderNest $ toList types
      zipWithM_ (checkAlt resultTySubst) bs alts
    VariantTy _ -> throw CompilerErr
      "Can't pattern-match partially-known variants"
    _ -> undefined
    _ -> throw TypeErr $ "Case analysis only supported on ADTs and variants, not on " ++ pprint ety
  return resultTySubst

typeAsBinderNest :: Type n -> Abs (Nest Binder) UnitE n
typeAsBinderNest ty = Abs (Nest (Ignore :> ty) Empty) UnitE

checkAlt :: HasType body => MonadTyper m
         => Type o -> EmptyAbs (Nest Binder) o -> AltP body i -> m i o ()
checkAlt = undefined
-- checkAlt resultTyReq reqBs (Abs bs body) = do
--   bs' <- substE (EmptyAbs bs)
--   checkAlphaEq reqBs bs'
--   withFreshAtomBinder bs \ext _ -> do
--     resultTy <- typeCheck body
--     let resultTyReq' = injectNamesL ext resultTyReq
--     checkAlphaEq resultTyReq' resultTy

checkApp :: MonadTyper m => Type o -> Atom i -> m i o (Type o)
checkApp = undefined
-- checkApp fTy x = do
--   Pi piTy <- return fTy
--   x |: absArgType piTy
--   x' <- substE x
--   let WithArrow arr resultTy = scopelessApplyAbs piTy x'
--   declareEffs $ arrowEff arr
--   return resultTy

checkArrow :: MonadTyper m => Arrow i -> m i o ()
checkArrow = mapM_ checkEffRow

typeCheckRef :: MonadTyper m => HasType e => e i -> m i o (Type o)
typeCheckRef x = do
  TC (RefType _ a) <- typeCheck x
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

typeCheckBaseType :: MonadTyper m => HasType e => e i -> m i o BaseType
typeCheckBaseType e =
  typeCheck e >>= \case
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

checkDataLike :: MonadError Err m => String -> Type n -> m ()
checkDataLike msg ty = case ty of
  Var _ -> error "Not implemented"
  -- TabTy _ b -> recur b
  -- RecordTy (NoExt items)  -> traverse_ recur items
  -- VariantTy (NoExt items) -> traverse_ recur items
  -- TypeCon def params ->
  --   mapM_ checkDataLikeDataCon $ applyDataDefParams def params
  TC con -> case con of
    BaseType _       -> return ()
    PairType a b     -> recur a >> recur b
    UnitType         -> return ()
    IntRange _ _     -> return ()
    IndexRange _ _ _ -> return ()
    IndexSlice _ _   -> return ()
    _ -> throw TypeErr $ pprint ty ++ msg
  _   -> throw TypeErr $ pprint ty ++ msg
  where recur x = checkDataLike msg x

-- checkDataLikeDataCon :: MonadError Err m => DataConDef -> m ()
-- checkDataLikeDataCon (DataConDef _ bs) =
--   mapM_ (checkDataLike "data con binder" . binderAnn) bs

checkData :: MonadError Err m => Type n -> m ()
checkData = checkDataLike " is not serializable"

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

--TODO: Make this work even if the type has type variables!
isData :: Type n -> Bool
isData ty = case checkData ty of
  Left  _ -> False
  Right _ -> True

projectLength :: Type n -> Int
projectLength ty = case ty of
  -- TypeCon def params ->
  --   let [DataConDef _ bs] = applyDataDefParams def params
  --   in length bs
  RecordTy (NoExt types) -> length types
  PairTy _ _ -> 2
  _ -> error $ "Projecting a type that doesn't support projecting: " ++ pprint ty

isTabTy :: Type n -> Bool
isTabTy (TabTy _ _) = True
isTabTy _ = False

-- === effects ===

checkEffRow :: MonadTyper m => EffectRow i -> m i o ()
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

declareEff :: MonadTyper m => Effect o -> m i o ()
declareEff eff = declareEffs $ oneEffect eff

declareEffs :: MonadTyper m => EffectRow o -> m i o ()
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

checkLabeledRow :: MonadTyper m => ExtLabeledItems (Type i) (AtomName i) -> m i o ()
checkLabeledRow (Ext items rest) = undefined
  -- mapM_ (|: TyKind) items
  -- forM_ rest \v -> do
  --   checkWithEnv \(env, _) -> case envLookup env (v:>()) of
  --     Nothing -> throw CompilerErr $ "Lookup failed: " ++ pprint v
  --     Just (ty, _) -> assertEq LabeledRowKind ty "Labeled row var"

labeledRowDifference :: MonadTyper m
                     => ExtLabeledItems (Type o) (AtomName o)
                     -> ExtLabeledItems (Type o) (AtomName o)
                     -> m i o (ExtLabeledItems (Type o) (AtomName o))
labeledRowDifference = undefined
-- labeledRowDifference (Ext (LabeledItems items) rest)
--                      (Ext (LabeledItems subitems) subrest) = do
--   -- Check types in the right.
--   _ <- flip M.traverseWithKey subitems \label subtypes ->
--     case M.lookup label items of
--       Just types -> assertEq subtypes
--           (NE.fromList $ NE.take (length subtypes) types) $
--           "Row types for label " ++ show label
--       Nothing -> throw TypeErr $ "Extracting missing label " ++ show label
--   -- Extract remaining types from the left.
--   let
--     neDiff xs ys = NE.nonEmpty $ NE.drop (length ys) xs
--     diffitems = M.differenceWith neDiff items subitems
--   -- Check tail.
--   diffrest <- case (subrest, rest) of
--     (Nothing, _) -> return rest
--     (Just v, Just v') | v == v' -> return Nothing
--     _ -> throw TypeErr $ "Row tail " ++ pprint subrest
--       ++ " is not known to be a subset of " ++ pprint rest
--   return $ Ext (LabeledItems diffitems) diffrest
