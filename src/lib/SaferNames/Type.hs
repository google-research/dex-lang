-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module SaferNames.Type (
  checkTypes, getType, litType, getBaseMonoidType) where

import Control.Category ((>>>))
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
    Lam (LamExpr arr b eff body) -> do
      checkArrowAndEffects arr eff
      checkB b \b' -> do
        eff' <- checkEffRow eff
        bodyTy <- getTypeE body
        return $ Pi $ PiType arr b' eff' bodyTy
    Pi (PiType arr b eff resultTy) -> do
      checkArrowAndEffects arr eff
      checkB b \_ -> do
        void $ checkEffRow eff
        resultTy|:TyKind
      return TyKind
    Con con  -> typeCheckPrimCon con
    TC tyCon -> typeCheckPrimTC  tyCon
    Eff eff  -> checkEffRow eff $> EffKind
    DataCon name params con args -> do
      name' <- substE name
      funTy <- dataConFunType name' con
      foldM checkApp funTy $ params ++ args
    TypeCon name params -> do
      name' <- substE name
      funTy <- typeConFunType name'
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
      DataDef _ paramBs [DataConDef _ argBs] <- lookupScopeM defName'
      paramTys <- nonDepBinderNestTypes paramBs
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

instance CheckableB Binder where

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
      tyReq' <- injectM decls' tyReq
      expr |: tyReq'
    return tyReq

instance CheckableB Decl where
  checkB (Let ann (b:>ty) expr) cont = do
    ty' <- checkTypeE TyKind ty
    expr' <- checkTypeE ty' expr
    let declInfo = TypedBinderInfo ty' $ LetBound ann expr'
    withFreshM declInfo \b' ->
      extendSubst (b @> Rename (binderName b')) $
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
  -- TabRef tabTy -> do
  --   TabTy b (RawRefTy a) <- getTypeE tabTy
  --   return $ RawRefTy $ TabTy b a
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
      MExtend x -> do
        updaterTy <- s --> s
        x|:updaterTy >> declareEff (RWSEffect Writer h') $> UnitTy
  IndexRef ref i -> do
    RefTy h (Pi (PiType TabArrow (b:>iTy) Pure eltTy)) <- getTypeE ref
    i' <- checkTypeE iTy i
    eltTy' <- applyAbs (Abs b eltTy) i'
    return $ RefTy h eltTy'
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
typeCheckPrimHof hof = case hof of
  For _ f -> do
    Pi (PiType _ b eff eltTy) <- getTypeE f
    eff' <- fromConstAbs $ Abs b eff
    declareEffs eff'
    return $ Pi $ PiType TabArrow b Pure eltTy
  -- Tile dim fT fS -> do
  --   FunTy tv eff  tr    <- typeCheck fT
  --   FunTy sv eff' sr    <- typeCheck fS
  --   TC (IndexSlice n l) <- return $ binderType tv
  --   (dv, b, b')         <- zipExtractDim dim tr sr
  --   checkEq l (binderType dv)
  --   checkEq n (binderType sv)
  --   when (dv `isin` freeVars b ) $ throw TypeErr "Cannot tile dimensions that other dimensions depend on"
  --   when (sv `isin` freeVars b') $ throw TypeErr "Cannot tile dimensions that other dimensions depend on"
  --   checkEq b b'
  --   checkEq eff eff'
  --   -- TODO: check `tv` and `sv` isn't free in `eff`
  --   declareEffs eff
  --   return $ replaceDim dim tr n
  --   where
  --     zipExtractDim 0 (TabTy dv b) b' = return (dv, b, b')
  --     zipExtractDim d (TabTy dv b) (TabTy sv b') =
  --       if binderType dv == binderType sv
  --         then zipExtractDim (d-1) b b'
  --         else throw TypeErr $ "Result type of tiled and non-tiled bodies differ along " ++
  --                              "dimension " ++ show (dim - d + 1) ++ ": " ++
  --                              pprint b ++ " and " ++ pprint b'
  --     zipExtractDim d _ _ = throw TypeErr $
  --       "Tiling over dimension " ++ show dim ++ " has to produce a result with at least " ++
  --       show (dim + 1) ++ " dimensions, but it has only " ++ show (dim - d)

  --     replaceDim 0 (TabTy _ b) n  = TabTy (Ignore n) b
  --     replaceDim d (TabTy dv b) n = TabTy dv $ replaceDim (d-1) b n
  --     replaceDim _ _ _ = error "This should be checked before"
  -- PTileReduce baseMonoids n mapping -> do
  --   -- mapping : gtid:IdxRepTy -> nthr:IdxRepTy -> (...((ParIndexRange n gtid nthr)=>a, acc{n})..., acc1)
  --   BinaryFunTy (Bind gtid) (Bind nthr) Pure mapResultTy <- typeCheck mapping
  --   (tiledArrTy, accTys) <- fromLeftLeaningConsListTy (length baseMonoids) mapResultTy
  --   let threadRange = TC $ ParIndexRange n (Var gtid) (Var nthr)
  --   TabTy threadRange' tileElemTy <- return tiledArrTy
  --   checkEq threadRange (binderType threadRange')
  --   -- TODO: Check compatibility of baseMonoids and accTys (need to be careful about lifting!)
  --   -- PTileReduce n mapping : (n=>a, (acc1, ..., acc{n}))
  --   return $ PairTy (TabTy (Ignore n) tileElemTy) $ mkConsListTy accTys
  While body -> do
    FunTy (b:>UnitTy) eff condTy <- getTypeE body
    PairE eff' condTy' <- fromConstAbs $ Abs b $ PairE eff condTy
    declareEffs eff'
    checkAlphaEq (BaseTy $ Scalar Word8Type) condTy'
    return UnitTy
  Linearize f -> do
    FunTy (binder:>a) Pure b <- getTypeE f
    b' <- fromConstAbs $ Abs binder b
    fLinTy <- a --@ b'
    a --> PairTy b' fLinTy
  Transpose f -> do
    Pi (PiType LinArrow (binder:>a) Pure b) <- getTypeE f
    b' <- fromConstAbs $ Abs binder b
    b' --@ a
  RunReader r f -> do
    (resultTy, readTy) <- checkRWSAction Reader f
    r |: readTy
    return resultTy
  RunWriter _ f -> do
    -- XXX: We can't verify compatibility between the base monoid and f, because
    --      the only way in which they are related in the runAccum definition is via
    --      the AccumMonoid typeclass. The frontend constraints should be sufficient
    --      to ensure that only well typed programs are accepted, but it is a bit
    --      disappointing that we cannot verify that internally. We might want to consider
    --      e.g. only disabling this check for prelude.
    uncurry PairTy <$> checkRWSAction Writer f
  RunState s f -> do
    (resultTy, stateTy) <- checkRWSAction State f
    s |: stateTy
    return $ PairTy resultTy stateTy
  RunIO f -> do
    Pi (PiType PlainArrow (b:>UnitTy) eff resultTy) <- getTypeE f
    PairE eff' resultTy' <- fromConstAbs $ Abs b $ PairE eff resultTy
    extendAllowedEffect IOEffect $ declareEffs eff'
    return resultTy'
  CatchException f -> do
    Pi (PiType PlainArrow (b:>UnitTy) eff resultTy) <- getTypeE f
    PairE eff' resultTy' <- fromConstAbs $ Abs b $ PairE eff resultTy
    extendAllowedEffect ExceptionEffect $ declareEffs eff'
    return $ maybeTy resultTy'
    where maybeTy :: Type n -> Type n
          maybeTy _ = error "need to implement Maybe"

checkRWSAction :: Typer m => RWS -> Atom i -> m i o (Type o, Type o)
checkRWSAction rws f = do
  BinaryFunTy regionBinder refBinder eff resultTy <- getTypeE f
  dropSubst $
    substB regionBinder \regionBinder' ->
      substB refBinder \refBinder' -> do
        eff' <- substE eff
        regionName <- injectM refBinder' $ binderName regionBinder'
        extendAllowedEffect (RWSEffect rws regionName) $ declareEffs eff'
  _ :> RefTy _ referentTy <- return refBinder
  referentTy' <- fromConstAbs $ Abs regionBinder referentTy
  resultTy' <- fromConstAbs $ Abs (NestPair regionBinder refBinder) resultTy
  return (resultTy', referentTy')

-- Having this as a separate helper function helps with "'b0' is untouchable" errors
-- from GADT+monad type inference.
checkEmpty :: MonadErr m => Nest b n l -> m ()
checkEmpty Empty = return ()
checkEmpty _  = throw TypeErr "Not empty"

nonDepBinderNestTypes :: ScopeReader m => Nest Binder l l' -> m n [Type n]
nonDepBinderNestTypes Empty = return []
-- nonDepBinderNestTypes (Nest (b:>ty) rest) = do
--   restTys <- nonDepBinderNestTypes rest
--   return $ projectNames ty : restTys

dataConFunType :: Typer m => Name DataDef o -> Int -> m i o (Type o)
dataConFunType name con = do
  DataDef _ paramBinders cons <- lookupScopeM name
  let DataConDef _ argBinders = cons !! con
  case argBinders of
    EmptyAbs argBinders' ->
      dropSubst $
        buildNaryPiType ImplicitArrow paramBinders \ext params ->
          buildNaryPiType PlainArrow argBinders' \ext' _ -> do
            params' <-  mapM (injectM ext') params
            name'   <-  injectM (ext >>> ext') name
            return $ TypeCon name' params'

typeConFunType :: Typer m => Name DataDef o -> m i o (Type o)
typeConFunType name = do
  DataDef _ paramBinders _ <- lookupScopeM name
  dropSubst $ buildNaryPiType ImplicitArrow paramBinders \ext params -> return TyKind

-- TODO: put this in Builder?
buildNaryPiType :: SubstReader AtomSubstVal m
                => Arrow
                -> Nest Binder i i'
                -> (forall o'. Ext o o' -> [Type o'] -> m i' o' (Type o'))
                -> m i o (Type o)
buildNaryPiType _ _ _ = undefined

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
checkDataConRefBindings = undefined
-- checkDataConRefBindings (EmptyAbs Empty) (Abs Empty UnitE) = return ()
-- checkDataConRefBindings (EmptyAbs (Nest b restBs)) (EmptyAbs (Nest refBinding restRefs)) = do
--   let DataConRefBinding b' ref = refBinding
--   ref |: RawRefTy (binderAnn b)
--   checkAlphaEq (binderAnn b) (binderAnn b')
--   restBs' <- scopelessSubst (b@>Var (binderName b')) restBs
--   checkB b' \_ -> checkDataConRefBindings restBs' restRefs
-- checkDataConRefBindings _ _ = throw CompilerErr $ "Mismatched args and binders"

typeAsBinderNest :: Type n -> Abs (Nest Binder) UnitE n
typeAsBinderNest ty = undefined --  Abs (Nest (Ignore :> ty) Empty) UnitE

checkAlt :: HasType body => Typer m
         => Type o -> EmptyAbs (Nest Binder) o -> AltP body i -> m i o ()
checkAlt resultTyReq reqBs (Abs bs body) = do
  bs' <- substE (EmptyAbs bs)
  checkAlphaEq reqBs bs'
  substB bs \bs' -> do
    resultTyReq' <- injectM bs' resultTyReq
    body |: resultTyReq'

checkApp :: Typer m => Type o -> Atom i -> m i o (Type o)
checkApp fTy x = do
  Pi (PiType _ (b:>argTy) eff resultTy) <- return fTy
  x' <- checkTypeE argTy x
  PairE eff' resultTy' <- applyAbs (Abs b (PairE eff resultTy)) x'
  declareEffs eff'
  return resultTy'

typeCheckRef :: Typer m => HasType e => e i -> m i o (Type o)
typeCheckRef x = do
  TC (RefType _ a) <- getTypeE x
  return a

checkArrowAndEffects :: MonadErr m => Arrow -> EffectRow n -> m ()
checkArrowAndEffects PlainArrow _ = return ()
checkArrowAndEffects _ Pure = return ()
checkArrowAndEffects _ _ = throw TypeErr $ "Only plain arrows may have effects"

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

getBaseMonoidType :: MonadErr1 m => ScopeReader m => Type n -> m n (Type n)
getBaseMonoidType ty = case ty of
  Pi (PiType _ b _ ty) -> fromConstAbs (Abs b ty)
  _     -> return ty

applyDataDefParams :: ScopeReader m => DataDef n -> [Type n] -> m n [DataConDef n]
applyDataDefParams (DataDef _ bs cons) params =
  fromListE <$> applyNaryAbs (Abs bs (ListE cons)) params

-- === effects ===

checkEffRow :: Typer m => EffectRow i -> m i o (EffectRow o)
checkEffRow _ = undefined -- return ()
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

extendAllowedEffect :: Typer m => Effect o -> m i o () -> m i o ()
extendAllowedEffect eff m = undefined -- updateAllowedEff (extendEffect eff) m

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
