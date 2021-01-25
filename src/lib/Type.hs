-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}  -- for MTL lifting

module Type (getType, checkType, HasType, EffectCtx (..),
             isData, extendEffect, EffectT) where

import Prelude hiding (pi)
import qualified Data.List.NonEmpty as NE
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.Maybe (fromMaybe)

import {-# SOURCE #-} Interpreter (indicesNoIO)

import Preamble
import Base
import Naming
import Syntax

class MonadChecker n m | m -> n where
  whenChecking :: (EffectRow n -> m ()) -> m ()
  extendAllowedEffects :: EffectRow n -> m a -> m a

type MonadTyper n m = (MonadChecker n m, DefReader n m, MonadErr m)

class HasType e where
  typeCheck :: MonadTyper n m => e n -> m (Type n)

getType :: (DefReader n m, HasType e) => e n -> m (Type n)
getType = undefined

checkType :: (DefReader n m, HasType e, MonadErr m) => e n -> m (Type n)
checkType = undefined

-- === Monad for carrying allowed effects ===

newtype EffectT n m a = EffectT (ReaderT (EffectRow n) m a)
  deriving (Functor, Applicative, Monad)

class Monad m => EffectCtx n m | m -> n where
  getAllowedEffects :: m (EffectRow n)
  extendEffects :: EffectRow n -> m a -> m a

instance Monad m => EffectCtx n (EffectT n m)

instance EffectCtx n m => EffectCtx n (ReaderT r m)

extendEffect :: EffectCtx n m => Effect n -> m a -> m a
extendEffect = undefined

-- === Core IR ===

instance HasType Atom where
  typeCheck atom = case atom of
    -- Var v -> lookupType v
    -- TODO: check arrowhead-specific effect constraints (both lam and arrow)
    -- Lam (Abs b (WithArrow arr body)) -> withBinder b $ do
    --   checkArrow arr
    --   bodyTy <- withAllowedEff (arrowEff arr) $ typeCheck body
    --   return $ Pi $ makeAbs b $ WithArrow arr bodyTy
    -- Pi (Abs b (WithArrow arr resultTy)) -> withBinder b $
    --   checkArrow arr >> resultTy|:TyKind $> TyKind
    PrimCon con -> typeCheckPrimCon con
    PrimTC  tc  -> typeCheckPrimTC  tc
    Eff eff  -> checkEffRow eff $> EffKind
    -- DataCon def@(DataDef _ paramBs cons) params con args -> do
    --   let paramVars = fmap (\(Bind v) -> Var v) $ fromNest paramBs
    --   let (DataConDef _ argBs) = cons !! con
    --   let funTy = foldr
    --         (\(arr, b) body -> Pi (Abs b (WithArrow arr body)))
    --         (TypeCon def paramVars)
    --         (   zip (repeat ImplicitArrow) (fromNest paramBs)
    --          ++ zip (repeat PureArrow    ) (fromNest argBs))
    --   foldM checkApp funTy $ params ++ args
    -- TypeCon (DataDef _ bs _) params -> do
    --   let paramTys = map binderType $ fromNest bs
    --   zipWithM_ (|:) params paramTys
    --   let paramTysRemaining = drop (length params) paramTys
    --   return $ foldr (:-->) TyKind paramTysRemaining
    -- LabeledRow row -> checkLabeledRow row $> LabeledRowKind
    -- Record items -> do
    --   types <- mapM typeCheck items
    --   return $ RecordTy (NoExt types)
    -- RecordTy row -> checkLabeledRow row $> TyKind
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
    --   checkAlphaEq (length paramBs) (length params)
    --   forM_ (zip (fromNest paramBs) (toList params)) \(b, param) ->
    --     param |: binderType b
    --   let argBs' = applyNaryAbs (Abs paramBs argBs) params
    --   checkDataConRefBindings argBs' args
    --   return $ RawRefTy $ TypeCon def params
    -- BoxedRef b ptr numel body -> do
    --   PtrTy (_, t) <- typeCheck ptr
    --   checkAlphaEq (binderType b) (BaseTy t)
    --   numel |: IdxRepTy
    --   void $ typeCheck b
    --   withBinder b $ typeCheck body
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
        --   let go j env (Nest b _) | i == j = scopelessSubst env $ binderType b
        --       go j env (Nest b rest) = go (j+1) (env <> (b @> proj)) rest
        --         where proj = ProjectElt (j NE.:| is) v
        --       go _ _ _ = error "Bad projection index"
        --   return $ go 0 mempty bs'
        -- RecordTy (NoExt types) -> return $ toList types !! i
        RecordTy _ -> throw CompilerErr "Can't project partially-known records"
        PairTy x _ | i == 0 -> return x
        PairTy _ y | i == 1 -> return y
        Var _ -> throw CompilerErr $ "Tried to project value of unreduced type " <> pprint ty
        _ -> throw TypeErr $
              "Only single-member ADTs and record types can be projected. Got " <> pprint ty <> "   " <> pprint v


-- checkDataConRefBindings :: MonadTyper n m => Nest Binder n -> Nest DataConRefBinding n -> m ()
-- checkDataConRefBindings Empty Empty = return ()
-- checkDataConRefBindings (Nest b restBs) (Nest refBinding restRefs) = do
--   let DataConRefBinding b'@(Bind v) ref = refBinding
--   ref |: RawRefTy (binderType b)
--   checkAlphaEq (binderType b) (binderType b')
--   let restBs' = scopelessSubst (b@>Var v) restBs
--   withBinder b' $ checkDataConRefBindings restBs' restRefs
-- checkDataConRefBindings _ _ = throw CompilerErr $ "Mismatched args and binders"

-- isDependent :: forall n. DataConDef n -> Bool
-- isDependent = undefined
-- isDependent (DataConDef _ binders) = go binders
--   where
--     go :: Nest Binder n -> Bool
--     go Empty = False
--     go (Nest b bs) = undefined --  (b `isin` freeVars bs) || go bs

instance HasType Expr where
  typeCheck expr = case expr of
    App arrow f x -> do
      fTy <- typeCheck f
      checkApp arrow fTy x
    Atom x   -> typeCheck x
    Op   op  -> typeCheckOp op
    Hof  hof -> typeCheckHof hof
    Case e alts resultTy -> checkCase e alts resultTy

checkCase :: (MonadTyper n m, PrettyH body, HasType body)
          => Atom n -> [NestedAbs Type body n] -> Type n -> m (Type n)
checkCase = undefined
-- checkCase e alts resultTy = do
--   checkWithEnv \_ -> do
--     ety <- typeCheck e
--     case ety of
--       TypeCon def params -> do
--         let cons = applyDataDefParams def params
--         checkAlphaEq  (length cons) (length alts)
--         forM_ (zip cons alts) \((DataConDef _ bs'), (Abs bs body)) -> do
--           checkAlphaEq bs' bs
--           resultTy' <- flip (foldr withBinder) (fromNest bs) $ typeCheck body
--           checkAlphaEq resultTy resultTy'
--       -- VariantTy (NoExt types) -> do
--       --   checkAlphaEq (length types) (length alts)
--       --   forM_ (zip (toList types) alts) \(ty, (Abs bs body)) -> do
--       --     [b] <- pure $ fromNest bs
--       --     checkAlphaEq (getType b) ty
--       --     resultTy' <- flip (foldr withBinder) (fromNest bs) $ typeCheck body
--       --     checkAlphaEq resultTy resultTy'
--       VariantTy _ -> throw CompilerErr
--         "Can't pattern-match partially-known variants"
--       _ -> throw TypeErr $ "Case analysis only supported on ADTs and variants, not on " ++ pprint ety
--   return resultTy

checkApp :: MonadTyper n m => Arrow -> Type n -> Atom n -> m (Type n)
checkApp = undefined
-- checkApp fTy x = do
--   Pi piTy <- return fTy
--   x |: absBinding piTy
--   let (WithArrow arr resultTy) = applyAbs undefined piTy x
--   declareEffs $ arrowEff arr
--   return resultTy

-- TODO: replace with something more precise (this is too cautious)
blockEffs :: Block n -> EffectRow n
blockEffs = undefined
-- blockEffs (Block decls result) =
--   foldMap declEffs (fromNest decls) <> exprEffs result
--   where declEffs (Let _ _ expr) = exprEffs expr

-- isPure :: Bindings n -> Expr n -> Bool
-- isPure env expr = exprEffs env expr == mempty

-- exprEffs :: Bindings n -> Expr n -> EffectRow n
-- exprEffs = undefined
-- exprEffs expr = case expr of
--   Atom _  -> Pure
--   App f _ -> functionEffs f
--   Op op   -> case op of
--     PrimEffect ref m -> case m of
--       MGet      -> oneEffect (RWSEffect State  h)
--       MPut    _ -> oneEffect (RWSEffect State  h)
--       MAsk      -> oneEffect (RWSEffect Reader h)
--       MExtend _ -> oneEffect (RWSEffect Writer h)
--       where RefTy (Var h) _ = getType ref
--     ThrowException _ -> oneEffect ExceptionEffect
--     IOAlloc  _ _  -> oneEffect IOEffect
--     IOFree   _    -> oneEffect IOEffect
--     PtrLoad  _    -> oneEffect IOEffect
--     PtrStore _ _  -> oneEffect IOEffect
--     FFICall _ _ _ -> oneEffect IOEffect
--     _ -> Pure
--   Hof hof -> case hof of
--     For _ f         -> functionEffs f
--     Tile _ _ _      -> error "not implemented"
--     While body      -> functionEffs body
--     Linearize _     -> mempty  -- Body has to be a pure function
--     Transpose _     -> mempty  -- Body has to be a pure function
--     -- RunReader _ f   -> handleRWSRunner Reader f
--     -- RunWriter _ f   -> handleRWSRunner Writer f
--     -- RunState  _ f   -> handleRWSRunner State  f
--     PTileReduce _ _ _ -> mempty
--     -- RunIO ~(Lam (Abs _ (WithArrow (PlainArrow (EffectRow effs t)) _))) ->
--     --   EffectRow (S.delete IOEffect effs) t
--     -- CatchException ~(Lam (Abs _ (WithArrow (PlainArrow (EffectRow effs t)) _))) ->
--     --   EffectRow (S.delete ExceptionEffect effs) t
--   -- Case _ alts _ -> foldMap (\(Abs _ block) -> blockEffs block) alts
--   -- where
--     -- handleRWSRunner rws ~(BinaryFunVal (Just h :>_) _ (EffectRow effs t) _) =
--     --   EffectRow (S.delete (RWSEffect rws h) effs) t

-- functionEffs :: Bindings n -> Atom n -> EffectRow n
-- functionEffs env f = undefined
-- case getType f of
--   -- Pi (Abs _ (WithArrow arr _)) -> arrowEff arr
--   _ -> error "Expected a function type"

instance HasType Block where
  typeCheck = undefined
  -- typeCheck (Block decls result) = do
  --   checkingEnv <- ask
  --   case checkingEnv of
  --     SkipChecks -> typeCheck result
  --     CheckWith (env, _) -> do
  --       env' <- catFoldM checkDecl env $ fromNest decls
  --       ty <- withBindings (env <> env') $ typeCheck result
  --       ty |: TyKind
  --       return ty

-- instance HasType Binder where
--   typeCheck b = do
--     checkWithEnv \(env, _) -> checkNoShadow env b
--     let ty = binderType b
--     ty |: TyKind
--     return ty

-- checkDecl :: MonadTyper n m => Bindings n -> Decl n -> m (Bindings n)
-- checkDecl = undefined
-- checkDecl env decl = withTypeEnv env $ addContext ctxStr $ case decl of
--   Let _ b rhs -> do
--     -- TODO: effects
--     ty  <- typeCheck b
--     ty' <- typeCheck rhs
--     checkAlphaEq ty ty'
--     return $ boundVars b
--   where ctxStr = "checking decl:\n" ++ pprint decl

infixr 7 |:
(|:) :: (MonadTyper n m, HasType e) => e n -> Type n -> m ()
(|:) x reqTy = do
  ty <- typeCheck x
  checkAlphaEq reqTy ty

-- checkAlphaEq :: (MonadTyper n m,  PrettyH e, AlphaEq e) => e n -> e n -> m ()
checkAlphaEq :: (MonadTyper n m,  PrettyH e) => e n -> e n -> m ()
checkAlphaEq reqTy ty = undefined -- checkWithEnv \_ -> assertEq reqTy ty ""

-- withBinder :: Binder n -> TypeM n a -> TypeM n a
-- withBinder = undefined
-- withBinder b m = typeCheck b >> extendTypeEnv (boundVars b) m

-- checkNoShadow :: (MonadErr m) => Env n a -> Binder n -> m ()
-- checkNoShadow env b = when (b `isin` env) $ throw CompilerErr $ pprint b ++ " shadowed"

-- === Core IR syntactic variants ===

type VariantM = ReaderT IRVariant Except

checkModuleVariant :: Module n -> Except ()
checkModuleVariant = undefined
-- checkModuleVariant (Module ir decls bindings) = do
--   flip runReaderT ir $ mapM_ checkVariant (fromNest decls)
--   flip runReaderT ir $ mapM_ (checkVariant . snd) bindings

class CoreVariant a where
  checkVariant :: a -> VariantM ()

instance CoreVariant (Atom n) where
  checkVariant atom = addExpr atom $ case atom of
    Var _ -> alwaysAllowed
    -- Lam (UnsafeMakeAbs ty _ (WithArrow _   body)) ->
    --   checkVariant ty >> checkVariant body
    -- Pi  (UnsafeMakeAbs ty _ (WithArrow arr body)) -> do
    --   case arr of
    --     -- The restriction on function types after Simp is a bit more subtle now
    --     -- that we allow non-inlined functions. TODO: decide what the
    --     -- restriction is and enforce it here.
    --     -- TabArrow -> alwaysAllowed
    --     -- _        -> goneBy Simp
    --     _ -> alwaysAllowed
    --   checkVariant ty >> checkVariant body
    Con _ _ -> alwaysAllowed
    PrimCon e -> checkVariant e >> forM_ e checkVariant
    PrimTC  e -> checkVariant e >> forM_ e checkVariant
    Eff _ -> alwaysAllowed
    LabeledRow _ -> goneBy Simp
    Record _ -> alwaysAllowed
    RecordTy _ -> alwaysAllowed
    Variant _ _ _ _ -> alwaysAllowed
    VariantTy _ -> alwaysAllowed
    ACase _ _ _ -> goneBy Simp
    DataConRef _ _ _ -> neverAllowed  -- only used internally in Imp lowering
    -- BoxedRef _ _ _ _ -> neverAllowed  -- only used internally in Imp lowering
    ProjectElt _ _ -> alwaysAllowed

instance CoreVariant (Expr n) where
  checkVariant expr = addExpr expr $ case expr of
    App _ f x -> checkVariant f >> checkVariant x
    Atom x  -> checkVariant x
    Op  e   -> checkVariant e >> forM_ e checkVariant
    Hof e   -> checkVariant e >> forM_ e checkVariant
    -- Case e alts _ -> do
    --   checkVariant e
    --   forM_ alts \(Abs _ body) -> checkVariant body

instance CoreVariant (Def n) where
  -- let annotation restrictions?
  checkVariant = undefined -- (Let ty _ expr) = checkVariant ty >> checkVariant expr
  -- checkVariant = undefined
  -- checkVariant info = case info of
  --   DataBoundTypeCon _   -> alwaysAllowed
  --   DataBoundDataCon _ _ -> alwaysAllowed
  --   LetBound _ _     -> absentUntil Simp
  --   _                -> neverAllowed

instance CoreVariant (Block n) where
  checkVariant = undefined
  -- checkVariant (Block ds e) = mapM_ checkVariant (fromNest ds) >> checkVariant e

instance CoreVariant (PrimTC (Atom n)) where
  checkVariant e = case e of
    -- TODO: only `TypeKind` past Simp is in the effect regions. We could make a
    -- distinct tyep for those, so we can rule out this case.
    TypeKind -> alwaysAllowed
    EffectRowKind  -> alwaysAllowed
    _ -> alwaysAllowed

instance CoreVariant (PrimOp (Atom n)) where
  checkVariant e = case e of
    ThrowException _ -> goneBy Simp
    Select _ _ _       -> alwaysAllowed  -- TODO: only scalar select after Simp
    _ -> alwaysAllowed

instance CoreVariant (PrimCon (Atom n)) where
  checkVariant e = case e of
    ClassDictHole _ _ -> goneBy Core
    _ -> alwaysAllowed

instance CoreVariant (PrimHof (Atom n)) where
  checkVariant e = case e of
    For _ _       -> alwaysAllowed
    While _       -> alwaysAllowed
    RunReader _ _ -> alwaysAllowed
    RunWriter _ _ -> alwaysAllowed
    RunState  _ _ -> alwaysAllowed
    RunIO     _   -> alwaysAllowed
    Linearize _   -> goneBy Simp
    Transpose _   -> goneBy Simp
    Tile _ _ _    -> alwaysAllowed
    PTileReduce _ _ _ -> absentUntil Simp -- really absent until parallelization
    CatchException _  -> goneBy Simp

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

addExpr :: (Pretty e, MonadErr m) => e -> m a -> m a
addExpr x m = modifyErr m \e -> case e of
  Err IRVariantErr ctx s -> Err CompilerErr ctx (s ++ ": " ++ pprint x)
  _ -> e

-- === effects ===

checkEffRow :: MonadTyper n m => EffectRow n -> m ()
checkEffRow (EffectRow effs effTail) = do
  forM_ effs \eff -> case eff of
    RWSEffect _ (NonInlinableName v) -> Var v |: TyKind
    ExceptionEffect -> return ()
    IOEffect        -> return ()
  -- forM_ effTail \v -> checkWithEnv \_ -> do
  --   ty <- lookupType v
  --   assertEq EffKind ty "Effect var"

declareEff :: MonadTyper n m => Effect n -> m ()
declareEff eff = declareEffs $ oneEffect eff

declareEffs :: MonadTyper n m => EffectRow n -> m ()
declareEffs = undefined
-- declareEffs effs = checkWithEnv \allowedEffects ->
--   checkExtends allowedEffects effs

checkExtends :: MonadErr m => EffectRow n -> EffectRow n -> m ()
checkExtends = undefined
-- checkExtends allowed (EffectRow effs effTail) = do
--   let (EffectRow allowedEffs allowedEffTail) = allowed
--   case effTail of
--     Just _ -> assertEq allowedEffTail effTail ""
--     Nothing -> return ()
--   forM_ effs \eff -> unless (eff `elem` allowedEffs) $
--     throw CompilerErr $ "Unexpected effect: " ++ pprint eff ++
--                       "\nAllowed: " ++ pprint allowed

oneEffect :: Effect n -> EffectRow n
oneEffect eff = EffectRow (S.singleton eff) Nothing

-- === labeled row types ===

checkLabeledRow :: MonadTyper n m => ExtLabeledItems Type n -> m ()
checkLabeledRow = undefined
-- checkLabeledRow (Ext items rest) = do
--   mapM_ (|: TyKind) items
--   forM_ rest \v -> checkWithEnv \_ -> do
--     ty <- lookupType v
--     assertEq LabeledRowKind ty "Labeled row var"

labeledRowDifference :: MonadTyper n m => ExtLabeledItems Type n -> ExtLabeledItems Type n
                     -> m (ExtLabeledItems Type n)
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

-- === primitive ops and constructors ===

typeCheckPrimTC :: MonadTyper n m => PrimTC (Atom n) -> m (Type n)
typeCheckPrimTC tc = case tc of
  BaseType _       -> return TyKind
  IntRange a b     -> a|:IdxRepTy >> b|:IdxRepTy >> return TyKind
  IndexRange t a b -> t|:TyKind >> mapM_ (|:t) a >> mapM_ (|:t) b >> return TyKind
  IndexSlice n l   -> n|:TyKind >> l|:TyKind >> return TyKind
  PairType a b     -> a|:TyKind >> b|:TyKind >> return TyKind
  UnitType         -> return TyKind
  RefType r a      -> mapM_ (|: TyKind) r >> a|:TyKind >> return TyKind
  TypeKind         -> return TyKind
  EffectRowKind    -> return TyKind
  LabeledRowKindTC -> return TyKind
  ParIndexRange t gtid nthr -> gtid|:IdxRepTy >> nthr|:IdxRepTy >> t|:TyKind >> return TyKind

typeCheckPrimCon :: MonadTyper n m => PrimCon (Atom n) -> m (Type n)
typeCheckPrimCon con = case con of
  Lit l -> return $ BaseTy $ litType l
  PairCon x y -> PairTy <$> typeCheck x <*> typeCheck y
  UnitCon -> return UnitTy
  SumAsProd ty tag _ -> tag |:TagRepTy >> return ty  -- TODO: check!
  ClassDictHole _ ty -> ty |: TyKind >> return ty
  IntRangeVal     l h i -> i|:IdxRepTy >> return (PrimTC $ IntRange     l h)
  IndexRangeVal t l h i -> i|:IdxRepTy >> return (PrimTC $ IndexRange t l h)
  IndexSliceVal _ _ _ -> error "not implemented"
  BaseTypeRef p -> do
    (PtrTy (_, b)) <- typeCheck p
    return $ RawRefTy $ BaseTy b
  -- TabRef tabTy -> do
  --   TabTy b (RawRefTy a) <- typeCheck tabTy
  --   return $ RawRefTy $ TabTy b a
  ConRef conRef -> case conRef of
    UnitCon -> return $ RawRefTy UnitTy
    PairCon x y ->
      RawRefTy <$> (PairTy <$> typeCheckRef x <*> typeCheckRef y)
    IntRangeVal     l h i ->
      i|:(RawRefTy IdxRepTy) >> return (RawRefTy $ PrimTC $ IntRange     l h)
    IndexRangeVal t l h i ->
      i|:(RawRefTy IdxRepTy) >> return (RawRefTy $ PrimTC $ IndexRange t l h)
    SumAsProd ty tag _ -> do    -- TODO: check args!
      tag |:(RawRefTy TagRepTy)
      return $ RawRefTy ty
    _ -> error $ "Not a valid ref: " ++ pprint conRef
  ParIndexCon t v -> t|:TyKind >> v|:IdxRepTy >> return t
  RecordRef _ -> error "Not implemented"

typeCheckRef :: MonadTyper n m => Atom n -> m (Type n)
typeCheckRef x = do
  PrimTC (RefType _ a) <- typeCheck x
  return a

checkIntBaseType :: MonadErr m => Bool -> Type n -> m ()
checkIntBaseType allowVector t = case t of
  BaseTy (Scalar sbt)               -> checkSBT sbt
  BaseTy (Vector sbt) | allowVector -> checkSBT sbt
  _ -> notInt
  where
    checkSBT sbt = case sbt of
      Int64Type -> return ()
      Int32Type -> return ()
      Word8Type  -> return ()
      _         -> notInt
    notInt = throw TypeErr $ "Expected a fixed-width " ++ (if allowVector then "" else "scalar ") ++
                             "integer type, but found: " ++ pprint t

checkFloatBaseType :: MonadErr m => Bool -> Type n -> m ()
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

checkValidCast :: MonadTyper n m => Type n -> Type n -> m ()
checkValidCast (BaseTy (PtrType _)) (BaseTy (PtrType _)) = return ()
checkValidCast (BaseTy (PtrType _)) (BaseTy (Scalar Int64Type)) = return ()
checkValidCast (BaseTy (Scalar Int64Type)) (BaseTy (PtrType _)) = return ()
checkValidCast sourceTy destTy =
  checkScalarType sourceTy >> checkScalarType destTy
  where
    checkScalarType ty = case ty of
      BaseTy (Scalar Int64Type  ) -> return ()
      BaseTy (Scalar Int32Type  ) -> return ()
      BaseTy (Scalar Word8Type  ) -> return ()
      BaseTy (Scalar Float64Type) -> return ()
      BaseTy (Scalar Float32Type) -> return ()
      _ -> throw TypeErr $ "Can't cast " ++ pprint sourceTy ++ " to " ++ pprint destTy

typeCheckOp :: MonadTyper n m => PrimOp (Atom n) -> m (Type n)
typeCheckOp op = case op of
  -- TabCon ty xs -> do
  --   ty |: TyKind
  --   TabTyAbs a <- return ty
  --   let idxs = indicesNoIO $ absArgType a
  --   mapM_ (uncurry (|:)) $ zip xs (fmap (withoutArrow . applyAbs a) idxs)
  --   assertEq (length idxs) (length xs) "Index set size mismatch"
  --   return ty
  ScalarBinOp binop x y -> bindM2 (checkBinOp binop) (typeCheck x) (typeCheck y)
  ScalarUnOp  unop  x   -> checkUnOp unop =<< typeCheck x
  Select p x y -> do
    p |: (BaseTy $ Scalar Word8Type)
    ty <- typeCheck x
    y |: ty
    return ty
  UnsafeFromOrdinal ty i -> ty|:TyKind >> i|:IdxRepTy $> ty
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
    return ansTy
  Inject i -> do
    PrimTC tc <- typeCheck i
    case tc of
      IndexRange ty _ _ -> return ty
      ParIndexRange ty _ _ -> return ty
      _ -> throw TypeErr $ "Unsupported inject argument type: " ++ pprint (PrimTC tc)
  PrimEffect ref m -> do
    PrimTC (RefType ~(Just (Var h')) s) <- typeCheck ref
    let h'' = fromName h'
    case m of
      MGet      ->                  declareEff (RWSEffect State  h'') $> s
      MPut  x   -> x|:s          >> declareEff (RWSEffect State  h'') $> UnitTy
      MAsk      ->                  declareEff (RWSEffect Reader h'') $> s
      MExtend x -> x|:(s :--> s) >> declareEff (RWSEffect Writer h'') $> UnitTy
  -- IndexRef ref i -> do
  --   RefTy h (TabTyAbs a) <- typeCheck ref
  --   i |: absArgType a
  --   return $ RefTy h $ withoutArrow $ applyAbs a i
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
    PrimTC (IndexSlice n l) <- typeCheck s
    l' <- typeCheck i
    checkAlphaEq l l'
    return n
  SliceCurry s i -> do
    PrimTC (IndexSlice n (PairTy u v)) <- typeCheck s
    u' <- typeCheck i
    checkAlphaEq u u'
    return $ PrimTC $ IndexSlice n v
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
    i |: PrimTC (IntRange (IdxRepVal 0) (IdxRepVal $ fromIntegral vectorWidth))
    return $ BaseTy $ Scalar sb
  ThrowError ty -> ty|:TyKind $> ty
  ThrowException ty -> do
    declareEff ExceptionEffect
    ty|:TyKind $> ty
  CastOp t@(Var _) _ -> t |: TyKind $> t
  CastOp destTy e -> do
    sourceTy <- typeCheck e
    destTy  |: TyKind
    checkValidCast sourceTy destTy
    return destTy
  -- RecordCons items record -> do
  --   types <- mapM typeCheck items
  --   rty <- typeCheck record
  --   rest <- case rty of
  --     RecordTy rest -> return rest
  --     _ -> throw TypeErr $ "Can't add fields to a non-record object "
  --                       <> pprint record <> " (of type " <> pprint rty <> ")"
  --   return $ RecordTy $ prefixExtLabeledItems types rest
  -- RecordSplit types record -> do
  --   mapM_ (|: TyKind) types
  --   fullty <- typeCheck record
  --   full <- case fullty of
  --     RecordTy full -> return full
  --     _ -> throw TypeErr $ "Can't split a non-record object " <> pprint record
  --                       <> " (of type " <> pprint fullty <> ")"
  --   diff <- labeledRowDifference full (NoExt types)
  --   return $ RecordTy $ NoExt $
  --     Unlabeled [ RecordTy $ NoExt types, RecordTy diff ]
  -- VariantLift types variant -> do
  --   mapM_ (|: TyKind) types
  --   rty <- typeCheck variant
  --   rest <- case rty of
  --     VariantTy rest -> return rest
  --     _ -> throw TypeErr $ "Can't add alternatives to a non-variant object "
  --                       <> pprint variant <> " (of type " <> pprint rty <> ")"
  --   return $ VariantTy $ prefixExtLabeledItems types rest
  -- VariantSplit types variant -> do
  --   mapM_ (|: TyKind) types
  --   fullty <- typeCheck variant
  --   full <- case fullty of
  --     VariantTy full -> return full
  --     _ -> throw TypeErr $ "Can't split a non-variant object "
  --                         <> pprint variant <> " (of type " <> pprint fullty
  --                         <> ")"
  --   diff <- labeledRowDifference full (NoExt types)
  --   return $ VariantTy $ NoExt $
  --     Unlabeled [ VariantTy $ NoExt types, VariantTy diff ]
  -- DataConTag x -> do
  --   Con _ _ <- typeCheck x
  --   return TagRepTy
  -- ToEnum t x -> do
  --   t |: TyKind
  --   x |: Word8Ty
  --   (TypeCon (DataDef _ _ dataConDefs) _) <- return t
  --   forM_ dataConDefs \(DataConDef _ binders) ->
  --     assertEq binders Empty "Not an enum"
  --   return t

typeCheckHof :: MonadTyper n m => PrimHof (Atom n) -> m (Type n)
typeCheckHof hof = case hof of
  -- For _ f -> do
  --   Pi (Abs n (WithArrow arr a)) <- typeCheck f
  --   -- TODO: check `n` isn't free in `eff`
  --   declareEffs $ arrowEff arr
  --   return $ Pi $ Abs n (WithArrow TabArrow a)
  -- Tile dim fT fS -> do
  --   FunTy tv eff  tr    <- typeCheck fT
  --   FunTy sv eff' sr    <- typeCheck fS
  --   PrimTC (IndexSlice n l) <- return $ binderType tv
  --   (dv, b, b')         <- zipExtractDim dim tr sr
  --   checkAlphaEq l (binderType dv)
  --   checkAlphaEq n (binderType sv)
  --   when (dv `isin` freeVars b ) $ throw TypeErr "Cannot tile dimensions that other dimensions depend on"
  --   when (sv `isin` freeVars b') $ throw TypeErr "Cannot tile dimensions that other dimensions depend on"
  --   checkAlphaEq b b'
  --   checkAlphaEq eff eff'
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
  --   let threadRange = PrimTC $ ParIndexRange n (Var gtid) (Var nthr)
  --   TabTy threadRange' tileElemTy <- return tiledArrTy
  --   checkAlphaEq threadRange (binderType threadRange')
  --   -- TODO: Check compatibility of baseMonoids and accTys (need to be careful about lifting!)
  --   -- PTileReduce n mapping : (n=>a, (acc1, ..., acc{n}))
  --   return $ PairTy (TabTy (Ignore n) tileElemTy) $ mkConsListTy accTys
  While body -> do
    Pi arr (ConstAbs eff) UnitTy (ConstAbs condTy) <- typeCheck body
    declareEffs eff
    checkAlphaEq (BaseTy $ Scalar Word8Type) condTy
    return UnitTy
  Linearize f -> do
    a :--> b <- typeCheck f
    return $ a :--> PairTy b (a :--@ b)
  Transpose f -> do
    a :--@ b <- typeCheck f
    return $ b :--@ a
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
  -- RunIO f -> do
  --   FunTy b eff resultTy <- typeCheck f
  --   checkAlphaEq (binderType b) UnitTy
  --   extendAllowedEffect IOEffect $ declareEffs eff
  --   return resultTy
  -- CatchException f -> do
  --   FunTy b eff resultTy <- typeCheck f
  --   checkAlphaEq (binderType b) UnitTy
  --   extendAllowedEffect ExceptionEffect $ declareEffs eff
  --   return $ MaybeTy resultTy

checkRWSAction :: MonadTyper n m => RWS -> Atom n -> m (Type n, Type n)
checkRWSAction = undefined
-- checkRWSAction rws f = do
--   BinaryFunTy (Bind regionBinder) refBinder eff resultTy <- typeCheck f
--   regionName:>_ <- return regionBinder
--   let region = Var regionBinder
--   extendAllowedEffect (RWSEffect rws regionName) $ declareEffs eff
--   checkAlphaEq (varAnn regionBinder) TyKind
--   RefTy region' referentTy <- return $ binderType refBinder
--   checkAlphaEq region' region
--   return (resultTy, referentTy)

litType :: LitVal -> BaseType
litType v = case v of
  Int64Lit   _ -> Scalar Int64Type
  Int32Lit   _ -> Scalar Int32Type
  Word8Lit   _ -> Scalar Word8Type
  Float64Lit _ -> Scalar Float64Type
  Float32Lit _ -> Scalar Float32Type
  PtrLit t _   -> PtrType t
  VecLit  l -> Vector sb
    where Scalar sb = litType $ head l

data ArgumentType = SomeFloatArg | SomeIntArg | SomeUIntArg
data ReturnType   = SameReturn | Word8Return

checkOpArgType :: MonadErr m => ArgumentType -> Type n -> m ()
checkOpArgType argTy x =
  case argTy of
    SomeIntArg   -> checkIntBaseType   True x
    -- SomeUIntArg  -> assertEq x Word8Ty ""
    -- SomeFloatArg -> checkFloatBaseType True x

checkBinOp :: MonadErr m => BinOp -> Type n -> Type n -> m (Type n)
checkBinOp = undefined
-- checkBinOp op x y = do
--   checkOpArgType argTy x
--   assertEq x y ""
--   return $ case retTy of
--     SameReturn -> x
--     Word8Return -> BaseTy $ Scalar Word8Type
--   where
--     (argTy, retTy) = case op of
--       IAdd   -> (ia, sr);  ISub   -> (ia, sr)
--       IMul   -> (ia, sr);  IDiv   -> (ia, sr)
--       IRem   -> (ia, sr);
--       ICmp _ -> (ia, br)
--       FAdd   -> (fa, sr);  FSub   -> (fa, sr)
--       FMul   -> (fa, sr);  FDiv   -> (fa, sr);
--       FPow   -> (fa, sr)
--       FCmp _ -> (fa, br)
--       BAnd   -> (ia, sr);  BOr    -> (ia, sr)
--       BShL   -> (ia, sr);  BShR   -> (ia, sr)
--       where
--         ia = SomeIntArg; fa = SomeFloatArg
--         br = Word8Return; sr = SameReturn

checkUnOp :: MonadErr m => UnOp -> Type n -> m (Type n)
checkUnOp op x = do
  checkOpArgType argTy x
  return $ case retTy of
    SameReturn -> x
    Word8Return -> BaseTy $ Scalar Word8Type
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

checkDataLike :: MonadErr m => String -> Type n -> m ()
checkDataLike = undefined
-- checkDataLike msg ty = case ty of
--   Var _ -> error "Not implemented"
--   -- TabTy _ b -> recur b
--   RecordTy  (NoExt items) -> mapM_ recur items
--   VariantTy (NoExt items) -> mapM_ recur items
--   -- TypeCon def params ->
--   --   mapM_ checkDataLikeDataCon $ applyDataDefParams def params
--   PrimTC con -> case con of
--     BaseType _       -> return ()
--     PairType a b     -> recur a >> recur b
--     UnitType         -> return ()
--     IntRange _ _     -> return ()
--     IndexRange _ _ _ -> return ()
--     IndexSlice _ _   -> return ()
--     _ -> throw TypeErr $ pprint ty ++ msg
--   _   -> throw TypeErr $ pprint ty ++ msg
--   where recur x = checkDataLike msg x

-- checkDataLikeDataCon :: MonadErr m => DataConDef n -> m ()
-- checkDataLikeDataCon = undefined
-- checkDataLikeDataCon (DataConDef _ bs) =
--   mapM_ (checkDataLike "data con binder" . binderType) $ fromNest bs

checkData :: MonadErr m => Type n -> m ()
checkData = checkDataLike " is not serializable"

--TODO: Make this work even if the type has type variables!
isData :: Type n -> Bool
isData ty = case checkData ty of
  Left  _ -> False
  Right _ -> True

projectLength :: Type n -> Int
projectLength = undefined
-- projectLength ty = case ty of
--   -- TypeCon def params ->
--   --   let [DataConDef _ bs] = applyDataDefParams def params
--   --   in length $ fromNest bs
--   RecordTy (NoExt types) -> length types
--   PairTy _ _ -> 2
--   _ -> error $ "Projecting a type that doesn't support projecting: " ++ pprint ty


-- === Type-level reduction using variables in scope. ===

-- Note: These are simple reductions that are performed when normalizing a
-- value to use it as a type annotation. If they succeed, these functions should
-- return atoms that can be compared for equality to check whether the types
-- are equivalent. If they fail (return Nothing), this means we cannot use
-- the value as a type in the IR.

-- typeReduceBlock :: Bindings n -> Block n -> Maybe (Atom n)
-- typeReduceBlock = undefined
-- typeReduceBlock scope (Block decls result) = do
--   let localScope = foldMap boundVars $ fromNest decls
--   ans <- typeReduceExpr (scope <> localScope) result
--   [] <- return $ toList $ localScope `envIntersect` freeVars ans
--   return ans

-- XXX: This should handle all terms of type Type. Otherwise type equality checking
--      will get broken.
-- typeReduceAtom :: Bindings n -> Atom n -> Atom n
-- typeReduceAtom = undefined
-- typeReduceAtom scope x = case x of
--   Var (Name InferenceName _ _ :> _) -> x
--   Var v -> case snd (scope ! v) of
--     -- TODO: worry about effects!
--     LetBound PlainLet expr -> fromMaybe x $ typeReduceExpr scope expr
--     _ -> x
--   PrimTC con -> PrimTC $ fmap (typeReduceAtom scope) con
--   Pi (Abs b (arr, ty)) -> Pi $ Abs b (arr, typeReduceAtom (scope <> (fmap (,PiBound) $ binderAsEnv b)) ty)
--   TypeCon def params -> TypeCon (reduceDataDef def) (fmap rec params)
--   RecordTy (Ext tys ext) -> RecordTy $ Ext (fmap rec tys) ext
--   VariantTy (Ext tys ext) -> VariantTy $ Ext (fmap rec tys) ext
--   ACase _ _ _ -> error "Not implemented"
--   _ -> x
--   where
--     rec = typeReduceAtom scope
--     reduceNest s n = case n of
--       Empty       -> Empty
--       -- Technically this should use a more concrete type than UnknownBinder, but anything else
--       -- than LetBound is indistinguishable for this reduction anyway.
--       Nest b rest -> Nest b' $ reduceNest (s <> (fmap (,UnknownBinder) $ binderAsEnv b)) rest
--         where b' = fmap (typeReduceAtom s) b
--     reduceDataDef (DataDef n bs cons) =
--       DataDef n (reduceNest scope bs)
--             (fmap (reduceDataConDef (scope <> (foldMap (fmap (,UnknownBinder) . binderAsEnv) bs))) cons)
--     reduceDataConDef s (DataConDef n bs) = DataConDef n $ reduceNest s bs

-- typeReduceExpr :: Scope n -> Expr n -> Maybe (Atom n)
-- typeReduceExpr = undefined
-- typeReduceExpr scope expr = case expr of
--   Atom val -> return $ typeReduceAtom scope val
--   App f x -> do
--     let f' = typeReduceAtom scope f
--     let x' = typeReduceAtom scope x
--     -- TODO: Worry about variable capture. Should really carry a substitution.
--     case f' of
--       Lam (Abs b (WithArrow arr block)) | arr == PureArrow || arr == ImplicitArrow ->
--         typeReduceBlock scope $ subst (b@>x', scope) block
--       TypeCon con xs -> Just $ TypeCon con $ xs ++ [x']
--       _ -> Nothing
--   _ -> Nothing
