-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module Interpreter (
  evalBlock, evalDecls, evalExpr, evalAtom,
  liftInterpM, InterpM, Interp, unsafeLiftInterpMCatch,
  indices, indicesLimit, matchUPat,
  applyIntBinOp, applyIntCmpOp,
  applyFloatBinOp, applyFloatUnOp, repValToCoreAtom) where

import Control.Monad
import Control.Monad.IO.Class
import qualified Data.List.NonEmpty as NE
import Data.Maybe (fromJust)
import Data.List (elemIndex)
import Data.Foldable (toList)
import Data.Functor
import Data.Word
import Foreign.Ptr
import Foreign.Marshal.Alloc
import System.IO.Unsafe

import Builder
import CUDA
import CheapReduction (cheapNormalize)
import Core
import Err
import IRVariants
import Imp
import LabeledItems
import Name
import PPrint ()
import QueryType
import Runtime
import Types.Core
import Types.Imp
import Types.Primitives
import Types.Source
import Util ((...), iota, onSndM, restructure, Tree (..), zipTrees, forMZipped)

newtype InterpM (i::S) (o::S) (a:: *) =
  InterpM { runInterpM' :: SubstReaderT (AtomSubstVal CoreIR) (EnvReaderT IO) i o a }
  deriving ( Functor, Applicative, Monad
           , MonadIO, ScopeReader, EnvReader, MonadFail, Fallible
           , SubstReader (AtomSubstVal CoreIR))

class ( SubstReader (AtomSubstVal CoreIR) m, EnvReader2 m
      , Monad2 m, MonadIO2 m, Fallible2 m)
      => Interp m

instance Interp (InterpM)

liftInterpM :: (EnvReader m, MonadIO1 m) => InterpM n n a -> m n a
liftInterpM cont = do
  resultIO <- liftEnvReaderT $ runSubstReaderT idSubst $ runInterpM' cont
  liftIO resultIO
{-# INLINE liftInterpM #-}

-- Variant of liftInterpM meant for internal interpretation.
-- Discharges the IO unsafely, and catches errors.
-- TODO Can we implement a FakeIOT monad transformer that provides
-- MonadIO but with liftIO = fail ?  Then we could call the interpreter
-- while guaranteeing that no real IO actually happens.
unsafeLiftInterpMCatch :: (EnvReader m) => InterpM n n a -> m n (Except a)
unsafeLiftInterpMCatch cont = do
  env <- unsafeGetEnv
  Distinct <- getDistinct
  return $ unsafePerformIO $ catchIOExcept $ runInterpM env cont
{-# INLINE unsafeLiftInterpMCatch #-}

evalBlock :: Interp m => CBlock i -> m i o (CAtom o)
evalBlock (Block _ decls result) = evalDecls decls $ evalAtom result

evalDecls :: Interp m => Nest CDecl i i' -> m i' o a -> m i o a
evalDecls Empty cont = cont
evalDecls (Nest (Let b (DeclBinding _ _ rhs)) rest) cont = do
  result <- evalExpr rhs
  extendSubst (b @> SubstVal result) $ evalDecls rest cont
{-# SCC evalDecls #-}

-- XXX: this doesn't go under lambda or pi binders
traverseSurfaceAtomNames
  :: (SubstReader (AtomSubstVal CoreIR) m, EnvReader2 m)
  => CAtom i
  -> (AtomName CoreIR i -> m i o (CAtom o))
  -> m i o (CAtom o)
traverseSurfaceAtomNames atom doWithName = case atom of
  Var v -> doWithName v
  Lam _ _ _ -> substM atom
  TabLam _ -> substM atom
  Pi  _    -> substM atom
  TabPi  _ -> substM atom
  DepPair l r ty -> DepPair <$> rec l <*> rec r <*> substM ty
  DepPairTy _ -> substM atom
  Con con -> Con <$> mapM rec con
  TC  tc  -> TC  <$> mapM rec tc
  DictCon _ -> substM atom
  DictTy  _ -> substM atom
  Eff _ -> substM atom
  PtrVar _ -> substM atom
  TypeCon sn defName (DataDefParams params) -> do
    defName' <- substM defName
    TypeCon sn defName' <$> (DataDefParams <$> mapM (onSndM rec) params)
  RecordTy _ -> substM atom
  VariantTy _      -> substM atom
  LabeledRow _     -> substM atom
  ACase scrut alts resultTy ->
    ACase <$> rec scrut <*> mapM substM alts <*> rec resultTy
  ProjectElt idxs v -> getProjection (toList idxs) <$> rec (Var v)
  where
    rec x = traverseSurfaceAtomNames x doWithName

evalAtom :: forall i o m. Interp m => CAtom i -> m i o (CAtom o)
evalAtom atom = traverseSurfaceAtomNames atom \v -> do
  env <- getSubst
  case env ! v of
    SubstVal x -> return x
    Rename v' -> do
      lookupAtomName v' >>= \case
        LetBound (DeclBinding _ _ (Atom x)) -> dropSubst $ evalAtom x
        TopFunBound _ _ -> return $ Var v'
        TopDataBound repVal ->
          unsafeCoerceIRE <$> repValToCoreAtom repVal
        bindingInfo -> error $ "shouldn't have irreducible atom names left. Got " ++ pprint bindingInfo
{-# SCC evalAtom #-}

evalExpr :: Interp m => Expr CoreIR i -> m i o (CAtom o)
evalExpr expr = case expr of
  App f xs -> do
    f' <- evalAtom f
    xs' <- mapM evalAtom xs
    case fromNaryLam (length xs) f' of
      Just (bsCount, LamExpr bs body) -> do
        let (xsPref, xsRest) = NE.splitAt bsCount xs'
        ans <- dropSubst $ extendSubst (bs@@>(SubstVal <$> xsPref)) $ evalBlock body
        case NE.nonEmpty xsRest of
          Nothing    -> return ans
          Just rest' -> dropSubst $ evalExpr $ App ans rest'
      Nothing -> error $ "Failed to reduce application!" ++ pprint expr
  -- TODO: de-dup with App
  TabApp f xs -> do
    f' <- evalAtom f
    xs' <- mapM evalAtom xs
    case fromNaryTabLam (length xs) f' of
      Just (bsCount, LamExpr bs body) -> do
        let (xsPref, xsRest) = NE.splitAt bsCount xs'
        ans <- dropSubst $ extendSubst (bs@@>(SubstVal <$> xsPref)) $ evalBlock body
        case NE.nonEmpty xsRest of
          Nothing    -> return ans
          Just rest' -> dropSubst $ evalExpr $ TabApp ans rest'
      Nothing -> error "Failed to reduce application!"
  Atom atom -> evalAtom atom
  PrimOp op     -> evalOp op
  Case e alts _ _ -> do
    e' <- evalAtom e
    case trySelectBranch e' of
      Nothing -> error "branch should be chosen at this point"
      Just (con, arg) -> do
        Abs b body <- return $ alts !! con
        extendSubst (b @> SubstVal arg) $ evalBlock body
  Hof hof -> case hof of
    RunIO body -> evalBlock body
    _ -> error $ "Not implemented: " ++ pprint expr
  RecordVariantOp rvo -> case rvo of
    VariantMake ty' label i v' -> do
      v <- evalAtom v'
      ty@(VariantTy (NoExt tys)) <- evalAtom ty'
      let ix = fromJust $ elemIndex (label, i) $ toList $ reflectLabels tys
      return $ Con $ Newtype ty $ SumVal (toList tys) ix v
    _ -> notImplemented
  ProjMethod dict' i -> do
    dict <- evalAtom dict'
    evalProjectDictMethod dict i
  _ -> notImplemented
  where notImplemented = error $ "Not implemented: " ++ pprint expr
{-# SCC evalExpr #-}

evalOp :: Interp m => PrimOp (CAtom i) -> m i o (CAtom o)
evalOp expr = mapM evalAtom expr >>= \case
  BinOp op x y -> return $ case op of
    IAdd -> applyIntBinOp   (+) x y
    ISub -> applyIntBinOp   (-) x y
    IMul -> applyIntBinOp   (*) x y
    IDiv -> applyIntBinOp   div x y
    IRem -> applyIntBinOp   rem x y
    FAdd -> applyFloatBinOp (+) x y
    FSub -> applyFloatBinOp (-) x y
    FMul -> applyFloatBinOp (*) x y
    FDiv -> applyFloatBinOp (/) x y
    ICmp cmp -> case cmp of
      Less         -> applyIntCmpOp (<)  x y
      Greater      -> applyIntCmpOp (>)  x y
      Equal        -> applyIntCmpOp (==) x y
      LessEqual    -> applyIntCmpOp (<=) x y
      GreaterEqual -> applyIntCmpOp (>=) x y
    _ -> error $ "Not implemented: " ++ pprint expr
  UnOp op x -> return $ case op of
    FNeg -> applyFloatUnOp (0-) x
    _ -> error $ "Not implemented: " ++ pprint expr
  MemOp memOp -> case memOp of
    PtrOffset p (IdxRepVal 0) -> return p
    PtrOffset ptrAtom (IdxRepVal i) -> do
      ((a, t), p) <- inlinePtrLit ptrAtom
      return $ Con $ Lit $ PtrLit (a, t) (PtrLitVal $ p `plusPtr` (sizeOf t * fromIntegral i))
    PtrLoad ptrAtom -> do
      ((a, t), p) <- inlinePtrLit ptrAtom
      case a of
        CPU -> Con . Lit <$> liftIO (loadLitVal p t)
        GPU ->  do
          liftIO $ allocaBytes (sizeOf t) $ \hostPtr -> do
            loadCUDAArray hostPtr p (sizeOf t)
            Con . Lit <$> loadLitVal hostPtr t
    _ ->  notImplemented
  MiscOp miscOp -> case miscOp of
    CastOp destTy x -> do
      sourceTy <- getType x
      let failedCast = error $ "Cast not implemented: " ++ pprint sourceTy ++
                               " -> " ++ pprint destTy
      case (sourceTy, destTy) of
        (BaseTy (Scalar sb), BaseTy (Scalar db)) -> case (sb, db) of
          (Int64Type, Int32Type) -> do
            let Con (Lit (Int64Lit v)) = x
            return $ Con $ Lit $ Int32Lit $ fromIntegral v
          (Word64Type, Word32Type) -> do
            let Con (Lit (Word64Lit v)) = x
            return $ Con $ Lit $ Word32Lit $ fromIntegral v
          _ -> failedCast
        _ -> failedCast
    Select cond t f -> case cond of
      Con (Lit (Word8Lit 0)) -> return f
      Con (Lit (Word8Lit 1)) -> return t
      _ -> error $ "Invalid select condition: " ++ pprint cond
    ToEnum ty@(TypeCon _ defName _) i -> do
        DataDef _ _ cons <- lookupDataDef defName
        return $ Con $ Newtype ty $ Con $
          SumAsProd (cons <&> const UnitTy) i (cons <&> const UnitVal)
    _ ->  notImplemented
  _ -> notImplemented
  where notImplemented = error $ "Not implemented: " ++ pprint expr

evalProjectDictMethod :: Interp m => CAtom o -> Int -> m i o (CAtom o)
evalProjectDictMethod d i = cheapNormalize d >>= \case
  DictCon (InstanceDict instanceName args) -> dropSubst do
    args' <- mapM evalAtom args
    InstanceDef _ bs _ body <- lookupInstanceDef instanceName
    let InstanceBody _ methods = body
    let method = methods !! i
    extendSubst (bs@@>(SubstVal <$> args')) $
      evalBlock $ unsafeCoerceIRE method
  Con (ExplicitDict _ method) -> do
    case i of
      0 -> return method
      _ -> error "ExplicitDict only supports single-method classes"
  DictCon (IxFin n) -> projectIxFinMethod (toEnum i) n
  Con (Newtype (DictTy (DictType _ clsName _)) (ProdVal mts)) -> do
    ClassDef _ _ _ _ mTys <- lookupClassDef clsName
    let (m, MethodType _ mTy) = (mts !! i, mTys !! i)
    case mTy of
      Pi _ -> return m
      _    -> dropSubst $ evalExpr $ App (head mts) (UnitVal NE.:| [])
  _ -> error $ "Not a simplified dict: " ++ pprint d

matchUPat :: Interp m => UPat i i' -> CAtom o -> m i o (SubstFrag (AtomSubstVal CoreIR) i i' o)
matchUPat (WithSrcB _ pat) x = do
  x' <- dropSubst $ evalAtom x
  case (pat, x') of
    (UPatBinder b, _) -> return $ b @> SubstVal x'
    (UPatCon _ ps, Con (Newtype (TypeCon _ dataDefName _) _)) -> do
      DataDef _ _ cons <- lookupDataDef dataDefName
      case cons of
        [DataConDef _ _ idxs] -> matchUPats ps [getProjection ix x' | ix <- idxs]
        _ -> error "Expected a single ADt constructor"
    (UPatPair (PairB p1 p2), PairVal x1 x2) -> do
      matchUPat p1 x1 >>= (`followedByFrag` matchUPat p2 x2)
    (UPatDepPair (PairB p1 p2), PairVal x1 x2) -> do
      matchUPat p1 x1 >>= (`followedByFrag` matchUPat p2 x2)
    (UPatUnit UnitB, UnitVal) -> return emptyInFrag
    (UPatRecord pats, Record initTys initXs) -> go initTys (restructure initXs initTys) pats
      where
        go :: Interp m
           => LabeledItems (CType o) -> LabeledItems (CAtom o)
           -> UFieldRowPat i i' -> m i o (SubstFrag (AtomSubstVal CoreIR) i i' o)
        go tys xs = \case
          UEmptyRowPat    -> return emptyInFrag
          URemFieldsPat b -> return $ b @> SubstVal (Record tys $ toList xs)
          UDynFieldsPat ~(InternalName _ (UAtomVar v)) b rest ->
            evalAtom (Var v) >>= \case
              LabeledRow f | [StaticFields fields] <- fromFieldRowElems f -> do
                let (items, remItems) = splitLabeledItems fields xs
                let (itemTys, remTys) = splitLabeledItems fields tys
                frag <- matchUPat b (Record itemTys $ toList items)
                frag `followedByFrag` go remTys remItems rest
              _ -> error "Unevaluated fields?"
          UDynFieldPat ~(InternalName _ (UAtomVar v)) b rest ->
            evalAtom (Var v) >>= \case
              Con (LabelCon l) -> go tys xs $ UStaticFieldPat l b rest
              _ -> error "Unevaluated label?"
          UStaticFieldPat l b rest -> case popLabeledItems l xs of
            Just (val, xsTail) -> do
              let Just (_, tysTail) = popLabeledItems l tys
              headFrag <- matchUPat b val
              headFrag `followedByFrag` go tysTail xsTail rest
            Nothing -> error "Field missing in record"
    (UPatVariant _ _ _  , _) -> error "can't have top-level may-fail pattern"
    (UPatVariantLift _ _, _) -> error "can't have top-level may-fail pattern"
    (UPatTable bs, tab) -> do
      getType tab >>= \case
        TabTy b _ -> do
          xs <- dropSubst do
            idxs <- indices (binderAnn b)
            forM idxs \i -> evalExpr $ TabApp tab (i NE.:| [])
          matchUPats bs xs
        _ -> error $ "not a table: " ++ pprint tab
    _ -> error "bad pattern match"
  where followedByFrag f m = extendSubst f $ fmap (f <.>) m

matchUPats :: Interp m => Nest UPat i i' -> [CAtom o] -> m i o (SubstFrag (AtomSubstVal CoreIR) i i' o)
matchUPats Empty [] = return emptyInFrag
matchUPats (Nest b bs) (x:xs) = do
  s <- matchUPat b x
  extendSubst s do
    ss <- matchUPats bs xs
    return $ s <.> ss
matchUPats _ _ = error "mismatched lengths"

-- XXX: It is a bit shady to unsafePerformIO here since this runs during typechecking.
-- We could have a partial version of the interpreter that fails when any IO is to happen.
liftBuilderInterp ::
  (forall l. (Emits l, DExt n l) => BuilderM CoreIR l (CAtom l))
  -> InterpM n n (CAtom n)
liftBuilderInterp cont = do
  Abs decls result <- liftBuilder $ buildScoped cont
  evalDecls decls $ evalAtom result
{-# SCC liftBuilderInterp #-}

runInterpM :: Distinct n => Env n -> InterpM n n a -> IO a
runInterpM bindings cont =
  runEnvReaderT bindings $ runSubstReaderT idSubst $ runInterpM' cont
{-# SCC runInterpM #-}

unsafeLiftInterpM :: (EnvReader m) => InterpM n n a -> m n a
unsafeLiftInterpM cont = do
  env <- unsafeGetEnv
  Distinct <- getDistinct
  return $ unsafePerformIO $ runInterpM env cont
{-# INLINE unsafeLiftInterpM #-}

indices :: EnvReader m => IxType CoreIR n -> m n [CAtom n]
indices ixTy = unsafeLiftInterpM $ do
  ~(IdxRepVal size) <- interpIndexSetSize ixTy
  forM (iota size) \i -> interpUnsafeFromOrdinal ixTy $ IdxRepVal i
{-# SCC indices #-}

interpIndexSetSize :: IxType CoreIR n -> InterpM n n (CAtom n)
interpIndexSetSize ixTy = liftBuilderInterp $ indexSetSize $ sink ixTy

interpUnsafeFromOrdinal :: IxType CoreIR n -> CAtom n -> InterpM n n (CAtom n)
interpUnsafeFromOrdinal ixTy i = liftBuilderInterp $ unsafeFromOrdinal (sink ixTy) (sink i)

-- A variant of `indices` that accepts an expected number of them and
-- only tries to construct the set if the expected number matches the
-- given index set's size.
indicesLimit :: EnvReader m => Int -> IxType r n -> m n (Either Word32 [Atom r n])
indicesLimit sizeReq ixTy' = unsafeLiftInterpM $ do
  let ixTy = unsafeCoerceIRE ixTy'
  ~(IdxRepVal size) <- interpIndexSetSize ixTy
  if size == fromIntegral sizeReq then
    Right <$> forM [0..size-1] \i -> unsafeCoerceIRE <$> interpUnsafeFromOrdinal ixTy (IdxRepVal i)
  else
    return $ Left size
{-# SCC indicesLimit #-}

inlinePtrLit :: (Fallible1 m, EnvReader m) => CAtom n -> m n (PtrType, Ptr ())
inlinePtrLit (PtrVar v) = do
  ~(PtrBinding t (PtrLitVal p)) <- lookupEnv v
  return (t, p)
inlinePtrLit (Con (Lit (PtrLit t (PtrLitVal p)))) = return (t, p)
inlinePtrLit _ = fail "not a pointer literal"

-- === Helpers for function evaluation over fixed-width types ===

applyIntBinOp' :: (forall a. (Eq a, Ord a, Num a, Integral a)
               => (a -> Atom r n) -> a -> a -> Atom r n) -> Atom r n -> Atom r n -> Atom r n
applyIntBinOp' f x y = case (x, y) of
  (Con (Lit (Int64Lit xv)), Con (Lit (Int64Lit yv))) -> f (Con . Lit . Int64Lit) xv yv
  (Con (Lit (Int32Lit xv)), Con (Lit (Int32Lit yv))) -> f (Con . Lit . Int32Lit) xv yv
  (Con (Lit (Word8Lit xv)), Con (Lit (Word8Lit yv))) -> f (Con . Lit . Word8Lit) xv yv
  (Con (Lit (Word32Lit xv)), Con (Lit (Word32Lit yv))) -> f (Con . Lit . Word32Lit) xv yv
  (Con (Lit (Word64Lit xv)), Con (Lit (Word64Lit yv))) -> f (Con . Lit . Word64Lit) xv yv
  _ -> error "Expected integer atoms"

applyIntBinOp :: (forall a. (Num a, Integral a) => a -> a -> a) -> Atom r n -> Atom r n -> Atom r n
applyIntBinOp f x y = applyIntBinOp' (\w -> w ... f) x y

applyIntCmpOp :: (forall a. (Eq a, Ord a) => a -> a -> Bool) -> Atom r n -> Atom r n -> Atom r n
applyIntCmpOp f x y = applyIntBinOp' (\_ -> (Con . Lit . Word8Lit . fromIntegral . fromEnum) ... f) x y

applyFloatBinOp :: (forall a. (Num a, Fractional a) => a -> a -> a) -> Atom r n -> Atom r n -> Atom r n
applyFloatBinOp f x y = case (x, y) of
  (Con (Lit (Float64Lit xv)), Con (Lit (Float64Lit yv))) -> Con $ Lit $ Float64Lit $ f xv yv
  (Con (Lit (Float32Lit xv)), Con (Lit (Float32Lit yv))) -> Con $ Lit $ Float32Lit $ f xv yv
  _ -> error "Expected float atoms"

applyFloatUnOp :: (forall a. (Num a, Fractional a) => a -> a) -> Atom r n -> Atom r n
applyFloatUnOp f x = applyFloatBinOp (\_ -> f) undefined x

-- === Working with RepVals ===

-- this whole section should disappear when we implement `Show` at the dex level.

data CoreRepVal n = CoreRepVal (Type CoreIR n) (Tree (Atom CoreIR n))

instance SinkableE CoreRepVal where
  sinkingProofE = undefined

litIExprToAtom ::  EnvReader m => IExpr n -> m n (Atom CoreIR n)
litIExprToAtom = \case
  IVar _ _ -> error "shouldn't have IVar in a literal IExpr"
  IPtrVar v _ -> return $ PtrVar v
  ILit x -> return $ Con $ Lit x

repValToCoreAtom :: (EnvReader m, Fallible1 m) => RepVal SimpToImpIR n -> m n (Atom CoreIR n)
repValToCoreAtom (RepVal topTy topTree) = do
  topTreeAtoms <- mapM litIExprToAtom topTree
  liftBuilder do
    Abs decls result <- buildScoped $ go True $
      CoreRepVal (sink $ unsafeCoerceIRE topTy) (fmap sink topTreeAtoms)
    case decls of
      Empty -> return result
      _ -> error $ "shouldn't emit decls at the top level"
 where
  -- We don't want to actually emit except under a table lambda.
  -- The `topLevel` flag tells us whether that condition holds.
  -- Ideally we'd pair it with `Emits`, and have a type-level
  -- `Maybe (Emits n)`.
  go :: Emits n
     => Bool -> CoreRepVal n -> BuilderM CoreIR n (Atom CoreIR n)
  go topLevel repVal@(CoreRepVal ty tree) = case (ty, tree) of
    (BaseTy _, Leaf x) -> return x
    (TabPi (TabPiType (_:>iTy) _), _) -> do
      buildTabLam noHint iTy \i -> do
        bodyRepVal <- indexCoreRepVal (sink repVal) (Var i)
        go False bodyRepVal
    (ProdTy ts, Branch xs) ->
      ProdVal <$> forMZipped ts xs  \t x -> rec $ CoreRepVal t x
    (SumTy  ts, Branch (tag:xs)) -> do
      tag' <- rec $ CoreRepVal TagRepTy tag
      if topLevel
        then do
          xs'  <- zipWithM (\t x -> rec $ CoreRepVal t x) ts xs
          return $ Con $ SumAsProd ts tag' xs'
        else do
          -- If we're under a table lambda, then we can't unconditionally recur
          -- into each branch because we might end up loading sizes from
          -- uninitialized memory and then generating `for` loops using them.
          let enumVal = Con $ SumAsProd (map (const UnitTy) ts) tag' (map (const UnitVal) ts)
          buildCase enumVal (SumTy ts) \i _ -> do
            xs' <- mapM (mapM sinkM) xs
            ts' <- mapM sinkM ts
            Con <$> SumCon ts' i <$> go topLevel (CoreRepVal (ts'!!i) (xs'!!i))
    (DepPairTy t, Branch [left, right]) -> do
      leftVal  <- rec $ CoreRepVal (depPairLeftTy t) left
      rightTy <- instantiateDepPairTy t leftVal
      rightVal <- rec $ CoreRepVal (rightTy) right
      return $ DepPair leftVal rightVal t
    (TypeCon _ defName params, _) -> do
      def <- lookupDataDef defName
      dcs <- instantiateDataDef def params
      goNewtype $ dataDefRep dcs
    (StaticRecordTy ts   , _) -> goNewtype (ProdTy $ toList ts)
    (VariantTy (NoExt ts), _) -> goNewtype (SumTy  $ toList ts)
    (NatTy, _)      -> goNewtype IdxRepTy
    (TC (Fin _), _) -> goNewtype NatTy
    _ -> error $ "unexpected type/tree pair: " ++ pprint ty ++ "\n" ++ show tree
    where
      goNewtype t = (Con . Newtype ty) <$> go topLevel (CoreRepVal t tree)
      rec = go topLevel

-- CoreIR version of `indexRepVal` (we could try to de-dup by thinking harder
-- about what they have in common, but wew plan to delete this soon anyway).
indexCoreRepVal :: Emits n => CoreRepVal n -> Atom CoreIR n -> BuilderM CoreIR n (CoreRepVal n)
indexCoreRepVal (CoreRepVal tabTy@(TabPi (TabPiType (b:>ixTy) eltTy)) vals) i = do
  eltTy' <- applySubst (b@>SubstVal i) eltTy
  ord <- ordinal ixTy i
  leafTys <- typeToTree (unsafeCoerceIRE tabTy)
  vals' <- forM (zipTrees leafTys vals) \(leafTy, ptr) -> do
    BufferPtr (BufferType (EmptyAbs ixStruct) _) <- return $ getIExprInterpretation leafTy
    ixStruct' <- return $ EmptyAbs (fmapNest (\(ib:>ann) -> ib:> unsafeCoerceIRE ann) ixStruct)
    offset <- computeOffsetCore ixStruct' ord
    ptr' <- ptrOffset ptr offset
    case ixStruct of
      Nest _ Empty -> unsafePtrLoad ptr'
      _            -> return ptr'
  return $ CoreRepVal eltTy' vals'
indexCoreRepVal _ _ = error "expected table type"

computeOffsetCore :: Emits n => IndexStructure CoreIR n -> CAtom n -> BuilderM CoreIR n (CAtom n)
computeOffsetCore (Abs idxNest UnitE) idx = do
  idxNest' <- return $ fmapNest (\(b:>t) -> b:>unsafeCoerceIRE t) idxNest
  idx'  <- return $ unsafeCoerceIRE idx
  block <- liftBuilder $ buildBlock $
    computeOffset (sink (EmptyAbs idxNest')) (sink idx')
  block' <- return $ unsafeCoerceIRE block
  emitBlock block'
