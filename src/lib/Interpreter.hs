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
  applyFloatBinOp, applyFloatUnOp)  where

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
import CheapReduction
import Core
import Err
import IRVariants
import LabeledItems
import Name
import Subst
import PPrint ()
import QueryType
import Runtime
import Types.Core
import Types.Primitives
import Types.Source
import Util ((...), iota, restructure)

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
  NewtypeCon _ _ -> substM atom
  NewtypeTyCon _ -> substM atom
  ACase scrut alts resultTy ->
    ACase <$> rec scrut <*> mapM substM alts <*> rec resultTy
  ProjectElt i x -> normalizeProj i =<< rec x
  SimpInCore _ _ -> error "shouldn't be interpreting SimpInCore"
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
      VariantTy (NoExt tys) <- evalAtom ty'
      let ix = fromJust $ elemIndex (label, i) $ toList $ reflectLabels tys
      return $ NewtypeCon (VariantCon (void tys)) (SumVal (toList tys) ix v)
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
    ToEnum (TypeCon _ defName params) i -> do
      DataDef _ _ cons <- lookupDataDef defName
      return $ NewtypeCon (UserADTData defName params) $
        Con $ SumAsProd (cons <&> const UnitTy) i (cons <&> const UnitVal)
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
  DictCon (IxFin n) -> projectIxFinMethod (toEnum i) n
  _ -> error $ "Not a simplified dict: " ++ pprint d

matchUPat :: Interp m => UPat i i' -> CAtom o -> m i o (SubstFrag (AtomSubstVal CoreIR) i i' o)
matchUPat (WithSrcB _ pat) x = do
  x' <- dropSubst $ evalAtom x
  case (pat, x') of
    (UPatBinder b, _) -> return $ b @> SubstVal x'
    (UPatCon _ ps, NewtypeCon (UserADTData dataDefName _) _) -> do
      DataDef _ _ cons <- lookupDataDef dataDefName
      case cons of
        [DataConDef _ _ idxs] -> do
          xs <- forM idxs \ix -> normalizeNaryProj ix x'
          matchUPats ps xs
        _ -> error "Expected a single ADt constructor"
    (UPatPair (PairB p1 p2), PairVal x1 x2) -> do
      matchUPat p1 x1 >>= (`followedByFrag` matchUPat p2 x2)
    (UPatDepPair (PairB p1 p2), PairVal x1 x2) -> do
      matchUPat p1 x1 >>= (`followedByFrag` matchUPat p2 x2)
    (UPatUnit UnitB, UnitVal) -> return emptyInFrag
    (UPatRecord pats, Record labels initXs) -> do
      tys <- mapM getType initXs
      go (restructure tys labels) (restructure initXs labels) pats
      where
        go :: Interp m
           => LabeledItems (CType o) -> LabeledItems (CAtom o)
           -> UFieldRowPat i i' -> m i o (SubstFrag (AtomSubstVal CoreIR) i i' o)
        go tys xs = \case
          UEmptyRowPat    -> return emptyInFrag
          URemFieldsPat b -> return $ b @> SubstVal (Record (void tys) $ toList xs)
          UDynFieldsPat ~(InternalName _ (UAtomVar v)) b rest ->
            evalAtom (Var v) >>= \case
              LabeledRow f | [StaticFields fields] <- fromFieldRowElems f -> do
                let (items, remItems) = splitLabeledItems fields xs
                let (itemTys, remTys) = splitLabeledItems fields tys
                frag <- matchUPat b (Record (void itemTys) $ toList items)
                frag `followedByFrag` go remTys remItems rest
              _ -> error "Unevaluated fields?"
          UDynFieldPat ~(InternalName _ (UAtomVar v)) b rest ->
            evalAtom (Var v) >>= \case
              NewtypeTyCon (LabelCon l) -> go tys xs $ UStaticFieldPat l b rest
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
  size <- interpIndexSetSize ixTy >>= \case
    IdxRepVal size -> return size
    NatVal size -> return size
    n -> error $ "Expected a size literal. Got: " ++ pprint n ++ "   " ++ show n
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
  size <- interpIndexSetSize ixTy >>= \case
     IdxRepVal size -> return size
     NatVal size -> return size
     n -> error $ "Expected a size literal. Got: " ++ pprint n ++ "   " ++ show n
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
