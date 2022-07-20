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
  applyFloatBinOp, applyFloatUnOp) where

import Control.Monad
import Control.Monad.IO.Class
import qualified Data.List.NonEmpty as NE
import Data.Foldable (toList)
import Data.Word
import Foreign.Ptr
import Foreign.Marshal.Alloc
import System.IO.Unsafe

import CUDA
import LLVMExec
import Err
import LabeledItems

import Name
import Syntax
import QueryType
import PPrint ()
import Util ((...), iota)
import Builder
import CheapReduction (cheapNormalize)

newtype InterpM (i::S) (o::S) (a:: *) =
  InterpM { runInterpM' :: SubstReaderT AtomSubstVal (EnvReaderT IO) i o a }
  deriving ( Functor, Applicative, Monad
           , MonadIO, ScopeReader, EnvReader, MonadFail, Fallible
           , SubstReader AtomSubstVal)

class ( SubstReader AtomSubstVal m, EnvReader2 m
      , Monad2 m, MonadIO2 m)
      => Interp m

instance Interp InterpM

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

evalBlock :: Interp m => Block i -> m i o (Atom o)
evalBlock (Block _ decls result) = evalDecls decls $ evalAtom result

evalDecls :: Interp m => Nest Decl i i' -> m i' o a -> m i o a
evalDecls Empty cont = cont
evalDecls (Nest (Let b (DeclBinding _ _ rhs)) rest) cont = do
  result <- evalExpr rhs
  extendSubst (b @> SubstVal result) $ evalDecls rest cont
{-# SCC evalDecls #-}

-- XXX: this doesn't go under lambda or pi binders
traverseSurfaceAtomNames
  :: (SubstReader AtomSubstVal m, EnvReader2 m)
  => Atom i
  -> (AtomName i -> m i o (Atom o))
  -> m i o (Atom o)
traverseSurfaceAtomNames atom doWithName = case atom of
  Var v -> doWithName v
  Lam _    -> substM atom
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
  TypeCon sn defName (DataDefParams params dicts) -> do
    defName' <- substM defName
    TypeCon sn defName' <$> (DataDefParams <$> mapM rec params <*> mapM rec dicts)
  DataCon printName defName (DataDefParams params dicts) con args -> do
    defName' <- substM defName
    DataCon printName defName'
      <$> (DataDefParams <$> mapM rec params <*> mapM rec dicts)
      <*> pure con <*> mapM rec args
  Record items -> Record <$> mapM rec items
  RecordTy _ -> substM atom
  Variant ty l con payload ->
    Variant
       <$> (fromExtLabeledItemsE <$> substM (ExtLabeledItemsE ty))
       <*> return l <*> return con <*> rec payload
  VariantTy _      -> substM atom
  LabeledRow _     -> substM atom
  ACase scrut alts resultTy ->
    ACase <$> rec scrut <*> mapM substM alts <*> rec resultTy
  DataConRef _ _ _ -> error "Should only occur in Imp lowering"
  BoxedRef _       -> error "Should only occur in Imp lowering"
  DepPairRef _ _ _ -> error "Should only occur in Imp lowering"
  ProjectElt idxs v -> getProjection (toList idxs) <$> rec (Var v)
  where rec x = traverseSurfaceAtomNames x doWithName

evalAtom :: Interp m => Atom i -> m i o (Atom o)
evalAtom atom = traverseSurfaceAtomNames atom \v -> do
  env <- getSubst
  case env ! v of
    SubstVal x -> return x
    Rename v' -> do
      ~(AtomNameBinding bindingInfo) <- lookupEnv v'
      case bindingInfo of
        LetBound (DeclBinding _ _ (Atom x)) -> dropSubst $ evalAtom x
        PtrLitBound _ ptrName -> do
          ~(PtrBinding ptr) <- lookupEnv ptrName
          return $ Con $ Lit $ PtrLit ptr
        _ -> error "shouldn't have irreducible atom names left"
{-# SCC evalAtom #-}

evalExpr :: Interp m => Expr i -> m i o (Atom o)
evalExpr expr = case expr of
  App f xs -> do
    f' <- evalAtom f
    xs' <- mapM evalAtom xs
    case fromNaryLam (length xs) f' of
      Just (bsCount, NaryLamExpr bs _ body) -> do
        let (xsPref, xsRest) = NE.splitAt bsCount xs'
        ans <- dropSubst $ extendSubst (bs@@>(SubstVal <$> xsPref)) $ evalBlock body
        case nonEmpty xsRest of
          Nothing    -> return ans
          Just rest' -> dropSubst $ evalExpr $ App ans rest'
      Nothing -> error $ "Failed to reduce application!" ++ pprint expr
  -- TODO: de-dup with App
  TabApp f xs -> do
    f' <- evalAtom f
    xs' <- mapM evalAtom xs
    case fromNaryTabLam (length xs) f' of
      Just (bsCount, NaryLamExpr bs _ body) -> do
        let (xsPref, xsRest) = NE.splitAt bsCount xs'
        ans <- dropSubst $ extendSubst (bs@@>(SubstVal <$> xsPref)) $ evalBlock body
        case nonEmpty xsRest of
          Nothing    -> return ans
          Just rest' -> dropSubst $ evalExpr $ TabApp ans rest'
      Nothing -> error "Failed to reduce application!"
  Atom atom -> evalAtom atom
  Op op     -> evalOp op
  Case e alts _ _ -> do
    e' <- evalAtom e
    case trySelectBranch e' of
      Nothing -> error "branch should be chosen at this point"
      Just (con, args) -> do
        Abs bs body <- return $ alts !! con
        extendSubst (bs @@> map SubstVal args) $ evalBlock body
  Hof hof -> case hof of
    RunIO (Lam (LamExpr b body)) ->
      extendSubst (b @> SubstVal UnitTy) $
        evalBlock body
    _ -> error $ "Not implemented: " ++ pprint expr
{-# SCC evalExpr #-}

evalOp :: Interp m => Op i -> m i o (Atom o)
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
  PtrOffset (Con (Lit (PtrLit (PtrLitVal (a, t) p)))) (IdxRepVal i) ->
    return $ Con $ Lit $ PtrLit (PtrLitVal (a, t) $ p `plusPtr` (sizeOf t * fromIntegral i))
  PtrLoad (Con (Lit (PtrLit (PtrLitVal (Heap CPU, t) p)))) ->
    Con . Lit <$> liftIO (loadLitVal p t)
  PtrLoad (Con (Lit (PtrLit (PtrLitVal (Heap GPU, t) p)))) ->
    liftIO $ allocaBytes (sizeOf t) $ \hostPtr -> do
      loadCUDAArray hostPtr p (sizeOf t)
      Con . Lit <$> loadLitVal hostPtr t
  PtrLoad (Con (Lit (PtrLit (PtrLitVal (Stack, _) _)))) ->
    error $ "Unexpected stack pointer in interpreter"
  CastOp destTy x -> do
    sourceTy <- getType x
    let failedCast = error $ "Cast not implemented: " ++ pprint sourceTy ++
                             " -> " ++ pprint destTy
    case (sourceTy, destTy) of
      (IdxRepTy, TC (Fin n)) -> return $ Con $ FinVal n x
      (TC (Fin _), IdxRepTy) -> do
        let Con (FinVal _ ord) = x
        return ord
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
      return $ Con $ SumAsProd ty i (map (const []) cons)
  ProjMethod dict i -> evalProjectDictMethod dict i
  _ -> error $ "Not implemented: " ++ pprint expr

evalProjectDictMethod :: Interp m => Atom o -> Int -> m i o (Atom o)
evalProjectDictMethod d i = cheapNormalize d >>= \case
  DictCon (InstanceDict instanceName args) -> dropSubst do
    args' <- mapM evalAtom args
    InstanceDef _ bs _ body <- lookupInstanceDef instanceName
    let InstanceBody _ methods = body
    let method = methods !! i
    extendSubst (bs@@>(SubstVal <$> args')) $
      evalBlock method
  Con (ExplicitDict _ method) -> do
    case i of
      0 -> return method
      _ -> error "ExplicitDict only supports single-method classes"
  DictCon (IxFin n) -> projectIxFinMethod i n
  _ -> error $ "Not a simplified dict: " ++ pprint d

matchUPat :: Interp m => UPat i i' -> Atom o -> m i o (SubstFrag AtomSubstVal i i' o)
matchUPat (WithSrcB _ pat) x = do
  x' <- dropSubst $ evalAtom x
  case (pat, x') of
    (UPatBinder b, _) -> return $ b @> SubstVal x'
    (UPatCon _ ps, DataCon _ _ _ _ xs) -> matchUPats ps xs
    (UPatPair (PairB p1 p2), PairVal x1 x2) -> do
      matchUPat p1 x1 >>= (`followedByFrag` matchUPat p2 x2)
    (UPatUnit UnitB, UnitVal) -> return emptyInFrag
    (UPatRecord pats, Record initXs) -> go initXs pats
      where
        go :: Interp m => LabeledItems (Atom o) -> UFieldRowPat i i' -> m i o (SubstFrag AtomSubstVal i i' o)
        go xs = \case
          UEmptyRowPat    -> return emptyInFrag
          URemFieldsPat b -> return $ b @> SubstVal (Record xs)
          UDynFieldsPat ~(InternalName _ (UAtomVar v)) b rest ->
            evalAtom (Var v) >>= \case
              LabeledRow f | [StaticFields fields] <- fromFieldRowElems f -> do
                let (items, remItems) = splitLabeledItems fields xs
                frag <- matchUPat b (Record items)
                frag `followedByFrag` go remItems rest
              _ -> error "Unevaluated fields?"
          UDynFieldPat ~(InternalName _ (UAtomVar v)) b rest ->
            evalAtom (Var v) >>= \case
              Con (LabelCon l) -> go xs $ UStaticFieldPat l b rest
              _ -> error "Unevaluated label?"
          UStaticFieldPat l b rest -> case popLabeledItems l xs of
            Just (val, xsTail) -> do
              headFrag <- matchUPat b val
              headFrag `followedByFrag` go xsTail rest
            Nothing -> error "Field missing in record"
    (UPatVariant _ _ _  , _) -> error "can't have top-level may-fail pattern"
    (UPatVariantLift _ _, _) -> error "can't have top-level may-fail pattern"
    (UPatTable bs, tab) -> do
      getType tab >>= \case
        TabTy b _ -> do
          xs <- dropSubst do
            idxs <- indices (binderAnn b)
            forM idxs \i -> evalExpr $ TabApp tab (i:|[])
          matchUPats bs xs
        _ -> error $ "not a table: " ++ pprint tab
    _ -> error "bad pattern match"
  where followedByFrag f m = extendSubst f $ fmap (f <.>) m

matchUPats :: Interp m => Nest UPat i i' -> [Atom o] -> m i o (SubstFrag AtomSubstVal i i' o)
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
  (forall l. (Emits l, DExt n l) => BuilderM l (Atom l))
  -> InterpM n n (Atom n)
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

indices :: EnvReader m => IxType n -> m n [Atom n]
indices ixTy = unsafeLiftInterpM $ do
  ~(IdxRepVal size) <- interpIndexSetSize ixTy
  forM (iota size) \i -> interpUnsafeFromOrdinal ixTy $ IdxRepVal i
{-# SCC indices #-}

interpIndexSetSize :: IxType n -> InterpM n n (Atom n)
interpIndexSetSize ixTy = liftBuilderInterp $ indexSetSize $ sink ixTy

interpUnsafeFromOrdinal :: IxType n -> Atom n -> InterpM n n (Atom n)
interpUnsafeFromOrdinal ixTy i = liftBuilderInterp $ unsafeFromOrdinal (sink ixTy) (sink i)

-- A variant of `indices` that accepts an expected number of them and
-- only tries to construct the set if the expected number matches the
-- given index set's size.
indicesLimit :: EnvReader m => Int -> IxType n -> m n (Either Word32 [Atom n])
indicesLimit sizeReq ixTy = unsafeLiftInterpM $ do
  ~(IdxRepVal size) <- interpIndexSetSize ixTy
  if size == fromIntegral sizeReq then
    Right <$> forM [0..size-1] \i -> interpUnsafeFromOrdinal ixTy $ IdxRepVal i
  else
    return $ Left size
{-# SCC indicesLimit #-}

-- === Helpers for function evaluation over fixed-width types ===

applyIntBinOp' :: (forall a. (Eq a, Ord a, Num a, Integral a)
               => (a -> Atom n) -> a -> a -> Atom n) -> Atom n -> Atom n -> Atom n
applyIntBinOp' f x y = case (x, y) of
  (Con (Lit (Int64Lit xv)), Con (Lit (Int64Lit yv))) -> f (Con . Lit . Int64Lit) xv yv
  (Con (Lit (Int32Lit xv)), Con (Lit (Int32Lit yv))) -> f (Con . Lit . Int32Lit) xv yv
  (Con (Lit (Word8Lit xv)), Con (Lit (Word8Lit yv))) -> f (Con . Lit . Word8Lit) xv yv
  (Con (Lit (Word32Lit xv)), Con (Lit (Word32Lit yv))) -> f (Con . Lit . Word32Lit) xv yv
  (Con (Lit (Word64Lit xv)), Con (Lit (Word64Lit yv))) -> f (Con . Lit . Word64Lit) xv yv
  _ -> error "Expected integer atoms"

applyIntBinOp :: (forall a. (Num a, Integral a) => a -> a -> a) -> Atom n -> Atom n -> Atom n
applyIntBinOp f x y = applyIntBinOp' (\w -> w ... f) x y

applyIntCmpOp :: (forall a. (Eq a, Ord a) => a -> a -> Bool) -> Atom n -> Atom n -> Atom n
applyIntCmpOp f x y = applyIntBinOp' (\_ -> (Con . Lit . Word8Lit . fromIntegral . fromEnum) ... f) x y

applyFloatBinOp :: (forall a. (Num a, Fractional a) => a -> a -> a) -> Atom n -> Atom n -> Atom n
applyFloatBinOp f x y = case (x, y) of
  (Con (Lit (Float64Lit xv)), Con (Lit (Float64Lit yv))) -> Con $ Lit $ Float64Lit $ f xv yv
  (Con (Lit (Float32Lit xv)), Con (Lit (Float32Lit yv))) -> Con $ Lit $ Float32Lit $ f xv yv
  _ -> error "Expected float atoms"

applyFloatUnOp :: (forall a. (Num a, Fractional a) => a -> a) -> Atom n -> Atom n
applyFloatUnOp f x = applyFloatBinOp (\_ -> f) undefined x
