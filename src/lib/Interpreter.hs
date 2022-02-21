-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving #-}

module Interpreter (
  evalBlock, evalExpr, indices,
  liftInterpM, InterpM, Interp,
  traverseSurfaceAtomNames, evalAtom, matchUPat) where

import Control.Monad
import Control.Monad.IO.Class
import qualified Data.List.NonEmpty as NE
import Data.Foldable (toList)
import Foreign.Ptr
import Foreign.Marshal.Alloc
import System.IO.Unsafe

import CUDA
import LLVMExec
import Err
import LabeledItems

import Name
import MTL1
import Syntax
import Simplify
import Type
import PPrint ()

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

evalBlock :: Interp m => Block i -> m i o (Atom o)
evalBlock (Block _ decls result) = evalDecls decls $ evalExpr result

evalDecls :: Interp m => Nest Decl i i' -> m i' o a -> m i o a
evalDecls Empty cont = cont
evalDecls (Nest (Let b (DeclBinding _ _ rhs)) rest) cont = do
  result <- evalExpr rhs
  extendSubst (b @> SubstVal result) $ evalDecls rest cont

-- XXX: this doesn't go under lambda or pi binders
traverseSurfaceAtomNames
  :: (SubstReader AtomSubstVal m, EnvReader2 m)
  => Atom i
  -> (AtomName i -> m i o (Atom o))
  -> m i o (Atom o)
traverseSurfaceAtomNames atom doWithName = case atom of
  Var v -> doWithName v
  Lam _ -> substM atom
  Pi  _ -> substM atom
  DepPair l r ty -> DepPair <$> rec l <*> rec r <*> substM ty
  DepPairTy _ -> substM atom
  Con con -> Con <$> mapM rec con
  TC  tc  -> TC  <$> mapM rec tc
  Eff _ -> substM atom
  TypeCon sn defName params -> do
    defName' <- substM defName
    TypeCon sn defName' <$> mapM rec params
  DataCon printName defName params con args -> do
    defName' <- substM defName
    DataCon printName defName' <$> mapM rec params
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
  BoxedRef _ _     -> error "Should only occur in Imp lowering"
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

evalExpr :: Interp m => Expr i -> m i o (Atom o)
evalExpr expr = case expr of
  App f xs -> do
    f' <- evalAtom f
    case fromNaryLam (length xs) f' of
      Just (NaryLamExpr bs _ body) -> do
        xs' <- mapM evalAtom xs
        let subst = bs @@> fmap SubstVal xs'
        dropSubst $ extendSubst subst $ evalBlock body
      _ -> do
        when (length xs == 1) $ error "Failed to reduce application!"
        case NE.uncons xs of
          (x, maybeRest) -> do
            ans <- evalExpr $ App f $ x :| []
            case maybeRest of
              Nothing   -> return ans
              Just rest -> do
                NonEmptyListE rest' <- substM $ NonEmptyListE rest
                dropSubst $ evalExpr $ App ans rest'
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

evalOp :: Interp m => Op i -> m i o (Atom o)
evalOp expr = mapM evalAtom expr >>= \case
  ScalarBinOp op x y -> return $ case op of
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
  ScalarUnOp op x -> return $ case op of
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
  ToOrdinal idxArg -> case idxArg of
    Con (IntRangeVal   _ _   i) -> return i
    Con (IndexRangeVal _ _ _ i) -> return i
    _ -> error "Not implemented"
  CastOp destTy x -> do
    sourceTy <- getType x
    let failedCast = error $ "Cast not implemented: " ++ pprint sourceTy ++
                             " -> " ++ pprint destTy
    case (sourceTy, destTy) of
      (IdxRepTy, TC (IntRange l h)) -> return $ Con $ IntRangeVal l h x
      (TC (IntRange _ _), IdxRepTy) -> do
        let Con (IntRangeVal _ _ ord) = x
        return ord
      (IdxRepTy, TC (IndexRange t l h)) -> return $ Con $ IndexRangeVal t l h x
      (TC (IndexRange _ _ _), IdxRepTy) -> do
        let Con (IndexRangeVal _ _ _ ord) = x
        return ord
      (BaseTy (Scalar sb), BaseTy (Scalar db)) -> case (sb, db) of
        (Int64Type, Int32Type) -> do
          let Con (Lit (Int64Lit v)) = x
          return $ Con $ Lit $ Int32Lit $ fromIntegral v
        _ -> failedCast
      _ -> failedCast
  Select cond t f -> case cond of
    Con (Lit (Word8Lit 0)) -> return f
    Con (Lit (Word8Lit 1)) -> return t
    _ -> error $ "Invalid select condition: " ++ pprint cond
  ToEnum ty@(TypeCon _ defName _) i -> do
      DataDef _ _ cons <- lookupDataDef defName
      return $ Con $ SumAsProd ty i (map (const []) cons)
  _ -> error $ "Not implemented: " ++ pprint expr

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
            idxs <- indices (binderType b)
            forM idxs \i -> evalExpr $ App tab (i:|[])
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
indices :: EnvReader m => Type n -> m n [Atom n]
indices ty = fmap fromListE $ flip runScopedT1 (mempty :: IxCache n) $ do
    env <- unsafeGetEnv
    Distinct <- getDistinct
    ix <- simplifiedIxInstance ty
    let IdxRepVal size = unsafePerformIO $ runInterpM env $ evalMethod ix simpleIxSize UnitVal
    return $ ListE $ unsafePerformIO $ runInterpM env $
      forM [0..size - 1] $ evalMethod ix simpleUnsafeFromOrdinal . IdxRepVal
    where
      evalMethod ix method x = case method ix of
        Abs decls lam -> do
          evalDecls decls $ evalExpr $ App (Lam lam) $ sinkFromTop x NE.:| []

      runInterpM :: Distinct n => Env n -> InterpM n n a -> IO a
      runInterpM bindings cont =
        runEnvReaderT bindings $ runSubstReaderT idSubst $ runInterpM' cont
