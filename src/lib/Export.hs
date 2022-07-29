-- Copyright 2020 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE UndecidableInstances #-}

module Export (
    exportFunctions, prepareFunctionForExport, exportedSignatureDesc,
    ExportedSignature (..), ExportType (..), ExportArg (..), ExportResult (..),
    ExportCC (..),
  ) where

import Data.List (intercalate)
import Control.Monad

import Name
import Err
import Syntax
import CheckType (asFirstOrderFunction)
import QueryType
import Builder
import Simplify
import Imp
import Util (scanM)

exportFunctions :: FilePath -> [(String, Atom n)] -> Env n -> IO ()
exportFunctions = error "Not implemented"
{-# SCC exportFunctions #-}

prepareFunctionForExport :: (EnvReader m, Fallible1 m) => ExportCC -> Atom n -> m n (ImpFunction n, ExportedSignature VoidS)
prepareFunctionForExport cc f = liftExcept =<< liftEnvReaderT (prepareFunctionForExport' cc f)
{-# INLINE prepareFunctionForExport #-}

prepareFunctionForExport' :: ExportCC -> Atom n -> EnvReaderT Except n (ImpFunction n, ExportedSignature VoidS)
prepareFunctionForExport' cc f = do
  naryPi <- getType f >>= asFirstOrderFunction >>= \case
    Nothing  -> throw TypeErr "Only first-order functions can be exported"
    Just npi -> return npi
  closedNaryPi <- case hoistToTop naryPi of
    HoistFailure _   -> throw TypeErr $ "Types of exported functions have to be closed terms. Got: " ++
      pprint naryPi
    HoistSuccess npi -> return npi
  sig <- case runFallibleM $ runEnvReaderT emptyOutMap $ naryPiToExportSig closedNaryPi of
    Success sig -> return sig
    Failure err -> throwErrs err
  argRecon <- case sig of
    ExportedSignature argSig _ _ -> do
      case sinkFromTop $ EmptyAbs argSig of
        Abs argSig' UnitE -> liftEnvReaderM $ exportArgRecon argSig'
  f' <- asNaryLam naryPi f
  -- TODO: figure out how to handle specialization cache emissions when compiling for export
  fSimp <- simplifyTopFunctionAssumeNoTopEmissions f'
  fImp <- toImpExportedFunction cc fSimp argRecon
  return (fImp, sig)
  where
    naryPiToExportSig :: (EnvReader m, EnvExtender m, Fallible1 m)
                      => NaryPiType n -> m n (ExportedSignature n)
    naryPiToExportSig (NaryPiType (NonEmptyNest tb tbs) effs resultTy) = do
        case effs of
          Pure -> return ()
          _    -> throw TypeErr "Only pure functions can be exported"
        goArgs Empty [] (Nest tb tbs) resultTy
      where
        goArgs :: (EnvReader m, EnvExtender m, Fallible1 m)
               => Nest ExportArg n l' -> [AtomName l'] -> Nest PiBinder l' l -> Type l -> m l' (ExportedSignature n)
        goArgs argSig argVs piBs piRes = case piBs of
          Empty -> goResult piRes \resSig ->
            return $ ExportedSignature argSig resSig $ case cc of
              FlatExportCC -> (fromListE $ sink $ ListE argVs) ++ nestToList (sink . binderName) resSig
              XLAExportCC  -> []
          Nest b bs -> do
            refreshAbs (Abs b (Abs bs piRes)) \(PiBinder v ty arrow) (Abs bs' piRes') -> do
              let invalidArrow = throw TypeErr
                                   "Exported functions can only have regular and implicit arrow types"
              vis <- case arrow of
                PlainArrow    -> return ExplicitArg
                ImplicitArrow -> return ImplicitArg
                ClassArrow    -> invalidArrow
                LinArrow      -> invalidArrow
              ety <- toExportType ty
              goArgs (argSig `joinNest` Nest (ExportArg vis (v:>ety)) Empty)
                     ((fromListE $ sink $ ListE argVs) ++ [binderName v]) bs' piRes'

        goResult :: (EnvReader m, EnvExtender m, Fallible1 m)
                 => Type l
                 -> (forall q. DExt l q => Nest ExportResult l q -> m q a)
                 -> m l a
        goResult ty cont = case ty of
          ProdTy [lty, rty] ->
            goResult lty \lres ->
              goResult (sink rty) \rres ->
                cont $ joinNest lres rres
          _ -> withFreshBinder noHint ty \b -> do
            ety <- toExportType ty
            cont $ Nest (ExportResult (b:>ety)) Empty

    exportArgRecon :: (EnvReader m, EnvExtender m) => Nest ExportArg n l -> m n (Abs (Nest IBinder) (ListE Block) n)
    exportArgRecon topArgs = go [] topArgs
      where
        go :: (EnvReader m, EnvExtender m)
           => [Block n] -> Nest ExportArg n l -> m n (Abs (Nest IBinder) (ListE Block) n)
        go argRecons = \case
          Empty -> return $ Abs Empty $ ListE argRecons
          Nest (ExportArg _ b) bs ->
            refreshAbs (Abs b (EmptyAbs bs)) \(v':>ety) (Abs bs' UnitE) -> do
              (ity, block) <- typeRecon (sink ety) $ Var $ binderName v'
              Abs ibs' allRecons' <- go (sinkList argRecons ++ [sink block]) bs'
              return $ Abs (Nest (IBinder v' ity) ibs') allRecons'

        typeRecon :: EnvExtender m => ExportType n -> Atom n -> m n (IType, Block n)
        typeRecon ety v = case ety of
          ScalarType sbt ->
            return (Scalar sbt, Block (BlockAnn (BaseTy $ Scalar sbt) Pure) Empty v)
          RectContArrayPtr sbt shape -> do
              block <- liftBuilder $ buildBlock $ tableAtom (sink v) (sink $ ListE shape) []
              return (PtrType (Heap CPU, Scalar sbt), block)
            where
              tableAtom :: Emits n => Atom n -> ListE ExportDim n
                        -> [(Atom n, ExportDim n)] -> BuilderM n (Atom n)
              tableAtom basePtr (ListE shapeTail) typedIdxs = case shapeTail of
                (ity:rest) -> buildTabLam noHint (exportDimToIxType ity) \i -> do
                  let typedIdxs' = [(sink ix, sink t) | (ix, t) <- typedIdxs]
                  tableAtom (sink basePtr) (sink $ ListE rest) (typedIdxs' ++ [(Var i, sink ity)])
                [] -> do
                  sizes <- mapM (indexSetSizeFin . finArg . snd) typedIdxs
                  strides <- reverse . fst <$> scanM (\si st -> dup <$> imul st si)
                                                     (IdxRepVal 1:reverse (tail sizes)) (IdxRepVal 1)
                  ords <- forM typedIdxs \(i, ity) -> ordinalFin (finArg ity) i
                  offset <- foldM iadd (IdxRepVal 0) =<< mapM (uncurry imul) (zip strides ords)
                  unsafePtrLoad =<< ptrOffset basePtr offset

              indexSetSizeFin n = projectIxFinMethod 0 n
              ordinalFin n ix = do
                Lam (LamExpr b body) <- projectIxFinMethod 1 n
                emitBlock =<< applySubst (b@>SubstVal ix) body
              dup x = (x, x)

    toExportType :: Fallible m => Type n -> m (ExportType n)
    toExportType ty = case ty of
      BaseTy (Scalar sbt) -> return $ ScalarType sbt
      TabTy  _ _          -> case parseTabTy ty of
        Nothing  -> unsupported
        Just ety -> return ety
      _ -> unsupported
      where unsupported = throw TypeErr $ "Unsupported type of argument in exported function: " ++ pprint ty

    parseTabTy :: Type n -> Maybe (ExportType n)
    parseTabTy = go []
      where
        go shape = \case
          BaseTy (Scalar sbt) -> Just $ RectContArrayPtr sbt shape

          TabTy  (b:>(IxType (TC (Fin n)) _)) a -> do
            dim <- case n of
              Var v       -> Just (ExportDimVar v)
              IdxRepVal s -> Just (ExportDimLit $ fromIntegral s)
              _           -> Nothing
            case hoist b a of
              HoistSuccess a' -> go (shape ++ [dim]) a'
              HoistFailure _  -> Nothing
          _ -> Nothing
{-# SCC prepareFunctionForExport #-}

-- === Exported function signature ===

data ArgVisibility = ImplicitArg | ExplicitArg

exportDimToIxType :: ExportDim n -> IxType n
exportDimToIxType dim = IxType (TC (Fin dim')) (DictCon $ IxFin dim')
  where dim' = finArg dim

finArg :: ExportDim n -> Atom n
finArg dim = case dim of
  ExportDimVar v -> Var v
  ExportDimLit n -> IdxRepVal (fromIntegral n)

data ExportDim n =
   ExportDimVar (AtomName n)
 | ExportDimLit Int

data ExportType n = RectContArrayPtr ScalarBaseType [ExportDim n]
                  | ScalarType ScalarBaseType

data    ExportArg    n l = ExportArg    ArgVisibility (BinderP AtomNameC ExportType n l)
newtype ExportResult n l = ExportResult               (BinderP AtomNameC ExportType n l)
data ExportedSignature n = forall l l'.
  ExportedSignature { exportedArgSig   :: Nest ExportArg n l
                    , exportedResSig   :: Nest ExportResult l l'
                    , exportedCCallSig :: [AtomName l']
                    }

instance GenericE ExportDim where
  type RepE ExportDim = EitherE AtomName (LiftE Int)
  fromE = \case
    ExportDimVar v -> LeftE v
    ExportDimLit n -> RightE (LiftE n)
  {-# INLINE fromE #-}
  toE = \case
    LeftE v -> ExportDimVar v
    RightE (LiftE n) -> ExportDimLit n
instance SubstE    Name ExportDim
instance SinkableE      ExportDim

instance GenericE ExportType where
  type RepE ExportType = EitherE (LiftE ScalarBaseType)
                                 (LiftE ScalarBaseType `PairE` ListE ExportDim)
  fromE = \case
    ScalarType sbt   -> LeftE $ LiftE sbt
    RectContArrayPtr sbt shape -> RightE $ LiftE sbt `PairE` ListE shape
  {-# INLINE fromE #-}
  toE = \case
    LeftE (LiftE sbt) -> ScalarType sbt
    RightE (LiftE sbt `PairE` ListE shape) -> RectContArrayPtr sbt shape
  {-# INLINE toE #-}
instance SubstE    Name ExportType
instance SinkableE      ExportType

instance ToBinding ExportType AtomNameC where
  toBinding = \case
    ScalarType       sbt   -> toBinding $ BaseTy $ Scalar sbt
    RectContArrayPtr sbt _ -> toBinding $ BaseTy $ PtrType (Heap CPU, Scalar sbt)

deriving via (BinderP AtomNameC ExportType) instance GenericB   ExportResult
deriving via (BinderP AtomNameC ExportType) instance ProvesExt  ExportResult
deriving via (BinderP AtomNameC ExportType) instance BindsNames ExportResult
instance BindsAtMostOneName ExportResult AtomNameC where
  (ExportResult b) @> v = b @> v
instance BindsOneName ExportResult AtomNameC where
  binderName (ExportResult b) = binderName b

instance GenericB ExportArg where
  type RepB ExportArg = PairB (LiftB (LiftE ArgVisibility)) (BinderP AtomNameC ExportType)
  fromB (ExportArg vis b) = PairB (LiftB (LiftE vis)) b
  toB (PairB (LiftB (LiftE vis)) b) = ExportArg vis b
instance ProvesExt       ExportArg
instance BindsNames      ExportArg
instance SinkableB       ExportArg
instance SubstB     Name ExportArg
instance BindsAtMostOneName ExportArg AtomNameC where
  (ExportArg _ b) @> v = b @> v
instance BindsOneName ExportArg AtomNameC where
  binderName (ExportArg _ b) = binderName b

-- Serialization

exportedSignatureDesc :: ExportedSignature n -> (String, String, String)
exportedSignatureDesc ExportedSignature{..} =
  ( intercalate "," $ nestToList show exportedArgSig
  , intercalate "," $ nestToList show exportedResSig
  , intercalate "," $ fmap pprint exportedCCallSig
  )

showExportSBT :: ScalarBaseType -> String
showExportSBT sbt = case sbt of
  Int64Type   -> "i64"
  Int32Type   -> "i32"
  Word8Type   -> "u8"
  Word32Type  -> "u32"
  Word64Type  -> "u64"
  Float64Type -> "f64"
  Float32Type -> "f32"

instance Show (ExportType n) where
  show arr = case arr of
    RectContArrayPtr sbt shape -> showExportSBT sbt <> showShape shape
    ScalarType       sbt       -> showExportSBT sbt
    where
      showShape shape = "[" <> (intercalate "," $ fmap showDim shape) <> "]"
      showDim size = case size of
        ExportDimVar v -> pprint v
        ExportDimLit n -> show n

instance Show (ExportArg n l) where
  show (ExportArg vis (name:>ty)) = showVis vis <> pprint name <> ":" <> show ty
    where
      showVis ImplicitArg = "?"
      showVis ExplicitArg = ""

instance Show (ExportResult n l) where
  show (ExportResult (name:>ty)) = pprint name <> ":" <> show ty
