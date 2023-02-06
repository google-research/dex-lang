-- Copyright 2020 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE UndecidableInstances #-}

module Export (
    exportFunctions, prepareFunctionForExport, exportedSignatureDesc,
    ExportedSignature (..), ExportType (..), ExportArg (..), ExportResult (..)
  ) where

import Data.List (intercalate)
import Foreign.Storable
import Foreign.C.String
import Foreign.Ptr

import Builder
import CheckType (asFirstOrderFunction)
import Core
import Err
import IRVariants
import Imp
import Lower (lowerFullySequential)
import Name
import QueryType
import Simplify
import TopLevel
import Types.Core
import Types.Imp
import Types.Primitives hiding (sizeOf)

type ExportAtomNameC = AtomNameC CoreIR

exportFunctions :: FilePath -> [(String, CAtom n)] -> Env n -> IO ()
exportFunctions = error "Not implemented"
{-# SCC exportFunctions #-}

prepareFunctionForExport
  :: (Mut n, Topper m) => CallingConvention -> CAtom n -> m n (ImpFunction n, ExportedSignature VoidS)
prepareFunctionForExport cc f = do
  (arrs, naryPi) <- getType f >>= asFirstOrderFunction >>= \case
    Nothing  -> throw TypeErr "Only first-order functions can be exported"
    Just npi -> return npi
  closedNaryPi <- case hoistToTop naryPi of
    HoistFailure _ ->
      throw TypeErr $ "Types of exported functions have to be closed terms. Got: " ++ pprint naryPi
    HoistSuccess npi -> return npi
  sig <- case runFallibleM $ runEnvReaderT emptyOutMap $ naryPiToExportSig arrs closedNaryPi of
    Success sig -> return sig
    Failure err -> throwErrs err
  f' <- asNaryLam naryPi f
  fSimp <- simplifyTopFunction f'
  fOpt <- simpOptimizations fSimp
  fLower <- lowerFullySequential fOpt
  flOpt <- loweredOptimizations fLower
  fImp <- toImpFunction cc flOpt
  return (fImp, sig)

  where
    naryPiToExportSig :: (EnvReader m, EnvExtender m, Fallible1 m)
                      => [Arrow] -> NaryPiType CoreIR n -> m n (ExportedSignature n)
    naryPiToExportSig arrs (NaryPiType tbs effs resultTy) = do
        case effs of
          Pure -> return ()
          _    -> throw TypeErr "Only pure functions can be exported"
        goArgs Empty [] arrs tbs resultTy
      where
        goArgs :: (EnvReader m, EnvExtender m, Fallible1 m)
               => Nest ExportArg n l' -> [CAtomName l'] -> [Arrow] -> Nest (Binder CoreIR) l' l
               -> CType l -> m l' (ExportedSignature n)
        goArgs argSig argVs argArrs piBs piRes = case (argArrs, piBs) of
          ([], Empty) -> goResult piRes \resSig ->
            return $ ExportedSignature argSig resSig $ case cc of
              StandardCC -> (fromListE $ sink $ ListE argVs) ++ nestToList (sink . binderName) resSig
              XLACC      -> []
              _ -> error $ "calling convention not supported: " ++ show cc
          (arrow:arrows, Nest b bs) -> do
            refreshAbs (Abs b (Abs bs piRes)) \(v:>ty) (Abs bs' piRes') -> do
              let invalidArrow = throw TypeErr
                                   "Exported functions can only have regular and implicit arrow types"
              vis <- case arrow of
                PlainArrow    -> return ExplicitArg
                ImplicitArrow -> return ImplicitArg
                ClassArrow    -> invalidArrow
                LinArrow      -> invalidArrow
              ety <- toExportType ty
              goArgs (argSig `joinNest` Nest (ExportArg vis (v:>ety)) Empty)
                     ((fromListE $ sink $ ListE argVs) ++ [binderName v]) arrows bs' piRes'
          _ -> error "zip error"

        goResult :: (EnvReader m, EnvExtender m, Fallible1 m)
                 => CType l
                 -> (forall q. DExt l q => Nest ExportResult l q -> m q a)
                 -> m l a
        goResult ty cont = case ty of
          ProdTy [lty, rty] ->
            goResult lty \lres ->
              goResult (sink rty) \rres ->
                cont $ joinNest lres rres
          _ -> withFreshBinder noHint ty \(b:>_) -> do
            ety <- toExportType ty
            cont $ Nest (ExportResult (b:>ety)) Empty

    toExportType :: Fallible m => CType n -> m (ExportType n)
    toExportType ty = case ty of
      BaseTy (Scalar sbt) -> return $ ScalarType sbt
      NatTy               -> return $ ScalarType IdxRepScalarBaseTy
      TabTy  _ _          -> case parseTabTy ty of
        Nothing  -> unsupported
        Just ety -> return ety
      _ -> unsupported
      where unsupported = throw TypeErr $ "Unsupported type of argument in exported function: " ++ pprint ty

    parseTabTy :: CType n -> Maybe (ExportType n)
    parseTabTy = go []
      where
        go :: [ExportDim n] -> CType n -> Maybe (ExportType n)
        go shape = \case
          BaseTy (Scalar sbt) -> Just $ RectContArrayPtr sbt shape
          NatTy               -> Just $ RectContArrayPtr IdxRepScalarBaseTy shape
          TabTy  (b:>(IxType (NewtypeTyCon (Fin n)) _)) a -> do
            dim <- case n of
              Var v    -> Just (ExportDimVar v)
              NatVal s -> Just (ExportDimLit $ fromIntegral s)
              _        -> Nothing
            case hoist b a of
              HoistSuccess a' -> go (shape ++ [dim]) a'
              HoistFailure _  -> Nothing
          _ -> Nothing

{-# INLINE prepareFunctionForExport #-}
{-# SCC prepareFunctionForExport #-}

-- === Exported function signature ===

data ArgVisibility = ImplicitArg | ExplicitArg

data ExportDim n =
   ExportDimVar (CAtomName n)
 | ExportDimLit Int

data ExportType n = RectContArrayPtr ScalarBaseType [ExportDim n]
                  | ScalarType ScalarBaseType

data    ExportArg    n l = ExportArg    ArgVisibility (BinderP ExportAtomNameC ExportType n l)
newtype ExportResult n l = ExportResult               (BinderP ExportAtomNameC ExportType n l)
data ExportedSignature n = forall l l'.
  ExportedSignature { exportedArgSig   :: Nest ExportArg n l
                    , exportedResSig   :: Nest ExportResult l l'
                    , exportedCCallSig :: [CAtomName l']
                    }

instance GenericE ExportDim where
  type RepE ExportDim = EitherE CAtomName (LiftE Int)
  fromE = \case
    ExportDimVar v -> LeftE v
    ExportDimLit n -> RightE (LiftE n)
  {-# INLINE fromE #-}
  toE = \case
    LeftE v -> ExportDimVar v
    RightE (LiftE n) -> ExportDimLit n
instance RenameE        ExportDim
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
instance RenameE        ExportType
instance SinkableE      ExportType

instance ToBinding ExportType ExportAtomNameC where
  toBinding = \case
    ScalarType       sbt   -> toBinding $ BaseTy $ Scalar sbt
    RectContArrayPtr sbt _ -> toBinding $ BaseTy $ PtrType (CPU, Scalar sbt)

deriving via (BinderP ExportAtomNameC ExportType) instance GenericB   ExportResult
deriving via (BinderP ExportAtomNameC ExportType) instance ProvesExt  ExportResult
deriving via (BinderP ExportAtomNameC ExportType) instance BindsNames ExportResult
instance BindsAtMostOneName ExportResult ExportAtomNameC where
  (ExportResult b) @> v = b @> v
instance BindsOneName ExportResult ExportAtomNameC where
  binderName (ExportResult b) = binderName b

instance GenericB ExportArg where
  type RepB ExportArg = PairB (LiftB (LiftE ArgVisibility)) (BinderP ExportAtomNameC ExportType)
  fromB (ExportArg vis b) = PairB (LiftB (LiftE vis)) b
  toB (PairB (LiftB (LiftE vis)) b) = ExportArg vis b
instance ProvesExt       ExportArg
instance BindsNames      ExportArg
instance SinkableB       ExportArg
instance RenameB         ExportArg
instance BindsAtMostOneName ExportArg ExportAtomNameC where
  (ExportArg _ b) @> v = b @> v
instance BindsOneName ExportArg ExportAtomNameC where
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

instance Storable (ExportedSignature 'VoidS) where
  sizeOf _ = 3 * sizeOf (undefined :: Ptr ())
  alignment _ = alignment (undefined :: Ptr ())
  peek _ = error "peek not implemented for ExportedSignature"
  poke addr sig = do
    let strAddr = castPtr @(ExportedSignature 'VoidS) @CString addr
    let (arg, res, ccall) = exportedSignatureDesc sig
    pokeElemOff strAddr 0 =<< newCString arg
    pokeElemOff strAddr 1 =<< newCString res
    pokeElemOff strAddr 2 =<< newCString ccall
