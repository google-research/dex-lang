-- Copyright 2020 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE UndecidableInstances #-}

module Export (
    exportFunctions, prepareFunctionForExport, exportedSignatureDesc,
    ExportedSignature (..), ExportType (..), ExportArg (..), ExportResult (..),
  ) where

import Data.List (intercalate)

import Name
import Err
import Syntax
import Type
import Simplify
import Imp

exportFunctions :: FilePath -> [(String, Atom n)] -> Env n -> IO ()
exportFunctions = error "Not implemented"

prepareFunctionForExport :: (EnvReader m, Fallible1 m) => Atom n -> m n (ImpFunction n, ExportedSignature VoidS)
prepareFunctionForExport f = do
  naryPi <- getType f >>= asFirstOrderFunction >>= \case
    Nothing  -> throw TypeErr "Only first-order functions can be exported"
    Just npi -> return npi
  closedNaryPi <- case hoistToTop naryPi of
    HoistFailure _   -> throw TypeErr "Types of exported functions have to be closed terms"
    HoistSuccess npi -> return npi
  sig <- case runFallibleM $ runEnvReaderT emptyOutMap $ naryPiToExportSig closedNaryPi of
    Success sig -> return sig
    Failure err -> throwErrs err
  fSimp <- simplifyTopFunction naryPi f
  fImp <- toImpExportedFunction fSimp
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
            return $ ExportedSignature argSig resSig $
              (fromListE $ sink $ ListE argVs) ++ nestToList (sink . binderName) resSig
          Nest b bs -> do
            refreshAbs (Abs b (Abs bs piRes)) \(PiBinder v ty arrow) (Abs bs' piRes') -> do
              let invalidArrow = throw TypeErr
                                   "Exported functions can only have regular and implicit arrow types"
              vis <- case arrow of
                PlainArrow    -> return ExplicitArg
                ImplicitArrow -> return ImplicitArg
                ClassArrow    -> invalidArrow
                TabArrow      -> invalidArrow
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
          _ -> withFreshBinder NoHint ty \b -> do
            ety <- toExportType ty
            cont $ Nest (ExportResult (b:>ety)) Empty

    toExportType :: Fallible m => Type n -> m (ExportType n)
    toExportType = \case
      BaseTy (Scalar sbt) -> return $ ScalarType sbt
      -- TODO: Arrays!
      ty -> throw TypeErr $ "Unsupported type of argument in exported function: " ++ pprint ty

-- === Exported function signature ===

data ArgVisibility = ImplicitArg | ExplicitArg
data ExportType n = RectContArrayPtr ScalarBaseType [Either (AtomName n) Int]
                  | ScalarType ScalarBaseType

data    ExportArg    n l = ExportArg    ArgVisibility (BinderP AtomNameC ExportType n l)
newtype ExportResult n l = ExportResult               (BinderP AtomNameC ExportType n l)
data ExportedSignature n = forall l l'.
  ExportedSignature { exportedArgSig   :: Nest ExportArg n l
                    , exportedResSig   :: Nest ExportResult l l'
                    , exportedCCallSig :: [AtomName l']
                    }

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
instance ProvesExt  ExportArg
instance BindsNames ExportArg
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
        Left  name -> pprint name
        Right lit  -> show lit

instance Show (ExportArg n l) where
  show (ExportArg vis (name:>ty)) = showVis vis <> pprint name <> ":" <> show ty
    where
      showVis ImplicitArg = "?"
      showVis ExplicitArg = ""

instance Show (ExportResult n l) where
  show (ExportResult (name:>ty)) = pprint name <> ":" <> show ty
