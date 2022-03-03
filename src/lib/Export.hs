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
import Control.Monad

import Name
import MTL1
import Err
import Syntax
import Type
import Builder
import Simplify
import Imp
import Util (scanM)

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
  argRecon <- case sig of
    ExportedSignature argSig _ _ -> do
      case sinkFromTop $ EmptyAbs argSig of
        Abs argSig' UnitE -> liftEnvReaderM $ exportArgRecon argSig'
  fSimp <- simplifyTopFunction naryPi f
  fImp <- toImpExportedFunction fSimp argRecon
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
            return (Scalar sbt, Block (BlockAnn $ BaseTy $ Scalar sbt) Empty $ Atom v)
          RectContArrayPtr sbt shape -> do
              block <- liftBuilder $ buildBlock $ tableAtom (sink v) (sink $ shapeToE shape) [] []
              return (PtrType (Heap CPU, Scalar sbt), block)
            where
              tableAtom :: Emits n => Atom n -> ListE (EitherE AtomName (LiftE Int)) n -> [Atom n] -> [Atom n] -> BuilderM n (Atom n)
              tableAtom basePtr (ListE shapeTail) is sizes = case shapeTail of
                (h:t) -> buildTabLam NoHint (Fin $ dimSize h) \i ->
                  tableAtom (sink basePtr) (sink $ ListE t)
                            (sinkList is ++ [Var i]) (sinkList $ sizes ++ [dimSize h])
                [] -> do
                  strides <- reverse . fst <$> scanM (\si st -> dup <$> imul st si)
                                                     (IdxRepVal 1:reverse (tail sizes)) (IdxRepVal 1)
                  ords <- flip evalStateT1 mempty $ forM is \i -> do
                    ity <- getType i
                    appSimplifiedIxMethod ity simpleToOrdinal i
                  offset <- foldM iadd (IdxRepVal 0) =<< mapM (uncurry imul) (zip strides ords)
                  unsafePtrLoad =<< ptrOffset basePtr offset

              dup x = (x, x)
              dimSize = \case LeftE n -> Var n; RightE (LiftE n) -> IdxRepVal (fromIntegral n)

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
          TabTy  (PiBinder b (Fin n) _) a -> do
            dim <- case n of
              Var v       -> Just (Left v)
              IdxRepVal s -> Just (Right $ fromIntegral s)
              _           -> Nothing
            case hoist b a of
              HoistSuccess a' -> go (shape ++ [dim]) a'
              HoistFailure _  -> Nothing
          _ -> Nothing

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

instance GenericE ExportType where
  type RepE ExportType = EitherE (LiftE ScalarBaseType)
                                 (LiftE ScalarBaseType `PairE` ListE (EitherE AtomName (LiftE Int)))
  fromE = \case
    ScalarType sbt   -> LeftE $ LiftE sbt
    RectContArrayPtr sbt shape -> RightE $ LiftE sbt `PairE` shapeToE shape
  toE = \case
    LeftE (LiftE sbt) -> ScalarType sbt
    RightE (LiftE sbt `PairE` shape) -> RectContArrayPtr sbt (shapeFromE shape)
instance SubstE    Name ExportType
instance SinkableE      ExportType

shapeToE :: [Either (AtomName n) Int] -> ListE (EitherE AtomName (LiftE Int)) n
shapeToE shape = ListE (dimToE <$> shape)
  where dimToE = \case Left n -> LeftE n; Right n -> RightE (LiftE n)

shapeFromE :: ListE (EitherE AtomName (LiftE Int)) n -> [Either (AtomName n) Int]
shapeFromE (ListE shape) = (dimFromE <$> shape)
  where dimFromE = \case LeftE n -> Left n; RightE (LiftE n) -> Right n

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
        Left  name -> pprint name
        Right lit  -> show lit

instance Show (ExportArg n l) where
  show (ExportArg vis (name:>ty)) = showVis vis <> pprint name <> ":" <> show ty
    where
      showVis ImplicitArg = "?"
      showVis ExplicitArg = ""

instance Show (ExportResult n l) where
  show (ExportResult (name:>ty)) = pprint name <> ":" <> show ty
