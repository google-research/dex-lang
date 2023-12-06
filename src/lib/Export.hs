-- Copyright 2020 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE UndecidableInstances #-}

module Export (
    exportFunctions, prepareFunctionForExport, exportedSignatureDesc,
    prepareSLamForExport,
    ExportedSignature (..), ExportNativeFunction (..)
  ) where

import Control.Category ((>>>))
import Data.List (intercalate)
import Foreign.Storable
import Foreign.C.String
import Foreign.Ptr

import Builder
import Core
import Err
import PPrint
import IRVariants
import Name
import QueryType
import Simplify
import Subst hiding (Rename)
import TopLevel
import Types.Core
import Types.Imp
import Types.Top
import Types.Primitives hiding (sizeOf)

type ExportAtomNameC = AtomNameC CoreIR

exportFunctions :: FilePath -> [(String, CAtom n)] -> Env n -> IO ()
exportFunctions = error "Not implemented"
{-# SCC exportFunctions #-}

data ExportNativeFunction = ExportNativeFunction
  { nativeFunction  :: NativeFunction
  , nativeSignature :: ExportedSignature 'VoidS }

prepareFunctionForExport :: (Mut n, Topper m)
  => CallingConvention -> CAtom n -> m n ExportNativeFunction
prepareFunctionForExport cc f = do
  naryPi <- case getType f of
    TyCon (Pi piTy) -> return piTy
    _ -> throwErr $ MiscErr $ MiscMiscErr "Only first-order functions can be exported"
  sig <- liftExportSigM $ corePiToExportSig cc naryPi
  closedSig <- case hoistToTop sig of
    HoistFailure _ ->
      throwErr $ MiscErr $ MiscMiscErr $ "Types of exported functions have to be closed terms. Got: " ++ pprint naryPi
    HoistSuccess s -> return s
  f' <- liftBuilder $ buildCoreLam naryPi \xs -> naryApp (sink f) (toAtom <$> xs)
  fSimp <- simplifyTopFunction $ coreLamToTopLam f'
  fImp <- compileTopLevelFun cc fSimp
  nativeFun <- toCFunction "userFunc" fImp >>= emitObjFile >>= loadObject
  return $ ExportNativeFunction nativeFun closedSig
{-# INLINE prepareFunctionForExport #-}
{-# SCC prepareFunctionForExport #-}

prepareSLamForExport :: (Mut n, Topper m)
  => CallingConvention -> STopLam n -> m n ExportNativeFunction
prepareSLamForExport cc f@(TopLam _ naryPi _) = do
  sig <- liftExportSigM $ simpPiToExportSig cc naryPi
  closedSig <- case hoistToTop sig of
    HoistFailure _ ->
      throwErr $ MiscErr $ MiscMiscErr $ "Types of exported functions have to be closed terms. Got: " ++ pprint naryPi
    HoistSuccess s -> return s
  fImp <- compileTopLevelFun cc f
  nativeFun <- toCFunction "userFunc" fImp >>= emitObjFile >>= loadObject
  return $ ExportNativeFunction nativeFun closedSig
{-# INLINE prepareSLamForExport #-}
{-# SCC prepareSLamForExport #-}

-- === Exported function signature ===

data Rename (r::IR) (c::C) (n::S) where
  Rename :: (Name (AtomNameC CoreIR) n) -> Rename r (AtomNameC r) n
  JustRefer :: Name c n -> Rename r c n

instance SinkableE (Rename r c) where
  sinkingProofE = todoSinkableProof
instance SinkableV (Rename r)
instance FromName (Rename r) where
  fromName = JustRefer

newtype ExportSigM (r::IR) (i::S) (o::S) (a:: *) = ExportSigM {
  runExportSigM :: SubstReaderT (Rename r) (EnvReaderT Except) i o a }
  deriving ( Functor, Applicative, Monad, ScopeReader, EnvExtender, Fallible
           , EnvReader, SubstReader (Rename r), MonadFail)

liftExportSigM :: (EnvReader m, Fallible1 m) => ExportSigM r n n a -> m n a
liftExportSigM cont = do
  Distinct <- getDistinct
  env <- unsafeGetEnv
  liftExcept $ runEnvReaderT env $ runSubstReaderT idSubst $
    runExportSigM cont

corePiToExportSig :: CallingConvention
  -> CorePiType i -> ExportSigM CoreIR i o (ExportedSignature o)
corePiToExportSig cc (CorePiType _ expls tbs (EffTy effs resultTy)) = do
    case effs of
      Pure -> return ()
      _    -> throwErr $ MiscErr $ MiscMiscErr "Only pure functions can be exported"
    goArgs cc Empty [] (zipAttrs expls tbs) resultTy

simpPiToExportSig :: CallingConvention
  -> PiType SimpIR i -> ExportSigM SimpIR i o (ExportedSignature o)
simpPiToExportSig cc (PiType bs (EffTy effs resultTy)) = do
  case effs of
    Pure -> return ()
    _    -> throwErr $ MiscErr $ MiscMiscErr "Only pure functions can be exported"
  bs' <- return $ fmapNest (\b -> WithAttrB Explicit b) bs
  goArgs cc Empty [] bs' resultTy

goArgs :: (IRRep r)
  => CallingConvention
  -> Nest ExportArg o o'
  -> [CAtomName o']
  -> Nest (WithAttrB Explicitness (Binder r)) i i'
  -> Type r i'
  -> ExportSigM r i o' (ExportedSignature o)
goArgs cc argSig argVs piBs piRes = case piBs of
  Empty -> goResult piRes \resSig ->
    return $ ExportedSignature argSig resSig $ case cc of
      StandardCC -> (fromListE $ sink $ ListE argVs) ++ nestToList (sink . binderName) resSig
      XLACC      -> []
      _ -> error $ "calling convention not supported: " ++ show cc
  Nest (WithAttrB expl (b:>ty)) bs -> do
    ety <- toExportType ty
    withFreshBinder (getNameHint b) ety \(v:>_) ->
      extendSubst (b @> Rename (binderName v)) $ do
        vis <- case expl of
          Explicit    -> return ExplicitArg
          Inferred _ _ -> return ImplicitArg
        goArgs cc (argSig >>> Nest (ExportArg vis (v:>ety)) Empty)
               ((fromListE $ sink $ ListE argVs) ++ [binderName v]) bs piRes

goResult :: IRRep r => Type r i
         -> (forall o'. DExt o o' =>
             Nest ExportResult o o' -> ExportSigM r i o' a)
         -> ExportSigM r i o a
goResult ty cont = case ty of
  TyCon (ProdType [one]) ->
    goResult one cont
  TyCon (ProdType (lty:rest)) ->
    goResult lty \lres ->
      goResult (TyCon (ProdType rest)) \rres ->
        cont $ lres >>> rres
  _ -> do
    ety <- toExportType ty
    withFreshBinder noHint ety \(b:>_) -> do
      cont $ Nest (ExportResult (b:>ety)) Empty

toExportType :: IRRep r => Type r i -> ExportSigM r i o (ExportType o)
toExportType ty = case ty of
  BaseTy (Scalar sbt) -> return $ ScalarType sbt
  TyCon (NewtypeTyCon Nat)    -> return $ ScalarType IdxRepScalarBaseTy
  TabTy _ _ _         -> parseTabTy ty >>= \case
    Nothing  -> unsupported
    Just ety -> return ety
  _ -> unsupported
  where unsupported = throwErr $ MiscErr $ MiscMiscErr $ "Unsupported type of argument in exported function: " ++ pprint ty
{-# INLINE toExportType #-}

parseTabTy :: IRRep r => Type r i -> ExportSigM r i o (Maybe (ExportType o))
parseTabTy = go []
  where
    go :: IRRep r => [ExportDim o] -> Type r i -> ExportSigM r i o (Maybe (ExportType o))
    go shape = \case
      TyCon (BaseType (Scalar sbt)) -> return $ Just $ RectContArrayPtr sbt shape
      TyCon (NewtypeTyCon Nat)    -> return $ Just $ RectContArrayPtr IdxRepScalarBaseTy shape
      TyCon (TabPi (TabPiType d (b:>ixty) a)) -> do
        maybeN <- fromIxFin $ IxType ixty d
        maybeDim <- case maybeN of
          Just (Stuck _ (Var v))    -> do
            s <- getSubst
            let (Rename v') = s ! atomVarName v
            return $ Just (ExportDimVar v')
          Just (Con (NewtypeCon NatCon (IdxRepVal s))) -> return $ Just (ExportDimLit $ fromIntegral s)
          Just (IdxRepVal s) -> return $ Just (ExportDimLit $ fromIntegral s)
          _        -> return Nothing
        case maybeDim of
          Just dim -> case hoist b a of
            HoistSuccess a' -> go (shape ++ [dim]) a'
            HoistFailure _  -> return Nothing
          Nothing -> return Nothing
      _ -> return Nothing

    fromIxFin :: IRRep r => IxType r i -> ExportSigM r i o (Maybe (Atom r i))
    fromIxFin = \case
      IxType (TyCon (NewtypeTyCon (Fin n))) (DictCon (IxFin _)) -> return $ Just n
      IxType _ (DictCon (IxRawFin n)) -> return $ Just n
      _ -> return Nothing

data ArgVisibility = ImplicitArg | ExplicitArg

data ExportDim n =
   ExportDimVar (CAtomName n)
 | ExportDimLit Int

data ExportType n = RectContArrayPtr ScalarBaseType [ExportDim n]
                  | ScalarType ScalarBaseType

data    ExportArg    n l = ExportArg    ArgVisibility (BinderP ExportAtomNameC ExportType n l)
newtype ExportResult n l = ExportResult               (BinderP ExportAtomNameC ExportType n l)
  deriving (SinkableB)
data ExportedSignature n = forall l l'.
  ExportedSignature { exportedArgSig   :: Nest ExportArg n l
                    , exportedResSig   :: Nest ExportResult l l'
                    , exportedCCallSig :: [CAtomName l']
                    }

instance GenericE ExportedSignature where
  type RepE ExportedSignature =
         (Abs (Nest ExportArg) (Abs (Nest ExportResult) (ListE CAtomName)))
  fromE (ExportedSignature x y z) = Abs x (Abs y (ListE z))
  toE   (Abs x (Abs y (ListE z))) = ExportedSignature x y z

instance HoistableE ExportedSignature

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
instance HoistableE     ExportDim
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
instance HoistableE     ExportType
instance SinkableE      ExportType

instance ToBinding ExportType ExportAtomNameC where
  toBinding = \case
    ScalarType       sbt   -> toBinding $ BaseTy $ Scalar sbt
    RectContArrayPtr sbt _ -> toBinding $ BaseTy $ PtrType (CPU, Scalar sbt)

deriving via (BinderP ExportAtomNameC ExportType) instance GenericB   ExportResult
deriving via (BinderP ExportAtomNameC ExportType) instance ProvesExt  ExportResult
deriving via (BinderP ExportAtomNameC ExportType) instance BindsNames ExportResult
deriving via (BinderP ExportAtomNameC ExportType) instance HoistableB  ExportResult
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
instance HoistableB      ExportArg

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
