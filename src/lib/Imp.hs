-- Copyright 2021 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# OPTIONS_GHC -Wno-orphans #-}

module Imp
  ( toImpFunction, ImpFunctionWithRecon (..)
  , toImpStandaloneFunction, toImpExportedFunction, ExportCC (..)
  , PtrBinder, impFunType, getIType) where

import Prelude hiding ((.), id)
import Data.Functor
import Data.Foldable (toList)
import Data.Text.Prettyprint.Doc (Pretty (..), hardline)
import Control.Category
import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.Writer.Strict
import qualified Data.List.NonEmpty as NE
import qualified Data.Map.Strict as M
import GHC.Exts (inline)

import Err
import MTL1
import Name
import Builder
import Syntax
import CheckType (CheckableE (..))
import Simplify (buildBlockSimplified, dceApproxBlock, emitSimplified)
import LabeledItems
import QueryType
import Util (enumerate, SnocList (..), unsnoc)
import Types.Primitives
import Types.Core
import Types.Imp
import Algebra
import RawName qualified as R

type AtomRecon = Abs (Nest (NameBinder AtomNameC)) Atom

type PtrBinder = IBinder

-- TODO: make it purely a function of the type and avoid the AtomRecon
toImpFunction :: EnvReader m
              => Backend -> CallingConvention
              -> Abs (Nest PtrBinder) Block n
              -> m n (ImpFunctionWithRecon n)
toImpFunction _ cc absBlock = liftImpM $
  translateTopLevel cc Nothing absBlock
{-# SCC toImpFunction #-}

toImpStandaloneFunction :: EnvReader m => NaryLamExpr n -> m n (ImpFunction n)
toImpStandaloneFunction lam = liftImpM $ toImpStandaloneFunction' lam
{-# SCC toImpStandaloneFunction #-}

toImpStandaloneFunction' :: NaryLamExpr o -> SubstImpM i o (ImpFunction o)
toImpStandaloneFunction' lam@(NaryLamExpr bs Pure body) = do
  ty <- naryLamExprType lam
  AbsPtrs (Abs ptrBinders argResultDest) ptrsInfo <- makeNaryLamDest ty Unmanaged
  let ptrHintTys = [(noHint, PtrType baseTy) | DestPtrInfo baseTy _ <- ptrsInfo]
  dropSubst $ buildImpFunction CInternalFun ptrHintTys \vs -> do
    argResultDest' <- applySubst (ptrBinders@@>vs) argResultDest
    (args, resultDest) <- loadArgDests argResultDest'
    extendSubst (bs @@> map SubstVal args) do
      void $ translateBlock (Just $ sink resultDest) body
      return []
toImpStandaloneFunction' (NaryLamExpr _ _ _) = error "effectful functions not implemented"

-- | Calling convention for exported function.
data ExportCC = FlatExportCC
              | XLAExportCC

data UnpackCC = FlatUnpackCC Int
              | XLAUnpackCC [FormalArg] [FormalArg]

type FormalArg = (NameHint, IType)
type ActualArg = AtomName

ccPrepareFormals :: ExportCC -> Nest IBinder n l -> [FormalArg] -> ([FormalArg], UnpackCC)
ccPrepareFormals cc args destFormals = case cc of
  FlatExportCC -> do
    (argFormals ++ destFormals, FlatUnpackCC (length argFormals))
  XLAExportCC -> ( [(getNameHint @String "out", i8pp), (getNameHint @String "in", i8pp)]
                 , XLAUnpackCC argFormals destFormals )
  where
    argFormals = nestToList ((noHint,) . iBinderType) args
    i8pp = PtrType (Heap CPU, PtrType (Heap CPU, Scalar Word8Type))

ccUnpackActuals :: Emits n => UnpackCC -> [ActualArg n] -> SubstImpM i n ([ActualArg n], [ActualArg n])
ccUnpackActuals cc actual = case cc of
  FlatUnpackCC n -> return $ splitAt n actual
  XLAUnpackCC argFormals destFormals -> case actual of
    [outsPtrName, insPtrName] -> do
      let (outsPtr, insPtr) = (IVar outsPtrName i8pp, IVar insPtrName i8pp)
      let loadPtr base i pointeeTy =
            flip cast (PtrType (Heap CPU, pointeeTy)) =<< load =<< impOffset base (IIdxRepVal $ fromIntegral i)
      args <- forM (enumerate argFormals) \(i, (_, argTy)) ->
        toAtomName <$> case argTy of
          PtrType (_, pointeeTy) -> loadPtr insPtr i pointeeTy
          _ -> load =<< loadPtr insPtr i argTy
      -- outsPtr points to the buffer when there's one output, not to the pointer array.
      ptrs <- case destFormals of
        [(_, destTy)] -> (:[]) . toAtomName <$> cast outsPtr destTy
        _ ->
          forM (enumerate destFormals) \(i, (_, destTy)) ->
            toAtomName <$> case destTy of
              PtrType (_, pointeeTy) -> loadPtr outsPtr i pointeeTy
              _ -> error "Destination arguments should all have pointer types"
      return (args, ptrs)
    _ -> error "Expected two arguments for the XLA calling convention"
  where
    toAtomName = \case
      IVar v _ -> v
      _ -> error "Expected a variable"
    i8pp = PtrType (Heap CPU, PtrType (Heap CPU, Scalar Word8Type))

toImpExportedFunction :: EnvReader m
                      => ExportCC
                      -> NaryLamExpr n
                      -> (Abs (Nest IBinder) (ListE Block) n)
                      -> m n (ImpFunction n)
toImpExportedFunction cc lam@(NaryLamExpr (NonEmptyNest fb tb) effs body) (Abs baseArgBs argRecons) = liftImpM do
  case effs of
    Pure -> return ()
    _    -> throw TypeErr "Can only export pure functions"
  let bs = Nest fb tb
  NaryPiType tbs _ resTy <- naryLamExprType lam
  (resDestAbsArgsPtrs, ptrFormals) <- refreshAbs (Abs tbs resTy) \tbs' resTy' -> do
    -- WARNING! This ties the makeDest implementation to the C API expected in export.
    -- In particular, every array has to be backend by a single pointer and pairs
    -- should be traversed left-to-right.
    AbsPtrs (Abs ptrBs' resDest') ptrInfo <- makeDest (LLVM, CPU, Unmanaged) resTy'
    let ptrFormals = ptrInfo <&> \(DestPtrInfo bt _) -> (noHint, PtrType bt)
    return (Abs tbs' (Abs ptrBs' resDest'), ptrFormals)
  let (ccFormals, ccCtx) = ccPrepareFormals cc baseArgBs ptrFormals
  dropSubst $ buildImpFunction CEntryFun ccFormals \ccActuals -> do
    (args, ptrs)   <- ccUnpackActuals ccCtx ccActuals
    resDestAbsPtrs <- applyNaryAbs (sink resDestAbsArgsPtrs) args
    resDest        <- applyNaryAbs resDestAbsPtrs            ptrs
    argAtoms <- extendSubst (baseArgBs @@> map SubstVal (Var <$> args)) $
      traverse (translateBlock Nothing) $ fromListE argRecons
    extendSubst (bs @@> map SubstVal argAtoms) do
      void $ translateBlock (Just $ sink resDest) body
      return []
{-# SCC toImpExportedFunction #-}

loadArgDests :: Emits n => NaryLamDest n -> SubstImpM i n ([Atom n], Dest n)
loadArgDests (Abs Empty resultDest) = return ([], resultDest)
loadArgDests (Abs (Nest (b:>argDest) bs) resultDest) = do
  arg <- destToAtom argDest
  restDest <- applySubst (b@>SubstVal arg) (Abs bs resultDest)
  (args, resultDest') <- loadArgDests restDest
  return (arg:args, resultDest')

storeArgDests :: Emits n => NaryLamDest n -> [Atom n] -> SubstImpM i n (Dest n)
storeArgDests (Abs Empty resultDest) [] = return resultDest
storeArgDests (Abs (Nest (b:>argDest) bs) resultDest) (x:xs) = do
  copyAtom argDest x
  restDest <- applySubst (b@>SubstVal x) (Abs bs resultDest)
  storeArgDests restDest xs
storeArgDests _ _ = error "dest/args mismatch"

data ImpFunctionWithRecon n = ImpFunctionWithRecon (ImpFunction n) (AtomRecon n)

instance GenericE ImpFunctionWithRecon where
  type RepE ImpFunctionWithRecon = PairE ImpFunction AtomRecon
  fromE (ImpFunctionWithRecon fun recon) = PairE fun recon
  {-# INLINE fromE #-}
  toE   (PairE fun recon) = ImpFunctionWithRecon fun recon
  {-# INLINE toE #-}

instance SinkableE ImpFunctionWithRecon
instance SubstE Name ImpFunctionWithRecon
instance CheckableE ImpFunctionWithRecon where
  checkE (ImpFunctionWithRecon f recon) =
    -- TODO: CheckableE instance for the recon too
    ImpFunctionWithRecon <$> checkE f <*> substM recon

instance Pretty (ImpFunctionWithRecon n) where
  pretty (ImpFunctionWithRecon f recon) =
    pretty f <> hardline <> "Reconstruction:" <> hardline <> pretty recon

-- === ImpM monad ===

type ImpBuilderEmissions = RNest ImpDecl

newtype ImpDeclEmission (n::S) (l::S) = ImpDeclEmission (ImpDecl n l)
instance ExtOutMap Env ImpDeclEmission where
  extendOutMap env (ImpDeclEmission d) = env `extendOutMap` toEnvFrag d
  {-# INLINE extendOutMap #-}
instance ExtOutFrag ImpBuilderEmissions ImpDeclEmission where
  extendOutFrag ems (ImpDeclEmission d) = RNest ems d
  {-# INLINE extendOutFrag #-}

newtype ImpM (n::S) (a:: *) =
  ImpM { runImpM' :: WriterT1 (ListE IExpr)
                       (InplaceT Env ImpBuilderEmissions HardFailM) n a }
  deriving ( Functor, Applicative, Monad, ScopeReader, Fallible, MonadFail)

type SubstImpM = SubstReaderT AtomSubstVal ImpM :: S -> S -> * -> *

instance ExtOutMap Env ImpBuilderEmissions where
  extendOutMap bindings emissions =
    bindings `extendOutMap` toEnvFrag emissions

class (ImpBuilder2 m, SubstReader AtomSubstVal m, EnvReader2 m, EnvExtender2 m)
      => Imper (m::MonadKind2) where

instance EnvReader ImpM where
  unsafeGetEnv = ImpM $ lift11 $ getOutMapInplaceT

instance EnvExtender ImpM where
  refreshAbs ab cont = ImpM $ lift11 $
    refreshAbs ab \b e -> do
      (result, ptrs) <- runWriterT1 $ runImpM' $ cont b e
      case ptrs of
        ListE [] -> return result
        _ -> error "shouldn't be able to emit pointers without `Mut`"

instance ImpBuilder ImpM where
  emitMultiReturnInstr instr = do
    Distinct <- getDistinct
    tys <- impInstrTypes instr
    -- The three cases below are all equivalent, but 0- and 1-return instructions
    -- are so common that it's worth spelling their cases out explicitly to enable
    -- more GHC optimizations.
    ImpM $ lift11 case tys of
      []   -> do
        extendTrivialSubInplaceT $ ImpDeclEmission $ ImpLet Empty instr
        return NoResults
      [ty] -> do
        OneResult <$> freshExtendSubInplaceT noHint \b ->
          (ImpDeclEmission $ ImpLet (Nest (IBinder b ty) Empty) instr, IVar (binderName b) ty)
      _ -> do
        Abs bs vs <- return $ newNames $ length tys
        let impBs = makeImpBinders bs tys
        let decl = ImpLet impBs instr
        ListE vs' <- extendInplaceT $ Abs (RNest REmpty decl) vs
        return $ MultiResult $ zipWith IVar vs' tys
    where
     makeImpBinders :: Nest (NameBinder AtomNameC) n l -> [IType] -> Nest IBinder n l
     makeImpBinders Empty [] = Empty
     makeImpBinders (Nest b bs) (ty:tys) = Nest (IBinder b ty) $ makeImpBinders bs tys
     makeImpBinders _ _ = error "zip error"

  buildScopedImp cont = ImpM $ WriterT1 \w ->
    liftM (, w) do
      Abs rdecls e <- locallyMutableInplaceT do
        Emits <- fabricateEmitsEvidenceM
        (result, (ListE ptrs)) <- runWriterT1 $ runImpM' do
           Distinct <- getDistinct
           cont
        _ <- runWriterT1 $ runImpM' do
          forM ptrs \ptr -> emitStatement $ Free ptr
        return result
      return $ Abs (unRNest rdecls) e

  extendAllocsToFree ptr = ImpM $ tell $ ListE [ptr]
  {-# INLINE extendAllocsToFree #-}

instance ImpBuilder m => ImpBuilder (SubstReaderT AtomSubstVal m i) where
  emitMultiReturnInstr instr = SubstReaderT $ lift $ emitMultiReturnInstr instr
  {-# INLINE emitMultiReturnInstr #-}
  buildScopedImp cont = SubstReaderT $ ReaderT \env ->
    buildScopedImp $ runSubstReaderT (sink env) $ cont
  {-# INLINE buildScopedImp #-}
  extendAllocsToFree ptr = SubstReaderT $ lift $ extendAllocsToFree ptr
  {-# INLINE extendAllocsToFree #-}

instance ImpBuilder m => Imper (SubstReaderT AtomSubstVal m)

liftImpM :: EnvReader m => SubstImpM n n a -> m n a
liftImpM cont = do
  env <- unsafeGetEnv
  Distinct <- getDistinct
  case runHardFail $ runInplaceT env $ runWriterT1 $
         runImpM' $ runSubstReaderT idSubst $ cont of
    (REmpty, (result, ListE [])) -> return result
    _ -> error "shouldn't be possible because of `Emits` constraint"

-- === the actual pass ===

-- We don't emit any results when a destination is provided, since they are already
-- going to be available through the dest.
translateTopLevel :: CallingConvention
                  -> MaybeDest o
                  -> Abs (Nest PtrBinder) Block i
                  -> SubstImpM i o (ImpFunctionWithRecon o)
translateTopLevel cc maybeDest (Abs bs body) = do
  let argTys = nestToList (\b -> (getNameHint b, iBinderType b)) bs
  ab  <- buildImpNaryAbs argTys \vs ->
    extendSubst (bs @@> map Rename vs) do
      outDest <- case maybeDest of
        Nothing   -> makeAllocDest Unmanaged =<< getTypeSubst body
        Just dest -> sinkM dest
      void $ translateBlock (Just outDest) body
      destToAtom outDest
  refreshAbs ab \bs' ab' -> refreshAbs ab' \decls resultAtom -> do
    (results, recon) <- buildRecon (PairB bs' decls) resultAtom
    let funImpl = Abs bs' $ ImpBlock decls results
    let funTy   = IFunType cc (nestToList iBinderType bs') (map getIType results)
    return $ ImpFunctionWithRecon (ImpFunction funTy funImpl) recon

buildRecon :: (HoistableB b, EnvReader m)
           => b n l
           -> Atom l
           -> m l ([IExpr l], AtomRecon n)
buildRecon b x = do
  let (vs, recon) = captureClosure b x
  xs <- forM vs \v -> do
    ~(BaseTy ty) <- getType $ Var v
    return $ IVar v ty
  return (xs, recon)

translateBlock :: forall i o. Emits o
               => MaybeDest o -> Block i -> SubstImpM i o (Atom o)
translateBlock dest (Block _ decls result) = translateDeclNest decls $ translateExpr dest $ Atom result

translateDeclNestSubst :: Emits o => Subst AtomSubstVal l o -> Nest Decl l i' -> SubstImpM i o (Subst AtomSubstVal i' o)
translateDeclNestSubst !s = \case
  Empty -> return s
  Nest (Let b (DeclBinding _ _ expr)) rest -> do
    x <- withSubst s $ translateExpr Nothing expr
    translateDeclNestSubst (s <>> (b@>SubstVal x)) rest

translateDeclNest :: Emits o => Nest Decl i i' -> SubstImpM i' o a -> SubstImpM i o a
translateDeclNest decls cont = do
  s  <- getSubst
  s' <- translateDeclNestSubst s decls
  withSubst s' cont
{-# INLINE translateDeclNest #-}

translateExpr :: Emits o => MaybeDest o -> Expr i -> SubstImpM i o (Atom o)
translateExpr maybeDest expr = confuseGHC >>= \_ -> case expr of
  Hof hof -> toImpHof maybeDest hof
  App f' xs' -> do
    f <- substM f'
    xs <- mapM substM xs'
    case f of
      Var v -> lookupAtomName v >>= \case
        TopFunBound _ (FFITopFun v') -> do
          resultTy <- getType $ App f xs
          scalarArgs <- liftM toList $ mapM fromScalarAtom xs
          results <- impCall v' scalarArgs
          restructureScalarOrPairType resultTy results
        TopFunBound piTy (SpecializedTopFun _) -> do
          if length (toList xs') /= numNaryPiArgs piTy
            then notASimpExpr
            else do
              Just fImp <- queryImpCache v
              result <- emitCall piTy fImp $ toList xs
              returnVal result
        _ -> notASimpExpr
      _ -> notASimpExpr
  TabApp f' xs' -> do
    f <- substM f'
    xs <- mapM substM xs'
    case fromNaryTabLamExact (length xs) f of
      Just (NaryLamExpr bs _ body) -> do
        let subst = bs @@> fmap SubstVal xs
        body' <- applySubst subst body
        dropSubst $ translateBlock maybeDest body'
      _ -> notASimpExpr
  Atom x -> substM x >>= returnVal
  -- Inlining the traversal helps GHC sink the substM below the case inside toImpOp.
  Op op -> (inline traversePrimOp) substM op >>= toImpOp maybeDest
  Case e alts ty _ -> do
    e' <- substM e
    case trySelectBranch e' of
      Just (con, args) -> do
        Abs bs body <- return $ alts !! con
        extendSubst (bs @@> map SubstVal args) $ translateBlock maybeDest body
      Nothing -> case e' of
        Con (SumAsProd _ tag xss) -> do
          tag' <- fromScalarAtom tag
          dest <- allocDest maybeDest =<< substM ty
          emitSwitch tag' (zip xss alts) $
            \(xs, Abs bs body) ->
               void $ extendSubst (bs @@> map (SubstVal . sink) xs) $
                 translateBlock (Just $ sink dest) body
          destToAtom dest
        _ -> error "not possible"
  where
    notASimpExpr = error $ "not a simplified expression: " ++ pprint expr
    returnVal atom = case maybeDest of
      Nothing   -> return atom
      Just dest -> copyAtom dest atom >> return atom

toImpOp :: forall i o .
           Emits o => MaybeDest o -> PrimOp (Atom o) -> SubstImpM i o (Atom o)
toImpOp maybeDest op = case op of
  TabCon ty rows -> do
    TabPi (TabPiType b _) <- return ty
    let ixTy = binderAnn b
    resultTy <- resultTyM
    dest <- allocDest maybeDest resultTy
    forM_ (zip [0..] rows) \(i, row) -> do
      ithDest <- destGet dest =<< unsafeFromOrdinalImp ixTy (IIdxRepVal i)
      copyAtom ithDest row
    destToAtom dest
  PrimEffect refDest m -> do
    case m of
      MAsk -> returnVal =<< destToAtom refDest
      MExtend (BaseMonoid _ combine) x -> do
        xTy <- getType x
        refVal <- destToAtom refDest
        result <- liftBuilderImp $
                    liftMonoidCombine (sink xTy) (sink combine) (sink refVal) (sink x)
        copyAtom refDest result
        returnVal UnitVal
      MPut x -> copyAtom refDest x >> returnVal UnitVal
      MGet -> do
        resultTy <- resultTyM
        dest <- allocDest maybeDest resultTy
        -- It might be more efficient to implement a specialized copy for dests
        -- than to go through a general purpose atom.
        copyAtom dest =<< destToAtom refDest
        destToAtom dest
    where
      liftMonoidCombine :: Emits n => Type n -> Atom n -> Atom n -> Atom n -> BuilderM n (Atom n)
      liftMonoidCombine accTy bc x y = do
        Pi baseCombineTy <- getType bc
        let baseTy = argType baseCombineTy
        alphaEq accTy baseTy >>= \case
          -- Immediately beta-reduce, beacuse Imp doesn't reduce non-table applications.
          True -> do
            Lam (BinaryLamExpr xb yb body) <- return bc
            body' <- applySubst (xb @> SubstVal x <.> yb @> SubstVal y) body
            emitBlock body'
          False -> case accTy of
            TabTy (b:>ixTy) eltTy -> do
              buildFor noHint Fwd ixTy \i -> do
                xElt <- tabApp (sink x) (Var i)
                yElt <- tabApp (sink y) (Var i)
                eltTy' <- applySubst (b@>i) eltTy
                liftMonoidCombine eltTy' (sink bc) xElt yElt
            _ -> error $ "Base monoid type mismatch: can't lift " ++
                   pprint baseTy ++ " to " ++ pprint accTy
  IndexRef refDest i -> returnVal =<< destGet refDest i
  ProjRef i ~(Con (ConRef (ProdCon refs))) -> returnVal $ refs !! i
  IOAlloc ty n -> do
    ptr <- emitAlloc (Heap CPU, ty) =<< fromScalarAtom n
    returnVal =<< toScalarAtom ptr
  IOFree ptr -> do
    ptr' <- fromScalarAtom ptr
    emitStatement $ Free ptr'
    return UnitVal
  PtrOffset arr (IdxRepVal 0) -> returnVal arr
  PtrOffset arr off -> do
    arr' <- fromScalarAtom arr
    off' <- fromScalarAtom off
    buf <- impOffset arr' off'
    returnVal =<< toScalarAtom buf
  PtrLoad arr ->
    returnVal =<< toScalarAtom =<< loadAnywhere =<< fromScalarAtom arr
  PtrStore ptr x -> do
    ptr' <- fromScalarAtom ptr
    x'   <- fromScalarAtom x
    store ptr' x'
    return UnitVal
  ThrowError _ -> do
    resultTy <- resultTyM
    dest <- allocDest maybeDest resultTy
    emitStatement IThrowError
    -- XXX: we'd be reading uninitialized data here but it's ok because control never reaches
    -- this point since we just threw an error.
    destToAtom dest
  CastOp destTy x -> do
    sourceTy <- getType x
    case (sourceTy, destTy) of
      (BaseTy _, BaseTy bt) -> do
        x' <- fromScalarAtom x
        returnVal =<< toScalarAtom =<< cast x' bt
      (TC (Fin _), IdxRepTy) -> do
        let Con (FinVal _ xord) = x
        returnVal xord
      (IdxRepTy, TC (Fin n)) ->
        returnVal $ Con $ FinVal n x
      _ -> error $ "Invalid cast: " ++ pprint sourceTy ++ " -> " ++ pprint destTy
  Select p x y -> do
    xTy <- getType x
    case xTy of
      BaseTy _ -> do
        p' <- fromScalarAtom p
        x' <- fromScalarAtom x
        y' <- fromScalarAtom y
        ans <- emitInstr $ IPrimOp $ Select p' x' y'
        returnVal =<< toScalarAtom ans
      _ -> unsupported
  DataConTag con -> case con of
    Con (SumAsProd _ tag _) -> returnVal tag
    DataCon _ _ _ i _ -> returnVal $ TagRepVal $ fromIntegral i
    _ -> error $ "Not a data constructor: " ++ pprint con
  ToEnum ty i -> returnVal =<< case ty of
    TypeCon _ defName _ -> do
      DataDef _ _ cons <- lookupDataDef defName
      return $ Con $ SumAsProd ty i (map (const []) cons)
    VariantTy (NoExt labeledItems) ->
      return $ Con $ SumAsProd ty i (map (const [UnitVal]) $ toList labeledItems)
    SumTy cases ->
      return $ Con $ SumAsProd ty i $ cases <&> const [UnitVal]
    _ -> error $ "Not an enum: " ++ pprint ty
  SumToVariant ~(Con c) -> do
    ~resultTy@(VariantTy labs) <- resultTyM
    returnVal $ case c of
      SumCon    _ tag payload -> Variant labs "c" tag payload
      SumAsProd _ tag payload -> Con $ SumAsProd resultTy tag payload
      _ -> error $ "Not a sum type: " ++ pprint (Con c)
  AllocDest ty  -> returnVal =<< alloc ty
  Place ref val -> copyAtom ref val >> returnVal UnitVal
  Freeze ref -> destToAtom ref
  -- Listing branches that should be dead helps GHC cut down on code size.
  ThrowException _        -> unsupported
  RecordCons _ _          -> unsupported
  RecordSplit _ _         -> unsupported
  RecordConsDynamic _ _ _ -> unsupported
  RecordSplitDynamic _ _  -> unsupported
  VariantLift _ _         -> unsupported
  VariantSplit _ _        -> unsupported
  ProjMethod _ _          -> unsupported
  ExplicitApply _ _       -> unsupported
  VectorBroadcast val vty -> do
    val' <- fromScalarAtom val
    emitInstr (IVectorBroadcast val' $ toIVectorType vty) >>= toScalarAtom >>= returnVal
  VectorIota vty -> emitInstr (IVectorIota $ toIVectorType vty) >>= toScalarAtom >>= returnVal
  VectorSubref ref i vty -> do
    Con (BaseTypeRef refi) <- liftBuilderImp $ indexDest (sink ref) (sink i)
    refi' <- fromScalarAtom refi
    let PtrType (addrSpace, _) = getIType refi'
    returnVal =<< case vty of
      BaseTy vty'@(Vector _ _) -> do
        Con . BaseTypeRef <$> (toScalarAtom =<< cast refi' (PtrType (addrSpace, vty')))
      _ -> error "Expected a vector type"
  _ -> do
    instr <- IPrimOp <$> (inline traversePrimOp) fromScalarAtom op
    emitInstr instr >>= toScalarAtom >>= returnVal
  where
    unsupported = error $ "Unsupported PrimOp encountered in Imp" ++ pprint op
    resultTyM :: SubstImpM i o (Type o)
    resultTyM = getType $ Op op
    returnVal atom = case maybeDest of
      Nothing   -> return atom
      Just dest -> copyAtom dest atom >> return atom

toImpHof :: Emits o => Maybe (Dest o) -> PrimHof (Atom i) -> SubstImpM i o (Atom o)
toImpHof maybeDest hof = do
  resultTy <- getTypeSubst (Hof hof)
  case hof of
    For d ixDict (Lam (LamExpr b body)) -> do
      ixTy <- ixTyFromDict =<< substM ixDict
      n <- indexSetSizeImp ixTy
      dest <- allocDest maybeDest resultTy
      emitLoop (getNameHint b) d n \i -> do
        idx <- unsafeFromOrdinalImp (sink ixTy) i
        ithDest <- destGet (sink dest) idx
        void $ extendSubst (b @> SubstVal idx) $
          translateBlock (Just ithDest) body
      destToAtom dest
    While (Lam (LamExpr b body)) -> do
      body' <- buildBlockImp $ extendSubst (b@>SubstVal UnitVal) do
        ans <- fromScalarAtom =<< translateBlock Nothing body
        return [ans]
      emitStatement $ IWhile body'
      return UnitVal
    RunReader r (Lam (BinaryLamExpr h ref body)) -> do
      r' <- substM r
      rDest <- alloc =<< getType r'
      copyAtom rDest r'
      extendSubst (h @> SubstVal UnitTy <.> ref @> SubstVal rDest) $
        translateBlock maybeDest body
    RunWriter (BaseMonoid e _) (Lam (BinaryLamExpr h ref body)) -> do
      let PairTy _ accTy = resultTy
      (aDest, wDest) <- destPairUnpack <$> allocDest maybeDest resultTy
      e' <- substM e
      emptyVal <- liftBuilderImp do
        PairE accTy' e'' <- sinkM $ PairE accTy e'
        liftMonoidEmpty accTy' e''
      copyAtom wDest emptyVal
      void $ extendSubst (h @> SubstVal UnitTy <.> ref @> SubstVal wDest) $
        translateBlock (Just aDest) body
      PairVal <$> destToAtom aDest <*> destToAtom wDest
    RunState s (Lam (BinaryLamExpr h ref body)) -> do
      s' <- substM s
      (aDest, sDest) <- destPairUnpack <$> allocDest maybeDest resultTy
      copyAtom sDest s'
      void $ extendSubst (h @> SubstVal UnitTy <.> ref @> SubstVal sDest) $
        translateBlock (Just aDest) body
      PairVal <$> destToAtom aDest <*> destToAtom sDest
    RunIO (Lam (LamExpr b body)) ->
      extendSubst (b@>SubstVal UnitVal) $
        translateBlock maybeDest body
    Seq d ixDict carry (Lam (LamExpr b body)) -> do
      ixTy <- ixTyFromDict =<< substM ixDict
      carry' <- substM carry
      n <- indexSetSizeImp ixTy
      emitLoop (getNameHint b) d n \i -> do
        idx <- unsafeFromOrdinalImp (sink ixTy) i
        void $ extendSubst (b @> SubstVal (PairVal idx (sink carry'))) $
          translateBlock Nothing body
      case maybeDest of
        Nothing -> return carry'
        Just _  -> error "Unexpected dest"
    _ -> error $ "not implemented: " ++ pprint hof
    where
      liftMonoidEmpty :: Type n -> Atom n -> BuilderM n (Atom n)
      liftMonoidEmpty accTy x = do
        xTy <- getType x
        alphaEq xTy accTy >>= \case
          True -> return x
          False -> case accTy of
            TabTy (b:>ixTy) eltTy -> do
              buildTabLam noHint ixTy \i -> do
                x' <- sinkM x
                ab <- sinkM $ Abs b eltTy
                eltTy' <- applyAbs ab i
                liftMonoidEmpty eltTy' x'
            _ -> error $ "Base monoid type mismatch: can't lift " ++
                  pprint xTy ++ " to " ++ pprint accTy


-- === Destination builder monad ===

-- It's shame to have to reimplement so much for this DestM monad. The problem
-- is that `makeDestRec` is emitting two sorts of names: (1) decls to compute
-- indexing offsets (often under a table lambda) and (2) pointer names, with
-- sizes, for the buffers themselves. The emissions are interleaved, but we're
-- really dealing with two separate scopes: the pointer binders are always
-- hoistable above the decls. Ideally we'd have a system with two scope
-- parameters, where you can separately emit into either. The types would then
-- look like this:

--   makeDestRec :: Idxs n -> Abs IdxNest Type n -> DestM n l (Dest l)
--   emitDecl    :: Expr  l -> DestM n l (AtomName l)
--   emitPointer :: Block n -> DestM n l (AtomName n)

data DestPtrInfo n = DestPtrInfo PtrType (Block n)
type PtrBinders  = Nest  AtomNameBinder
type RPtrBinders = RNest AtomNameBinder
data DestEmissions n l where
  DestEmissions
    :: {-# UNPACK #-} !(DestPtrEmissions n h)  -- pointers to allocate
    ->                !(RNest Decl h l)        -- decls to compute indexing offsets
    -> DestEmissions n l

instance GenericB DestEmissions where
  type RepB DestEmissions = DestPtrEmissions `PairB` RNest Decl
  fromB (DestEmissions bs ds) = bs `PairB` ds
  {-# INLINE fromB #-}
  toB   (bs `PairB` ds) = DestEmissions bs ds
  {-# INLINE toB #-}
instance ProvesExt   DestEmissions
instance BindsNames  DestEmissions
instance SinkableB DestEmissions
instance SubstB Name DestEmissions
instance HoistableB  DestEmissions

instance BindsEnv DestEmissions where
  toEnvFrag (DestEmissions ptrs decls) =
    withSubscopeDistinct decls $
      toEnvFrag ptrs `catEnvFrags` toEnvFrag decls

instance ExtOutMap Env DestEmissions where
  extendOutMap bindings emissions = bindings `extendOutMap` toEnvFrag emissions

instance OutFrag DestEmissions where
  emptyOutFrag = emptyDestEmissions
  {-# INLINE emptyOutFrag #-}
  catOutFrags _ = catDestEmissions
  {-# INLINE catOutFrags #-}

emptyDestEmissions :: DestEmissions n n
emptyDestEmissions = DestEmissions emptyOutFrag REmpty
{-# NOINLINE [1] emptyDestEmissions #-}

catDestEmissions :: Distinct l => DestEmissions n h -> DestEmissions h l -> DestEmissions n l
catDestEmissions (DestEmissions ptrs1 d1) (DestEmissions ptrs2 d2) =
  case withSubscopeDistinct d2 $ ignoreHoistFailure $ exchangeBs $ PairB d1 ptrs2 of
    PairB ptrs2' d1' -> DestEmissions (ptrs1 >>> ptrs2') (d1' >>> d2)
{-# NOINLINE [1] catDestEmissions #-}
{-# RULES
      "catDestEmissions Empty *"  forall e. catDestEmissions emptyDestEmissions e = e;
      "catDestEmissions * Empty"  forall e. catDestEmissions e emptyDestEmissions = e;
      "catDestEmissions reassoc"  forall e1 e2 e3. catDestEmissions e1 (catDestEmissions e2 e3) = withSubscopeDistinct e3 (catDestEmissions (catDestEmissions e1 e2) e3)
  #-}

newtype DestDeclEmissions (n::S) (l::S)
  = DestDeclEmissions (Decl n l)
  deriving (ProvesExt, BindsNames, SinkableB, SubstB Name)
instance ExtOutMap Env DestDeclEmissions where
  extendOutMap env (DestDeclEmissions decl) = env `extendOutMap` toEnvFrag decl
instance ExtOutFrag DestEmissions DestDeclEmissions where
  extendOutFrag (DestEmissions p d) (DestDeclEmissions d') = DestEmissions p $ RNest d d'
  {-# INLINE extendOutFrag #-}

data DestPtrEmissions (n::S) (l::S)
  = DestPtrEmissions (SnocList (DestPtrInfo n))  -- pointer types and allocation sizes
                     (RPtrBinders n l)           -- pointer binders for allocations we require

instance GenericB DestPtrEmissions where
  type RepB DestPtrEmissions = LiftB (ListE DestPtrInfo) `PairB` RPtrBinders
  fromB (DestPtrEmissions (ReversedList i) b) = (LiftB (ListE i)) `PairB` b
  toB   ((LiftB (ListE i)) `PairB` b) = DestPtrEmissions (ReversedList i) b
instance ProvesExt   DestPtrEmissions
instance BindsNames  DestPtrEmissions
instance SinkableB   DestPtrEmissions
instance HoistableB  DestPtrEmissions
instance SubstB Name DestPtrEmissions

instance Category DestPtrEmissions where
  id = DestPtrEmissions mempty emptyOutFrag
  (DestPtrEmissions i2 b2) . (DestPtrEmissions i1 b1) = DestPtrEmissions i' b'
    where
      i' = i1 <> (ReversedList $ fromListE $ ignoreHoistFailure $ hoist b1 $ ListE $ fromReversedList i2)
      b' = b1 >>> b2
  {-# INLINE (.) #-}
instance OutFrag DestPtrEmissions where
  emptyOutFrag = id
  {-# INLINE emptyOutFrag #-}
  catOutFrags _ = (>>>)
  {-# INLINE catOutFrags #-}

instance BindsEnv DestPtrEmissions where
  toEnvFrag (DestPtrEmissions ptrInfo ptrs) = ptrBindersToEnvFrag ptrInfo ptrs
    where
      ptrBindersToEnvFrag :: Distinct l => SnocList (DestPtrInfo n) -> RNest AtomNameBinder n l -> EnvFrag n l
      ptrBindersToEnvFrag (ReversedList []) REmpty = emptyOutFrag
      ptrBindersToEnvFrag (ReversedList (DestPtrInfo ty _ : rest)) (RNest restBs b) =
        withSubscopeDistinct b do
          let frag1 = toEnvFrag $ b :> PtrTy ty
          let frag2 = withExtEvidence (toExtEvidence b) $
                         ptrBindersToEnvFrag (ReversedList rest) restBs
          frag2 `catEnvFrags` frag1
      ptrBindersToEnvFrag _ _ = error "mismatched indices"

instance ExtOutFrag DestEmissions DestPtrEmissions where
  extendOutFrag (DestEmissions ptrs d) emissions =
    case ignoreHoistFailure $ exchangeBs $ PairB d emissions of
      PairB emissions' d' -> DestEmissions (ptrs >>> emissions') d'
  {-# INLINE extendOutFrag #-}

instance ExtOutMap Env DestPtrEmissions where
  extendOutMap bindings emissions = bindings `extendOutMap` toEnvFrag emissions


newtype DestM (n::S) (a:: *) =
  DestM { runDestM' :: (InplaceT Env DestEmissions
                         (ReaderT AllocInfo HardFailM)) n a }
  deriving ( Functor, Applicative, Monad, MonadFail
           , ScopeReader, Fallible, EnvReader, EnvExtender )

liftDestM :: forall m n a. EnvReader m
          => AllocInfo
          -> DestM n a
          -> m n a
liftDestM allocInfo m = do
  env <- unsafeGetEnv
  Distinct <- getDistinct
  let result = runHardFail $ flip runReaderT allocInfo $
                 runInplaceT env $ runDestM' m
  case result of
    (DestEmissions (DestPtrEmissions (ReversedList []) REmpty) REmpty, result') -> return result'
    _ -> error "not implemented"
{-# INLINE liftDestM #-}

getAllocInfo :: DestM n AllocInfo
getAllocInfo = DestM $ lift1 ask
{-# INLINE getAllocInfo #-}

introduceNewPtr :: Mut n => NameHint -> PtrType -> Block n -> DestM n (AtomName n)
introduceNewPtr hint ptrTy numel =
  DestM $ freshExtendSubInplaceT hint \b ->
    (DestPtrEmissions (ReversedList [DestPtrInfo ptrTy numel]) $ RNest REmpty b, binderName b)

buildLocalDest
  :: (SinkableE e)
  => (forall l. (Mut l, DExt n l) => DestM l (e l))
  -> DestM n (AbsPtrs e n)
buildLocalDest cont = do
  Abs (DestEmissions (DestPtrEmissions ptrInfo ptrBs) decls) e <-
    DestM do
      Abs bs e <- locallyMutableInplaceT $ runDestM' cont
      return $ Abs bs e
  case decls of
    REmpty -> return $ AbsPtrs (Abs (unRNest ptrBs) e) $ unsnoc ptrInfo
    _ -> error "shouldn't have decls without `Emits`"

-- TODO: this is mostly copy-paste from Inference
buildDeclsDest
  :: (Mut n, SubstE Name e, SinkableE e)
  => (forall l. (Emits l, DExt n l) => DestM l (e l))
  -> DestM n (Abs (Nest Decl) e n)
buildDeclsDest cont = do
  DestM do
    Abs (DestEmissions ptrs decls) result <- locallyMutableInplaceT do
      Emits <- fabricateEmitsEvidenceM
      runDestM' cont
    Abs decls' e <- extendSubInplaceT $ Abs ptrs $ Abs decls result
    return $ Abs (unRNest decls') e
{-# INLINE buildDeclsDest #-}

buildBlockDest
  :: Mut n
  => (forall l. (Emits l, DExt n l) => DestM l (Atom l))
  -> DestM n (Block n)
buildBlockDest cont = buildDeclsDest (cont >>= withType) >>= computeAbsEffects >>= absToBlock
{-# INLINE buildBlockDest #-}

-- TODO: this is mostly copy-paste from Inference
buildAbsDest
  :: (SinkableE e, SubstE Name e, HoistableE e, Color c, ToBinding binding c)
  => Mut n
  => NameHint -> binding n
  -> (forall l. (Mut l, DExt n l) => Name c l -> DestM l (e l))
  -> DestM n (Abs (BinderP c binding) e n)
buildAbsDest hint binding cont = DestM do
  resultWithEmissions <- withFreshBinder hint binding \b -> do
    ab <- locallyMutableInplaceT do
      runDestM' $ cont $ sink $ binderName b
    refreshAbs ab \emissions result -> do
      PairB emissions' b' <- liftHoistExcept $ exchangeBs $ PairB b emissions
      return $ Abs emissions' $ Abs b' result
  Abs b e <- extendInplaceT resultWithEmissions
  return $ Abs (b:>binding) e

-- decls emitted at the inner scope are hoisted to the outer scope
-- (they must be hoistable, otherwise we'll get a hoisting error)
buildAbsHoistingDeclsDest
  :: (SinkableE e, SubstE Name e, HoistableE e, Color c, ToBinding binding c)
  => Emits n
  => NameHint -> binding n
  -> (forall l. (Emits l, DExt n l) => Name c l -> DestM l (e l))
  -> DestM n (Abs (BinderP c binding) e n)
buildAbsHoistingDeclsDest hint binding cont =
  -- XXX: here we're using the fact that `buildAbsDest` doesn't actually check
  -- that the function produces no decls (it assumes it can't because it doesn't
  -- give it `Emits`) and so it just hoists all the emissions.
  buildAbsDest hint binding \v -> do
    Emits <- fabricateEmitsEvidenceM
    cont v

buildTabLamDest
  :: Mut n
  => NameHint -> IxType n
  -> (forall l. (Emits l, DExt n l) => AtomName l -> DestM l (Atom l))
  -> DestM n (Atom n)
buildTabLamDest hint ty cont = do
  Abs (b:>_) body <- buildAbsDest hint ty \v ->
    buildBlockDest $ sinkM v >>= cont
  return $ TabLam $ TabLamExpr (b:>ty) body

instance Builder DestM where
  emitDecl hint ann expr = do
    ty <- getType expr
    DestM $ freshExtendSubInplaceT hint \b ->
      (DestDeclEmissions $ Let b $ DeclBinding ann ty expr, binderName b)
  {-# INLINE emitDecl #-}

instance GenericE DestPtrInfo where
  type RepE DestPtrInfo = PairE (LiftE PtrType) Block
  fromE (DestPtrInfo ty n) = PairE (LiftE ty) n
  toE   (PairE (LiftE ty) n) = DestPtrInfo ty n

instance SinkableE DestPtrInfo
instance HoistableE  DestPtrInfo
instance SubstE Name DestPtrInfo
instance SubstE AtomSubstVal DestPtrInfo

-- === Destination builder ===

type Dest = Atom  -- has type `Ref a` for some a
type MaybeDest n = Maybe (Dest n)

data AbsPtrs e n = AbsPtrs (Abs PtrBinders e n) [DestPtrInfo n]

instance GenericE (AbsPtrs e) where
  type RepE (AbsPtrs e) = PairE (NaryAbs AtomNameC e) (ListE DestPtrInfo)
  fromE (AbsPtrs ab ptrInfo) = PairE ab (ListE ptrInfo)
  toE   (PairE ab (ListE ptrInfo)) = AbsPtrs ab ptrInfo

instance SinkableE e => SinkableE (AbsPtrs e)
instance HoistableE e => HoistableE (AbsPtrs e)
instance SubstE Name e => SubstE Name (AbsPtrs e)
instance SubstE AtomSubstVal e => SubstE AtomSubstVal (AbsPtrs e)

-- builds a dest and a list of pointer binders along with their required allocation sizes
makeDest :: AllocInfo -> Type n -> SubstImpM i n (AbsPtrs Dest n)
makeDest allocInfo ty =
  liftDestM allocInfo $ buildLocalDest $ makeSingleDest [] $ sink ty
{-# SCC makeDest #-}

makeSingleDest :: Mut n => [AtomName n] -> Type n -> DestM n (Dest n)
makeSingleDest depVars ty = do
  Abs decls dest <- buildDeclsDest $
    makeDestRec (Abs Empty UnitE, []) (map sink depVars) (sink ty)
  case decls of
    Empty -> return dest
    _ -> error
     $ "shouldn't need to emit decls if we're not working with indices"
     ++ pprint decls

extendIdxsTy
  :: EnvReader m
  => DestIdxs n -> IxType n -> m n (EmptyAbs IdxNest n)
extendIdxsTy (idxsTy, idxs) new = do
  let newAbs = abstractFreeVarsNoAnn idxs new
  Abs bs (Abs b UnitE) <- liftBuilder $ buildNaryAbs idxsTy \idxs' -> do
    ty' <- applyNaryAbs (sink newAbs) idxs'
    singletonBinderNest noHint ty'
  return $ Abs (bs >>> b) UnitE

type Idxs n = [AtomName n]
type IdxNest = Nest IxBinder
type DestIdxs n = (EmptyAbs IdxNest n, Idxs n)
type DepVars n = [AtomName n]

-- TODO: make `DestIdxs` a proper E-kinded thing
sinkDestIdxs :: DExt n l => DestIdxs n -> DestIdxs l
sinkDestIdxs (idxsTy, idxs) = (sink idxsTy, map sink idxs)

-- dest for the args and the result
-- TODO: de-dup some of the plumbing stuff here with the ordinary makeDest path
type NaryLamDest = Abs (Nest (BinderP AtomNameC Dest)) Dest

makeNaryLamDest :: NaryPiType n -> AllocType -> SubstImpM i n (AbsPtrs NaryLamDest n)
makeNaryLamDest piTy mgmt = do
  let allocInfo = (LLVM, CPU, mgmt) -- TODO! This is just a placeholder
  liftDestM allocInfo $ buildLocalDest do
    Abs decls dest <- buildDeclsDest $
                        makeNaryLamDestRec (Abs Empty UnitE, []) [] (sink piTy)
    case decls of
      Empty -> return dest
      _ -> error "shouldn't have decls if we have empty indices"

makeNaryLamDestRec :: forall n. Emits n => DestIdxs n -> DepVars n
                   -> NaryPiType n -> DestM n (NaryLamDest n)
makeNaryLamDestRec idxs depVars (NaryPiType (NonEmptyNest b bs) Pure resultTy) = do
  let argTy = binderType b
  argDest <- makeDestRec idxs depVars argTy
  Abs (b':>_) (Abs bs' resultDest) <-
    buildDepDest idxs depVars (getNameHint b) argTy \idxs' depVars' v -> do
      case bs of
        Empty -> do
          resultTy' <- applySubst (b@>v) resultTy
          Abs Empty <$> makeDestRec idxs' depVars' resultTy'
        Nest b1 bsRest -> do
          restPiTy <- applySubst (b@>v) $ NaryPiType (NonEmptyNest b1 bsRest) Pure resultTy
          makeNaryLamDestRec idxs' depVars' restPiTy
  return $ Abs (Nest (b':>argDest) bs') resultDest
makeNaryLamDestRec _ _ _ = error "effectful functions not implemented"

-- TODO: should we put DestIdxs/DepVars in the monad? And maybe it should also
-- be a substituting one.
buildDepDest
  :: (SinkableE e, SubstE Name e, HoistableE e, Emits n)
  => DestIdxs n -> DepVars n -> NameHint -> Type n
  -> (forall l. (Emits l, DExt n l) => DestIdxs l -> DepVars l -> AtomName l -> DestM l (e l))
  -> DestM n (Abs Binder e n)
buildDepDest idxs depVars hint ty cont =
  buildAbsHoistingDeclsDest hint ty \v -> do
    let depVars' = map sink depVars ++ [v]
    cont (sinkDestIdxs idxs) depVars' v

-- `makeDestRec` builds an array of dests. The curried index type, `EmptyAbs
-- IdxNest n`, determines a set of valid indices, `Idxs n`. At each valid value
-- of `Idxs n` we should have a distinct dest. The `depVars` are a list of
-- variables whose values we won't know until we actually store something. The
-- resulting `Dest n` may mention these variables, but the pointer allocation
-- sizes can't.
makeDestRec :: forall n. Emits n => DestIdxs n -> DepVars n -> Type n -> DestM n (Dest n)
makeDestRec idxs depVars ty = confuseGHC >>= \_ -> case ty of
  TabTy (b:>iTy) bodyTy -> do
    if depVars `anyFreeIn` iTy
      then do
        AbsPtrs (Abs bs dest) ptrsInfo <- buildLocalDest $ makeSingleDest [] $ sink ty
        ptrs <- forM ptrsInfo \(DestPtrInfo ptrTy size) -> do
                  ptr <- makeBaseTypePtr idxs (PtrType ptrTy)
                  return $ BoxPtr ptr size
        return $ BoxedRef $ Abs (NonDepNest bs ptrs) dest
      else do
        Distinct <- getDistinct
        idxsTy <- extendIdxsTy idxs iTy
        Con <$> TabRef <$> buildTabLamDest noHint iTy \v -> do
          let newIdxVals = map sink (snd idxs) <> [v]
          bodyTy' <- applyAbs (sink $ Abs b bodyTy) v
          makeDestRec (sink idxsTy, newIdxVals) (map sink depVars) bodyTy'
  TypeCon _ defName params -> do
    def <- lookupDataDef defName
    dcs <- instantiateDataDef def params
    case dcs of
      [] -> error "Void type not allowed"
      [DataConDef _ dataConBinders] -> do
        Distinct <- getDistinct
        dests <- makeDataConDest depVars dataConBinders
        return $ DataConRef defName params dests
        where
          makeDataConDest :: (Emits l, DExt n l)
                          => [AtomName l]
                          -> EmptyAbs (Nest Binder) l
                          -> DestM l (EmptyAbs (Nest DataConRefBinding) l)
          makeDataConDest depVars' (Abs bs UnitE) = case bs of
            Empty -> return $ EmptyAbs Empty
            Nest (b:>bTy) rest -> do
              dest <- makeDestRec (sinkDestIdxs idxs) depVars' bTy
              Abs b' (EmptyAbs restDest) <- buildAbsHoistingDeclsDest (getNameHint b) bTy \v -> do
                let depVars'' = map sink depVars' ++ [v]
                rest' <- applySubst (b@>v) $ EmptyAbs rest
                makeDataConDest depVars'' rest'
              return $ EmptyAbs $ Nest (DataConRefBinding b' dest) restDest
      _ -> do
        tag <- rec TagRepTy
        contents <- forM dcs \dc -> case nonDepDataConTys dc of
          Nothing -> error "Dependent data constructors only allowed for single-constructor types"
          Just tys -> mapM (makeDestRec idxs depVars) tys
        return $ Con $ ConRef $ SumAsProd ty tag contents
  DepPairTy depPairTy@(DepPairType (lBinder:>lTy) rTy) -> do
    lDest <- rec lTy
    rDestAbs <- buildDepDest idxs depVars (getNameHint lBinder) lTy \idxs' depVars' v -> do
      rTy' <- applySubst (lBinder@>v) rTy
      makeDestRec idxs' depVars' rTy'
    return $ DepPairRef lDest rDestAbs depPairTy
  StaticRecordTy types -> (Con . RecordRef) <$> forM types rec
  VariantTy (NoExt types) -> recSumType $ toList types
  TC con -> case con of
    BaseType b -> do
      ptr <- makeBaseTypePtr idxs b
      return $ Con $ BaseTypeRef ptr
    SumType cases -> recSumType cases
    ProdType tys  -> (Con . ConRef) <$> (ProdCon <$> traverse rec tys)
    Fin n -> do
      x <- rec IdxRepTy
      return $ Con $ ConRef $ FinVal n x
    _ -> error $ "not implemented: " ++ pprint con
  _ -> error $ "not implemented: " ++ pprint ty
  where
    rec = makeDestRec idxs depVars

    recSumType cases = do
      tag <- rec TagRepTy
      contents <- forM cases rec
      return $ Con $ ConRef $ SumAsProd ty tag $ map (\x->[x]) contents

makeBaseTypePtr :: Emits n => DestIdxs n -> BaseType -> DestM n (Atom n)
makeBaseTypePtr (idxsTy, idxs) ty = do
  offset <- liftEmitBuilder $ computeOffset idxsTy idxs
  numel <- liftBuilder $ buildBlock $ computeElemCount (sink idxsTy)
  allocInfo <- getAllocInfo
  let addrSpace = chooseAddrSpace allocInfo numel
  let ptrTy = (addrSpace, ty)
  ptr <- Var <$> introduceNewPtr (getNameHint @String "ptr") ptrTy numel
  ptrOffset ptr offset
{-# SCC makeBaseTypePtr #-}

copyAtom :: Emits n => Dest n -> Atom n -> SubstImpM i n ()
copyAtom topDest topSrc = copyRec topDest topSrc
  where
    copyRec :: Emits n => Dest n -> Atom n -> SubstImpM i n ()
    copyRec dest src = confuseGHC >>= \_ -> case (dest, src) of
      (BoxedRef (Abs (NonDepNest bs ptrsSizes) boxedDest), _) -> do
        -- TODO: load old ptr and free (recursively)
        ptrs <- forM ptrsSizes \(BoxPtr ptrPtr sizeBlock) -> do
          PtrTy (_, (PtrType ptrTy)) <- getType ptrPtr
          size <- dropSubst $ translateBlock Nothing sizeBlock
          ptr <- emitAlloc ptrTy =<< fromScalarAtom size
          ptrPtr' <- fromScalarAtom ptrPtr
          storeAnywhere ptrPtr' ptr
          toScalarAtom ptr
        dest' <- applySubst (bs @@> map SubstVal ptrs) boxedDest
        copyRec dest' src
      (DepPairRef lRef rRefAbs _, DepPair l r _) -> do
        copyAtom lRef l
        rRef <- applyAbs rRefAbs (SubstVal l)
        copyAtom rRef r
      (DataConRef _ _ refs, DataCon _ _ _ _ vals) ->
        copyDataConArgs refs vals
      (Con destRefCon, _) -> case (destRefCon, src) of
        (RecordRef refs, Record vals)
          | fmap (const ()) refs == fmap (const ()) vals -> do
              zipWithM_ copyRec (toList refs) (toList vals)
        (TabRef _, TabLam _) -> zipTabDestAtom copyRec dest src
        (BaseTypeRef ptr, _) -> do
          ptr' <- fromScalarAtom ptr
          src' <- fromScalarAtom src
          storeAnywhere ptr' src'
        (ConRef (SumAsProd _ tag payload), _) -> case src of
          DataCon _ _ _ con x -> do
            copyRec tag $ TagRepVal $ fromIntegral con
            zipWithM_ copyRec (payload !! con) x
          Con (SumAsProd _ tagSrc payloadSrc) -> do
            copyRec tag tagSrc
            unless (all null payload) do -- optimization
              tagSrc' <- fromScalarAtom tagSrc
              emitSwitch tagSrc' (zip payload payloadSrc)
                \(d, s) -> zipWithM_ copyRec (map sink d) (map sink s)
          SumVal _ con x -> do
            copyRec tag $ TagRepVal $ fromIntegral con
            case payload !! con of
              [xDest] -> copyRec xDest x
              _       -> error "Expected singleton payload in SumAsProd"
          Variant (NoExt types) label i x -> do
            let LabeledItems ixtypes = enumerate types
            let index = fst $ (ixtypes M.! label) NE.!! i
            copyRec tag (TagRepVal $ fromIntegral index)
            zipWithM_ copyRec (payload !! index) [x]
          _ -> error "unexpected src/dest pair"
        (ConRef destCon, Con srcCon) -> case (destCon, srcCon) of
          (ProdCon ds, ProdCon ss) -> zipWithM_ copyRec ds ss
          (FinVal _ iRef, FinVal _ i) -> copyRec iRef i
          _ -> error $ "Unexpected ref/val " ++ pprint (destCon, srcCon)
        _ -> error "unexpected src/dest pair"
      _ -> error "unexpected src/dest pair"

    zipTabDestAtom :: Emits n
                   => (forall l. (Emits l, DExt n l) => Dest l -> Atom l -> SubstImpM i l ())
                   -> Dest n -> Atom n -> SubstImpM i n ()
    zipTabDestAtom f dest src = do
      Con (TabRef (TabLam (TabLamExpr b _))) <- return dest
      TabLam (TabLamExpr b' _)               <- return src
      checkAlphaEq (binderType b) (binderType b')
      let idxTy = binderAnn b
      n <- indexSetSizeImp idxTy
      emitLoop noHint Fwd n \i -> do
        idx <- unsafeFromOrdinalImp (sink idxTy) i
        destIndexed <- destGet (sink dest) idx
        srcIndexed  <- dropSubst $ translateExpr Nothing (TabApp (sink src) (idx:|[]))
        f destIndexed srcIndexed

    copyDataConArgs :: Emits n
                    => EmptyAbs (Nest DataConRefBinding) n -> [Atom n] -> SubstImpM i n ()
    copyDataConArgs (Abs Empty UnitE) [] = return ()
    copyDataConArgs (Abs (Nest (DataConRefBinding b ref) rest) UnitE) (x:xs) = do
      copyAtom ref x
      rest' <- applySubst (b@>SubstVal x) (EmptyAbs rest)
      copyDataConArgs rest' xs
    copyDataConArgs bindings args =
      error $ "Mismatched bindings/args: " ++ pprint (bindings, args)
{-# SCC copyAtom #-}

loadAnywhere :: Emits n => IExpr n -> SubstImpM i n (IExpr n)
loadAnywhere ptr = load ptr -- TODO: generalize to GPU backend

storeAnywhere :: Emits n => IExpr n -> IExpr n -> SubstImpM i n ()
storeAnywhere ptr val = store ptr val

store :: Emits n => IExpr n -> IExpr n -> SubstImpM i n ()
store dest src = emitStatement $ Store dest src

alloc :: Emits n => Type n -> SubstImpM i n (Dest n)
alloc ty = makeAllocDest Managed ty

indexDest :: Emits n => Dest n -> Atom n -> BuilderM n (Dest n)
indexDest (Con (TabRef (TabVal b body))) i = do
  body' <- applyAbs (Abs b body) $ SubstVal i
  emitBlock body'
indexDest dest _ = error $ pprint dest

loadDest :: Emits n => Dest n -> BuilderM n (Atom n)
loadDest (DataConRef def params bs) = do
  DataDef _ _ cons <- lookupDataDef def
  let DataConDef conName _ = cons !! 0
  DataCon conName def params 0 <$> loadDataConArgs bs
loadDest (DepPairRef lr rra a) = do
  l <- loadDest lr
  r <- loadDest =<< applyAbs rra (SubstVal l)
  return $ DepPair l r a
loadDest (BoxedRef (Abs (NonDepNest bs ptrsSizes) boxedDest)) = do
  ptrs <- forM ptrsSizes \(BoxPtr ptrPtr _) -> unsafePtrLoad ptrPtr
  dest <- applySubst (bs @@> map SubstVal ptrs) boxedDest
  loadDest dest
loadDest (Con dest) = do
 case dest of
   BaseTypeRef ptr -> unsafePtrLoad ptr
   TabRef (TabLam (TabLamExpr b body)) ->
     liftEmitBuilder $ buildTabLam (getNameHint b) (binderAnn b) \i -> do
       body' <- applySubst (b@>i) body
       result <- emitBlock body'
       loadDest result
   RecordRef xs -> Record <$> traverse loadDest xs
   ConRef con -> Con <$> case con of
     ProdCon ds -> ProdCon <$> traverse loadDest ds
     SumAsProd ty tag xss -> SumAsProd ty <$> loadDest tag <*> mapM (mapM loadDest) xss
     FinVal n iRef -> FinVal n <$> loadDest iRef
     _        -> error $ "Not a valid dest: " ++ pprint dest
   _ -> error $ "not implemented" ++ pprint dest
loadDest dest = error $ "not implemented" ++ pprint dest

loadDataConArgs :: Emits n => EmptyAbs (Nest DataConRefBinding) n -> BuilderM n [Atom n]
loadDataConArgs (Abs bs UnitE) = case bs of
  Empty -> return []
  Nest (DataConRefBinding b ref) rest -> do
    val <- loadDest ref
    rest' <- applySubst (b @> SubstVal val) $ EmptyAbs rest
    (val:) <$> loadDataConArgs rest'

-- TODO: Consider targeting LLVM's `switch` instead of chained conditionals.
emitSwitch :: forall i n a.  Emits n
           => IExpr n
           -> [a]
           -> (forall l. (Emits l, DExt n l) => a -> SubstImpM i l ())
           -> SubstImpM i n ()
emitSwitch testIdx args cont = do
  Distinct <- getDistinct
  rec 0 args
  where
    rec :: forall l. (Emits l, DExt n l) => Int -> [a] -> SubstImpM i l ()
    rec _ [] = error "Shouldn't have an empty list of alternatives"
    rec _ [arg] = cont arg
    rec curIdx (arg:rest) = do
      curTag     <- fromScalarAtom $ TagRepVal $ fromIntegral curIdx
      cond       <- emitInstr $ IPrimOp $ BinOp (ICmp Equal) (sink testIdx) curTag
      thisCase   <- buildBlockImp $ cont arg >> return []
      otherCases <- buildBlockImp $ rec (curIdx + 1) rest >> return []
      emitStatement $ ICond cond thisCase otherCases

emitLoop :: Emits n
         => NameHint -> Direction -> IExpr n
         -> (forall l. (DExt n l, Emits l) => IExpr l -> SubstImpM i l ())
         -> SubstImpM i n ()
emitLoop hint d n cont = do
  loopBody <- do
    withFreshIBinder hint (getIType n) \b@(IBinder _ ty)  -> do
      let i = IVar (binderName b) ty
      body <- buildBlockImp do
                cont =<< sinkM i
                return []
      return $ Abs b body
  emitStatement $ IFor d n loopBody

restructureScalarOrPairType :: Type n -> [IExpr n] -> SubstImpM i n (Atom n)
restructureScalarOrPairType topTy topXs =
  go topTy topXs >>= \case
    (atom, []) -> return atom
    _ -> error "Wrong number of scalars"
  where
    go (PairTy t1 t2) xs = do
      (atom1, rest1) <- go t1 xs
      (atom2, rest2) <- go t2 rest1
      return (PairVal atom1 atom2, rest2)
    go (BaseTy _) (x:xs) = do
      x' <- toScalarAtom x
      return (x', xs)
    go ty _ = error $ "Not a scalar or pair: " ++ pprint ty

buildBlockImp
  :: (forall l. (Emits l, DExt n l) => SubstImpM i l [IExpr l])
  -> SubstImpM i n (ImpBlock n)
buildBlockImp cont = do
  Abs decls (ListE results) <- buildScopedImp $ ListE <$> cont
  return $ ImpBlock decls results

destToAtom :: Emits n => Dest n -> SubstImpM i n (Atom n)
destToAtom dest = liftBuilderImp $ loadDest =<< sinkM dest

destGet :: Emits n => Dest n -> Atom n -> SubstImpM i n (Dest n)
destGet dest i = liftBuilderImp $ do
  Distinct <- getDistinct
  indexDest (sink dest) (sink i)

destPairUnpack :: Dest n -> (Dest n, Dest n)
destPairUnpack (Con (ConRef (ProdCon [l, r]))) = (l, r)
destPairUnpack d = error $ "Not a pair destination: " ++ show d

_fromDestConsList :: Dest n -> [Dest n]
_fromDestConsList dest = case dest of
  Con (ConRef (ProdCon [h, t])) -> h : _fromDestConsList t
  Con (ConRef (ProdCon []))     -> []
  _ -> error $ "Not a dest cons list: " ++ pprint dest

makeAllocDest :: Emits n => AllocType -> Type n -> SubstImpM i n (Dest n)
makeAllocDest allocTy ty = fst <$> makeAllocDestWithPtrs allocTy ty

backend_TODO_DONT_HARDCODE :: Backend
backend_TODO_DONT_HARDCODE = LLVM

curDev_TODO_DONT_HARDCODE :: Device
curDev_TODO_DONT_HARDCODE = CPU

makeAllocDestWithPtrs :: Emits n
                      => AllocType -> Type n -> SubstImpM i n (Dest n, [IExpr n])
makeAllocDestWithPtrs allocTy ty = do
  let backend = backend_TODO_DONT_HARDCODE
  let curDev  = curDev_TODO_DONT_HARDCODE
  AbsPtrs absDest ptrDefs <- makeDest (backend, curDev, allocTy) ty
  ptrs <- forM ptrDefs \(DestPtrInfo ptrTy sizeBlock) -> do
    Distinct <- getDistinct
    size <- dropSubst $ translateBlock Nothing sizeBlock
    ptr <- emitAlloc ptrTy =<< fromScalarAtom size
    case ptrTy of
      (Heap _, _) | allocTy == Managed -> extendAllocsToFree ptr
      _ -> return ()
    return ptr
  ptrAtoms <- mapM toScalarAtom ptrs
  dest' <- applyNaryAbs absDest $ map SubstVal ptrAtoms
  return (dest', ptrs)

_copyDest :: Emits n => Maybe (Dest n) -> Atom n -> SubstImpM i n (Atom n)
_copyDest maybeDest atom = case maybeDest of
  Nothing   -> return atom
  Just dest -> copyAtom dest atom >> return atom

allocDest :: Emits n => Maybe (Dest n) -> Type n -> SubstImpM i n (Dest n)
allocDest maybeDest t = case maybeDest of
  Nothing   -> alloc t
  Just dest -> return dest

type AllocInfo = (Backend, Device, AllocType)

data AllocType = Managed | Unmanaged  deriving (Show, Eq)

chooseAddrSpace :: AllocInfo -> Block n -> AddressSpace
chooseAddrSpace (backend, curDev, allocTy) numel = case allocTy of
  Unmanaged -> Heap mainDev
  Managed | curDev == mainDev -> if isSmall then Stack else Heap mainDev
          | otherwise -> Heap mainDev
  where
    mainDev = case backend of
      LLVM        -> CPU
      LLVMMC      -> CPU
      LLVMCUDA    -> GPU
      MLIR        -> error "Shouldn't be compiling to Imp with MLIR backend"
      Interpreter -> error "Shouldn't be compiling to Imp with interpreter backend"

    isSmall :: Bool
    isSmall = case numel of
      Block _ Empty (Con (Lit l)) | getIntLit l <= 256 -> True
      _ -> False
{-# NOINLINE chooseAddrSpace #-}

-- === Determining buffer sizes and offsets using polynomials ===

-- These document that we're only building terms that are valid in the
-- post-simplification IR (one day we should enforce this properly)
type SimpleBuilderM = BuilderM
type SimpleBlock = Block

type IndexStructure = EmptyAbs IdxNest :: E

computeElemCount :: Emits n => IndexStructure n -> SimpleBuilderM n (Atom n)
computeElemCount (EmptyAbs Empty) =
  -- XXX: this optimization is important because we don't want to emit any decls
  -- in the case that we don't have any indices. The more general path will
  -- still compute `1`, but it might emit decls along the way.
  return $ IdxRepVal 1
computeElemCount idxNest' = do
  let (idxList, idxNest) = indexStructureSplit idxNest'
  sizes <- forM idxList \ixTy -> emitSimplified $ indexSetSize $ sink ixTy
  listSize <- foldM imul (IdxRepVal 1) sizes
  nestSize <- emitSimplified $ elemCountPoly (sink idxNest)
  imul listSize nestSize

elemCountPoly :: Emits n => IndexStructure n -> SimpleBuilderM n (Atom n)
elemCountPoly (Abs bs UnitE) = case bs of
  Empty -> return $ IdxRepVal 1
  Nest b@(_:>ixTy) rest -> do
   curSize <- emitSimplified $ indexSetSize $ sink ixTy
   restSizes <- computeSizeGivenOrdinal b $ EmptyAbs rest
   sumUsingPolysImp curSize restSizes

computeSizeGivenOrdinal
  :: EnvReader m
  => IxBinder n l -> IndexStructure l -> m n (Abs Binder SimpleBlock n)
computeSizeGivenOrdinal (b:>idxTy) idxStruct = liftBuilder do
  withFreshBinder noHint IdxRepTy \bOrdinal ->
    Abs (bOrdinal:>IdxRepTy) <$> buildBlockSimplified do
      i <- unsafeFromOrdinal (sink idxTy) $ Var $ sink $ binderName bOrdinal
      idxStruct' <- applySubst (b@>SubstVal i) idxStruct
      elemCountPoly $ sink idxStruct'

-- Split the index structure into a prefix of non-dependent index types
-- and a trailing nest of indices that can contain inter-dependencies.
indexStructureSplit :: IndexStructure n -> ([IxType n], IndexStructure n)
indexStructureSplit (Abs Empty UnitE) = ([], EmptyAbs Empty)
indexStructureSplit s@(Abs (Nest b rest) UnitE) =
  case hoist b (EmptyAbs rest) of
    HoistFailure _     -> ([], s)
    HoistSuccess rest' -> (binderAnn b:ans1, ans2)
      where (ans1, ans2) = indexStructureSplit rest'

getIxType :: EnvReader m => AtomName n -> m n (IxType n)
getIxType name = do
  lookupAtomName name >>= \case
    IxBound ixTy -> return ixTy
    _ -> error $ "not an ix-bound name" ++ pprint name

computeOffset :: forall n. Emits n
              => IndexStructure n -> [AtomName n] -> SimpleBuilderM n (Atom n)
computeOffset idxNest' idxs = do
  let (idxList , idxNest ) = indexStructureSplit idxNest'
  let (listIdxs, nestIdxs) = splitAt (length idxList) idxs
  nestOffset   <- rec idxNest nestIdxs
  nestSize     <- computeElemCount idxNest
  listOrds     <- forM listIdxs \i -> emitSimplified do
    i' <- sinkM i
    ixTy <- getIxType i'
    ordinal ixTy (Var i')
  -- We don't compute the first size (which we don't need!) to avoid emitting unnecessary decls.
  idxListSizes <- case idxList of
    [] -> return []
    _  -> (IdxRepVal 0:) <$> forM (tail idxList) \ixTy -> do
      emitSimplified $ indexSetSize $ sink ixTy
  listOffset   <- fst <$> foldM accumStrided (IdxRepVal 0, nestSize) (reverse $ zip idxListSizes listOrds)
  iadd listOffset nestOffset
  where
   accumStrided (total, stride) (size, i) = (,) <$> (iadd total =<< imul i stride) <*> imul stride size
   -- Recursively process the dependent part of the nest
   rec :: IndexStructure n -> [AtomName n] -> SimpleBuilderM n (Atom n)
   rec (Abs Empty UnitE) [] = return $ IdxRepVal 0
   rec (Abs (Nest b@(_:>ixTy) bs) UnitE) (i:is) = do
     let rest = EmptyAbs bs
     rhsElemCounts <- computeSizeGivenOrdinal b rest
     iOrd <- emitSimplified $ ordinal (sink ixTy) (Var $ sink i)
     significantOffset <- sumUsingPolysImp iOrd rhsElemCounts
     remainingIdxStructure <- applySubst (b@>i) rest
     otherOffsets <- rec remainingIdxStructure is
     iadd significantOffset otherOffsets
   rec _ _ = error "zip error"

sumUsingPolysImp :: Emits n => Atom n -> Abs Binder SimpleBlock n -> SimpleBuilderM n (Atom n)
sumUsingPolysImp lim (Abs i body) = do
  ab <- hoistDecls i body
  sumUsingPolys lim ab

hoistDecls
  :: ( Builder m, EnvReader m, Emits n
     , BindsNames b, BindsEnv b, SubstB Name b, SinkableB b)
  => b n l -> Block l -> m n (Abs b Block n)
hoistDecls b block = do
  Abs hoistedDecls rest <- liftEnvReaderM $
    refreshAbs (Abs b block) \b' (Block _ decls result) ->
      hoistDeclsRec b' Empty decls result
  ab <- emitDecls hoistedDecls rest
  refreshAbs ab \b'' blockAbs' ->
    Abs b'' <$> absToBlockInferringTypes blockAbs'

hoistDeclsRec
  :: (BindsNames b, SinkableB b)
  => b n1 n2 -> Decls n2 n3 -> Decls n3 n4 -> Atom n4
  -> EnvReaderM n3 (Abs Decls (Abs b (Abs Decls Atom)) n1)
hoistDeclsRec b declsAbove Empty result =
  return $ Abs Empty $ Abs b $ Abs declsAbove result
hoistDeclsRec b declsAbove (Nest decl declsBelow) result  = do
  let (Let _ expr) = decl
  exprIsPure <- isPure expr
  refreshAbs (Abs decl (Abs declsBelow result))
    \decl' (Abs declsBelow' result') ->
      case exchangeBs (PairB (PairB b declsAbove) decl') of
        HoistSuccess (PairB hoistedDecl (PairB b' declsAbove')) | exprIsPure -> do
          Abs hoistedDecls fullResult <- hoistDeclsRec b' declsAbove' declsBelow' result'
          return $ Abs (Nest hoistedDecl hoistedDecls) fullResult
        _ -> hoistDeclsRec b (declsAbove >>> Nest decl' Empty) declsBelow' result'

-- === Imp IR builder ===

data ImpInstrResult (n::S) = NoResults | OneResult !(IExpr n) | MultiResult !([IExpr n])

class (EnvReader m, EnvExtender m, Fallible1 m) => ImpBuilder (m::MonadKind1) where
  emitMultiReturnInstr :: Emits n => ImpInstr n -> m n (ImpInstrResult n)
  buildScopedImp
    :: SinkableE e
    => (forall l. (Emits l, DExt n l) => m l (e l))
    -> m n (Abs (Nest ImpDecl) e n)
  extendAllocsToFree :: Mut n => IExpr n -> m n ()

type ImpBuilder2 (m::MonadKind2) = forall i. ImpBuilder (m i)

withFreshIBinder
  :: ImpBuilder m
  => NameHint -> IType
  -> (forall l. DExt n l => IBinder n l -> m l a)
  -> m n a
withFreshIBinder hint ty cont = do
  withFreshBinder hint (MiscBound $ BaseTy ty) \b ->
    cont $ IBinder b ty
{-# INLINE withFreshIBinder #-}

emitCall :: Emits n
         => NaryPiType n -> ImpFunName n -> [Atom n] -> SubstImpM i n (Atom n)
emitCall piTy f xs = do
  AbsPtrs absDest ptrDefs <- makeNaryLamDest piTy Managed
  ptrs <- forM ptrDefs \(DestPtrInfo ptrTy sizeBlock) -> do
    Distinct <- getDistinct
    size <- dropSubst $ translateBlock Nothing sizeBlock
    emitAlloc ptrTy =<< fromScalarAtom size
  ptrAtoms <- mapM toScalarAtom ptrs
  dest <- applyNaryAbs absDest $ map SubstVal ptrAtoms
  resultDest <- storeArgDests dest xs
  _ <- impCall f ptrs
  destToAtom resultDest

buildImpFunction
  :: CallingConvention
  -> [(NameHint, IType)]
  -> (forall l. (Emits l, DExt n l) => [AtomName l] -> SubstImpM i l [IExpr l])
  -> SubstImpM i n (ImpFunction n)
buildImpFunction cc argHintsTys body = do
  Abs bs (Abs decls (ListE results)) <-
    buildImpNaryAbs argHintsTys \vs -> ListE <$> body vs
  let resultTys = map getIType results
  let impFun = IFunType cc (map snd argHintsTys) resultTys
  return $ ImpFunction impFun $ Abs bs $ ImpBlock decls results

buildImpNaryAbs
  :: (SinkableE e, HasNamesE e, SubstE Name e, HoistableE e)
  => [(NameHint, IType)]
  -> (forall l. (Emits l, DExt n l) => [AtomName l] -> SubstImpM i l (e l))
  -> SubstImpM i n (Abs (Nest IBinder) (Abs (Nest ImpDecl) e) n)
buildImpNaryAbs [] cont = do
  Distinct <- getDistinct
  Abs Empty <$> buildScopedImp (cont [])
buildImpNaryAbs ((hint,ty) : rest) cont = do
  withFreshIBinder hint ty \b -> do
    ab <- buildImpNaryAbs rest \vs -> do
      v <- sinkM $ binderName b
      cont (v : vs)
    Abs bs body <- return ab
    return $ Abs (Nest b bs) body

emitInstr :: (ImpBuilder m, Emits n) => ImpInstr n -> m n (IExpr n)
emitInstr instr = do
  xs <- emitMultiReturnInstr instr
  case xs of
    OneResult x -> return x
    _   -> error "unexpected numer of return values"
{-# INLINE emitInstr #-}

emitStatement :: (ImpBuilder m, Emits n) => ImpInstr n -> m n ()
emitStatement instr = do
  xs <- emitMultiReturnInstr instr
  case xs of
    NoResults -> return ()
    _         -> error "unexpected numer of return values"
{-# INLINE emitStatement #-}

impCall :: (ImpBuilder m, Emits n) => ImpFunName n -> [IExpr n] -> m n [IExpr n]
impCall f args = emitMultiReturnInstr (ICall f args) <&> \case
  NoResults      -> []
  OneResult x    -> [x]
  MultiResult xs -> xs

emitAlloc :: (ImpBuilder m, Emits n) => PtrType -> IExpr n -> m n (IExpr n)
emitAlloc (addr, ty) n = emitInstr $ Alloc addr ty n
{-# INLINE emitAlloc #-}

impOffset :: Emits n => IExpr n -> IExpr n -> SubstImpM i n (IExpr n)
impOffset ref off = emitInstr $ IPrimOp $ PtrOffset ref off

cast :: Emits n => IExpr n -> BaseType -> SubstImpM i n (IExpr n)
cast x bt = emitInstr $ ICastOp bt x

load :: Emits n => IExpr n -> SubstImpM i n (IExpr n)
load x = emitInstr $ IPrimOp $ PtrLoad x

-- === Atom <-> IExpr conversions ===

fromScalarAtom :: Atom n -> SubstImpM i n (IExpr n)
fromScalarAtom atom = confuseGHC >>= \_ -> case atom of
  Var v -> do
    BaseTy b <- getType v
    return $ IVar v b
  Con (Lit x) -> return $ ILit x
  _ -> error $ "Expected scalar, got: " ++ pprint atom

toScalarAtom :: Monad m => IExpr n -> m (Atom n)
toScalarAtom ie = case ie of
  ILit l   -> return $ Con $ Lit l
  IVar v _ -> return $ Var v

-- === Type classes ===

-- TODO: we shouldn't need the rank-2 type here because ImpBuilder and Builder
-- are part of the same conspiracy.
liftBuilderImp :: (Emits n, SubstE AtomSubstVal e, SinkableE e)
               => (forall l. (Emits l, DExt n l) => BuilderM l (e l))
               -> SubstImpM i n (e n)
liftBuilderImp cont = do
  Abs decls result <- liftBuilder $ buildScoped cont
  dropSubst $ translateDeclNest decls $ substM result
{-# INLINE liftBuilderImp #-}

-- TODO: should we merge this with `liftBuilderImp`? Not much harm in
-- simplifying even if it's not needed.
liftBuilderImpSimplify
  :: Emits n
  => (forall l. (Emits l, DExt n l) => BuilderM l (Atom l))
  -> SubstImpM i n (Atom n)
liftBuilderImpSimplify cont = do
  block <- dceApproxBlock <$> buildBlockSimplified cont
  dropSubst $ translateBlock Nothing block
{-# INLINE liftBuilderImpSimplify #-}

unsafeFromOrdinalImp :: Emits n => IxType n -> IExpr n -> SubstImpM i n (Atom n)
unsafeFromOrdinalImp ixTy i = liftBuilderImpSimplify do
  i' <- toScalarAtom =<< sinkM i
  unsafeFromOrdinal (sink ixTy) i'

indexSetSizeImp :: Emits n => IxType n -> SubstImpM i n (IExpr n)
indexSetSizeImp ty = fromScalarAtom =<< liftBuilderImpSimplify do
  indexSetSize $ sink ty

-- === type checking imp programs ===

toIVectorType :: Type n -> IVectorType
toIVectorType = \case
  BaseTy vty@(Vector _ _) -> vty
  _ -> error "Not a vector type"

impFunType :: ImpFunction n -> IFunType
impFunType (ImpFunction ty _) = ty
impFunType (FFIFunction ty _) = ty

getIType :: IExpr n -> IType
getIType (ILit l) = litType l
getIType (IVar _ ty) = ty

impInstrTypes :: EnvReader m => ImpInstr n -> m n [IType]
impInstrTypes instr = case instr of
  IPrimOp op      -> return [impOpType op]
  ICastOp t _     -> return [t]
  Alloc a ty _    -> return [PtrType (a, ty)]
  Store _ _       -> return []
  Free _          -> return []
  IThrowError     -> return []
  MemCopy _ _ _   -> return []
  IFor _ _ _      -> return []
  IWhile _        -> return []
  ICond _ _ _     -> return []
  ILaunch _ _ _   -> return []
  ISyncWorkgroup  -> return []
  IVectorBroadcast _ vty -> return [vty]
  IVectorIota vty        -> return [vty]
  IQueryParallelism _ _ -> return [IIdxRepTy, IIdxRepTy]
  ICall f _ -> do
    IFunType _ _ resultTys <- impFunType <$> lookupImpFun f
    return resultTys

-- TODO: reuse type rules in Type.hs
impOpType :: IPrimOp n -> IType
impOpType pop = case pop of
  BinOp op x _       -> typeBinOp op (getIType x)
  UnOp  op x         -> typeUnOp  op (getIType x)
  Select  _ x  _     -> getIType x
  PtrLoad ref        -> ty  where PtrType (_, ty) = getIType ref
  PtrOffset ref _    -> PtrType (addr, ty)  where PtrType (addr, ty) = getIType ref
  OutputStreamPtr -> hostPtrTy $ hostPtrTy $ Scalar Word8Type
    where hostPtrTy ty = PtrType (Heap CPU, ty)
  _ -> unreachable
  where unreachable = error $ "Not allowed in Imp IR: " ++ show pop

instance CheckableE ImpFunction where
  checkE = substM -- TODO!

-- TODO: Don't use Core Envs for Imp!
instance BindsEnv ImpDecl where
  toEnvFrag (ImpLet bs _) = toEnvFrag bs

instance BindsEnv IBinder where
  toEnvFrag (IBinder b ty) = toEnvFrag $ b :> BaseTy ty

instance SubstB AtomSubstVal IBinder

captureClosure
  :: (HoistableB b, HoistableE e, Color c)
  => b n l -> e l -> ([Name c l], NaryAbs c e n)
captureClosure decls result = do
  let vs = capturedVars decls result
  let ab = abstractFreeVarsNoAnn vs result
  case hoist decls ab of
    HoistSuccess abHoisted -> (vs, abHoisted)
    HoistFailure _ ->
      error "shouldn't happen"  -- but it will if we have types that reference
                                -- local vars. We really need a telescope.

capturedVars :: (Color c, BindsNames b, HoistableE e)
             => b n l -> e l -> [Name c l]
capturedVars b e = nameSetToList nameSet
  where nameSet = R.intersection (toNameSet (toScopeFrag b)) (freeVarsE e)

-- See Note [Confuse GHC] from Simplify.hs
confuseGHC :: EnvReader m => m n (DistinctEvidence n)
confuseGHC = getDistinct
{-# INLINE confuseGHC #-}
