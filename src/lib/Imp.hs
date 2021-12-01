-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE Rank2Types #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Imp (toImpModule, getIType, impBlockType, impFunType, impFunVar,
            toScalarType, fromScalarType, impInstrTypes) where

import Prelude hiding (pi, abs)
import Control.Monad.Reader
import Control.Monad.Except hiding (Except)
import Control.Monad.State.Strict
import Control.Monad.Writer hiding (Alt)
import Data.Text.Prettyprint.Doc
import Data.Either
import Data.Functor
import Data.Maybe
import Data.Foldable (toList)
import Data.String (fromString)
import GHC.Stack
import qualified Data.List.NonEmpty as NE
import qualified Data.Map.Strict as M

import Builder
import LabeledItems
import Syntax
import Env
import Err
import Type
import PPrint ()
import Cat
import Algebra
import Util

-- Note [Valid Imp atoms]
--
-- The Imp translation functions as an interpreter for the core IR, which has a side effect
-- of emitting a low-level Imp program that would do the actual math. As an interpreter, each
-- expression has to produce a valid result Atom, that can be used as an input to all later
-- equations. However, because the Imp IR only supports a very limited selection of types
-- (really only base types and pointers to scalar tables), it is safe to assume that only
-- a subset of atoms can be returned by the impSubst. In particular, the atoms might contain
-- only:
--   * Variables of base type or array type
--   * Table lambdas
--   * Constructors for: pairs, sum types, Unit and Coerce
--
-- TODO: Use an ImpAtom type alias to better document the code

data ParallelismLevel = TopLevel | ThreadLevel  deriving (Show, Eq)
data ImpCtx = ImpCtx
  { impBackend :: Backend
  , curDevice  :: Device
  , curLevel   :: ParallelismLevel }

data ImpCatEnv = ImpCatEnv
  { envPtrsToFree :: [IExpr]
  , envScope      :: Scope
  , envDecls      :: [ImpDecl]
  , envFunctions  :: Env ImpFunction }

type ImpM = ExceptT () (ReaderT ImpCtx (Cat ImpCatEnv))
type AtomRecon = Abs (Nest Binder) Atom

toImpModule :: Bindings -> Backend -> CallingConvention -> Name
            -> [IBinder] -> Maybe Dest -> Block
            -> (ImpFunction, ImpModule, AtomRecon)
toImpModule env backend cc entryName argBinders maybeDest block = do
  let standaloneFunctions =
        for (requiredFunctions env block) \(v, f) ->
          runImpM initCtx inVarScope $ toImpStandalone v f
  runImpM initCtx inVarScope $ do
    (reconAtom, impBlock) <- scopedBlock $ translateTopLevel env (maybeDest, block)
    otherFunctions <- toList <$> looks envFunctions
    let ty = IFunType cc (map binderAnn argBinders) (impBlockType impBlock)
    let mainFunction = ImpFunction (entryName:>ty) argBinders impBlock
    let allFunctions = standaloneFunctions ++ otherFunctions ++ [mainFunction]
    return (mainFunction, ImpModule allFunctions, reconAtom)
  where
    inVarScope :: Scope  -- TODO: fix (shouldn't use UnitTy)
    inVarScope = binderScope <> destScope
    binderScope = foldMap binderAsEnv $ fmap (fmap $ const ImpBound) argBinders
    destScope = fromMaybe mempty $ fmap freeVars maybeDest
    initCtx = ImpCtx backend CPU TopLevel

requiredFunctions :: HasVars a => Scope -> a -> [(Name, Atom)]
requiredFunctions scope expr =
  flip foldMap (transitiveClosure getParents immediateParents) \fname ->
    case scope ! fname of
       AtomBinderInfo _ (LetBound _ (Atom f)) -> [(fname, f)]
       _ -> []
  where
    getParents :: Name -> [Name]
    getParents fname = envNames $ freeVars $ scope ! fname

    immediateParents :: [Name]
    immediateParents = envNames $ freeVars expr `envIntersect` scope

-- We don't emit any results when a destination is provided, since they are already
-- going to be available through the dest.
translateTopLevel :: Bindings -> WithDest Block -> ImpM (AtomRecon, [IExpr])
translateTopLevel topEnv (maybeDest, block) = do
  outDest <- case maybeDest of
        Nothing   -> makeAllocDest Unmanaged $ getType block
        Just dest -> return dest
  handleErrors $ void $ translateBlock mempty (Just outDest, block)
  resultAtom <- destToAtom outDest
  -- Some names in topEnv refer to global constants, like the virtual stdout channel
  let vsOut = envAsVars $ freeVars resultAtom `envDiff` topEnv
  let reconAtom = Abs (toNest $ [Bind (v:>ty) | (v :> AtomBinderInfo ty _) <- vsOut]) resultAtom
  let resultIExprs = case maybeDest of
        Nothing -> [IVar (v:>fromScalarType ty) | (v :> AtomBinderInfo ty _) <- vsOut]
        Just _  -> []
  return (reconAtom, resultIExprs)

runImpM :: ImpCtx -> Scope -> ImpM a -> a
runImpM ctx inVarScope m =
  fromRight (error "Unexpected top level error") $
    fst $ runCat (runReaderT (runExceptT m) ctx) $ mempty {envScope = inVarScope}

toImpStandalone :: Name -> Atom -> ImpM ImpFunction
toImpStandalone fname ~(LamVal b body) = do
  let argTy = binderAnn b
  let outTy = getType body
  backend <- asks impBackend
  curDev <- asks curDevice
  (ptrSizes, ~(Con (ConRef (ProdCon [outDest, argDest])))) <- fromBuilder $
    makeDest (backend, curDev, Unmanaged) (PairTy outTy argTy)
  impBlock <- scopedErrBlock $ do
    arg <- destToAtom argDest
    void $ translateBlock (b@>SubstVal arg) (Just outDest, body)
  let bs = for ptrSizes \(Bind (v:>BaseTy ty), _) -> Bind $ v:>ty
  let fTy = IFunType CEntryFun (map binderAnn bs) (impBlockType impBlock)
  return $ ImpFunction (fname:>fTy) bs impBlock

translateBlock :: SubstEnv -> WithDest Block -> ImpM Atom
translateBlock env destBlock = do
  let (decls, result, copies) = splitDest destBlock
  env' <- (env<>) <$> catFoldM translateDecl env decls
  forM_ copies \(dest, atom) -> copyAtom dest =<< impSubst env' atom
  translateExpr env' result

translateDecl :: SubstEnv -> WithDest Decl -> ImpM SubstEnv
translateDecl env (maybeDest, (Let _ b bound)) = do
  b' <- traverse (impSubst env) b
  ans <- translateExpr env (maybeDest, bound)
  return $ b' @> SubstVal ans

translateExpr :: SubstEnv -> WithDest Expr -> ImpM Atom
translateExpr env (maybeDest, expr) = case expr of
  Hof hof     -> toImpHof env (maybeDest, hof)
  App f' x' -> do
    f <- impSubst env f'
    x <- impSubst env x'
    case getType f of
      TabTy _ _ -> do
        case f of
          Lam a@(Abs _ (TabArrow, _)) ->
            translateBlock mempty (maybeDest, snd $ applyAbs a x)
          _ -> error $ "Invalid Imp atom: " ++ pprint f
      -- Runtime function calls for non-inlined functions
      _ -> do
        let (Var (fname:>(FunTy argBinder _ outTy))) = f
        let argTy = binderAnn argBinder
        (argDest, argDestElts) <- makeAllocDestWithPtrs Managed $ argTy
        -- There's a missed opportunity here to use maybeDest. The problem is
        -- that we can't guarantee that the table refs are in a canonical
        -- representation. We could consider tracking that information with
        -- dests so that we can take advantage of it when it happens.
        (outDest, outDestElts) <- makeAllocDestWithPtrs Managed $ outTy
        let allElts = outDestElts ++ argDestElts
        let iFunTy = IFunType CEntryFun (map getIType allElts) []
        copyAtom argDest x
        void $ emitStatement $ ICall (fname:>iFunTy) allElts
        result <- destToAtom outDest
        copyDest maybeDest result
  Atom x   -> copyDest maybeDest =<< impSubst env x
  Op   op  -> toImpOp . (maybeDest,) =<< traverse (impSubst env) op
  Case e alts _ -> do
    e' <- impSubst env e
    case e' of
      DataCon _ _ con args -> do
        let Abs bs body = alts !! con
        translateBlock (env <> newEnv bs (map SubstVal args)) (maybeDest, body)
      Variant (NoExt types) label i x -> do
        let LabeledItems ixtypes = enumerate types
        let index = fst $ ixtypes M.! label NE.!! i
        let Abs bs body = alts !! index
        translateBlock (env <> newEnv bs [SubstVal x]) (maybeDest, body)
      Con (SumAsProd _ tag xss) -> do
        let tag' = fromScalarAtom tag
        dest <- allocDest maybeDest =<< impSubst env (getType expr)
        emitSwitch tag' $ flip map (zip xss alts) $
          \(xs, Abs bs body) ->
             void $ translateBlock (env <> newEnv bs (map SubstVal xs)) (Just dest, body)
        destToAtom dest
      _ -> error $ "Unexpected scrutinee: " ++ pprint e'

emitFunction :: Name -> CallingConvention
             -> [IBinder] -> ImpBlock -> ImpM IFunVar
emitFunction nameHint cc bs body = do
  funEnv <- looks envFunctions
  let name = genFresh (Name TopFunctionName (nameTag nameHint) 0) funEnv
  let fvar = name :> IFunType cc (map binderAnn bs) (impBlockType body)
  extend $ mempty {envFunctions = fvar @> ImpFunction fvar bs body}
  return fvar

emitFFIFunction :: String -> [IType] -> [IType] -> ImpM IFunVar
emitFFIFunction s argTys resultTys = do
  let fname = Name FFIName (fromString s) 0
  let cc = case length resultTys of
        0 -> error "Not implemented"
        1 -> FFIFun
        _ -> FFIMultiResultFun
  let f = fname :> IFunType cc argTys resultTys
  -- TODO: check that if it's already in the env, it's with the same type
  extend $ mempty {envFunctions = fname @> FFIFunction f}
  return f

impSubst :: Subst a => SubstEnv -> a -> ImpM a
impSubst env x = do
  scope <- variableScope
  return $ subst (env, scope) x

toImpOp :: WithDest (PrimOp Atom) -> ImpM Atom
toImpOp (maybeDest, op) = case op of
  TabCon (TabTy b _) rows -> do
    dest <- allocDest maybeDest resultTy
    forM_ (zip [0..] rows) \(i, row) -> do
      ithDest <- destGet dest =<< intToIndex (binderType b) (IIdxRepVal i)
      copyAtom ithDest row
    destToAtom dest
  PrimEffect refDest m -> do
    case m of
      MAsk      -> returnVal =<< destToAtom refDest
      MExtend ~(Lam f) -> do
        -- TODO: Update in-place?
        refValue <- destToAtom refDest
        result <- translateBlock mempty (Nothing, snd $ applyAbs f refValue)
        copyAtom refDest result
        returnVal UnitVal
      MPut x    -> copyAtom  refDest x >> returnVal UnitVal
      MGet -> do
        dest <- allocDest maybeDest resultTy
        -- It might be more efficient to implement a specialized copy for dests
        -- than to go through a general purpose atom.
        copyAtom dest =<< destToAtom refDest
        destToAtom dest
  UnsafeFromOrdinal n i -> returnVal =<< (intToIndex n $ fromScalarAtom i)
  IdxSetSize n -> returnVal . toScalarAtom  =<< indexSetSize n
  ToOrdinal idx -> case idx of
    Con (IntRangeVal   _ _   i) -> returnVal $ i
    Con (IndexRangeVal _ _ _ i) -> returnVal $ i
    _ -> returnVal . toScalarAtom =<< indexToInt idx
  Inject e -> case e of
    Con (IndexRangeVal t low _ restrictIdx) -> do
      offset <- case low of
        InclusiveLim a -> indexToInt a
        ExclusiveLim a -> indexToInt a >>= iaddI (IIdxRepVal 1)
        Unlimited      -> return (IIdxRepVal 0)
      returnVal =<< intToIndex t =<< iaddI (fromScalarAtom restrictIdx) offset
    Con (ParIndexCon (TC (ParIndexRange realIdxTy _ _)) i) -> do
      returnVal =<< intToIndex realIdxTy (fromScalarAtom i)
    _ -> error $ "Unsupported argument to inject: " ++ pprint e
  IndexRef refDest i -> returnVal =<< destGet refDest i
  ProjRef i ~(Con (ConRef (ProdCon refs))) -> returnVal $ refs !! i
  IOAlloc ty n -> do
    ptr <- emitAlloc (Heap CPU, ty) (fromScalarAtom n)
    returnVal $ toScalarAtom ptr
  IOFree ptr -> do
    emitStatement $ Free $ fromScalarAtom ptr
    return UnitVal
  PtrOffset arr (IdxRepVal 0) -> returnVal arr
  PtrOffset arr off -> do
    buf <- impOffset (fromScalarAtom arr) (fromScalarAtom off)
    returnVal $ toScalarAtom buf
  PtrLoad arr -> returnVal . toScalarAtom =<< loadAnywhere (fromScalarAtom arr)
  PtrStore ptr x -> do
    store (fromScalarAtom ptr) (fromScalarAtom x)
    return UnitVal
  SliceOffset ~(Con (IndexSliceVal n _ tileOffset)) idx -> do
    i' <- indexToInt idx
    i <- iaddI (fromScalarAtom tileOffset) i'
    returnVal =<< intToIndex n i
  SliceCurry ~(Con (IndexSliceVal _ (PairTy _ v) tileOffset)) idx -> do
    vz <- intToIndex v $ IIdxRepVal 0
    extraOffset <- indexToInt (PairVal idx vz)
    tileOffset' <- iaddI (fromScalarAtom tileOffset) extraOffset
    returnVal $ toScalarAtom tileOffset'
  ThrowError _ -> throwError ()
  CastOp destTy x -> case (getType x, destTy) of
    (BaseTy _, BaseTy bt) -> returnVal =<< toScalarAtom <$> cast (fromScalarAtom x) bt
    _ -> error $ "Invalid cast: " ++ pprint (getType x) ++ " -> " ++ pprint destTy
  Select p x y -> do
    case getType x of
      BaseTy _ -> do
        ans <- emitInstr $ IPrimOp $
                 Select (fromScalarAtom p) (fromScalarAtom x) (fromScalarAtom y)
        returnVal $ toScalarAtom ans
      _ -> do
        dest <- allocDest maybeDest resultTy
        p' <- cast (fromScalarAtom p) tagBT
        emitSwitch p' [copyAtom dest y, copyAtom dest x]
        destToAtom dest
        where (BaseTy tagBT) = TagRepTy
  RecordCons   _ _ -> error "Unreachable: should have simplified away"
  RecordSplit  _ _ -> error "Unreachable: should have simplified away"
  VariantLift  _ _ -> error "Unreachable: should have simplified away"
  VariantSplit _ _ -> error "Unreachable: should have simplified away"
  DataConTag con -> case con of
    (Con (SumAsProd _ tag _)) -> returnVal tag
    (DataCon _ _ i _) -> returnVal $ TagRepVal $ fromIntegral i
    _ -> error $ "Not a data constructor: " ++ pprint con
  ToEnum ty i -> returnVal $ case ty of
    TypeCon (_, DataDef _ _ cons) _ ->
      Con $ SumAsProd ty i (map (const []) cons)
    VariantTy (NoExt labeledItems) ->
      Con $ SumAsProd ty i (map (const [UnitVal]) $ toList labeledItems)
    SumTy cases -> Con $ SumAsProd ty i $ cases <&> const [UnitVal]
    _ -> error $ "Not an enum: " ++ pprint ty
  FFICall name returnTy xs -> do
    let returnTys = fromScalarOrPairType returnTy
    let xTys = map (fromScalarType . getType) xs
    f <- emitFFIFunction name xTys returnTys
    results <- emitMultiReturnInstr $ ICall f $ map fromScalarAtom xs
    returnVal $ restructureScalarOrPairType returnTy results
  SumToVariant ~(Con c) -> returnVal $ case c of
    SumCon    _ tag payload -> Variant labs "c" tag payload
    SumAsProd _ tag payload -> Con $ SumAsProd resultTy tag payload
    _ -> error $ "Not a sum type: " ++ pprint (Con c)
    where ~(VariantTy labs) = resultTy
  _ -> do
    returnVal . toScalarAtom =<< emitInstr (IPrimOp $ fmap fromScalarAtom op)
  where
    resultTy = getType $ Op op
    returnVal atom = case maybeDest of
      Nothing   -> return atom
      Just dest -> copyAtom dest atom >> return atom

toImpHof :: SubstEnv -> WithDest Hof -> ImpM Atom
toImpHof env (maybeDest, hof) = do
  resultTy <- impSubst env $ getType $ Hof hof
  case hof of
    For (RegularFor d) ~(LamVal b body) -> do
      idxTy <- impSubst env $ binderType b
      dev   <- asks curDevice
      case idxTy of
        TC (ParIndexRange realIdxTy gtid numThreads) -> do
          let gtidI = fromScalarAtom gtid
          let numThreadsI = fromScalarAtom numThreads
          n    <- indexSetSize realIdxTy
          dest <- allocDest maybeDest resultTy
          case dev of
            CPU -> do -- Chunked loop
              usualChunkSize  <- n `idivI` numThreadsI
              chunkStart      <- gtidI `imulI` usualChunkSize
              isLast          <- (gtidI `ieqI`) =<< (numThreadsI `isubI` IIdxRepVal 1)
              elemsUntilEnd   <- n `isubI` chunkStart
              threadChunkSize <- toImpOp $ (Nothing,
                                            Select (toScalarAtom isLast)
                                                   (toScalarAtom elemsUntilEnd)
                                                   (toScalarAtom usualChunkSize))
              emitLoop "li" Fwd (fromScalarAtom threadChunkSize) \li -> do
                i <- li `iaddI` chunkStart
                let idx = Con $ ParIndexCon idxTy $ toScalarAtom i
                ithDest <- destGet dest idx
                void $ translateBlock (env <> b @> SubstVal idx) (Just ithDest, body)
            GPU -> do -- Grid stride loop
              iPtr <- alloc IdxRepTy
              copyAtom iPtr gtid
              cond <- liftM snd $ scopedBlock $ do
                i <- destToAtom iPtr
                inRange <- (fromScalarAtom i) `iltI` n
                emitWhen inRange $ do
                  let idx = Con $ ParIndexCon idxTy i
                  ithDest <- destGet dest idx
                  void $ translateBlock (env <> b @> SubstVal idx) (Just ithDest, body)
                  copyAtom iPtr . toScalarAtom =<< iaddI (fromScalarAtom i)
                                                     (fromScalarAtom numThreads)
                return ((), [inRange])
              emitStatement $ IWhile cond
          destToAtom dest
        _ -> do
          n <- indexSetSize idxTy
          dest <- allocDest maybeDest resultTy
          emitLoop (binderNameHint b) d n \i -> do
            idx <- intToIndex idxTy i
            ithDest <- destGet dest idx
            void $ translateBlock (env <> b @> SubstVal idx) (Just ithDest, body)
          destToAtom dest
    For ParallelFor ~fbody@(LamVal b _) -> do
      idxTy <- impSubst env $ binderType b
      dest <- allocDest maybeDest resultTy
      buildKernel idxTy \LaunchInfo{..} buildBody -> do
        liftM (,()) $ buildBody \ThreadInfo{..} -> do
          let threadBody = fst $ runSubstBuilder (freeVars fbody) mempty $
                buildLam (Bind $ "hwidx" :> threadRange) PureArrow \hwidx ->
                  appReduce fbody =<< (emitOp $ Inject hwidx)
          let threadDest = Con $ TabRef $ fst $ runSubstBuilder (freeVars dest) mempty $
                buildLam (Bind $ "hwidx" :> threadRange) TabArrow \hwidx ->
                  indexDest dest =<< (emitOp $ Inject hwidx)
          void $ toImpHof env (Just threadDest, For (RegularFor Fwd) threadBody)
      destToAtom dest
    Tile d ~(LamVal tb tBody) ~(LamVal sb sBody) -> do
      ~(TC (IndexSlice idxTy tileIdxTy)) <- impSubst env $ binderType tb
      n <- indexSetSize idxTy
      dest <- allocDest maybeDest resultTy
      tileLen <- indexSetSize tileIdxTy
      nTiles      <- n `idivI` tileLen
      epilogueOff <- nTiles `imulI` tileLen
      nEpilogue   <- n `isubI` epilogueOff
      emitLoop (binderNameHint tb) Fwd nTiles \iTile -> do
        tileOffset <- toScalarAtom <$> iTile `imulI` tileLen
        let tileAtom = Con $ IndexSliceVal idxTy tileIdxTy tileOffset
        tileDest <- fromBuilder $ sliceDestDim d dest tileOffset tileIdxTy
        void $ translateBlock (env <> tb @> SubstVal tileAtom) (Just tileDest, tBody)
      emitLoop (binderNameHint sb) Fwd nEpilogue \iEpi -> do
        i <- iEpi `iaddI` epilogueOff
        idx <- intToIndex idxTy i
        sDest <- fromBuilder $ indexDestDim d dest idx
        void $ translateBlock (env <> sb @> SubstVal idx) (Just sDest, sBody)
      destToAtom dest
    PTileReduce baseMonoids idxTy' ~(BinaryFunVal gtidB nthrB _ body) -> do
      idxTy <- impSubst env idxTy'
      (mappingDest, finalAccDest) <- destPairUnpack <$> allocDest maybeDest resultTy
      let PairTy _ accTypes = resultTy
      (numTileWorkgroups, wgAccsArr, widIdxTy) <- buildKernel idxTy \LaunchInfo{..} buildBody -> do
        let widIdxTy = Fin $ toScalarAtom numWorkgroups
        let tidIdxTy = Fin $ toScalarAtom workgroupSize
        wgAccsArr  <- alloc $ TabTy (Ignore widIdxTy) accTypes
        thrAccsArr <- alloc $ TabTy (Ignore widIdxTy) $ TabTy (Ignore tidIdxTy) accTypes
        mappingKernelBody <- buildBody \ThreadInfo{..} -> do
          let TC (ParIndexRange _ gtid nthr) = threadRange
          let tileDest = Con $ TabRef $ fst $ runSubstBuilder (freeVars mappingDest) mempty $ do
                buildLam (Bind $ "hwidx":>threadRange) TabArrow \hwidx -> do
                  indexDest mappingDest =<< (emitOp $ Inject hwidx)
          wgThrAccs <- destGet thrAccsArr =<< intToIndex widIdxTy wid
          thrAccs   <- destGet wgThrAccs  =<< intToIndex tidIdxTy tid
          let thrAccsList = fromDestConsList thrAccs
          let mkPair = \x y -> ProdCon [x, y]
          let threadDest = foldr ((Con . ConRef) ... flip mkPair) tileDest thrAccsList
          case (getType threadDest) == (RawRefTy $ getType body) of
            True -> return ()
            _    -> error "Invalid threadDest type"
          void $ translateBlock (env <> gtidB @> SubstVal gtid <> nthrB @> SubstVal nthr)
                   (Just threadDest, body)
          wgAccs <- destGet wgAccsArr =<< intToIndex widIdxTy wid
          workgroupReduce tid wgAccs wgThrAccs workgroupSize
        return (mappingKernelBody, (numWorkgroups, wgAccsArr, widIdxTy))
      -- TODO: Skip the reduction kernel if unnecessary?
      -- TODO: Reduce sequentially in the CPU backend?
      -- TODO: Actually we only need the previous-power-of-2 many threads
      buildKernel widIdxTy \LaunchInfo{..} buildBody -> do
        -- We only do a one-level reduciton in the workgroup, so it is correct
        -- only if the end up scheduling a single workgroup.
        moreThanOneGroup <- (IIdxRepVal 1) `iltI` numWorkgroups
        guardBlock moreThanOneGroup $ emitStatement IThrowError
        redKernelBody <- buildBody \ThreadInfo{..} ->
          workgroupReduce tid finalAccDest wgAccsArr numTileWorkgroups
        return (redKernelBody, ())
      PairVal <$> destToAtom mappingDest <*> destToAtom finalAccDest
      where
        guardBlock cond m = do
          block <- scopedErrBlock m
          emitStatement $ ICond cond block (ImpBlock mempty mempty)
        -- XXX: Overwrites the contents of arrDest, writes result in resDest
        workgroupReduce tid resDest arrDest elemCount = do
          elemCountDown2 <- prevPowerOf2 elemCount
          let RawRefTy (TabTy arrIdxB _) = getType arrDest
          let arrIdxTy = binderType arrIdxB
          offPtr <- alloc IdxRepTy
          copyAtom offPtr $ toScalarAtom elemCountDown2
          let wbody = do
                off       <- fromScalarAtom <$> destToAtom offPtr
                loadIdx   <- iaddI tid off
                shouldAdd <- bindM2 bandI (tid `iltI` off) (loadIdx `iltI` elemCount)
                guardBlock shouldAdd $ do
                  threadDest <- destGet arrDest =<< intToIndex arrIdxTy tid
                  combineWithDest threadDest =<< destToAtom =<< destGet arrDest =<< intToIndex arrIdxTy loadIdx
                emitStatement ISyncWorkgroup
                copyAtom offPtr . toScalarAtom =<< off `idivI` (IIdxRepVal 2)
          cond <- liftM snd $ scopedBlock $ do
            off  <- fromScalarAtom <$> destToAtom offPtr
            cond <- emitInstr $ IPrimOp $ ScalarBinOp (ICmp Greater) off (IIdxRepVal 0)
            emitWhen cond wbody
            return ((), [cond])
          emitStatement $ IWhile cond
          firstThread <- tid `iltI` (IIdxRepVal 1)
          guardBlock firstThread $
            copyAtom resDest =<< destToAtom =<< destGet arrDest =<< intToIndex arrIdxTy tid
        combineWithDest :: Dest -> Atom -> ImpM ()
        combineWithDest accsDest ~(ProdVal accsUpdatesList) = do
          let accsDestList = fromDestConsList accsDest
          forM_ (zip3 accsDestList baseMonoids accsUpdatesList) $ \(dest, bm, update) -> do
            extender <- fromBuilder $ mextendForRef dest bm update
            void $ toImpOp (Nothing, PrimEffect dest $ MExtend extender)
        -- TODO: Do some popcount tricks?
        prevPowerOf2 :: IExpr -> ImpM IExpr
        prevPowerOf2 x = do
          rPtr <- alloc IdxRepTy
          copyAtom rPtr (IdxRepVal 1)
          let getNext = imulI (IIdxRepVal 2) . fromScalarAtom =<< destToAtom rPtr
          cond <- liftM snd $ scopedBlock $ do
            canGrow <- getNext >>= (`iltI` x)
            emitWhen canGrow $ copyAtom rPtr . toScalarAtom =<< getNext
            return ((), [canGrow])
          emitStatement $ IWhile cond
          fromScalarAtom <$> destToAtom rPtr
    While ~(Lam (Abs _ (_, body))) -> do
      body' <- liftM snd $ scopedBlock $ do
                 ans <- translateBlock env (Nothing, body)
                 return ((), [fromScalarAtom ans])
      emitStatement $ IWhile body'
      return UnitVal
    RunReader r ~(BinaryFunVal _ ref _ body) -> do
      rDest <- alloc $ getType r
      copyAtom rDest =<< impSubst env r
      translateBlock (env <> ref @> SubstVal rDest) (maybeDest, body)
    RunWriter (BaseMonoid e' _) ~(BinaryFunVal _ ref _ body) -> do
      let PairTy _ accTy = resultTy
      (aDest, wDest) <- destPairUnpack <$> allocDest maybeDest resultTy
      copyAtom wDest =<< (liftNeutral accTy <$> impSubst env e')
      void $ translateBlock (env <> ref @> SubstVal wDest) (Just aDest, body)
      PairVal <$> destToAtom aDest <*> destToAtom wDest
      where liftNeutral accTy e = foldr TabValA e $ monoidLift (getType e) accTy
    RunState s ~(BinaryFunVal _ ref _ body) -> do
      (aDest, sDest) <- destPairUnpack <$> allocDest maybeDest resultTy
      copyAtom sDest =<< impSubst env s
      void $ translateBlock (env <> ref @> SubstVal sDest) (Just aDest, body)
      PairVal <$> destToAtom aDest <*> destToAtom sDest
    RunIO ~(Lam (Abs _ (_, body))) ->
      translateBlock env (maybeDest, body)
    Linearize _ -> error "Unexpected Linearize"
    Transpose _ -> error "Unexpected Transpose"
    CatchException _ -> error "Unexpected CatchException"

data LaunchInfo = LaunchInfo { numWorkgroups :: IExpr, workgroupSize :: IExpr }
data ThreadInfo = ThreadInfo { tid :: IExpr, wid :: IExpr, threadRange :: Type }
type KernelBuilder kernel = (ThreadInfo -> ImpM ()) -> ImpM kernel

-- The rank 2 signature ensures that the call sites returns the result of the
buildKernel :: Type -> (forall k. LaunchInfo -> KernelBuilder k -> ImpM (k, a)) -> ImpM a
buildKernel idxTy f = do
  n <- indexSetSize idxTy
  -- Launch info vars
  numWorkgroupsVar <- freshVar $ "numWorkgroups" :> IIdxRepTy
  workgroupSizeVar <- freshVar $ "workgroupSize" :> IIdxRepTy
  let numWorkgroups = IVar numWorkgroupsVar
  let workgroupSize = IVar workgroupSizeVar
  -- Thread info vars
  tidVar  <- freshVar $ "tid"  :> IIdxRepTy
  widVar  <- freshVar $ "wid"  :> IIdxRepTy
  wszVar  <- freshVar $ "wsz"  :> IIdxRepTy
  nthrVar <- freshVar $ "nthr" :> IIdxRepTy
  let tid  = IVar tidVar
  let wid  = IVar widVar
  let wsz  = IVar wszVar
  let nthr = IVar nthrVar
  let threadInfoVars = [tidVar, widVar, wszVar, nthrVar]
  -- Emit the kernel function
  opts <- ask
  let (cc, dev) = case impBackend opts of
        LLVMCUDA -> (CUDAKernelLaunch, GPU)
        LLVMMC   -> (MCThreadLaunch  , CPU)
        backend  -> error $ "Shouldn't be launching kernels from " ++ show backend
  ((kernelBody, aux), env) <- scoped $ f LaunchInfo{..} \mkBody ->
    withDevice dev $ withLevel ThreadLevel $ scopedErrBlock $ do
      gtid <- iaddI tid =<< imulI wid wsz
      let threadRange = TC $ ParIndexRange idxTy (toScalarAtom gtid) (toScalarAtom nthr)
      mkBody ThreadInfo{..}
  let args = envAsVars $ freeIVars kernelBody `envDiff` (newEnv threadInfoVars (repeat ()))
  kernelFunc <- emitFunction "kernel" cc
    (fmap Bind (tidVar:widVar:wszVar:nthrVar:args)) kernelBody
  -- Carefully emit the decls so that the launch info gets bound before the kernel call
  emitImpDecl $ ImpLet [Bind numWorkgroupsVar, Bind workgroupSizeVar]
                       (IQueryParallelism kernelFunc n)
  extend env
  emitStatement $ ILaunch kernelFunc n $ map IVar args
  return aux

-- === Destination type ===

type Dest = Atom  -- has type `Ref a` for some a
type WithDest a = (Maybe Dest, a)

data DestEnv = DestEnv
       { _allocationInfo :: AllocInfo
       , enclosingIdxs :: IndexStructure
       , destDepVars :: Env () }

-- The Cat env carries names for the pointers needed, along with their types and
-- blocks that compute allocation sizes needed
type DestM = ReaderT DestEnv (CatT (Env (Type, Block)) Builder)

-- builds a dest and a list of pointer binders along with their required allocation sizes
makeDest :: AllocInfo -> Type -> Builder ([(Binder, Atom)], Dest)
makeDest allocInfo ty = do
  (dest, ptrs) <- flip runCatT mempty $ flip runReaderT env $ makeDestRec ty
  ptrs' <- forM (envPairs ptrs) \(v, (ptrTy, numel)) -> do
    numel' <- emitBlock numel
    return (Bind (v:>ptrTy), numel')
  return (ptrs', dest)
  where env = DestEnv allocInfo mempty mempty

makeDestRec :: Type -> DestM Dest
makeDestRec ty = case ty of
  TabTy b bodyTy -> do
    depVars <- asks destDepVars
    if not $ null $ freeVars b `envIntersect` depVars
      then do
        (dest, ptrs) <- local (\env -> env { enclosingIdxs = mempty
                                           , destDepVars   = mempty }) $ scoped $
                          makeDestRec ty
        makeBoxes (envPairs ptrs) dest
      else do
        lam <- buildLam (Bind ("i":> binderAnn b)) TabArrow \(Var i) -> do
          bodyTy' <- substBuilder (b@>SubstVal (Var i)) bodyTy
          withEnclosingIdxs (Bind i) $ makeDestRec bodyTy'
        return $ Con $ TabRef lam
  TypeCon def params -> do
    let dcs = applyDataDefParams (snd def) params
    case dcs of
      [] -> error "Void type not allowed"
      [DataConDef _ bs] -> do
        dests <- makeDataConDest bs
        return $ DataConRef def params dests
      _ -> do
        when (any isDependent dcs) $ error
          "Dependent data constructors only allowed for single-constructor types"
        tag <- rec TagRepTy
        let dcs' = applyDataDefParams (snd def) params
        contents <- forM dcs' \(DataConDef _ bs) -> forM (toList bs) (rec . binderType)
        return $ Con $ ConRef $ SumAsProd ty tag contents
  DepPairTy a@(Abs b _) -> do
    lhsDest <- makeDestRec $ absArgType a
    v       <- freshVarE UnknownBinder $ binderType b  -- TODO: scope names more carefully
    rhsDest <- withDepVar (Bind v) $ makeDestRec $ applyAbs a $ Var v
    return $ DepPairRef lhsDest (Abs (Bind v) rhsDest) a
  RecordTy (NoExt types) -> (Con . RecordRef) <$> forM types rec
  VariantTy (NoExt types) -> recSumType $ toList types
  TC con -> case con of
    BaseType b -> do
      ptr <- makeBaseTypePtr b
      return $ Con $ BaseTypeRef ptr
    SumType cases -> recSumType cases
    ProdType tys  -> (Con . ConRef) <$> (ProdCon <$> traverse rec tys)
    IntRange     l h -> (Con . ConRef . IntRangeVal     l h) <$> rec IdxRepTy
    IndexRange t l h -> (Con . ConRef . IndexRangeVal t l h) <$> rec IdxRepTy
    _ -> error $ "not implemented: " ++ pprint con
  _ -> error $ "not implemented: " ++ pprint ty
  where
    rec = makeDestRec
    recSumType cases = do
      tag <- rec TagRepTy
      contents <- forM cases rec
      return $ Con $ ConRef $ SumAsProd ty tag $ map (\x->[x]) contents

makeBoxes :: [(Name, (Type, Block))] -> Dest -> DestM Dest
makeBoxes [] dest = return dest
makeBoxes ((v, (ptrTy, numel)):rest) dest = do
  ptrPtr <- makeBaseTypePtr $ fromScalarType ptrTy
  dest' <- makeBoxes rest dest
  return $ BoxedRef (Bind (v:>ptrTy)) ptrPtr numel dest'

makeBaseTypePtr :: BaseType -> DestM Atom
makeBaseTypePtr ty = do
  DestEnv allocInfo idxs _ <- ask
  numel <- buildScoped $ elemCountE idxs
  ptrScope <- fmap (const $ ImpBound) <$> look
  scope <- getScope
  -- We use a different namespace because these will be hoisted to the top
  -- where they could cast shadows
  let addrSpace = chooseAddrSpace allocInfo numel
  let ptrName = genFresh (Name AllocPtrName "ptr" 0) (scope <> ptrScope)
  let ptrTy = PtrTy (addrSpace, ty)
  extend (ptrName @> (ptrTy, numel))
  let ptr = Var (ptrName :> ptrTy)
  applyIdxs ptr idxs

withEnclosingIdxs :: Binder -> DestM a -> DestM a
withEnclosingIdxs i m =
  local (\env -> env {enclosingIdxs = enclosingIdxs env <> Nest i Empty}) m

withDepVar :: Binder -> DestM a -> DestM a
withDepVar v m =
  local (\env -> env {destDepVars = destDepVars env <> (v@>())}) m

makeDataConDest :: Nest Binder -> DestM (Nest DataConRefBinding)
makeDataConDest Empty = return Empty
makeDataConDest (Nest b rest) = do
  let ty = binderAnn b
  dest <- makeDestRec ty
  v <- withNameHint b $ freshVarE UnknownBinder ty  -- TODO: scope names more carefully
  rest'  <- substBuilder (b @> SubstVal (Var v)) rest
  rest'' <- withDepVar (Bind v) $ makeDataConDest rest'
  return $ Nest (DataConRefBinding (Bind v) dest) rest''

copyAtom :: Dest -> Atom -> ImpM ()
copyAtom topDest topSrc = do
  backend <- asks impBackend
  device  <- asks curDevice
  let canParallelize = backend == LLVMCUDA && device == CPU
  copyRec canParallelize topDest topSrc
  where
    copyRec canParallelize dest src = case (dest, src) of
      (BoxedRef b ptrPtr size body, _) -> do
        -- TODO: load old ptr and free (recursively)
        let PtrTy ptrTy = binderAnn b
        size' <- translateBlock mempty (Nothing, size)
        ptr <- emitAlloc ptrTy $ fromScalarAtom size'
        body' <- impSubst (b@>SubstVal (toScalarAtom ptr)) body
        rec body' src
        storeAnywhere (fromScalarAtom ptrPtr) ptr
      (DataConRef _ _ refs, DataCon _ _ _ vals) -> copyDataConArgs refs vals
      (DepPairRef lr rra _, DepPair l r _) ->
        copyAtom lr l >> copyAtom (applyAbs rra l) r
      (Con destRefCon, _) -> case (destRefCon, src) of
        (BaseTypeRef ptr, _) -> storeAnywhere (fromScalarAtom ptr) (fromScalarAtom src)
        (TabRef _, TabVal _ _) -> case (canParallelize, tryParallelCopy) of
          (True, Just parallelCopy) -> parallelCopy
          _ -> zipTabDestAtom rec dest src
        (ConRef (SumAsProd _ tag payload), DataCon _ _ con x) -> do
          rec tag $ TagRepVal $ fromIntegral con
          zipWithM_ rec (payload !! con) x
        (ConRef (SumAsProd _ tag payload), SumVal _ con x) -> do
          rec tag $ TagRepVal $ fromIntegral con
          case payload !! con of
            [xDest] -> rec xDest x
            _       -> error "Expected singleton payload in SumAsProd"
        (ConRef (SumAsProd _ tagDest payloadDest), Con (SumAsProd _ tag payload)) -> do
          rec tagDest tag
          unless (all null payload) $ -- optimization
            emitSwitch (fromScalarAtom tag) $
              zipWith (zipWithM_ rec) payloadDest payload
        (ConRef destCon, Con srcCon) -> zipWithRefConM rec destCon srcCon
        (RecordRef refs, Record vals)
          | fmap (const ()) refs == fmap (const ()) vals -> do
              zipWithM_ rec (toList refs) (toList vals)
        (ConRef (SumAsProd _ tag payload), Variant (NoExt types) label i x) -> do
          let LabeledItems ixtypes = enumerate types
          let index = fst $ (ixtypes M.! label) NE.!! i
          rec tag (TagRepVal $ fromIntegral index)
          zipWithM_ rec (payload !! index) [x]
        _ -> error $ "Not implemented: " ++ pprint (dest, src)
      _ -> error $ "Not a valid dest-source pair: " ++ pprint (dest, src)
      where
        rec = copyRec canParallelize

        tryParallelCopy :: Maybe (ImpM ())
        tryParallelCopy =
          case flattenIndexSet (getType src) of
            Nothing -> Nothing
            Just [] -> Nothing  -- No point in parallelizing a scalar store
            Just idxTys -> do
              let (flatIndex, indexBundleDesc) = mkBundleTy idxTys
              return $ void $ fromBuilder $ do
                buildForAnn ParallelFor (Bind $ "pari" :> flatIndex) \pari -> do
                  indices <- unpackBundle pari indexBundleDesc
                  destElem <- foldM indexDest dest indices
                  srcElem <- foldM app src indices
                  emitOp $ PrimEffect destElem $ MPut srcElem  -- XXX: Not sure if this is well typed?

        -- TODO: We should really be able to do parallel copies on anything that doesn't
        -- include boxed refs. We don't need to be quite as strict as asserting that the
        -- table ends with a base type.
        flattenIndexSet :: Type -> Maybe [Type]
        flattenIndexSet ty = go [] ty
          where
            go idxs (TabTy (Ignore n) a) = go (n:idxs) a
            go idxs (BaseTy _) = Just $ reverse idxs
            go _ _ = Nothing


copyDataConArgs :: Nest DataConRefBinding -> [Atom] -> ImpM ()
copyDataConArgs Empty [] = return ()
copyDataConArgs (Nest (DataConRefBinding b ref) rest) (x:xs) = do
  copyAtom ref x
  rest' <- impSubst (b@>SubstVal x) rest
  copyDataConArgs rest' xs
copyDataConArgs bindings args =
  error $ "Mismatched bindings/args: " ++ pprint (bindings, args)

loadDest :: MonadBuilder m => Dest -> m Atom
loadDest (BoxedRef b ptrPtr _ body) = do
  ptr <- unsafePtrLoad ptrPtr
  body' <- substBuilder (b@>SubstVal ptr) body
  loadDest body'
loadDest (DataConRef def params bs) = do
  DataCon def params 0 <$> loadDataConArgs bs
loadDest (DepPairRef lr rra a) = do
  l <- loadDest lr
  r <- loadDest $ applyAbs rra l
  return $ DepPair l r a
loadDest (Con dest) = do
 case dest of
  BaseTypeRef ptr -> unsafePtrLoad ptr
  TabRef (TabVal b body) -> buildLam b TabArrow \i -> do
    body' <- substBuilder (b@>SubstVal i) body
    result <- emitBlock body'
    loadDest result
  RecordRef xs -> Record <$> traverse loadDest xs
  ConRef con -> Con <$> case con of
    ProdCon ds -> ProdCon <$> traverse loadDest ds
    SumAsProd ty tag xss -> SumAsProd ty <$> loadDest tag <*> mapM (mapM loadDest) xss
    IntRangeVal     l h iRef -> IntRangeVal     l h <$> loadDest iRef
    IndexRangeVal t l h iRef -> IndexRangeVal t l h <$> loadDest iRef
    _        -> error $ "Not a valid dest: " ++ pprint dest
  _          -> error $ "Not a valid dest: " ++ pprint dest
loadDest dest = error $ "Not a valid dest: " ++ pprint dest

loadDataConArgs :: MonadBuilder m => Nest DataConRefBinding -> m [Atom]
loadDataConArgs Empty = return []
loadDataConArgs (Nest (DataConRefBinding b ref) rest) = do
  val <- loadDest ref
  rest' <- substBuilder (b@> SubstVal val) rest
  (val:) <$> loadDataConArgs rest'

indexDestDim :: MonadBuilder m => Int->Dest -> Atom -> m Dest
indexDestDim 0 dest i = indexDest dest i
indexDestDim d dest i = buildFor Fwd (Bind ("i":>idxTy)) \j -> do
  dest' <- indexDest dest j
  indexDestDim (d-1) dest' i
  where
    RawRefTy (TabTy idxBinder _) = dest
    idxTy = binderType idxBinder

indexDest :: MonadBuilder m => Dest -> Atom -> m Dest
indexDest (Con (TabRef tabVal)) i = appReduce tabVal i
indexDest dest _ = error $ pprint dest

sliceDestDim :: MonadBuilder m => Int -> Dest -> Atom -> Type -> m Dest
sliceDestDim 0 dest i sliceIdxTy = sliceDest dest i sliceIdxTy
sliceDestDim d dest i sliceIdxTy = buildFor Fwd (Bind ("i":>idxTy)) \j -> do
  dest' <- indexDest dest j
  sliceDestDim (d-1) dest' i sliceIdxTy
  where
    RawRefTy (TabTy idxBinder _) = dest
    idxTy = binderType idxBinder

sliceDest :: MonadBuilder m => Dest -> Atom -> Type -> m Dest
sliceDest ~(Con (TabRef tab@(TabVal b _))) i sliceIdxTy = (Con . TabRef) <$> do
  buildFor Fwd (Bind ("j" :> sliceIdxTy)) \j -> do
    j' <- indexToIntE j
    ioff <- iadd j' i
    vidx <- intToIndexE (binderType b) ioff
    appReduce tab vidx

destToAtom :: Dest -> ImpM Atom
destToAtom dest = fromBuilder $ loadDest dest

destGet :: Dest -> Atom -> ImpM Dest
destGet dest i = fromBuilder $ indexDest dest i

destPairUnpack :: Dest -> (Dest, Dest)
destPairUnpack (Con (ConRef (ProdCon [l, r]))) = (l, r)
destPairUnpack d = error $ "Not a pair destination: " ++ show d

fromDestConsList :: Dest -> [Dest]
fromDestConsList dest = case dest of
  Con (ConRef (ProdCon [h, t])) -> h : fromDestConsList t
  Con (ConRef (ProdCon []))     -> []
  _ -> error $ "Not a dest cons list: " ++ pprint dest

makeAllocDest :: AllocType -> Type -> ImpM Dest
makeAllocDest allocTy ty = fst <$> makeAllocDestWithPtrs allocTy ty

makeAllocDestWithPtrs :: AllocType -> Type -> ImpM (Dest, [IExpr])
makeAllocDestWithPtrs allocTy ty = do
  backend <- asks impBackend
  curDev <- asks curDevice
  (ptrsSizes, dest) <- fromBuilder $ makeDest (backend, curDev, allocTy) ty
  (env, ptrs) <- flip foldMapM ptrsSizes \(Bind (ptr:>PtrTy ptrTy), size) -> do
    ptr' <- emitAlloc ptrTy $ fromScalarAtom size
    case ptrTy of
      (Heap _, _) | allocTy == Managed -> extendAlloc ptr'
      _ -> return ()
    return (ptr @> SubstVal (toScalarAtom ptr'), [ptr'])
  dest' <- impSubst env dest
  return (dest', ptrs)

splitDest :: WithDest Block -> ([WithDest Decl], WithDest Expr, [(Dest, Atom)])
splitDest (maybeDest, (Block decls ans)) = do
  case (maybeDest, ans) of
    (Just dest, Atom atom) -> do
      let (gatherCopies, varDests) = runState (execWriterT $ gatherVarDests dest atom) mempty
      -- If any variable appearing in the ans atom is not defined in the
      -- current block (e.g. it comes from the surrounding block), then we need
      -- to do the copy explicitly, as there is no let binding that will use it
      -- as the destination.
      let closureCopies = fmap (\(n, (d, t)) -> (d, Var $ n :> t))
                               (envPairs $ varDests `envDiff` foldMap letBoundVars decls)
      let destDecls = flip fmap (toList decls) \d -> case d of
                        Let _ b _  -> (fst <$> varDests `envLookup` b, d)
      (destDecls, (Nothing, ans), gatherCopies ++ closureCopies)
    _ -> (fmap (Nothing,) $ toList decls, (maybeDest, ans), [])
  where
    -- Maps all variables used in the result atom to their respective destinations.
    gatherVarDests :: Dest -> Atom -> WriterT [(Dest, Atom)] (State (Env (Dest, Type))) ()
    gatherVarDests dest result = case (dest, result) of
      (_, Var v) -> do
        dests <- get
        case dests `envLookup` v of
          Nothing -> modify $ (<> (v @> (dest, varType v)))
          Just _  -> tell [(dest, result)]
      -- If the result is a table lambda then we can propagate the dest if and only if
      -- it is an injective view on another array.
      (_, TabVal _ _)  -> case adaptBijectiveTableView dest result of
        Just (v, vDest) -> modify $ (<> (v @> (vDest, varType v)))
        Nothing         -> tell [(dest, result)]
      (_, Con (Lit _)) -> tell [(dest, result)]
      -- This is conservative, in case the type is dependent. We could do better.
      (DataConRef _ _ _, DataCon _ _ _ _) -> tell [(dest, result)]
      (DepPairRef _ _ _, DepPair _ _ _  ) -> tell [(dest, result)]
      -- This is conservative. Without it, we hit bugs like #348
      (Con (ConRef (SumAsProd _ _ _)), _) -> tell [(dest, result)]
      (Con (ConRef destCon), Con srcCon) -> do
        zipWithRefConM gatherVarDests destCon srcCon
      (Con (RecordRef items), Record items')
        | fmap (const ()) items == fmap (const ()) items' -> do
            zipWithM_ gatherVarDests (toList items) (toList items')
      (_, ProjectElt _ _) -> tell [(dest, result)]  -- TODO: is this reasonable?
      _ -> unreachable
      where
        unreachable = error $ "Invalid dest-result pair:\n"
                        ++ pprint dest ++ "\n  and:\n" ++ pprint result

    -- This lets us propagate destinations upward for table views such as this one:
    --  (\for pari:(Fin 128) j:(Fin 128) k:(Fin 32) => tmp (pari, (j, k)))
    adaptBijectiveTableView :: Dest -> Atom -> Maybe (Var, Dest)
    adaptBijectiveTableView dest result = do
      (loopBinders, block) <- gatherLoopBinders [] result
      let resultClosure = freeVars block `envDiff` foldMap binderAsEnv loopBinders
      case bindingsAsVars resultClosure of
        [array] -> do
          indices <- getBodyExpr (Var array) block
          arrayDest <- adaptDest loopBinders indices
          -- traceCheckM arrayDest
          -- error $ pprint arrayDest
          return (array, arrayDest)
        _ -> Nothing
      where
        gatherLoopBinders :: [Binder] -> Atom -> Maybe ([Binder], Block)
        gatherLoopBinders bs res = case res of
          TabVal b (Block Empty (Atom r)) -> gatherLoopBinders (b:bs) r
          TabVal b block                  -> Just (reverse (b:bs), block)
          _                               -> Nothing

        getBodyExpr :: Atom -> Block -> Maybe [Atom]
        getBodyExpr array block = go [] array block
          where
            go :: [Atom] -> Atom -> Block -> Maybe [Atom]
            go idxs slice (Block Empty (App slice' idx))
              | slice == slice' = return $ reverse $ idx:idxs
            go idxs slice (Block (Nest (Let _ (Bind newSlice) (App slice' idx)) t) e)
              | slice == slice' = go (idx:idxs) (Var newSlice) $ Block t e
            go _ _ _ = Nothing

        -- TODO: Think hard about scoping (in both runBuilder and buildLam)!!!
        adaptDest :: [Binder] -> [Atom] -> Maybe Dest
        adaptDest loopBinders indices = fst <$> runBuilderT mempty mempty (go mempty indices)
          where
            go :: Env Atom -> [Atom] -> BuilderT Maybe Dest
            go env [] = do
              let reindexDest d b = indexDest d (env ! b)
              foldM reindexDest dest loopBinders
            go env (idx:idxs) = do
              lam <- buildLam (Bind $ "q":>getType idx) TabArrow \newIdx -> do
                env' <- lift $ idxProjectionEnv idx newIdx
                -- TODO: What about indices with dependent types?
                case null $ env `envIntersect` env' of
                  True  -> go (env <> env') idxs
                  False -> lift $ Nothing  -- Non-bijective indexing!
              return $ Con $ TabRef lam

            idxProjectionEnv :: Atom -> Atom -> Maybe (Env Atom)
            idxProjectionEnv (Var v) newIdx = Just $ v @> newIdx
            idxProjectionEnv (PairVal l r) newIdx =
              (<>) <$> (idxProjectionEnv l (getProjection [0] newIdx))
                   <*> (idxProjectionEnv r (getProjection [1] newIdx))
            idxProjectionEnv _ _ = Nothing

letBoundVars :: Decl -> Env ()
letBoundVars (Let _ b _) = b @> ()

copyDest :: Maybe Dest -> Atom -> ImpM Atom
copyDest maybeDest atom = case maybeDest of
  Nothing   -> return atom
  Just dest -> copyAtom dest atom >> return atom

allocDest :: Maybe Dest -> Type -> ImpM Dest
allocDest maybeDest t = case maybeDest of
  Nothing   -> alloc t
  Just dest -> return dest

type AllocInfo = (Backend, Device, AllocType)

chooseAddrSpace :: AllocInfo -> Block -> AddressSpace
chooseAddrSpace (backend, curDev, allocTy) numel = case allocTy of
  Unmanaged -> Heap mainDev
  Managed | curDev == mainDev -> if isSmall numel then Stack
                                                  else Heap mainDev
          | otherwise -> Heap mainDev
  where mainDev = case backend of
          LLVM      -> CPU
          LLVMMC    -> CPU
          LLVMCUDA  -> GPU
          MLIR      -> error "Shouldn't be compiling to Imp with MLIR backend"
          Interpreter -> error "Shouldn't be compiling to Imp with interpreter backend"

isSmall :: Block -> Bool
isSmall numel = case numel of
  Block Empty (Atom (Con (Lit l)))
    | getIntLit l <= 256 -> True
    | otherwise          -> False
  -- TODO: remove this check if we're convinced it's always passing
  _ | null (freeVars numel) ->
        error $ "Blocks without free vars should have been fully reduced"
          ++ pprint numel
    | otherwise -> False

allocateBuffer :: AddressSpace -> Bool -> BaseType -> IExpr -> ImpM IExpr
allocateBuffer addrSpace mustFree b numel = do
  buffer <- emitAlloc (addrSpace, b) numel
  when mustFree $ extendAlloc buffer
  return buffer

-- TODO: separate these concepts in IFunType?
deviceFromCallingConvention :: CallingConvention -> Device
deviceFromCallingConvention cc = case cc of
  CEntryFun         -> CPU
  EntryFun _        -> CPU
  FFIFun            -> CPU
  FFIMultiResultFun -> CPU
  MCThreadLaunch    -> CPU
  CUDAKernelLaunch  -> GPU

-- === Atom <-> IExpr conversions ===

fromScalarAtom :: HasCallStack => Atom -> IExpr
fromScalarAtom atom = case atom of
  Var (v:>BaseTy b) -> IVar (v :> b)
  Con (Lit x)       -> ILit x
  _ -> error $ "Expected scalar, got: " ++ pprint atom

toScalarAtom :: IExpr -> Atom
toScalarAtom ie = case ie of
  ILit l -> Con $ Lit l
  IVar (v:>b) -> Var (v:>BaseTy b)

fromScalarType :: HasCallStack => Type -> IType
fromScalarType (BaseTy b) =  b
fromScalarType ty = error $ "Not a scalar type: " ++ pprint ty

toScalarType :: IType -> Type
toScalarType b = BaseTy b

-- === Type classes ===

fromBuilder :: Subst a => Builder a -> ImpM a
fromBuilder m = do
  scope <- variableScope
  let (ans, (_, decls)) = runBuilder scope mempty m
  env <- catFoldM translateDecl mempty $ fmap (Nothing,) decls
  impSubst env ans

intToIndex :: Type -> IExpr -> ImpM Atom
intToIndex ty i = fromBuilder (intToIndexE ty (toScalarAtom i))

indexToInt :: Atom -> ImpM IExpr
indexToInt idx = fromScalarAtom <$> fromBuilder (indexToIntE idx)

indexSetSize :: Type -> ImpM IExpr
indexSetSize ty = fromScalarAtom <$> fromBuilder (indexSetSizeE ty)

zipTabDestAtom :: HasCallStack => (Dest -> Atom -> ImpM ()) -> Dest -> Atom -> ImpM ()
zipTabDestAtom f ~dest@(Con (TabRef (TabVal b _))) ~src@(TabVal b' _) = do
  unless (binderType b == binderType b') $
    error $ "Mismatched dimensions: " <> pprint b <> " != " <> pprint b'
  let idxTy = binderType b
  n <- indexSetSize idxTy
  emitLoop "i" Fwd n \i -> do
    idx <- intToIndex idxTy i
    destIndexed <- destGet dest idx
    srcIndexed  <- translateExpr mempty (Nothing, App src idx)
    f destIndexed srcIndexed

zipWithRefConM :: HasCallStack => Monad m => (Dest -> Atom -> m ()) -> Con -> Con -> m ()
zipWithRefConM f destCon srcCon = case (destCon, srcCon) of
  (ProdCon ds, ProdCon ss) -> zipWithM_ f ds ss
  (IntRangeVal     _ _ iRef, IntRangeVal     _ _ i) -> f iRef i
  (IndexRangeVal _ _ _ iRef, IndexRangeVal _ _ _ i) -> f iRef i
  _ -> error $ "Unexpected ref/val " ++ pprint (destCon, srcCon)

loadAnywhere :: IExpr -> ImpM IExpr
loadAnywhere ptr = do
  curDev <- asks curDevice
  let (PtrType (addrSpace, ty)) = getIType ptr
  case addrSpace of
    Heap ptrDev | ptrDev /= curDev -> do
      localPtr <- allocateStackSingleton ty
      memcopy localPtr ptr (IIdxRepVal 1)
      load localPtr
    _ -> load ptr

storeAnywhere :: IExpr -> IExpr -> ImpM ()
storeAnywhere ptr val = do
  curDev <- asks curDevice
  let (PtrType (addrSpace, ty)) = getIType ptr
  case addrSpace of
    Heap ptrDev | ptrDev /= curDev -> do
      localPtr <- allocateStackSingleton ty
      store localPtr val
      memcopy ptr localPtr (IIdxRepVal 1)
    _ -> store ptr val

allocateStackSingleton :: IType -> ImpM IExpr
allocateStackSingleton ty = allocateBuffer Stack False ty (IIdxRepVal 1)

-- === Imp IR builders ===

buildBinOp :: (Atom -> Atom -> Builder Atom) -> (IExpr -> IExpr -> ImpM IExpr)
buildBinOp f x y =
  fromScalarAtom <$> fromBuilder (f (toScalarAtom x) (toScalarAtom y))

iaddI :: IExpr -> IExpr -> ImpM IExpr
iaddI = buildBinOp iadd

isubI :: IExpr -> IExpr -> ImpM IExpr
isubI = buildBinOp isub

imulI :: IExpr -> IExpr -> ImpM IExpr
imulI = buildBinOp imul

idivI :: IExpr -> IExpr -> ImpM IExpr
idivI = buildBinOp idiv

iltI :: IExpr -> IExpr -> ImpM IExpr
iltI = buildBinOp ilt

ieqI :: IExpr -> IExpr -> ImpM IExpr
ieqI = buildBinOp ieq

bandI :: IExpr -> IExpr -> ImpM IExpr
bandI x y = emitInstr $ IPrimOp $ ScalarBinOp BAnd x y

impOffset :: IExpr -> IExpr -> ImpM IExpr
impOffset ref off = emitInstr $ IPrimOp $ PtrOffset ref off

cast :: IExpr -> BaseType -> ImpM IExpr
cast x bt = emitInstr $ ICastOp bt x

load :: IExpr -> ImpM IExpr
load x = emitInstr $ IPrimOp $ PtrLoad x

memcopy :: IExpr -> IExpr -> IExpr -> ImpM ()
memcopy dest src numel = emitStatement $ MemCopy dest src numel

store :: HasCallStack => IExpr -> IExpr -> ImpM ()
store dest src = emitStatement $ Store dest src

alloc :: HasCallStack => Type -> ImpM Dest
alloc ty = makeAllocDest Managed ty

handleErrors :: ImpM () -> ImpM ()
handleErrors m = m `catchError` (const $ emitStatement IThrowError)

emitWhen :: IExpr -> ImpM () -> ImpM ()
emitWhen cond doIfTrue = emitSwitch cond [return (), doIfTrue]

-- TODO: Consider targeting LLVM's `switch` instead of chained conditionals.
emitSwitch :: IExpr -> [ImpM ()] -> ImpM ()
emitSwitch testIdx = rec 0
  where
    rec :: Int -> [ImpM ()] -> ImpM ()
    rec _ [] = error "Shouldn't have an empty list of alternatives"
    rec _ [body] = body
    rec curIdx (body:rest) = do
      let curTag = fromScalarAtom $ TagRepVal $ fromIntegral curIdx
      cond       <- emitInstr $ IPrimOp $ ScalarBinOp (ICmp Equal) testIdx curTag
      thisCase   <- scopedErrBlock $ body
      otherCases <- scopedErrBlock $ rec (curIdx + 1) rest
      emitStatement $ ICond cond thisCase otherCases

emitLoop :: Name -> Direction -> IExpr -> (IExpr -> ImpM ()) -> ImpM ()
emitLoop hint d n body = do
  (i, loopBody) <- scopedBlock $ do
    i <- freshVar (hint:>getIType n)
    handleErrors $ body $ IVar i
    return (i, [])
  emitStatement $ IFor d (Bind i) n loopBody

fromScalarOrPairType :: Type -> [IType]
fromScalarOrPairType (PairTy a b) =
  fromScalarOrPairType a <> fromScalarOrPairType b
fromScalarOrPairType (BaseTy ty) = [ty]
fromScalarOrPairType ty = error $ "Not a scalar or pair: " ++ pprint ty

restructureScalarOrPairType :: Type -> [IExpr] -> Atom
restructureScalarOrPairType ty xs =
  case restructureScalarOrPairTypeRec ty xs of
    (atom, []) -> atom
    _ -> error "Wrong number of scalars"

restructureScalarOrPairTypeRec :: Type -> [IExpr] -> (Atom, [IExpr])
restructureScalarOrPairTypeRec (PairTy t1 t2) xs = do
  let (atom1, rest1) = restructureScalarOrPairTypeRec t1 xs
  let (atom2, rest2) = restructureScalarOrPairTypeRec t2 rest1
  (PairVal atom1 atom2, rest2)
restructureScalarOrPairTypeRec (BaseTy _) (x:xs) = (toScalarAtom x, xs)
restructureScalarOrPairTypeRec ty _ = error $ "Not a scalar or pair: " ++ pprint ty

emitMultiReturnInstr :: ImpInstr -> ImpM [IExpr]
emitMultiReturnInstr instr = do
  vs <- forM (impInstrTypes instr) \ty -> freshVar ("v":>ty)
  emitImpDecl $ ImpLet (map Bind vs) instr
  return (map IVar vs)

emitInstr :: ImpInstr -> ImpM IExpr
emitInstr instr = do
  xs <- emitMultiReturnInstr instr
  case xs of
    [x] -> return x
    _ -> error "unexpected numer of return values"

emitStatement :: ImpInstr -> ImpM ()
emitStatement instr = do
  xs <- emitMultiReturnInstr instr
  case xs of
    [] -> return ()
    _ -> error "unexpected numer of return values"

data AllocType = Managed | Unmanaged  deriving (Show, Eq)

extendAlloc :: IExpr -> ImpM ()
extendAlloc v = extend $ mempty { envPtrsToFree = [v] }

emitAlloc :: HasCallStack => PtrType -> IExpr -> ImpM IExpr
emitAlloc (addr, ty) n = emitInstr $ Alloc addr ty n

scopedErrBlock :: ImpM () -> ImpM ImpBlock
scopedErrBlock body = liftM snd $ scopedBlock $ handleErrors body $> ((),[])

-- XXX: This does not handle errors that happen inside the block!
scopedBlock :: ImpM (a, [IExpr]) -> ImpM (a, ImpBlock)
scopedBlock body = do
  ((aux, results), env) <- scoped body
  -- Keep the scope extension to avoid reusing variable names
  extend $ mempty { envScope     = envScope     env
                  , envFunctions = envFunctions env }
  let frees = [ImpLet [] (Free x) | x <- envPtrsToFree env]
  return (aux, ImpBlock (toNest (envDecls env <> frees)) results)

emitImpDecl :: ImpDecl -> ImpM ()
emitImpDecl decl = extend $ mempty { envDecls = [decl] }

variableScope :: ImpM Scope
variableScope = looks envScope

freshVar :: VarP a -> ImpM (VarP a)
freshVar (hint:>t) = do
  scope <- looks envScope
  let v = genFresh (rawName GenName $ nameTag hint) scope
  extend $ mempty { envScope = v @> ImpBound }
  return $ v:>t

withLevel :: ParallelismLevel -> ImpM a -> ImpM a
withLevel level = local (\opts -> opts {curLevel = level })

withDevice :: Device -> ImpM a -> ImpM a
withDevice device = local (\opts -> opts {curDevice = device })

-- === type checking imp programs ===

-- TODO: track parallelism level and current device and add validity checks like
-- "shouldn't launch a kernel from device/thread code"

-- State keeps track of _all_ names used in the program, Reader keeps the type env.
type ImpCheckM a = StateT (Env ()) (ReaderT (Env IType, Device) Except) a

instance Checkable ImpModule where
  -- TODO: check main function defined
  checkValid scope (ImpModule fs) = mapM_ (checkValid scope) fs

instance Checkable ImpFunction where
  checkValid _ f@(ImpFunction (_:> IFunType cc _ _) bs block) = addContext ctx $ do
    let scope = foldMap (binderAsEnv . fmap (const ())) bs
    let env   = foldMap (binderAsEnv                  ) bs
    void $ flip runReaderT (env, deviceFromCallingConvention cc) $
      flip runStateT scope $ checkBlock block
    where ctx = "Checking:\n" ++ pprint f
  checkValid _ (FFIFunction _) = return ()

checkBlock :: ImpBlock -> ImpCheckM [IType]
checkBlock (ImpBlock Empty val) = mapM checkIExpr val
checkBlock (ImpBlock (Nest decl rest) val) = do
  env <- checkDecl decl
  withTypeEnv env $ checkBlock $ ImpBlock rest val

checkDecl :: ImpDecl -> ImpCheckM (Env IType)
checkDecl decl@(ImpLet bs instr) = addContext ctx $ do
  tys <- instrTypeChecked instr
  mapM_ checkBinder bs
  assertEq (map binderAnn bs) tys $ "Type mismatch in decl " ++ pprint decl
  return $ newEnv bs tys
  where ctx = "Checking:\n" ++ pprint decl

instrTypeChecked :: ImpInstr -> ImpCheckM [IType]
instrTypeChecked instr = case instr of
  IFor _ i size block -> do
    checkIdxRep size
    checkBinder i
    assertEq (binderAnn i) (getIType size) $ "Mismatch between the loop iterator and upper bound type"
    [] <- withTypeEnv (i @> getIType size) $ checkBlock block
    return []
  IWhile body -> do
    [condTy] <- checkBlock body
    assertEq (Scalar Word8Type) condTy $ "Not a bool: " ++ pprint body
    return []
  ICond predicate consequent alternative -> do
    predTy <- checkIExpr predicate
    assertEq (Scalar Word8Type) predTy "Type mismatch in predicate"
    [] <- checkBlock consequent
    [] <- checkBlock alternative
    return []
  ISyncWorkgroup -> return []
  IQueryParallelism _ _ -> return [IIdxRepTy, IIdxRepTy]
  ILaunch _ n args -> [] <$ do
    -- TODO: check args against type of function
    assertHost
    checkInt n
    mapM_ checkIExpr args
  IPrimOp op -> (:[]) <$> checkImpOp op
  ICastOp dt x -> (:[]) <$> do
    let st = getIType x
    case (dt, st) of
      (PtrType _, PtrType _) -> return ()
      (Scalar  _, Scalar  _) -> return ()
      (Scalar Int64Type, PtrType  _) -> return ()
      (PtrType _,  Scalar Int64Type) -> return ()
      _ -> throw CompilerErr $
            "Can't cast " ++ pprint st ++ " to " ++ pprint dt
    return dt
  Alloc a ty n -> (:[]) <$> do
    checkIdxRep n
    when (a /= Stack) assertHost
    return $ PtrType (a, ty)
  MemCopy dest src numel -> [] <$ do
    PtrType (_, destTy) <- checkIExpr dest
    PtrType (_, srcTy)  <- checkIExpr src
    assertEq destTy srcTy "pointer type mismatch"
    checkIdxRep numel
  Store dest val -> [] <$ do
    PtrType (addr, ty) <- checkIExpr dest
    checkAddrAccessible addr
    valTy <- checkIExpr val
    assertEq ty valTy "Type mismatch in store"
  Free _ -> return []  -- TODO: check matched alloc/free
  IThrowError -> return []
  ICall (_:>IFunType _ argTys resultTys) args -> do
    argTys' <- mapM checkIExpr args
    assertEq argTys argTys' "Args types don't match function type"
    return resultTys

checkBinder :: IBinder -> ImpCheckM ()
checkBinder v = do
  scope <- get
  when (v `isin` scope) $ throw CompilerErr $ "shadows: " ++ pprint v
  modify (<>(v@>()))

checkAddrAccessible :: AddressSpace -> ImpCheckM ()
checkAddrAccessible Stack = return ()
checkAddrAccessible (Heap device) = do
  curDev <- asks snd
  when (device /= curDev) $ throw CompilerErr "Address not accessible"

assertHost :: ImpCheckM ()
assertHost = do
  curDev <- asks snd
  when (curDev /= CPU) $ throw CompilerErr "Only allowed on host"

checkIExpr :: IExpr -> ImpCheckM IType
checkIExpr expr = case expr of
  ILit val -> return $ litType val
  IVar v -> do
    env <- asks fst
    case envLookup env v of
      Nothing -> throw CompilerErr $ "Lookup failed: " ++ pprint v
      Just x -> return x

checkIdxRep :: IExpr -> ImpCheckM ()
checkIdxRep expr = do
  t <- checkIExpr expr
  assertEq IIdxRepTy t $ "Not an index rep tye: " ++ pprint t

checkInt :: IExpr -> ImpCheckM ()
checkInt expr = do
  bt <- checkIExpr expr
  checkIntBaseType False (BaseTy bt)

-- TODO: reuse type rules in Type.hs
checkImpOp :: IPrimOp -> ImpCheckM IType
checkImpOp op = do
  op' <- traverse checkIExpr op
  case op' of
    ScalarBinOp bop x y -> checkImpBinOp bop x y
    VectorBinOp bop x y -> checkImpBinOp bop x y
    ScalarUnOp  uop x   -> checkImpUnOp  uop x
    Select _ x y -> checkEq x y >> return x
    VectorPack xs -> do
      Scalar ty <- return $ head xs
      mapM_ (checkEq (Scalar ty)) xs
      return $ Vector ty
    VectorIndex x i -> do
      Vector ty <- return x
      ibt       <- return i
      checkIntBaseType False $ BaseTy ibt
      return $ Scalar ty
    PtrLoad ref -> do
      PtrType (addr, ty) <- return ref
      checkAddrAccessible addr
      return ty
    PtrOffset ref _ -> do  -- TODO: check offset too
      PtrType (addr, ty) <- return ref
      return $ PtrType (addr, ty)
    OutputStreamPtr -> return $ hostPtrTy $ hostPtrTy $ Scalar Word8Type
      where hostPtrTy ty = PtrType (Heap CPU, ty)
    _ -> error $ "Not allowed in Imp IR: " ++ pprint op
  where
    checkEq :: (Pretty a, Show a, Eq a) => a -> a -> ImpCheckM ()
    checkEq t t' = assertEq t t' (pprint op)

class HasIType a where
  getIType :: a -> IType

instance HasIType IExpr where
  getIType x = case x of
    ILit val -> litType val
    IVar v   -> varAnn v

impFunType :: ImpFunction -> IFunType
impFunType = varAnn . impFunVar

impFunVar :: ImpFunction -> IFunVar
impFunVar (ImpFunction v _ _) = v
impFunVar (FFIFunction v) = v

impBlockType :: ImpBlock -> [IType]
impBlockType (ImpBlock _ results) = map getIType results

impInstrTypes :: ImpInstr -> [IType]
impInstrTypes instr = case instr of
  IPrimOp op      -> [impOpType op]
  ICastOp t _     -> [t]
  Alloc a ty _    -> [PtrType (a, ty)]
  Store _ _       -> []
  Free _          -> []
  IThrowError     -> []
  MemCopy _ _ _   -> []
  IFor _ _ _ _    -> []
  IWhile _        -> []
  ICond _ _ _     -> []
  ILaunch _ _ _   -> []
  ISyncWorkgroup  -> []
  IQueryParallelism _ _ -> [IIdxRepTy, IIdxRepTy]
  ICall (_:>IFunType _ _ resultTys) _ -> resultTys

checkImpBinOp :: Fallible m => BinOp -> IType -> IType -> m IType
checkImpBinOp op x y = do
  retTy <- checkBinOp True op (BaseTy x) (BaseTy y)
  case retTy of
    BaseTy bt -> return bt
    _         -> throw CompilerErr $ "Unexpected BinOp return type: " ++ pprint retTy

checkImpUnOp :: Fallible m => UnOp -> IType -> m IType
checkImpUnOp op x = do
  retTy <- checkUnOp op (BaseTy x)
  case retTy of
    BaseTy bt -> return bt
    _         -> throw CompilerErr $ "Unexpected UnOp return type: " ++ pprint retTy

-- TODO: reuse type rules in Type.hs
impOpType :: IPrimOp -> IType
impOpType pop = case pop of
  ScalarBinOp op x y -> ignoreExcept $ checkImpBinOp op (getIType x) (getIType y)
  ScalarUnOp  op x   -> ignoreExcept $ checkImpUnOp  op (getIType x)
  VectorBinOp op x y -> ignoreExcept $ checkImpBinOp op (getIType x) (getIType y)
  Select  _ x  _     -> getIType x
  VectorPack xs      -> Vector ty  where Scalar ty = getIType $ head xs
  VectorIndex x _    -> Scalar ty  where Vector ty = getIType x
  PtrLoad ref        -> ty  where PtrType (_, ty) = getIType ref
  PtrOffset ref _    -> PtrType (addr, ty)  where PtrType (addr, ty) = getIType ref
  OutputStreamPtr -> hostPtrTy $ hostPtrTy $ Scalar Word8Type
    where hostPtrTy ty = PtrType (Heap CPU, ty)
  _ -> unreachable
  where unreachable = error $ "Not allowed in Imp IR: " ++ pprint pop

withTypeEnv :: Env IType -> ImpCheckM a -> ImpCheckM a
withTypeEnv env m = local (\(prev, dev) -> (prev <> env, dev)) m

instance Semigroup ImpCatEnv where
  (ImpCatEnv a b c d) <> (ImpCatEnv a' b' c' d') =
    ImpCatEnv (a<>a') (b<>b') (c<>c') (d<>d')

instance Monoid ImpCatEnv where
  mempty = ImpCatEnv mempty mempty mempty mempty
  mappend = (<>)
