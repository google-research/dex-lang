-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE Rank2Types #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Imp (toScalarType, fromScalarType) where
-- module Imp (toImpModule, getIType, impBlockType, impFunType, impFunVar,
--             toScalarType, fromScalarType, impInstrTypes) where

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

import Preamble
import Base
import Core

import Algebra
import Simplify -- TODO: remove

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

data ImpBinding n = ImpBinding

type ImpM n m = (MonadErr m, MonadReader ImpCtx m, BindingWriter ImpBinding n m)

-- data ImpCatEnv = ImpCatEnv
--   { envPtrsToFree :: [IExpr] -- safe-names: shouldn't need this with pointers as names
--   , envBindings   :: Bindings ()
--   , envDecls      :: [ImpDecl]
--   , envFunctions  :: Env () (HLift ImpFunction) () }

type AtomRecon n = ()  -- Abs (Nest Type) Atom n



-- TODO: figure out where to put this
getTypeInExpr :: (HasType e, ImpM n m) => DeferredSubst Atom e n -> m (Type n)
getTypeInExpr = undefined

-- toImpModule :: forall n. Bindings n -> Backend -> CallingConvention -> Name n
--             -> [IBinder] -> Maybe Dest n -> Block n
--             -> (ImpFunction, ImpModule, AtomRecon n)
-- toImpModule = undefined
-- toImpModule env backend cc entryName argBinders maybeDest block = do
--   let standaloneFunctions =
--         for (requiredFunctions env block) \(v, f) ->
--           runImpM initCtx inVarScope $ toImpStandalone v f
--   runImpM initCtx inVarScope $ do
--     (reconAtom, impBlock) <- scopedBlock $ translateTopLevel env (maybeDest, block)
--     otherFunctions <- toList <$> looks envFunctions
--     let ty = IFunType cc (map snd argBinders) (impBlockType impBlock)
--     let mainFunction = ImpFunction (entryName:>ty) argBinders impBlock
--     let allFunctions = standaloneFunctions ++ otherFunctions ++ [mainFunction]
--     return (mainFunction, ImpModule allFunctions, reconAtom)
--   where
--     inVarScope :: Scope n  -- TODO: fix (shouldn't use UnitTy)
--     inVarScope = binderScope <> destScope
--     binderScope = foldMap binderAsEnv $ fmap (fmap $ const (UnitTy, UnknownBinder)) argBinders
--     destScope = fromMaybe mempty $ fmap freeVars maybeDest
--     initCtx = ImpCtx backend CPU TopLevel

-- requiredFunctions :: Scope n -> e n -> [(Name n, Atom n)]
-- requiredFunctions = undefined
-- requiredFunctions scope expr =
--   flip foldMap (transitiveClosure getParents immediateParents) \fname ->
--     case scope ! fname of
--        (_, LetBound _ (Atom f)) -> [(fname, f)]
--        -- we treat runtime-supplied global constants (e.g. the virtual stdout
--        -- channel) as lambda-bound. TODO: consider a new annotation.
--        (_, LamBound _) -> []
--        _ -> error "Shouldn't have other free variables left"
--   where
--     getParents :: Name n -> [Name n]
--     getParents fname = envNames $ freeVars $ scope ! fname

--     immediateParents :: [Name n]
--     immediateParents = envNames $ freeVars expr `envIntersect` scope

-- We don't emit any results when a destination is provided, since they are already
-- going to be available through the dest.
translateTopLevel :: ImpM n m => WithDest n (Block n) -> m (AtomRecon n, [IExpr n])
translateTopLevel = undefined
-- translateTopLevel topEnv (maybeDest, block) = do
--   outDest <- case maybeDest of
--         Nothing   -> makeAllocDest Unmanaged $ getType block
--         Just dest -> return dest
--   handleErrors $ void $ translateBlock mempty (Just outDest, block)
--   resultAtom <- destToAtom outDest
--   -- Some names in topEnv refer to global constants, like the virtual stdout channel
--   let vsOut = envPairs $ freeVars resultAtom `envDiff` topEnv
--   let reconAtom = Abs (toNest $ [Just v :> ty | (v,(ty, _)) <- vsOut]) resultAtom
--   let resultIExprs = case maybeDest of
--         Nothing -> map (IVar . fst) vsOut
--         Just _  -> []
--   return (reconAtom, resultIExprs)

-- runImpM :: ImpCtx -> Bindings n -> ImpM a -> a
-- runImpM ctx inVarScope m =
--   fromRight (error "Unexpected top level error") $
--     fst $ runCat (runReaderT (runExceptT m) ctx) $ mempty {envBindings = inVarScope}

-- toImpStandalone :: ImpM n m => Name n -> Atom n -> m ImpFunction
-- toImpStandalone = undefined
-- toImpStandalone fname ~(LamVal b body) = do
--   let argTy = binderType b
--   let outTy = getType body
--   backend <- asks impBackend
--   curDev <- asks curDevice
--   (ptrSizes, ~(Con (ConRef (PairCon outDest argDest)))) <- fromBuilder $
--     makeDest (backend, curDev, Unmanaged) (PairTy outTy argTy)
--   impBlock <- scopedErrBlock $ do
--     arg <- destToAtom argDest
--     void $ translateBlock (b@>arg) (Just outDest, body)
--   let bs = for ptrSizes \((Just v :> BaseTy ty), _) -> (v,ty)
--   let fTy = IFunType CEntryFun (map snd bs) (impBlockType impBlock)
--   return $ ImpFunction (fname, fTy) bs impBlock

translateBlock :: ImpM n m => AtomSubst i n -> WithDest n (Block i) -> m (Atom n)
translateBlock subst (maybeDest, Block _ decls) = do
  result <- translateDecls subst decls
  copyDest maybeDest result

translateDecls :: ImpM n m => AtomSubst i n -> NestedAbs Decl Atom i -> m (Atom n)
translateDecls subst (Result atom) = applySubst subst atom
translateDecls subst (Nest (Let _ _ expr) abs) = do
  ans <- translateExpr subst (Nothing, expr)
  Defer subst' rest <- return $ openAbs (Defer subst abs) ans
  translateDecls subst' rest

translateExpr :: ImpM n m => AtomSubst i n -> WithDest n (Expr i) -> m (Atom n)
translateExpr subst (maybeDest, expr) = case expr of
  Hof hof     -> toImpHof subst (maybeDest, hof)
  -- App f' x' -> do
  --   f <- impSubst subst f'
  --   x <- impSubst subst x'
  --   case getType f of
  --     TabTy _ _ -> do
  --       case f of
  --         Lam a@(Abs _ (WithArrow TabArrow _)) ->
  --           translateBlock mempty (maybeDest, sndH $ applyAbs a x)
  --         _ -> error $ "Invalid Imp atom: " ++ pprint f
  --     -- Runtime function calls for non-inlined functions
  --     _ -> do
  --       let (Var (Occ fname (FunTy argBinder _ outTy))) = f
  --       let argTy = binderType argBinder
  --       (argDest, argDestElts) <- makeAllocDestWithPtrs Managed $ argTy
  --       -- There's a missed opportunity here to use maybeDest. The problem is
  --       -- that we can't guarantee that the table refs are in a canonical
  --       -- representation. We could consider tracking that information with
  --       -- dests so that we can take advantage of it when it happens.
  --       (outDest, outDestElts) <- makeAllocDestWithPtrs Managed $ outTy
  --       let allElts = outDestElts ++ argDestElts
  --       let iFunTy = IFunType CEntryFun (map getIType allElts) []
  --       copyAtom argDest x
  --       void $ emitStatement $ ICall (fname, iFunTy) allElts
  --       result <- destToAtom outDest
  --       copyDest maybeDest result
  Atom x   -> copyDest maybeDest =<< impSubst subst x
  Op   op  -> toImpOp . (maybeDest,) =<< traverse (impSubst subst) op
  -- Case e alts _ -> do
  --   e' <- impSubst subst e
  --   case e' of
  --     DataCon _ _ con args -> do
  --       let Abs bs body = alts !! con
  --       translateBlock (subst <> newSubst bs args) (maybeDest, body)
  --     Variant (NoExt types) label i x -> do
  --       let LabeledItems ixtypes = enumerate types
  --       let index = fst $ ixtypes M.! label NE.!! i
  --       let Abs bs body = alts !! index
  --       translateBlock (subst <> newSubst bs [x]) (maybeDest, body)
  --     Con (SumAsProd _ tag xss) -> do
  --       let tag' = fromScalarAtom tag
  --       dest <- allocDest maybeDest =<< impSubst subst (getType expr)
  --       emitSwitch tag' $ flip map (zip xss alts) $
  --         \(xs, Abs bs body) ->
  --            void $ translateBlock (subst <> newSubst bs xs) (Just dest, body)
  --       destToAtom dest
  --     _ -> error $ "Unexpected scrutinee: " ++ pprint e'

-- newSubst :: Nest Type i -> [Atom o] -> AtomSubst i o
-- newSubst = undefined

-- emitFunction :: NameStr -> CallingConvention
--              -> [IBinder] -> ImpBlock -> ImpM IFunVar
-- emitFunction nameHint cc bs body = do
--   funEnv <- looks envFunctions
--   let name = genFresh TopFunctionName nameHint funEnv
--   let fvar = (name, IFunType cc (map snd bs) (impBlockType body))
--   extend $ mempty {envFunctions = name @> HLift (ImpFunction fvar bs body)}
--   return fvar

-- emitFFIFunction :: String -> [IType n] -> [IType n] -> ImpM IFunVar n
-- emitFFIFunction = undefined
-- emitFFIFunction s argTys resultTys = do
--   let fname = ffiFunName s
--   let cc = case length resultTys of
--         0 -> error "Not implemented"
--         1 -> FFIFun
--         _ -> FFIMultiResultFun
--   let f = (fname, IFunType cc argTys resultTys)
--   -- TODO: check that if it's already in the env, it's with the same type
--   extend $ mempty {envFunctions = fname @> HLift (FFIFunction f)}
--   return f

impSubst :: ImpM n m => AtomSubst i n -> e i -> m (e n)
impSubst = undefined
-- impSubst env x = do
--   scope <- variableScope
--   return $ subst (env, scope) x

toImpOp :: ImpM n m => WithDest n (PrimOp (Atom n)) -> m (Atom n)
toImpOp (maybeDest, op) = do
 resultTy <- liftDefReader $ getType $ Op op
 case op of
  TabCon (TabTy ixTy _) rows -> do
    dest <- allocDest maybeDest resultTy
    forM_ (zip [0..] rows) \(i, row) -> do
      ithDest <- destGet dest =<< intToIndex ixTy (IIdxRepVal i)
      copyAtom ithDest row
    destToAtom dest
  PrimEffect refDest m -> do
    case m of
      MAsk      -> returnVal =<< destToAtom refDest
      -- MExtend ~(Lam f) -> do
      --   -- TODO: Update in-place?
      --   refValue <- destToAtom refDest
      --   result <- translateBlock mempty (Nothing, sndH $ applyAbs f refValue)
      --   copyAtom refDest result
      --   returnVal UnitVal
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
    PrimCon (IntRangeVal   _ _   i) -> returnVal $ i
    PrimCon (IndexRangeVal _ _ _ i) -> returnVal $ i
    _ -> returnVal . toScalarAtom =<< indexToInt idx
  Inject e -> case e of
    -- PrimCon (IndexRangeVal t low _ restrictIdx) -> do
    --   offset <- case low of
    --     InclusiveLim a -> indexToInt a
    --     ExclusiveLim a -> indexToInt a >>= iaddI (IIdxRepVal 1)
    --     Unlimited      -> return (IIdxRepVal 0)
    --   returnVal =<< intToIndex t =<< iaddI (fromScalarAtom restrictIdx) offset
    PrimCon (ParIndexCon (PrimTC (ParIndexRange realIdxTy _ _)) i) -> do
      returnVal =<< intToIndex realIdxTy (fromScalarAtom i)
    _ -> error $ "Unsupported argument to inject: " ++ pprint e
  IndexRef refDest i -> returnVal =<< destGet refDest i
  FstRef ~(PrimCon (ConRef (PairCon ref _  ))) -> returnVal ref
  SndRef ~(PrimCon (ConRef (PairCon _   ref))) -> returnVal ref
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
  -- SliceOffset ~(PrimCon (IndexSliceVal n _ tileOffset)) idx -> do
  --   i' <- indexToInt idx
  --   i <- iaddI (fromScalarAtom tileOffset) i'
  --   returnVal =<< intToIndex n i
  -- SliceCurry ~(PrimCon (IndexSliceVal _ (PairTy _ v) tileOffset)) idx -> do
  --   vz <- intToIndex v $ IIdxRepVal 0
  --   extraOffset <- indexToInt (PairVal idx vz)
  --   tileOffset' <- iaddI (fromScalarAtom tileOffset) extraOffset
  --   returnVal $ toScalarAtom tileOffset'
  -- ThrowError _ -> throwError ()
  -- CastOp destTy x -> case (getType bindings x, destTy) of
  --   (BaseTy _, BaseTy bt) -> returnVal =<< toScalarAtom <$> cast (fromScalarAtom x) bt
  --   _ -> do
  --     bindings <- looks envBindings
  --     error $ "Invalid cast: " ++ pprint (getType bindings x) ++ " -> " ++ pprint destTy
  Select p x y -> do
    xTy <- liftDefReader $ getType x
    case xTy of
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
    (PrimCon (SumAsProd _ tag _)) -> returnVal tag
    -- (Con _ _ i _) -> returnVal $ TagRepVal $ fromIntegral i
    _ -> error $ "Not a data constructor: " ++ pprint con
  -- ToEnum ~ty@(TypeCon (DataDef _ _ cons) _) i ->
  --   returnVal $ Con $ SumAsProd ty i (map (const []) cons)
  -- FFICall name returnTy xs -> do
  --   let returnTys = fromScalarOrPairType returnTy
  --   let xTys = map (fromScalarType . getType bindings) xs
  --   f <- emitFFIFunction name xTys returnTys
  --   results <- emitMultiReturnInstr $ ICall f $ map fromScalarAtom xs
  --   returnVal $ restructureScalarOrPairType returnTy results
  _ -> do
    returnVal . toScalarAtom =<< emitInstr (IPrimOp $ fmap fromScalarAtom op)
  where
    returnVal atom = case maybeDest of
      Nothing   -> return atom
      Just dest -> copyAtom dest atom >> return atom

toImpHof :: ImpM n m => AtomSubst i n -> WithDest n (PrimHof (Atom i)) -> m (Atom n)
toImpHof = undefined
-- toImpHof subst (maybeDest, hof) = do
--   resultTy <- getTypeInExpr $ Defer subst (Hof hof)
--   case hof of
--     For (RegularFor d) ~(LamVal b body) -> do
--       idxTy <- impSubst subst $ binderType b
--       dev   <- asks curDevice
--       case idxTy of
--         TC (ParIndexRange realIdxTy gtid numThreads) -> do
--           let gtidI = fromScalarAtom gtid
--           let numThreadsI = fromScalarAtom numThreads
--           n    <- indexSetSize realIdxTy
--           dest <- allocDest maybeDest resultTy
--           case dev of
--             CPU -> do -- Chunked loop
--               usualChunkSize  <- n `idivI` numThreadsI
--               chunkStart      <- gtidI `imulI` usualChunkSize
--               isLast          <- (gtidI `ieqI`) =<< (numThreadsI `isubI` IIdxRepVal 1)
--               elemsUntilEnd   <- n `isubI` chunkStart
--               threadChunkSize <- toImpOp $ (Nothing,
--                                             Select (toScalarAtom isLast)
--                                                    (toScalarAtom elemsUntilEnd)
--                                                    (toScalarAtom usualChunkSize))
--               emitLoop "li" Fwd (fromScalarAtom threadChunkSize) \li -> do
--                 i <- li `iaddI` chunkStart
--                 let idx = Con $ ParIndexCon idxTy $ toScalarAtom i
--                 ithDest <- destGet dest idx
--                 void $ translateBlock (subst <> b @> idx) (Just ithDest, body)
--             GPU -> do -- Grid stride loop
--               iPtr <- alloc IdxRepTy
--               copyAtom iPtr gtid
--               cond <- liftM snd $ scopedBlock $ do
--                 i <- destToAtom iPtr
--                 inRange <- (fromScalarAtom i) `iltI` n
--                 emitWhen inRange $ do
--                   let idx = Con $ ParIndexCon idxTy i
--                   ithDest <- destGet dest idx
--                   void $ translateBlock (subst <> b @> idx) (Just ithDest, body)
--                   copyAtom iPtr . toScalarAtom =<< iaddI (fromScalarAtom i)
--                                                      (fromScalarAtom numThreads)
--                 return ((), [inRange])
--               emitStatement $ IWhile cond
--           destToAtom dest
--         _ -> do
--           n <- indexSetSize idxTy
--           dest <- allocDest maybeDest resultTy
--           emitLoop (getNameStr b) d n \i -> do
--             idx <- intToIndex idxTy i
--             ithDest <- destGet dest idx
--             void $ translateBlock (subst <> b @> idx) (Just ithDest, body)
--           destToAtom dest
    -- For ParallelFor ~fbody@(LamVal b _) -> do
    --   idxTy <- impSubst subst $ binderType b
    --   dest <- allocDest maybeDest resultTy
    --   buildKernel idxTy \LaunchInfo{..} buildBody -> do
    --     liftM (,()) $ buildBody \ThreadInfo{..} -> do
    --       let threadBody = fst $ flip runSubstBuilder (freeVars fbody) $
    --             buildLam (Just "hwidx" :> threadRange) PureArrow \hwidx ->
    --               appReduce fbody =<< (emitOp $ Inject hwidx)
    --       let threadDest = Con $ TabRef $ fst $ flip runSubstBuilder (freeVars dest) $
    --             buildLam (Just "hwidx" :> threadRange) TabArrow \hwidx ->
    --               indexDest dest =<< (emitOp $ Inject hwidx)
    --       void $ toImpHof subst (Just threadDest, For (RegularFor Fwd) threadBody)
    --   destToAtom dest
    -- Tile d ~(LamVal tb tBody) ~(LamVal sb sBody) -> do
    --   ~(TC (IndexSlice idxTy tileIdxTy)) <- impSubst subst $ binderType tb
    --   n <- indexSetSize idxTy
    --   dest <- allocDest maybeDest resultTy
    --   tileLen <- indexSetSize tileIdxTy
    --   nTiles      <- n `idivI` tileLen
    --   epilogueOff <- nTiles `imulI` tileLen
    --   nEpilogue   <- n `isubI` epilogueOff
    --   emitLoop (getNameStr tb) Fwd nTiles \iTile -> do
    --     tileOffset <- toScalarAtom <$> iTile `imulI` tileLen
    --     let tileAtom = Con $ IndexSliceVal idxTy tileIdxTy tileOffset
    --     tileDest <- fromBuilder $ sliceDestDim d dest tileOffset tileIdxTy
    --     void $ translateBlock (subst <> tb @> tileAtom) (Just tileDest, tBody)
    --   emitLoop (getNameStr sb) Fwd nEpilogue \iEpi -> do
    --     i <- iEpi `iaddI` epilogueOff
    --     idx <- intToIndex idxTy i
    --     sDest <- fromBuilder $ indexDestDim d dest idx
    --     void $ translateBlock (subst <> sb @> idx) (Just sDest, sBody)
    --   destToAtom dest
    -- PTileReduce baseMonoids idxTy' ~(BinaryFunVal gtidB nthrB _ body) -> do
    --   idxTy <- impSubst subst idxTy'
    --   (mappingDest, finalAccDest) <- destPairUnpack <$> allocDest maybeDest resultTy
    --   let PairTy _ accTypes = resultTy
    --   (numTileWorkgroups, wgAccsArr, widIdxTy) <- buildKernel idxTy \LaunchInfo{..} buildBody -> do
    --     let widIdxTy = Fin $ toScalarAtom numWorkgroups
    --     let tidIdxTy = Fin $ toScalarAtom workgroupSize
    --     wgAccsArr  <- alloc $ TabTy (Ignore widIdxTy) accTypes
    --     thrAccsArr <- alloc $ TabTy (Ignore widIdxTy) $ TabTy (Ignore tidIdxTy) accTypes
    --     mappingKernelBody <- buildBody \ThreadInfo{..} -> do
    --       let TC (ParIndexRange _ gtid nthr) = threadRange
    --       let scope = freeVars mappingDest
    --       let tileDest = Con $ TabRef $ fst $ flip runSubstBuilder scope $ do
    --             buildLam (Bind $ "hwidx":>threadRange) TabArrow \hwidx -> do
    --               indexDest mappingDest =<< (emitOp $ Inject hwidx)
    --       wgThrAccs <- destGet thrAccsArr =<< intToIndex widIdxTy wid
    --       thrAccs   <- destGet wgThrAccs  =<< intToIndex tidIdxTy tid
    --       let thrAccsList = fromDestConsList thrAccs
    --       let threadDest = foldr ((Con . ConRef) ... flip PairCon) tileDest thrAccsList
    --       -- TODO: Make sure that threadDest has the right type
    --       void $ translateBlock (subst <> gtidB @> gtid <> nthrB @> nthr) (Just threadDest, body)
    --       wgAccs <- destGet wgAccsArr =<< intToIndex widIdxTy wid
    --       workgroupReduce tid wgAccs wgThrAccs workgroupSize
    --     return (mappingKernelBody, (numWorkgroups, wgAccsArr, widIdxTy))
    --   -- TODO: Skip the reduction kernel if unnecessary?
    --   -- TODO: Reduce sequentially in the CPU backend?
    --   -- TODO: Actually we only need the previous-power-of-2 many threads
    --   buildKernel widIdxTy \LaunchInfo{..} buildBody -> do
    --     -- We only do a one-level reduciton in the workgroup, so it is correct
    --     -- only if the end up scheduling a single workgroup.
    --     moreThanOneGroup <- (IIdxRepVal 1) `iltI` numWorkgroups
    --     guardBlock moreThanOneGroup $ emitStatement IThrowError
    --     redKernelBody <- buildBody \ThreadInfo{..} ->
    --       workgroupReduce tid finalAccDest wgAccsArr numTileWorkgroups
    --     return (redKernelBody, ())
    --   PairVal <$> destToAtom mappingDest <*> destToAtom finalAccDest
    --   where
    --     guardBlock cond m = do
    --       block <- scopedErrBlock m
    --       emitStatement $ ICond cond block (ImpBlock mempty mempty)
    --     -- XXX: Overwrites the contents of arrDest, writes result in resDest
    --     workgroupReduce tid resDest arrDest elemCount = do
    --       elemCountDown2 <- prevPowerOf2 elemCount
    --       let RawRefTy (TabTy arrIdxB _) = getType arrDest
    --       let arrIdxTy = binderType arrIdxB
    --       offPtr <- alloc IdxRepTy
    --       copyAtom offPtr $ toScalarAtom elemCountDown2
    --       let wbody = do
    --             off       <- fromScalarAtom <$> destToAtom offPtr
    --             loadIdx   <- iaddI tid off
    --             shouldAdd <- bindM2 bandI (tid `iltI` off) (loadIdx `iltI` elemCount)
    --             guardBlock shouldAdd $ do
    --               threadDest <- destGet arrDest =<< intToIndex arrIdxTy tid
    --               combineWithDest threadDest =<< destToAtom =<< destGet arrDest =<< intToIndex arrIdxTy loadIdx
    --             emitStatement ISyncWorkgroup
    --             copyAtom offPtr . toScalarAtom =<< off `idivI` (IIdxRepVal 2)
    --       cond <- liftM snd $ scopedBlock $ do
    --         off  <- fromScalarAtom <$> destToAtom offPtr
    --         cond <- emitInstr $ IPrimOp $ ScalarBinOp (ICmp Greater) off (IIdxRepVal 0)
    --         emitWhen cond wbody
    --         return ((), [cond])
    --       emitStatement $ IWhile cond
    --       firstThread <- tid `iltI` (IIdxRepVal 1)
    --       guardBlock firstThread $
    --         copyAtom resDest =<< destToAtom =<< destGet arrDest =<< intToIndex arrIdxTy tid
    --     combineWithDest :: Dest n -> Atom () -> ImpM ()
    --     combineWithDest accsDest accsUpdates = do
    --       let accsDestList = fromDestConsList accsDest
    --       let Right accsUpdatesList = fromConsList accsUpdates
    --       forM_ (zip3 accsDestList baseMonoids accsUpdatesList) $ \(dest, bm, update) -> do
    --         extender <- fromBuilder $ mextendForRef dest bm update
    --         void $ toImpOp (Nothing, PrimEffect dest $ MExtend extender)
    --     -- TODO: Do some popcount tricks?
    --     prevPowerOf2 :: IExpr n -> m (IExpr n)
    --     prevPowerOf2 x = do
    --       rPtr <- alloc IdxRepTy
    --       copyAtom rPtr (IdxRepVal 1)
    --       let getNext = imulI (IIdxRepVal 2) . fromScalarAtom =<< destToAtom rPtr
    --       cond <- liftM snd $ scopedBlock $ do
    --         canGrow <- getNext >>= (`iltI` x)
    --         emitWhen canGrow $ copyAtom rPtr . toScalarAtom =<< getNext
    --         return ((), [canGrow])
    --       emitStatement $ IWhile cond
    --       fromScalarAtom <$> destToAtom rPtr
    -- While ~(Lam (Abs _ (WithArrow _ body))) -> do
    --   body' <- liftM snd $ scopedBlock $ do
    --              ans <- translateBlock subst (Nothing, body)
    --              return ((), [fromScalarAtom ans])
    --   emitStatement $ IWhile body'
    --   return UnitVal
    -- RunReader r ~(BinaryFunVal _ ref _ body) -> do
    --   rDest <- alloc $ getType r
    --   copyAtom rDest =<< impSubst subst r
    --   translateBlock (subst <> ref @> rDest) (maybeDest, body)
    -- RunWriter (BaseMonoid e' _) ~(BinaryFunVal _ ref _ body) -> do
    --   let PairTy _ accTy = resultTy
    --   (aDest, wDest) <- destPairUnpack <$> allocDest maybeDest resultTy
    --   copyAtom wDest =<< (liftNeutral accTy <$> impSubst subst e')
    --   void $ translateBlock (subst <> ref @> wDest) (Just aDest, body)
    --   PairVal <$> destToAtom aDest <*> destToAtom wDest
    --   where liftNeutral accTy e = foldr TabValA e $ monoidLift (getType e) accTy
    -- RunState s ~(BinaryFunVal _ ref _ body) -> do
    --   (aDest, sDest) <- destPairUnpack <$> allocDest maybeDest resultTy
    --   copyAtom sDest =<< impSubst subst s
    --   void $ translateBlock (subst <> ref @> sDest) (Just aDest, body)
    --   PairVal <$> destToAtom aDest <*> destToAtom sDest
    -- RunIO ~(Lam (Abs _ (WithArrow _ body))) ->
    --   translateBlock subst (maybeDest, body)
    -- Linearize _ -> error "Unexpected Linearize"
    -- Transpose _ -> error "Unexpected Transpose"
    -- CatchException _ -> error "Unexpected CatchException"

data LaunchInfo n = LaunchInfo { numWorkgroups :: IExpr n, workgroupSize :: IExpr n }
data ThreadInfo n = ThreadInfo { tid :: IExpr n, wid :: IExpr n, threadRange :: Type n }
-- type KernelBuilder n kernel = (ThreadInfo n -> ImpM ()) -> ImpM kernel

-- -- The rank 2 signature ensures that the call sites returns the result of the
-- buildKernel :: Type n
--             -> (forall k. LaunchInfo -> KernelBuilder n k -> ImpM (k, a))
--             -> ImpM a
-- buildKernel idxTy f = undefined
-- buildKernel idxTy f = do
--   n <- indexSetSize idxTy
--   -- Launch info vars
--   numWorkgroupsVar <- freshVar $ "numWorkgroups" :> IIdxRepTy
--   workgroupSizeVar <- freshVar $ "workgroupSize" :> IIdxRepTy
--   let numWorkgroups = IVar numWorkgroupsVar
--   let workgroupSize = IVar workgroupSizeVar
--   -- Thread info vars
--   tidVar  <- freshVar ("tid"  , IIdxRepTy)
--   widVar  <- freshVar ("wid"  , IIdxRepTy)
--   wszVar  <- freshVar ("wsz"  , IIdxRepTy)
--   nthrVar <- freshVar ("nthr" , IIdxRepTy)
--   let tid  = IVar tidVar
--   let wid  = IVar widVar
--   let wsz  = IVar wszVar
--   let nthr = IVar nthrVar
--   let threadInfoVars = [tidVar, widVar, wszVar, nthrVar]
--   -- Emit the kernel function
--   opts <- ask
--   let (cc, dev) = case impBackend opts of
--         LLVMCUDA -> (CUDAKernelLaunch, GPU)
--         LLVMMC   -> (MCThreadLaunch  , CPU)
--         backend  -> error $ "Shouldn't be launching kernels from " ++ show backend
--   ((kernelBody, aux), subst) <- scoped $ f LaunchInfo{..} \mkBody ->
--     withDevice dev $ withLevel ThreadLevel $ scopedErrBlock $ do
--       gtid <- iaddI tid =<< imulI wid wsz
--       let threadRange = TC $ ParIndexRange idxTy (toScalarAtom gtid) (toScalarAtom nthr)
--       mkBody ThreadInfo{..}
--   let args = envPairs $ freeIVars kernelBody `envDiff` (newEnv threadInfoVars (repeat ()))
--   kernelFunc <- emitFunction "kernel" cc
--     (fmap Bind (tidVar:widVar:wszVar:nthrVar:args)) kernelBody
--   -- Carefully emit the decls so that the launch info gets bound before the kernel call
--   emitImpDecl $ ImpLet [Bind numWorkgroupsVar, Bind workgroupSizeVar]
--                        (IQueryParallelism kernelFunc n)
--   extend subst
--   emitStatement $ ILaunch kernelFunc n $ map IVar args
--   return aux

-- === Destination type ===

type Dest = Atom  -- has type `Ref a` for some a
type WithDest n a = (Maybe (Dest n), a)

data DestEnv n = DestEnv
       { _allocationInfo :: AllocInfo
       , enclosingIdxs :: IndexStructure n
       , destDepVars :: Scope n }

-- The Cat env carries names for the pointers needed, along with their types and
-- blocks that compute allocation sizes needed
-- type DestM n = ReaderT DestEnv (CatT (Env n (HPair Type Block) n) (Builder n))

-- builds a dest and a list of pointer binders along with their required allocation sizes
makeDest :: Builder n m => AllocInfo -> Type n -> m ([(Type n, Atom n)], Dest n)
makeDest = undefined
-- makeDest allocInfo ty = do
--   (dest, ptrs) <- flip runCatT mempty $ flip runReaderT env $ makeDestRec ty
--   ptrs' <- forM (envPairs ptrs) \(v, (ptrTy, numel)) -> do
--     numel' <- emitBlock numel
--     return (Just v:>ptrTy, numel')
--   return (ptrs', dest)
--   where env = DestEnv allocInfo mempty mempty

-- makeDestRec :: Type n -> DestM Dest
-- makeDestRec = undefined
-- makeDestRec ty = case ty of
--   TabTy b bodyTy -> do
--     depVars <- asks destDepVars
--     if not $ null $ freeVars b `envIntersect` depVars
--       then do
--         (dest, ptrs) <- local (\env -> env { enclosingIdxs = mempty
--                                            , destDepVars   = mempty }) $ scoped $
--                           makeDestRec ty
--         makeBoxes (envPairs ptrs) dest
--       else do
--         lam <- buildLam (binderType b) TabArrow \(Var i) -> do
--           bodyTy' <- substBuilder (b@>Var i) bodyTy
--           withEnclosingIdxs (Bind i) $ makeDestRec bodyTy'
--         return $ Con $ TabRef lam
--   TypeCon def params -> do
--     let dcs = applyDataDefParams def params
--     case dcs of
--       [] -> error "Void type not allowed"
--       [DataConDef _ bs] -> do
--         dests <- makeDataConDest bs
--         return $ DataConRef def params dests
--       _ -> do
--         when (any isDependent dcs) $ error
--           "Dependent data constructors only allowed for single-constructor types"
--         tag <- rec TagRepTy
--         let dcs' = applyDataDefParams def params
--         contents <- forM dcs' \(DataConDef _ bs) -> forM (fromNest bs) (rec . binderType)
--         return $ Con $ ConRef $ SumAsProd ty tag contents
--   RecordTy (NoExt types) -> (Con . RecordRef) <$> forM types rec
--   VariantTy (NoExt types) -> do
--     tag <- rec TagRepTy
--     contents <- forM (toList types) rec
--     return $ Con $ ConRef $ SumAsProd ty tag $ map (\x->[x]) contents
--   TC con -> case con of
--     BaseType b -> do
--       ptr <- makeBaseTypePtr b
--       return $ Con $ BaseTypeRef ptr
--     PairType a b -> (Con . ConRef) <$> (PairCon <$> rec a <*> rec b)
--     UnitType     -> (Con . ConRef) <$> return UnitCon
--     IntRange     l h -> (Con . ConRef . IntRangeVal     l h) <$> rec IdxRepTy
--     IndexRange t l h -> (Con . ConRef . IndexRangeVal t l h) <$> rec IdxRepTy
--     _ -> error $ "not implemented: " ++ pprint con
--   _ -> error $ "not implemented: " ++ pprint ty
--   where rec = makeDestRec

-- makeBoxes :: [(Name n, (Type n, Block n))] -> Dest n -> DestM Dest
-- makeBoxes [] dest = return dest
-- makeBoxes ((v, (ptrTy, numel)):rest) dest = do
--   ptrPtr <- makeBaseTypePtr $ fromScalarType ptrTy
--   dest' <- makeBoxes rest dest
--   return $ BoxedRef (Just v:>ptrTy) ptrPtr numel dest'

-- makeBaseTypePtr :: BaseType -> DestM (Atom n)
-- makeBaseTypePtr = undefined
-- makeBaseTypePtr ty = do
--   DestEnv allocInfo idxs _ <- ask
--   numel <- buildScopedBlock $ elemCountE idxs
--   ptrScope <- fmapH (const (HPair UnitTy UnknownBinder)) <$> look
--   scope <- getBindings
--   -- We use a different namespace because these will be hoisted to the top
--   -- where they could cast shadows
--   let addrSpace = chooseAddrSpace allocInfo numel
--   let ptrName = genFresh AllocPtrName "ptr" (scope <> ptrScope)
--   let ptrTy = PtrTy (addrSpace, ty)
--   extend (ptrName @> HPair ptrTy numel)
--   applyIdxs (Var ptrName) idxs

-- withEnclosingIdxs :: IndexStructure n -> DestM a -> DestM a
-- withEnclosingIdxs = undefined
-- withEnclosingIdxs i m =
--   local (\env -> env {enclosingIdxs = enclosingIdxs env <> Nest i Empty}) m

-- withDepVar :: Type n -> DestM a -> DestM a
-- withDepVar = undefined
-- withDepVar v m =
--   local (\env -> env {destDepVars = destDepVars env <> (v@>n)}) m

-- makeDataConDest :: Nest Type n -> DestM (Nest DataConRefBinding n)
-- makeDataConDest = undefined
-- makeDataConDest Empty = return Empty
-- makeDataConDest (Nest b rest) = do
--   let ty = binderType b
--   dest <- makeDestRec ty
--   v <- freshVarE UnknownBinder b  -- TODO: scope names more carefully
--   (Abs rest' HUnit)  <- substBuilder (b @> Var v) $ Abs rest HUnit
--   rest'' <- withDepVar (Bind v) $ makeDataConDest rest'
--   return $ Nest (DataConRefBinding (Bind v) dest) rest''

copyAtom :: ImpM n m => Dest n -> Atom n -> m ()
copyAtom (BoxedRef ptrPtr size (PtrTy ptrTy) abs) src = do
  -- TODO: load old ptr and free (recursively)
  size' <- translateBlock idSubst (Nothing, size)
  ptr <- emitAlloc ptrTy $ fromScalarAtom size'
  body' <- forceSubst $ openAbs (Defer idSubst abs) (toScalarAtom ptr)
  copyAtom body' src
  storeAnywhere (fromScalarAtom ptrPtr) ptr
-- copyAtom (DataConRef _ _ refs) (DataCon _ _ _ vals) = copyDataConArgs refs vals
copyAtom (PrimCon dest) src = case (dest, src) of
  (BaseTypeRef ptr, _) -> storeAnywhere (fromScalarAtom ptr) (fromScalarAtom src)
  -- (TabRef _, TabVal _ _) -> zipTabDestAtom copyAtom (Con dest) src
  -- (ConRef (SumAsProd _ tag payload), DataCon _ _ con x) -> do
  --   copyAtom tag (TagRepVal $ fromIntegral con)
  --   zipWithM_ copyAtom (payload !! con) x
  (ConRef (SumAsProd _ tagDest payloadDest), PrimCon (SumAsProd _ tag payload)) -> do
    copyAtom tagDest tag
    unless (all null payload) $ -- optimization
      emitSwitch (fromScalarAtom tag) $
        zipWith (zipWithM_ copyAtom) payloadDest payload
  -- (ConRef destCon, PrimCon srcCon) -> zipWithRefConM copyAtom destCon srcCon
  (RecordRef refs, Record vals)
    | fmap (const ()) refs == fmap (const ()) vals -> do
        zipWithM_ copyAtom (toList refs) (toList vals)
  (ConRef (SumAsProd _ tag payload), Variant (NoExt types) label i x) -> do
    let LabeledItems ixtypes = enumerate types
    let index = fst $ (ixtypes M.! label) NE.!! i
    copyAtom tag (TagRepVal $ fromIntegral index)
    zipWithM_ copyAtom (payload !! index) [x]
  _ -> error $ "Not implemented: " ++ pprint (dest, src)
copyAtom dest src = error $ "Not a valid dest-source pair: " ++ pprint (dest, src)

-- copyDataConArgs :: Nest DataConRefBinding n -> [Atom n] -> ImpM n
-- copyDataConArgs = undefined
-- copyDataConArgs Empty [] = return ()
-- copyDataConArgs (Nest (DataConRefBinding b ref) rest) (x:xs) = do
--   copyAtom ref x
--   (Abs rest' HUnit) <- impSubst (b@>x) $ Abs rest HUnit
--   copyDataConArgs rest' xs
-- copyDataConArgs bindings args =
--   error $ "Mismatched bindings/args: " ++ pprint (bindings, args)

loadDest :: Builder n m => Dest n -> m (Atom n)
loadDest (BoxedRef ptrPtr _ _ abs) = do
  ptr <- unsafePtrLoad ptrPtr
  body' <- forceSubst $ openAbs (Defer idSubst abs) ptr
  loadDest body'
-- loadDest (DataConRef def params bs) = do
--   DataCon def params 0 <$> loadDataConArgs bs
loadDest (PrimCon dest) = do
 case dest of
  BaseTypeRef ptr -> unsafePtrLoad ptr
--   TabRef (TabVal b body) -> buildLam (binderType b) TabArrow \i -> do
--     body' <- substBuilder (b@>i) body
--     result <- emitBlock body'
--     loadDest result
  RecordRef xs -> Record <$> traverse loadDest xs
  ConRef con -> PrimCon <$> case con of
    PairCon d1 d2 -> PairCon <$> loadDest d1 <*> loadDest d2
    UnitCon -> return UnitCon
    SumAsProd ty tag xss -> SumAsProd ty <$> loadDest tag <*> mapM (mapM loadDest) xss
    IntRangeVal     l h iRef -> IntRangeVal     l h <$> loadDest iRef
    IndexRangeVal t l h iRef -> IndexRangeVal t l h <$> loadDest iRef
    _        -> error $ "Not a valid dest: " ++ pprint dest
  _          -> error $ "Not a valid dest: " ++ pprint dest
loadDest dest = error $ "Not a valid dest: " ++ pprint dest

-- loadDataConArgs :: Builder n m => Nest DataConRefBinding n -> m [Atom n]
-- loadDataConArgs = undefined
-- loadDataConArgs Empty = return []
-- loadDataConArgs (Nest (DataConRefBinding b ref) rest) = do
--   val <- loadDest ref
--   (Abs rest' HUnit) <- substBuilder (b@>val) (Abs rest HUnit)
--   (val:) <$> loadDataConArgs rest'

indexDestDim :: Builder n m => Int -> Dest n -> Atom n -> m (Dest n)
indexDestDim 0 dest i = indexDest dest i
indexDestDim d dest i = buildFor Fwd idxTy \j -> do
  dest' <- indexDest dest j
  indexDestDim (d-1) dest' i
  where RawRefTy (TabTy idxTy _) = dest

indexDest :: Builder n m => Dest n -> Atom n -> m (Dest n)
indexDest (PrimCon (TabRef tabVal)) i = appReduce tabVal i
indexDest dest _ = error $ pprint dest

sliceDestDim :: Builder n m => Int -> Dest n -> Atom n -> Type n -> m (Dest n)
sliceDestDim d dest i sliceIdxTy = buildFor Fwd idxTy \j -> do
  dest' <- indexDest dest j
  sliceDestDim (d-1) dest' i sliceIdxTy
  where RawRefTy (TabTy idxTy _) = dest

sliceDest :: Builder n m => Dest n -> Atom n -> Type n -> m (Dest n)
sliceDest ~(PrimCon (TabRef tab@(TabVal idxTy _))) i sliceIdxTy = (PrimCon . TabRef) <$> do
  buildFor Fwd sliceIdxTy \j -> do
    j' <- indexToIntE j
    ioff <- iadd j' i
    vidx <- intToIndexE idxTy ioff
    appReduce tab vidx

destToAtom :: ImpM n m => Dest n -> m (Atom n)
destToAtom = undefined
-- destToAtom dest = fromBuilder $ loadDest dest

destGet :: ImpM n m => Dest n -> Atom n -> m (Dest n)
destGet = undefined
-- destGet dest i = fromBuilder $ indexDest dest i

destPairUnpack :: Dest n -> (Dest n, Dest n)
destPairUnpack (PrimCon (ConRef (PairCon l r))) = (l, r)
destPairUnpack d = error $ "Not a pair destination: " ++ show d

fromDestConsList :: Dest n -> [Dest n]
fromDestConsList dest = case dest of
  PrimCon (ConRef (PairCon h t)) -> h : fromDestConsList t
  PrimCon (ConRef UnitCon)       -> []
  _ -> error $ "Not a dest cons list: " ++ pprint dest

makeAllocDest :: ImpM n m => AllocType -> Type n -> m (Dest n)
makeAllocDest allocTy ty = fst <$> makeAllocDestWithPtrs allocTy ty

makeAllocDestWithPtrs :: ImpM n m => AllocType -> Type n -> m (Dest n, [IExpr n])
makeAllocDestWithPtrs = undefined
-- makeAllocDestWithPtrs allocTy ty = do
--   backend <- asks impBackend
--   curDev <- asks curDevice
--   (ptrsSizes, dest) <- fromBuilder $ makeDest (backend, curDev, allocTy) ty
--   (env, ptrs) <- flip foldMapM ptrsSizes \(Bind (ptr:>PtrTy ptrTy), size) -> do
--     ptr' <- emitAlloc ptrTy $ fromScalarAtom size
--     case ptrTy of
--       (Heap _, _) | allocTy == Managed -> extendAlloc ptr'
--       _ -> return ()
--     return (ptr @> toScalarAtom ptr', [ptr'])
--   dest' <- impSubst env dest
--   return (dest', ptrs)

-- splitDest :: WithDest n (Block n)
--           -> ([WithDest n (Decl n)], WithDest n (Expr n), [(Dest n, Atom n)])
-- splitDest (maybeDest, (Block decls ans)) = undefined
-- splitDest (maybeDest, (Block decls ans)) = do
--   case (maybeDest, ans) of
--     (Just dest, Atom atom) -> do
--       let (gatherCopies, varDests) = runState (execWriterT $ gatherVarDests dest atom) mempty
--       -- if any variable appearing in the ans atom is not defined in the
--       -- current block (e.g. it comes from the surrounding block), then we need
--       -- to do the copy explicitly, as there is no let binding that will use it
--       -- as the destination.
--       let closureCopies = fmap (\(n, (d, t)) -> (d, Var $ n :> t))
--                                (envPairs $ varDests `envDiff` foldMap letBoundVars decls)

--       let destDecls = flip fmap (toList decls) \d -> case d of
--                         Let _ b _  -> (fst <$> varDests `envLookup` b, d)
--       (destDecls, (Nothing, ans), gatherCopies ++ closureCopies)
--     _ -> (fmap (Nothing,) $ toList decls, (maybeDest, ans), [])
--   where
--     -- Maps all variables used in the result atom to their respective destinations.
--     gatherVarDests :: Dest n -> Atom -> WriterT [(Dest, Atom)] (State (Env (Dest, Type n))) ()
--     gatherVarDests dest result = case (dest, result) of
--       (_, Var v) -> do
--         dests <- get
--         case dests `envLookup` v of
--           Nothing -> modify $ (<> (v @> (dest, varType v)))
--           Just _  -> tell [(dest, result)]
--       -- If the result is a table lambda then there is nothing we can do, except for a copy.
--       (_, TabVal _ _)  -> tell [(dest, result)]
--       (_, Con (Lit _)) -> tell [(dest, result)]
--       -- This is conservative, in case the type is dependent. We could do better.
--       (DataConRef _ _ _, DataCon _ _ _ _) -> tell [(dest, result)]
--       -- This is conservative. Without it, we hit bugs like #348
--       (Con (ConRef (SumAsProd _ _ _)), _) -> tell [(dest, result)]
--       (Con (ConRef destCon), Con srcCon) ->
--         zipWithRefConM gatherVarDests destCon srcCon
--       (Con (RecordRef items), Record items')
--         | fmap (const ()) items == fmap (const ()) items' -> do
--             zipWithM_ gatherVarDests (toList items) (toList items')
--       (_, ProjectElt _ _) -> tell [(dest, result)]  -- TODO: is this reasonable?
--       _ -> unreachable
--       where
--         unreachable = error $ "Invalid dest-result pair:\n"
--                         ++ pprint dest ++ "\n  and:\n" ++ pprint result

-- letBoundVars :: Decl n -> Scope n
-- letBoundVars (Let _ b _) = b @> ()

copyDest :: ImpM n m => Maybe (Dest n) -> Atom n -> m (Atom n)
copyDest maybeDest atom = case maybeDest of
  Nothing   -> return atom
  Just dest -> copyAtom dest atom >> return atom

allocDest :: ImpM n m => Maybe (Dest n) -> Type n -> m (Dest n)
allocDest maybeDest t = case maybeDest of
  Nothing   -> alloc t
  Just dest -> return dest

type AllocInfo = (Backend, Device, AllocType)

chooseAddrSpace :: AllocInfo -> Block n -> AddressSpace
chooseAddrSpace (backend, curDev, allocTy) numel = case allocTy of
  Unmanaged -> Heap mainDev
  Managed | curDev == mainDev -> if isSmall numel then Stack
                                                  else Heap mainDev
          | otherwise -> Heap mainDev
  where mainDev = case backend of
          LLVM      -> CPU
          LLVMMC    -> CPU
          LLVMCUDA  -> GPU
          Interpreter -> error "Shouldn't be compiling with interpreter backend"

isSmall :: Block n -> Bool
isSmall numel = case numel of
  Block _ (Result (PrimCon (Lit l)))
    | getIntLit l <= 256 -> True
    | otherwise          -> False
  -- TODO: remove this check if we're convinced it's always passing
  _ | null (freeNames numel) ->
        error $ "Blocks without free vars should have been fully reduced"
          ++ pprint numel
    | otherwise -> False

allocateBuffer :: ImpM n m => AddressSpace -> Bool -> BaseType -> IExpr n -> m (IExpr n)
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

fromScalarAtom :: HasCallStack => Atom n -> IExpr n
fromScalarAtom atom = case atom of
  Var  v          -> IVar v
  PrimCon (Lit x) -> ILit x
  _ -> error $ "Expected scalar, got: " ++ pprint atom

toScalarAtom :: IExpr n -> Atom n
toScalarAtom ie = case ie of
  ILit l -> PrimCon $ Lit l
  IVar v -> Var v

fromScalarType :: HasCallStack => Type n -> IType
fromScalarType (BaseTy b) =  b
fromScalarType ty = error $ "Not a scalar type: " ++ pprint ty

toScalarType :: IType -> Type n
toScalarType b = BaseTy b

-- === Type classes ===

liftDefReader :: ImpM n m => (forall m'. DefReader n m' => m' a) -> m a
liftDefReader _ = undefined

fromBuilder :: ImpM n m => (forall m'. Builder n m' => m' a) -> m a
fromBuilder _ = undefined
-- fromBuilder m = do
--   scope <- variableScope
--   let (ans, (_, decls)) = runBuilder m scope
--   env <- catFoldM translateDecl mempty $ fmap (Nothing,) $ fromNest decls
--   impSubst env ans

intToIndex :: ImpM n m => Type n -> IExpr n -> m (Atom n)
intToIndex = undefined
-- intToIndex ty i = fromBuilder (intToIndexE ty (toScalarAtom i))

indexToInt :: ImpM n m => Atom n -> m (IExpr n)
indexToInt idx = fromScalarAtom <$> fromBuilder (indexToIntE idx)

indexSetSize :: ImpM n m => Type n -> m (IExpr n)
indexSetSize = undefined
-- indexSetSize ty = fromScalarAtom <$> fromBuilder (indexSetSizeE ty)

zipTabDestAtom :: HasCallStack => ImpM n m
               => (Dest n -> Atom n -> m ())
               -> Dest n -> Atom n -> m ()
zipTabDestAtom = undefined
-- zipTabDestAtom f ~dest@(Con (TabRef (TabVal b _))) ~src@(TabVal b' _) = do
--   unless (binderType b == binderType b') $
--     error $ "Mismatched dimensions: " <> pprint b <> " != " <> pprint b'
--   let idxTy = binderType b
--   n <- indexSetSize idxTy
--   emitLoop "i" Fwd n \i -> do
--     idx <- intToIndex idxTy i
--     destIndexed <- destGet dest idx
--     srcIndexed  <- translateExpr mempty (Nothing, App src idx)
--     f destIndexed srcIndexed

-- zipWithRefConM :: Monad m => (Dest n -> Atom () -> m ()) -> Con () -> Con () -> m ()
-- zipWithRefConM f destCon srcCon = case (destCon, srcCon) of
--   (PairCon d1 d2, PairCon s1 s2) -> f d1 s1 >> f d2 s2
--   (UnitCon, UnitCon) -> return ()
--   (IntRangeVal     _ _ iRef, IntRangeVal     _ _ i) -> f iRef i
--   (IndexRangeVal _ _ _ iRef, IndexRangeVal _ _ _ i) -> f iRef i
--   _ -> error $ "Unexpected ref/val " ++ pprint (destCon, srcCon)

loadAnywhere :: ImpM n m => IExpr n -> m (IExpr n)
loadAnywhere ptr = do
  curDev <- asks curDevice
  ~(PtrType (addrSpace, ty)) <- getITypeM ptr
  case addrSpace of
    Heap ptrDev | ptrDev /= curDev -> do
      localPtr <- allocateStackSingleton ty
      memcopy localPtr ptr (IIdxRepVal 1)
      load localPtr
    _ -> load ptr

storeAnywhere :: ImpM n m => IExpr n -> IExpr n -> m ()
storeAnywhere ptr val = do
  curDev <- asks curDevice
  ~(PtrType (addrSpace, ty)) <- getITypeM ptr
  case addrSpace of
    Heap ptrDev | ptrDev /= curDev -> do
      localPtr <- allocateStackSingleton ty
      store localPtr val
      memcopy ptr localPtr (IIdxRepVal 1)
    _ -> store ptr val

allocateStackSingleton :: ImpM n m => IType -> m (IExpr n)
allocateStackSingleton ty = allocateBuffer Stack False ty (IIdxRepVal 1)

-- === Imp IR builders ===


-- ImpM should be able to imply builder



-- buildBinOp :: ImpM n m
--            => (Atom n -> Atom n -> Builder n (Atom n))
--            -> (IExpr n -> IExpr n -> m (IExpr n))
-- buildBinOp f x y =
--   fromScalarAtom <$> fromBuilder (f (toScalarAtom x) (toScalarAtom y))

-- iaddI :: ImpM n m => IExpr n -> IExpr n -> m (IExpr n)
-- iaddI = buildBinOp iadd

-- isubI :: ImpM n m => IExpr n -> IExpr n -> m (IExpr n)
-- isubI = buildBinOp isub

-- imulI :: ImpM n m => IExpr n -> IExpr n -> m (IExpr n)
-- imulI = buildBinOp imul

-- idivI :: ImpM n m => IExpr n -> IExpr n -> m (IExpr n)
-- idivI = buildBinOp idiv

-- iltI :: ImpM n m => IExpr n -> IExpr n -> m (IExpr n)
-- iltI = buildBinOp ilt

-- ieqI :: ImpM n m => IExpr n -> IExpr n -> m (IExpr n)
-- ieqI = buildBinOp ieq

bandI :: ImpM n m => IExpr n -> IExpr n -> m (IExpr n)
bandI x y = emitInstr $ IPrimOp $ ScalarBinOp BAnd x y

impOffset :: ImpM n m => IExpr n -> IExpr n -> m (IExpr n)
impOffset ref off = emitInstr $ IPrimOp $ PtrOffset ref off

cast :: ImpM n m => IExpr n -> BaseType -> m (IExpr n)
cast x bt = emitInstr $ ICastOp bt x

load :: ImpM n m => IExpr n -> m (IExpr n)
load x = emitInstr $ IPrimOp $ PtrLoad x

memcopy :: ImpM n m => IExpr n -> IExpr n -> IExpr n -> m ()
memcopy dest src numel = emitStatement $ MemCopy dest src numel

store :: HasCallStack => ImpM n m => IExpr n -> IExpr n -> m ()
store dest src = emitStatement $ Store dest src

alloc :: HasCallStack => ImpM n m => Type n -> m (Dest n)
alloc ty = makeAllocDest Managed ty

handleErrors :: ImpM n m => m () -> m ()
handleErrors m = m `catchError` (const $ emitStatement IThrowError)

emitWhen :: ImpM n m => IExpr n -> m () -> m ()
emitWhen cond doIfTrue = emitSwitch cond [return (), doIfTrue]

-- TODO: Consider targeting LLVM's `switch` instead of chained conditionals.
emitSwitch :: ImpM n m => IExpr n -> [m ()] -> m ()
emitSwitch = undefined
-- emitSwitch testIdx = rec 0
--   where
--     rec :: Int -> [m n] -> m ()
--     rec _ [] = error "Shouldn't have an empty list of alternatives"
--     rec _ [body] = body
--     rec curIdx (body:rest) = do
--       let curTag = fromScalarAtom $ TagRepVal $ fromIntegral curIdx
--       cond       <- emitInstr $ IPrimOp $ ScalarBinOp (ICmp Equal) testIdx curTag
--       thisCase   <- scopedErrBlock $ body
--       otherCases <- scopedErrBlock $ rec (curIdx + 1) rest
--       emitStatement $ ICond cond thisCase otherCases

emitLoop :: ImpM n m => NameStr -> Direction -> IExpr n -> (IExpr n -> m ()) -> m ()
emitLoop = undefined
-- emitLoop hint d n body = do
--   nTy <- getITypeM n
--   (i, loopBody) <- scopedBlock $ do
--     i <- freshVar hint nTy
--     handleErrors $ body $ IVar i
--     return (i, [])
--   emitStatement $ IFor d (i,nTy) n loopBody

fromScalarOrPairType :: Type n -> [IType]
fromScalarOrPairType (PairTy a b) =
  fromScalarOrPairType a <> fromScalarOrPairType b
fromScalarOrPairType (BaseTy ty) = [ty]
fromScalarOrPairType ty = error $ "Not a scalar or pair: " ++ pprint ty

restructureScalarOrPairType :: Type n -> [IExpr n] -> Atom n
restructureScalarOrPairType ty xs =
  case restructureScalarOrPairTypeRec ty xs of
    (atom, []) -> atom
    _ -> error "Wrong number of scalars"

restructureScalarOrPairTypeRec :: Type n -> [IExpr n] -> (Atom n, [IExpr n])
restructureScalarOrPairTypeRec (PairTy t1 t2) xs = do
  let (atom1, rest1) = restructureScalarOrPairTypeRec t1 xs
  let (atom2, rest2) = restructureScalarOrPairTypeRec t2 rest1
  (PairVal atom1 atom2, rest2)
restructureScalarOrPairTypeRec (BaseTy _) (x:xs) = (toScalarAtom x, xs)
restructureScalarOrPairTypeRec ty _ = error $ "Not a scalar or pair: " ++ pprint ty

emitMultiReturnInstr :: ImpM n m => ImpInstr n -> m [IExpr n]
emitMultiReturnInstr = undefined
-- emitMultiReturnInstr instr = do
--   bindings <- variableScope
--   bs <- forM (impInstrTypes bindings instr) \ty -> (,ty) <$> freshVar "v" ty
--   emitImpDecl $ ImpLet bs instr
--   return $ map (IVar . fst) bs

emitInstr :: ImpM n m => ImpInstr n -> m (IExpr n)
emitInstr instr = do
  xs <- emitMultiReturnInstr instr
  case xs of
    [x] -> return x
    _ -> error "unexpected numer of return values"

emitStatement :: ImpM n m => ImpInstr n -> m ()
emitStatement instr = do
  xs <- emitMultiReturnInstr instr
  case xs of
    [] -> return ()
    _ -> error "unexpected numer of return values"

data AllocType = Managed | Unmanaged  deriving (Show, Eq)

extendAlloc :: ImpM n m => IExpr n -> m ()
extendAlloc = undefined
-- extendAlloc v = extend $ mempty { envPtrsToFree = [v] }

emitAlloc :: (ImpM n m, HasCallStack) => PtrType -> IExpr n -> m (IExpr n)
emitAlloc (addr, ty) n = emitInstr $ Alloc addr ty n

scopedErrBlock :: ImpM n m => m n -> m (ImpBlock n)
scopedErrBlock = undefined --  body = liftM snd $ scopedBlock $ handleErrors body $> ((),[])

-- XXX: This does not handle errors that happen inside the block!
scopedBlock :: ImpM n m => m (a, [IExpr n]) -> m (a, ImpBlock n)
scopedBlock = undefined
-- scopedBlock body = do
--   ((aux, results), env) <- scoped body
--   -- Keep the scope extension to avoid reusing variable names
--   extend $ mempty { envBindings  = envBindings  env
--                   , envFunctions = envFunctions env }
--   let frees = [ImpLet [] (Free x) | x <- envPtrsToFree env]
--   return (aux, ImpBlock (envDecls env <> frees) results)

emitImpDecl :: ImpM n m => ImpDecl n -> m ()
emitImpDecl decl = undefined -- extend $ mempty { envDecls = [decl] }

-- variableScope :: ImpM (Bindings ())
-- variableScope = looks envBindings

withLevel :: ImpM n m => ParallelismLevel -> m a -> m a
withLevel level = local (\opts -> opts {curLevel = level })

withDevice :: ImpM n m => Device -> m a -> m a
withDevice device = local (\opts -> opts {curDevice = device })

-- -- === type checking imp programs ===

-- -- TODO: track parallelism level and current device and add validity checks like
-- -- "shouldn't launch a kernel from device/thread code"

-- -- State keeps track of _all_ names used in the program, Reader keeps the type env.
-- type ImpCheckM a = StateT (Scope ())
--        (ReaderT (Env () (HLift IType) () , Device) (Either Err)) a

-- -- instance Checkable ImpModule where
-- --   -- TODO: check main function defined
-- --   checkValid (ImpModule fs) = mapM_ checkValid fs

-- -- instance Checkable ImpFunction where
-- --   checkValid = undefined
--   -- checkValid f@(ImpFunction (_:> IFunType cc _ _) bs block) = addContext ctx $ do
--   --   let scope = foldMap (binderAsEnv . fmap (const ())) bs
--   --   let env   = foldMap (binderAsEnv                  ) bs
--   --            <> fmap (fromScalarType . fst) initBindings
--   --   void $ flip runReaderT (env, deviceFromCallingConvention cc) $
--   --     flip runStateT scope $ checkBlock block
--   --   where ctx = "Checking:\n" ++ pprint f
--   -- checkValid (FFIFunction _) = return ()

-- checkBlock :: ImpBlock -> ImpCheckM [IType]
-- checkBlock = undefined
-- -- checkBlock (ImpBlock [] val) = mapM checkIExpr val
-- -- checkBlock (ImpBlock (decl:rest) val) = do
-- --   env <- checkDecl decl
-- --   withTypeEnv env $ checkBlock $ ImpBlock rest val

-- checkDecl :: ImpDecl -> ImpCheckM (Env () (HLift IType) ())
-- checkDecl = undefined
-- -- checkDecl decl@(ImpLet bs instr) = addContext ctx $ do
-- --   tys <- instrTypeChecked instr
-- --   mapM_ checkBinder bs
-- --   assertEq (map snd bs) tys $ "Type mismatch in decl " ++ pprint decl
-- --   return $ foldMap (uncurry (@>)) $ zip (map fst bs) tys
-- --   where ctx = "Checking:\n" ++ pprint decl

-- instrTypeChecked :: ImpInstr -> ImpCheckM [IType]
-- instrTypeChecked = undefined
-- -- instrTypeChecked instr = case instr of
--   -- IFor _ i size block -> do
--   --   checkIdxRep size
--   --   checkBinder i
--   --   assertEq (snd i) (getIType size) $ "Mismatch between the loop iterator and upper bound type"
--   --   [] <- withTypeEnv (fst i @> getIType size) $ checkBlock block
--   --   return []
--   -- IWhile body -> do
--   --   [condTy] <- checkBlock body
--   --   assertEq (Scalar Word8Type) condTy $ "Not a bool: " ++ pprint body
--   --   return []
--   -- ICond predicate consequent alternative -> do
--   --   predTy <- checkIExpr predicate
--   --   assertEq (Scalar Word8Type) predTy "Type mismatch in predicate"
--   --   [] <- checkBlock consequent
--   --   [] <- checkBlock alternative
--   --   return []
--   -- ISyncWorkgroup -> return []
--   -- IQueryParallelism _ _ -> return [IIdxRepTy, IIdxRepTy]
--   -- ILaunch _ n args -> [] <$ do
--   --   -- TODO: check args against type of function
--   --   assertHost
--   --   checkInt n
--   --   mapM_ checkIExpr args
--   -- IPrimOp op -> (:[]) <$> checkImpOp op
--   -- ICastOp dt x -> (:[]) <$> do
--   --   st <- getITypeM x
--   --   case (dt, st) of
--   --     (PtrType _, PtrType _) -> return ()
--   --     (Scalar  _, Scalar  _) -> return ()
--   --     (Scalar Int64Type, PtrType  _) -> return ()
--   --     (PtrType _,  Scalar Int64Type) -> return ()
--   --     _ -> throw CompilerErr $
--   --           "Can't cast " ++ pprint st ++ " to " ++ pprint dt
--   --   return dt
--   -- Alloc a ty n -> (:[]) <$> do
--   --   checkIdxRep n
--   --   when (a /= Stack) assertHost
--   --   return $ PtrType (a, ty)
--   -- MemCopy dest src numel -> [] <$ do
--   --   PtrType (_, destTy) <- checkIExpr dest
--   --   PtrType (_, srcTy)  <- checkIExpr src
--   --   assertEq destTy srcTy "pointer type mismatch"
--   --   checkIdxRep numel
--   -- Store dest val -> [] <$ do
--   --   PtrType (addr, ty) <- checkIExpr dest
--   --   checkAddrAccessible addr
--   --   valTy <- checkIExpr val
--   --   assertEq ty valTy "Type mismatch in store"
--   -- Free _ -> return []  -- TODO: check matched alloc/free
--   -- IThrowError -> return []
--   -- ICall (_:>IFunType _ argTys resultTys) args -> do
--   --   argTys' <- mapM checkIExpr args
--   --   assertEq argTys argTys' "Args types don't match function type"
--   --   return resultTys

-- checkBinder :: IBinder -> ImpCheckM ()
-- checkBinder (v,_) = do
--   scope <- get
--   when (v `isin` scope) $ throw CompilerErr $ "shadows: " ++ pprint v
--   modify (<>(v@>HUnit))

-- checkAddrAccessible :: AddressSpace -> ImpCheckM ()
-- checkAddrAccessible Stack = return ()
-- checkAddrAccessible (Heap device) = do
--   curDev <- asks snd
--   when (device /= curDev) $ throw CompilerErr "Address not accessible"

-- assertHost :: ImpCheckM ()
-- assertHost = do
--   curDev <- asks snd
--   when (curDev /= CPU) $ throw CompilerErr "Only allowed on host"

-- checkIExpr :: IExpr n -> ImpCheckM IType
-- checkIExpr expr = case expr of
--   ILit val -> return $ litType val
--   IVar v -> do
--     env <- asks fst
--     case envLookup env v of
--       Nothing -> throw CompilerErr $ "Lookup failed: " ++ pprint v
--       Just x -> return $ fromHLift x

-- checkIdxRep :: IExpr n -> ImpCheckM ()
-- checkIdxRep expr = do
--   t <- checkIExpr expr
--   assertEq IIdxRepTy t $ "Not an index rep tye: " ++ pprint t

-- checkInt :: IExpr n -> ImpCheckM ()
-- checkInt expr = do
--   bt <- checkIExpr expr
--   checkIntBaseType False (BaseTy bt)

-- -- TODO: reuse type rules in Type.hs
-- checkImpOp :: IPrimOp -> ImpCheckM IType
-- checkImpOp op = do
--   op' <- traverse checkIExpr op
--   case op' of
--     ScalarBinOp bop x y -> checkImpBinOp bop x y
--     VectorBinOp bop x y -> checkImpBinOp bop x y
--     ScalarUnOp  uop x   -> checkImpUnOp  uop x
--     Select _ x y -> checkEq x y >> return x
--     VectorPack xs -> do
--       Scalar ty <- return $ head xs
--       mapM_ (checkEq (Scalar ty)) xs
--       return $ Vector ty
--     VectorIndex x i -> do
--       Vector ty <- return x
--       ibt       <- return i
--       checkIntBaseType False $ BaseTy ibt
--       return $ Scalar ty
--     PtrLoad ref -> do
--       PtrType (addr, ty) <- return ref
--       checkAddrAccessible addr
--       return ty
--     PtrOffset ref _ -> do  -- TODO: check offset too
--       PtrType (addr, ty) <- return ref
--       return $ PtrType (addr, ty)
--     _ -> error $ "Not allowed in Imp IR: " ++ pprint op
--   where
--     checkEq :: (Pretty a, Show a, Eq a) => a -> a -> ImpCheckM ()
--     checkEq t t' = assertEq t t' (pprint op)

getITypeM :: ImpM n m => a -> m IType
getITypeM x = undefined

-- class HasIType a where
--   getIType :: Bindings () -> a -> IType

-- instance HasIType IExpr where
--   getIType env x = case x of
--     ILit val -> litType val
--     IVar _ -> undefined

-- impFunType :: ImpFunction -> IFunType
-- impFunType = snd . impFunVar

-- -- impFunVar :: ImpFunction -> IFunVar
-- -- impFunVar (ImpFunction v _ _) = v
-- -- impFunVar (FFIFunction v) = v

-- impBlockType :: ImpBlock -> [IType]
-- impBlockType = undefined
-- -- impBlockType (ImpBlock _ results) = map getIType results

-- -- impInstrTypes :: Bindings () -> ImpInstr -> [IType]
-- -- impInstrTypes env instr = case instr of
-- --   -- IPrimOp op      -> [impOpType env op]
-- --   ICastOp t _     -> [t]
-- --   Alloc a ty _    -> [PtrType (a, ty)]
-- --   Store _ _       -> []
-- --   Free _          -> []
-- --   IThrowError     -> []
-- --   MemCopy _ _ _   -> []
-- --   IFor _ _ _ _    -> []
-- --   IWhile _        -> []
-- --   ICond _ _ _     -> []
-- --   ILaunch _ _ _   -> []
-- --   ISyncWorkgroup  -> []
-- --   IQueryParallelism _ _ -> [IIdxRepTy, IIdxRepTy]
-- --   -- ICall (_:>IFunType _ _ resultTys) _ -> resultTys

-- checkImpBinOp :: MonadError Err m => BinOp -> IType -> IType -> m IType
-- checkImpBinOp op x y = do
--   retTy <- checkBinOp op (BaseTy x) (BaseTy y)
--   case retTy of
--     BaseTy bt -> return bt
--     _         -> throw CompilerErr $ "Unexpected BinOp return type: " ++ pprint retTy

-- checkImpUnOp :: MonadError Err m => UnOp -> IType -> m IType
-- checkImpUnOp op x = do
--   retTy <- checkUnOp op (BaseTy x)
--   case retTy of
--     BaseTy bt -> return bt
--     _         -> throw CompilerErr $ "Unexpected UnOp return type: " ++ pprint retTy

-- -- TODO: reuse type rules in Type.hs
-- -- impOpType :: Bindings () -> IPrimOp -> IType
-- -- impOpType = undefined
-- -- impOpType pop = case pop of
-- --   ScalarBinOp op x y -> ignoreExcept $ checkImpBinOp op (getIType x) (getIType y)
-- --   ScalarUnOp  op x   -> ignoreExcept $ checkImpUnOp  op (getIType x)
-- --   VectorBinOp op x y -> ignoreExcept $ checkImpBinOp op (getIType x) (getIType y)
-- --   Select  _ x  _     -> getIType x
-- --   VectorPack xs      -> Vector ty  where Scalar ty = getIType $ head xs
-- --   VectorIndex x _    -> Scalar ty  where Vector ty = getIType x
-- --   PtrLoad ref        -> ty  where PtrType (_, ty) = getIType ref
-- --   PtrOffset ref _    -> PtrType (addr, ty)  where PtrType (addr, ty) = getIType ref
-- --   _ -> unreachable
-- --   where unreachable = error $ "Not allowed in Imp IR: " ++ pprint pop

-- -- withTypeEnv :: Env () (HLift IType) () -> ImpCheckM a -> ImpCheckM a
-- -- withTypeEnv = undefined
-- -- withTypeEnv env m = local (\(prev, dev) -> (prev <> env, dev)) m

-- instance Semigroup ImpCatEnv where
--   (ImpCatEnv a b c d) <> (ImpCatEnv a' b' c' d') =
--     ImpCatEnv (a<>a') (b<>b') (c<>c') (d<>d')

-- instance Monoid ImpCatEnv where
--   mempty = ImpCatEnv mempty mempty mempty mempty
--   mappend = (<>)
