-- Copyright 2021 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Imp
  ( toImpFunction, ImpFunctionWithRecon (..), toImpStandaloneFunction
  , PtrBinder, impFunType, getIType) where

import Data.Functor
import Data.Foldable (toList)
import Data.Text.Prettyprint.Doc (Pretty (..), hardline)
import Control.Category ((>>>))
import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.State.Class
import Control.Monad.Writer.Strict
import GHC.Stack
import qualified Data.List.NonEmpty as NE
import qualified Data.Map.Strict as M

import Err
import MTL1
import Name
import Builder
import Syntax
import Type
import Simplify
import LabeledItems
import qualified Algebra as A
import Util (enumerate)

type AtomRecon = Abs (Nest (NameBinder AtomNameC)) Atom

type PtrBinder = IBinder

-- TODO: make it purely a function of the type and avoid the AtomRecon
toImpFunction :: EnvReader m
              => Backend -> CallingConvention
              -> Abs (Nest PtrBinder) Block n
              -> m n (ImpFunctionWithRecon n)
toImpFunction _ cc absBlock = liftImpM $
  translateTopLevel cc idSubst Nothing absBlock

toImpStandaloneFunction :: EnvReader m => NaryLamExpr n -> m n (ImpFunction n)
toImpStandaloneFunction lam = liftImpM $ toImpStandaloneFunction' idSubst lam

toImpStandaloneFunction' :: Imper m => ImpSubst i o -> NaryLamExpr i -> m i o (ImpFunction o)
toImpStandaloneFunction' subst lam@(NaryLamExpr bs Pure body) = undefined
--   ty <- naryLamExprType lam
--   AbsPtrs (Abs ptrBinders argResultDest) ptrsInfo <- makeNaryLamDest ty
--   let ptrHintTys = [("ptr"::NameHint, PtrType baseTy) | DestPtrInfo baseTy _ <- ptrsInfo]
--   dropSubst $ buildImpFunction CInternalFun ptrHintTys \vs -> do
--     argResultDest' <- applySubst (ptrBinders@@>vs) argResultDest
--     (args, resultDest) <- loadArgDests argResultDest'
--     let subst' = sink subst <>> bs @@> map SubstVal args
--     void $ translateBlock (sink subst') (Just $ sink resultDest) body
--     return []
-- toImpStandaloneFunction' _ (NaryLamExpr _ _ _) = error "effectful functions not implemented"

loadArgDests :: (Emits n, ImpBuilder m) => NaryLamDest n -> m n ([ImpAtom n], Dest n)
loadArgDests (Abs Empty resultDest) = return ([], resultDest)
loadArgDests (Abs (Nest (b:>argDest) bs) resultDest) = do
  arg@(ImpAtom arg') <- destToAtom argDest
  restDest <- applySubst (b@>SubstVal arg') (Abs bs resultDest)
  (args, resultDest') <- loadArgDests restDest
  return (arg:args, resultDest')

storeArgDests :: (Emits n, ImpBuilder m) => NaryLamDest n -> [ImpAtom n] -> m n (Dest n)
storeArgDests (Abs Empty resultDest) [] = return resultDest
storeArgDests (Abs (Nest (b:>argDest) bs) resultDest) (x@(ImpAtom x'):xs) = do
  copyAtom argDest x
  restDest <- applySubst (b@>SubstVal x') (Abs bs resultDest)
  storeArgDests restDest xs
storeArgDests _ _ = error "dest/args mismatch"

data ImpFunctionWithRecon n = ImpFunctionWithRecon (ImpFunction n) (AtomRecon n)

instance GenericE ImpFunctionWithRecon where
  type RepE ImpFunctionWithRecon = PairE ImpFunction AtomRecon
  fromE (ImpFunctionWithRecon fun recon) = PairE fun recon
  toE   (PairE fun recon) = ImpFunctionWithRecon fun recon

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

type ImpBuilderEmissions = Nest ImpDecl

newtype ImpM (n::S) (a:: *) =
  ImpM { runImpM' :: ScopedT1 IxCache
                       (WriterT1 (ListE IExpr)
                         (InplaceT Env ImpBuilderEmissions HardFailM)) n a }
  deriving ( Functor, Applicative, Monad, ScopeReader, Fallible, MonadFail, MonadState (IxCache n))

-- TODO: use a dedicated type (e.g. a tree of ImpExpr) instead of using Atom
newtype ImpAtom (n::S) = ImpAtom { fromImpAtom :: Atom n }
        deriving (Show, SinkableE, SubstE Name, SubstE AtomSubstVal, HoistableE)
type ImpSubst = Subst (SubstVal AtomNameC ImpAtom)
type ImpIM = EnvReaderIT ImpM :: S -> S -> * -> *

instance ExtOutMap Env ImpBuilderEmissions where
  extendOutMap bindings emissions =
    bindings `extendOutMap` toEnvFrag emissions

class ( ImpBuilder2 m, EnvReaderI m
      , EnvReader2 m, EnvExtender2 m)
      => Imper (m::MonadKind2) where

instance EnvReader ImpM where
  unsafeGetEnv = ImpM $ lift11 $ lift11 $ getOutMapInplaceT

instance EnvExtender ImpM where
  refreshAbs ab cont = ImpM $ ScopedT1 \s -> lift11 $
    liftM (,s) $ refreshAbs ab \b e -> do
      (result, ptrs) <- runWriterT1 $ flip runScopedT1 (sink s) $ runImpM' $ cont b e
      case ptrs of
        ListE [] -> return result
        _ -> error "shouldn't be able to emit pointers without `Mut`"

instance ImpBuilder ImpM where
  emitMultiReturnInstr instr = do
    tys <- impInstrTypes instr
    ListE vs <- ImpM $ ScopedT1 \s -> lift11 do
      Abs bs vs <- return $ newNames $ map (const "v") tys
      let impBs = makeImpBinders bs tys
      let decl = ImpLet impBs instr
      liftM (,s) $ extendInplaceT $ Abs (Nest decl Empty) vs
    return $ zipWith IVar vs tys
    where
     makeImpBinders :: Nest (NameBinder AtomNameC) n l -> [IType] -> Nest IBinder n l
     makeImpBinders Empty [] = Empty
     makeImpBinders (Nest b bs) (ty:tys) = Nest (IBinder b ty) $ makeImpBinders bs tys
     makeImpBinders _ _ = error "zip error"

  buildScopedImp cont = ImpM $ ScopedT1 \s -> WriterT1 $ WriterT $
    liftM (, ListE []) $ liftM (,s) $ locallyMutableInplaceT do
      Emits <- fabricateEmitsEvidenceM
      (result, (ListE ptrs)) <- runWriterT1 $ flip runScopedT1 (sink s) $ runImpM' do
         Distinct <- getDistinct
         cont
      _ <- runWriterT1 $ flip runScopedT1 (sink s) $ runImpM' do
        forM ptrs \ptr -> emitStatement $ Free ptr
      return result

  extendAllocsToFree ptr = ImpM $ lift11 $ tell $ ListE [ptr]

instance ImpBuilder m => ImpBuilder (EnvReaderIT m i) where
  emitMultiReturnInstr instr = EnvReaderIT $ lift $ emitMultiReturnInstr instr
  buildScopedImp cont = EnvReaderIT $ ReaderT \(Distinct, env) ->
    buildScopedImp $ runEnvReaderIT env $ cont
  extendAllocsToFree ptr = EnvReaderIT $ lift $ extendAllocsToFree ptr

instance ImpBuilder m => Imper (EnvReaderIT m)

liftImpM :: EnvReader m => ImpIM n n a -> m n a
liftImpM cont = do
  env <- unsafeGetEnv
  Distinct <- getDistinct
  case runHardFail $ runInplaceT env $ runWriterT1 $
         flip runScopedT1 mempty $ runImpM' $ runEnvReaderIT env $ cont of
    (Empty, (result, ListE [])) -> return result
    _ -> error "shouldn't be possible because of `Emits` constraint"

-- === the actual pass ===

-- We don't emit any results when a destination is provided, since they are already
-- going to be available through the dest.
translateTopLevel :: Imper m
                  => CallingConvention
                  -> ImpSubst i o
                  -> MaybeDest o
                  -> Abs (Nest PtrBinder) Block i
                  -> m i o (ImpFunctionWithRecon o)
translateTopLevel cc subst maybeDest ab = do
  refreshAbsI ab \bs body -> do
    let argTys = nestToList (\b -> (getNameHint b, iBinderType b)) bs
    ab <- buildImpNaryAbs argTys \vs -> do
      let subst' = sink subst <>> bs @@> map Rename vs
      outDest <- case maybeDest of
        Nothing   -> do
          bodyTy <- getTypeI body
          makeAllocDest subst' Unmanaged bodyTy
        Just dest -> sinkM dest
      void $ translateBlock subst' (Just outDest) body
      destToAtom outDest
    refreshAbs ab \bs' ab' -> refreshAbs ab' \decls (ImpAtom resultAtom) -> do
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

translateBlock :: forall m i o. (Imper m, Emits o)
               => ImpSubst i o -> MaybeDest o -> Block i -> m i o (ImpAtom o)
translateBlock subst dest (Block _ decls result) =
  translateDeclNest subst (Abs decls result) \subst' result' -> do
    translateExpr subst' dest result'

translateDeclNest
  :: (Imper m, SubstE Name e, Emits o)
  => ImpSubst i o -> Abs (Nest Decl) e i
  -> (forall i'. ImpSubst i' o -> e i' -> m i' o a)
  -> m i o a
translateDeclNest subst (Abs Empty e) cont = cont subst e
translateDeclNest subst (Abs (Nest decl rest) e) cont =
  translateDecl subst (Abs decl (Abs rest e)) \subst' (Abs rest' e') -> do
    translateDeclNest subst' (Abs rest' e') \e'' -> cont e''

translateDecl :: (Imper m, SubstE Name e, Emits o)
              => ImpSubst i o -> Abs Decl e i
              -> (forall i'. ImpSubst i' o -> e i' -> m i' o a)
              -> m i o a
translateDecl subst ab cont = do
  Abs (Let _ (DeclBinding _ _ expr)) _ <- return ab
  ans <- translateExpr subst Nothing expr
  refreshAbsI ab \(Let b _) result -> do
    let subst' = subst <>> b @> SubstVal ans
    cont subst' result

translateExpr :: forall m i o. (Imper m, Emits o)
              => ImpSubst i o -> MaybeDest o -> Expr i -> m i o (ImpAtom o)
translateExpr subst maybeDest expr = case expr of
  Hof hof -> toImpHof subst maybeDest hof
  App f' xs' -> do
    f <- (atomToImpAtom subst) f'
    xs <- mapM (atomToImpAtom subst) xs'
    getTypeI f' >>= \case
      TabTy _ _ -> do
        case fromNaryLam (length xs) (fromImpAtom f) of
          Just (NaryLamExpr bs _ body) -> do
            body' <- applySubst (bs @@> fmap (SubstVal . fromImpAtom) xs) body
            env <- unsafeGetEnv
            Distinct <- getDistinct
            withEnvI env $ translateBlock idSubst maybeDest body'
          _ -> notASimpExpr
      _ -> case f of
        ImpAtom (Var v) -> lookupAtomName v >>= \case
          FFIFunBound _ v' -> do
            resultTy <- getTypeI expr
            scalarArgs <- liftM toList $ mapM fromScalarAtom xs
            results <- emitMultiReturnInstr $ ICall v' scalarArgs
            restructureScalarOrPairType resultTy results
          SimpLamBound piTy _ -> do
            if length (toList xs') /= numNaryPiArgs piTy
              then notASimpExpr
              else do
                Just fImp <- queryImpCache v
                result <- emitCall piTy fImp $ toList xs
                returnVal result
          _ -> notASimpExpr
        _ -> notASimpExpr
  Atom x -> atomToImpAtom subst x >>= returnVal
  Op op -> toImpOp subst maybeDest op
  Case e alts ty _ -> do
    e' <- atomToImpAtom subst e
    case trySelectBranch (fromImpAtom e') of
      Just (con, args) -> refreshAbsI (alts !! con) \bs body -> do
        let subst' = subst <>> bs @@> map (SubstVal . ImpAtom) args
        translateBlock subst' maybeDest body
      Nothing -> case fromImpAtom e' of
        Con (SumAsProd _ tag xss) -> do
          tag' <- fromScalarAtom $ ImpAtom tag
          dest <- allocDest subst maybeDest ty
          emitSwitch tag' (zip xss alts) $
            \(xs, ab) -> refreshAbsI ab \bs body -> do
               let subst' = subst <>> bs @@> map (SubstVal . ImpAtom) xs
               void $ translateBlock (sink subst') (Just $ sink dest) body
          destToAtom dest
      _ -> error "not possible"
  where
    notASimpExpr = error $ "not a simplified expression: " ++ pprint expr

    returnVal:: ImpAtom o -> m i o (ImpAtom o)
    returnVal atom = case maybeDest of
      Nothing   -> return atom
      Just dest -> copyAtom dest atom >> return atom

toImpOp :: forall m i o . (Imper m, Emits o)
        => ImpSubst i o -> MaybeDest o
        -> PrimOp (Atom i) -> m i o (ImpAtom o)
toImpOp subst maybeDest op = do
  resultTy <- getTypeI (Op op)
  case op of
    TabCon ~(Pi tabTy) rows -> do
      let ixTy = piArgType tabTy
      dest <- allocDest subst maybeDest resultTy
      forM_ (zip [0..] rows) \(i, row) -> do
        row' <- toImp row
        ithDest <- destGet dest =<< intToIndexImp subst ixTy (IIdxRepVal i)
        copyAtom ithDest row'
      destToAtom dest
    PrimEffect refDest m -> do
      refDest' <- refAtomToDest <$> toImp refDest
      case m of
        MAsk -> returnVal =<< destToAtom refDest'
        -- MExtend (BaseMonoid _ combine) x -> do
        --   xTy <- getType x
        --   refVal <- destToAtom refDest
        --   result <- liftBuilderImpSimplify $
        --               liftMonoidCombine (sink xTy) (sink combine) (sink refVal) (sink x)
        --   copyAtom refDest result
        --   returnVal UnitVal
        MPut x -> do
          x' <- toImp x
          copyAtom refDest' x' >> returnVal (ImpAtom UnitVal)
        -- MGet -> do
        --   resultTy <- resultTyM
        --   dest <- allocDest maybeDest resultTy
        --   -- It might be more efficient to implement a specialized copy for dests
        --   -- than to go through a general purpose atom.
        --   copyAtom dest =<< destToAtom refDest
        --   destToAtom dest
    UnsafeFromOrdinal n i -> do
      i' <- toImp i
      returnVal =<< intToIndexImp subst n =<< fromScalarAtom i'
    IdxSetSize n -> returnVal =<< toScalarAtom  =<< indexSetSizeImp subst n
    ToOrdinal idx -> case idx of
      Con (IntRangeVal   _ _   i) -> returnVal =<< toImp i
      Con (IndexRangeVal _ _ _ i) -> returnVal =<< toImp i
      _ -> returnVal =<< toScalarAtom =<< indexToIntImp =<< toImp idx
    -- Inject e -> case e of
    --   Con (IndexRangeVal t low _ restrictIdx) -> do
    --     offset <- case low of
    --       InclusiveLim a -> indexToIntImp a
    --       ExclusiveLim a -> indexToIntImp a >>= iaddI (IIdxRepVal 1)
    --       Unlimited      -> return (IIdxRepVal 0)
    --     restrictIdx' <- fromScalarAtom restrictIdx
    --     returnVal =<< intToIndexImp t =<< iaddI restrictIdx' offset
    --   Con (ParIndexCon (TC (ParIndexRange realIdxTy _ _)) i) -> do
    --     i' <- fromScalarAtom i
    --     returnVal =<< intToIndexImp realIdxTy i'
    --   _ -> error $ "Unsupported argument to inject: " ++ pprint e
    -- IndexRef refDest i -> returnVal =<< destGet refDest i
    -- ProjRef i ~(Con (ConRef (ProdCon refs))) -> returnVal $ refs !! i
    IOAlloc ty n -> do
      ptr <- emitAlloc (Heap CPU, ty) =<< fromScalarAtom =<< toImp n
      returnVal =<< toScalarAtom ptr
    IOFree ptr -> do
      ptr' <- fromScalarAtom =<< toImp ptr
      emitStatement $ Free ptr'
      return $ ImpAtom UnitVal
    PtrOffset arr (IdxRepVal 0) -> returnVal =<< toImp arr
    PtrOffset arr off -> do
      arr' <- fromScalarAtom =<< toImp arr
      off' <- fromScalarAtom =<< toImp off
      buf <- impOffset arr' off'
      returnVal =<< toScalarAtom buf
    PtrLoad arr ->
      returnVal =<< toScalarAtom =<< loadAnywhere =<< fromScalarAtom =<< toImp arr
    PtrStore ptr x -> do
      ptr' <- fromScalarAtom =<< toImp ptr
      x'   <- fromScalarAtom =<< toImp x
      store ptr' x'
      return $ ImpAtom UnitVal
    -- SliceOffset ~(Con (IndexSliceVal n _ tileOffset)) idx -> do
    --   i' <- indexToIntImp idx
    --   tileOffset' <- fromScalarAtom tileOffset
    --   i <- iaddI tileOffset' i'
    --   returnVal =<< intToIndexImp n i
    -- SliceCurry ~(Con (IndexSliceVal _ (PairTy _ v) tileOffset)) idx -> do
    --   vz <- intToIndexImp v $ IIdxRepVal 0
    --   extraOffset <- indexToIntImp (PairVal idx vz)
    --   tileOffset' <- fromScalarAtom tileOffset
    --   tileOffset'' <- iaddI tileOffset' extraOffset
    --   returnVal =<< toScalarAtom tileOffset''
    ThrowError _ -> do
      dest <- allocDest subst maybeDest resultTy
      emitStatement IThrowError
      -- XXX: we'd be reading uninitialized data here but it's ok because control never reaches
      -- this point since we just threw an error.
      destToAtom dest
    CastOp destTy x -> do
      sourceTy <- getTypeI x
      case (sourceTy, destTy) of
        (BaseTy _, BaseTy bt) -> do
          x' <- fromScalarAtom =<< toImp x
          returnVal =<< toScalarAtom =<< cast x' bt
        (TC (IntRange _ _), IdxRepTy) -> do
          ImpAtom (Con (IntRangeVal _ _ xord)) <- toImp x
          returnVal $ ImpAtom xord
        (IdxRepTy, TC (IntRange l h)) -> undefined
          -- returnVal $ ImpAtom $ Con $ IntRangeVal l h x
        (TC (IndexRange _ _ _), IdxRepTy) -> undefined
          -- let Con (IndexRangeVal _ _ _ xord) = x
          -- returnVal $ ImpAtom xord
        (IdxRepTy, TC (IndexRange t l h)) -> undefined
          -- returnVal $ ImpAtom $ Con $ IndexRangeVal t l h x
        _ -> error $ "Invalid cast: " ++ pprint sourceTy ++ " -> " ++ pprint destTy
    -- Select p x y -> do
    --   xTy <- getType x
    --   case xTy of
    --     BaseTy _ -> do
    --       p' <- fromScalarAtom p
    --       x' <- fromScalarAtom x
    --       y' <- fromScalarAtom y
    --       ans <- emitInstr $ IPrimOp $ Select p' x' y'
    --       returnVal =<< toScalarAtom ans
    --     _ -> do
    --       resultTy <- resultTyM
    --       dest <- allocDest maybeDest resultTy
    --       p' <- fromScalarAtom p
    --       p'' <- cast p' tagBT
    --       -- XXX: this is `[y, x]` and not `[x, y]`! `Select` gives the first
    --       -- element if the predicate is `1` ("true") and the second if it's `0`
    --       -- ("false") but the binary case of the n-ary `switch` does the
    --       -- opposite.
    --       emitSwitch p'' [y, x] (\arg -> copyAtom (sink dest) (sink arg))
    --       destToAtom dest
    --       where (BaseTy tagBT) = TagRepTy
    RecordCons   _ _ -> error "Unreachable: should have simplified away"
    RecordSplit  _ _ -> error "Unreachable: should have simplified away"
    VariantLift  _ _ -> error "Unreachable: should have simplified away"
    VariantSplit _ _ -> error "Unreachable: should have simplified away"
    -- DataConTag con -> case con of
    --   Con (SumAsProd _ tag _) -> returnVal tag
    --   DataCon _ _ _ i _ -> returnVal $ TagRepVal $ fromIntegral i
    --   _ -> error $ "Not a data constructor: " ++ pprint con
    -- ToEnum ty i -> returnVal =<< case ty of
    --   TypeCon _ defName _ -> do
    --     DataDef _ _ cons <- lookupDataDefI defName
    --     return $ Con $ SumAsProd ty i (map (const []) cons)
    --   VariantTy (NoExt labeledItems) ->
    --     return $ Con $ SumAsProd ty i (map (const [UnitVal]) $ toList labeledItems)
    --   SumTy cases ->
    --     return $ Con $ SumAsProd ty i $ cases <&> const [UnitVal]
    --   _ -> error $ "Not an enum: " ++ pprint ty
    -- SumToVariant ~(Con c) -> do
    --   ~resultTy@(VariantTy labs) <- return resultTy
    --   returnVal $ case c of
    --     SumCon    _ tag payload -> Variant labs "c" tag payload
    --     SumAsProd _ tag payload -> Con $ SumAsProd resultTy tag payload
    --     _ -> error $ "Not a sum type: " ++ pprint (Con c)
    _ -> do
      instr <- IPrimOp <$> forM op \x -> fromScalarAtom =<< toImp x
      emitInstr instr >>= toScalarAtom >>= returnVal
  where
    toImp atom = atomToImpAtom subst atom

    returnVal atom = case maybeDest of
      Nothing   -> return atom
      Just dest -> copyAtom dest atom >> return atom

toImpHof :: (Imper m, Emits o)
         => ImpSubst i o -> Maybe (Dest o) -> PrimHof (Atom i) -> m i o (ImpAtom o)
toImpHof subst maybeDest hof = do
  resultTy <- getTypeI $ Hof hof
  case hof of
    For (RegularFor d) (Lam lam) -> do
      let idxTy = lamArgType lam
      refreshLamI lam \b body -> do
        case idxTy of
          _ -> do
            n <- indexSetSizeImp subst idxTy
            dest <- allocDest subst maybeDest resultTy
            emitLoop (getNameHint b) d n \i -> do
              idx <- intToIndexImp (sink subst) idxTy i
              ithDest <- destGet (sink dest) idx
              let subst' = sink subst <>> b @> SubstVal idx
              void $ translateBlock subst' (Just ithDest) body
            destToAtom dest
    While (Lam lam) -> refreshLamI lam \b body -> do
      let subst' = subst <>> b @> SubstVal (ImpAtom UnitVal)
      body' <- buildBlockImp do
        ans <- fromScalarAtom =<< translateBlock (sink subst') Nothing body
        return [ans]
      emitStatement $ IWhile body'
      return $ ImpAtom UnitVal
    RunReader r (Lam (BinaryLamExpr h ref body)) -> do
      r' <- atomToImpAtom subst r
      rDest <- alloc subst =<< getTypeI r
      copyAtom rDest r'
      refreshAbsI (Abs (PairB h ref) body) \(PairB h' ref') body' -> do
        let subst' = subst <>> (h'   @> SubstVal (ImpAtom UnitTy)
                           <.>  ref' @> SubstVal (destToRefAtom rDest))
        translateBlock subst' maybeDest body'
--     RunWriter (BaseMonoid e _) (Lam (BinaryLamExpr h ref body)) -> do
--       let PairTy _ accTy = resultTy
--       (aDest, wDest) <- destPairUnpack <$> allocDest maybeDest resultTy
--       e' <- substM e
--       emptyVal <- liftBuilderImp do
--         PairE accTy' e'' <- sinkM $ PairE accTy e'
--         liftMonoidEmpty accTy' e''
--       copyAtom wDest emptyVal
--       void $ extendSubst (h @> SubstVal UnitTy <.> ref @> SubstVal wDest) $
--         translateBlock (Just aDest) body
--       PairVal <$> destToAtom aDest <*> destToAtom wDest
    RunState s (Lam (BinaryLamExpr h ref body)) -> do
      s' <- atomToImpAtom subst s
      (aDest, sDest) <- destPairUnpack <$> allocDest subst maybeDest resultTy
      copyAtom sDest s'
      refreshAbsI (Abs (PairB h ref) body) \(PairB h' ref') body' -> do
        let subst' = subst <>> (h'   @> SubstVal (ImpAtom UnitTy)
                           <.>  ref' @> SubstVal (destToRefAtom sDest) )
        void $ translateBlock subst' (Just aDest) body'
      liftM ImpAtom $ PairVal <$> (fromImpAtom <$> destToAtom aDest)
                              <*> (fromImpAtom <$> destToAtom sDest)
    RunIO (Lam lam) -> refreshLamI lam \b body -> do
      let subst' = subst <>> b @> SubstVal (ImpAtom UnitVal)
      translateBlock subst' maybeDest body
    _ -> error $ "not implemented: " ++ pprint hof

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
type PtrBinders = Nest AtomNameBinder
data DestEmissions n l where
  DestEmissions
    :: [DestPtrInfo n]   -- pointer types and allocation sizes
    -> PtrBinders n h    -- pointer binders for allocations we require
    ->   Nest Decl h l   -- decls to compute indexing offsets
    -> DestEmissions n l

instance GenericB DestEmissions where
  type RepB DestEmissions =         LiftB (ListE DestPtrInfo)
                            `PairB` Nest AtomNameBinder
                            `PairB` Nest Decl
  fromB (DestEmissions ps bs ds) = LiftB (ListE ps) `PairB` bs `PairB` ds
  toB   (LiftB (ListE ps) `PairB` bs `PairB` ds) = DestEmissions ps bs ds

instance BindsEnv DestEmissions where
  toEnvFrag = undefined -- TODO: might need to add pointer types to pointer binders?

instance ProvesExt   DestEmissions
instance BindsNames  DestEmissions
instance SinkableB DestEmissions
instance SubstB Name DestEmissions
instance HoistableB  DestEmissions

instance OutFrag DestEmissions where
  emptyOutFrag = DestEmissions [] Empty Empty
  catOutFrags _ (DestEmissions p1 b1 d1) (DestEmissions p2 b2 d2) =
    ignoreHoistFailure do
      ListE p2' <- hoist (PairB b1 d1) (ListE p2)
      PairB b2' d1' <- withSubscopeDistinct d2 $exchangeBs $ PairB d1 b2
      return $ DestEmissions (p1 <> p2') (b1 >>> b2') (d1' >>> d2)

newtype DestM (n::S) (a:: *) =
  DestM { runDestM' :: StateT1 IxCache
                         (InplaceT Env DestEmissions
                           (ReaderT AllocInfo HardFailM)) n a }
  deriving ( Functor, Applicative, Monad, MonadFail
           , ScopeReader, Fallible, MonadState (IxCache n) )

liftDestM :: forall m n a. EnvReader m
          => AllocInfo -> IxCache n
          -> DestM n a
          -> m n (a, IxCache n)
liftDestM allocInfo cache m = do
  env <- unsafeGetEnv
  Distinct <- getDistinct
  let result = runHardFail $ flip runReaderT allocInfo $
                 runInplaceT env $ flip runStateT1 cache $ runDestM' m
  case result of
    (DestEmissions _ Empty Empty, result') -> return result'
    _ -> error "not implemented"

getAllocInfo :: DestM n AllocInfo
getAllocInfo = DestM $ lift11 $ lift1 ask

introduceNewPtr :: Mut n => NameHint -> PtrType -> Block n -> DestM n (AtomName n)
introduceNewPtr hint ptrTy numel = do
  Abs b v <- newNameM hint
  let ptrInfo = DestPtrInfo ptrTy numel
  let emission = DestEmissions [ptrInfo] (Nest b Empty) Empty
  DestM $ StateT1 \s -> fmap (,s) $ extendInplaceT $ Abs emission v

buildLocalDest
  :: (SinkableE e)
  => (forall l. (Mut l, DExt n l) => DestM l (e l))
  -> DestM n (AbsPtrs e n)
buildLocalDest cont = do
  Abs (DestEmissions ptrInfo ptrBs decls) e <-
    DestM $ StateT1 \s -> do
      Abs bs (PairE e s') <- locallyMutableInplaceT $ fmap toPairE $ flip runStateT1 (sink s) $ runDestM' cont
      s'' <- hoistState s bs s'
      return $ (Abs bs e, s'')
  case decls of
    Empty -> return $ AbsPtrs (Abs ptrBs e) ptrInfo
    _ -> error "shouldn't have decls without `Emits`"

-- TODO: this is mostly copy-paste from Inference
buildDeclsDest
  :: (Mut n, SubstE Name e, SinkableE e)
  => (forall l. (Emits l, DExt n l) => DestM l (e l))
  -> DestM n (Abs (Nest Decl) e n)
buildDeclsDest cont = do
  DestM $ StateT1 \s -> do
    Abs (DestEmissions ptrInfo ptrBs decls) result <- locallyMutableInplaceT do
      Emits <- fabricateEmitsEvidenceM
      toPairE <$> flip runStateT1 (sink s) (runDestM' cont)
    Abs decls' (PairE e s') <- extendInplaceT $
                                 Abs (DestEmissions ptrInfo ptrBs Empty) $ Abs decls result
    s'' <- hoistState s decls' s'
    return (Abs decls' e, s'')

buildBlockDest
  :: Mut n
  => (forall l. (Emits l, DExt n l) => DestM l (Atom l))
  -> DestM n (Block n)
buildBlockDest cont = do
  Abs decls (PairE result ty) <- buildDeclsDest do
    result <- cont
    ty <- getType result
    return $ result `PairE` ty
  ty' <- liftHoistExcept $ hoist decls ty
  return $ Block (BlockAnn ty') decls $ Atom result

-- TODO: this is mostly copy-paste from Inference
buildAbsDest
  :: (SinkableE e, SubstE Name e, HoistableE e, Color c, ToBinding binding c)
  => Mut n
  => NameHint -> binding n
  -> (forall l. (Mut l, DExt n l) => Name c l -> DestM l (e l))
  -> DestM n (Abs (BinderP c binding) e n)
buildAbsDest hint binding cont = DestM $ StateT1 \s -> do
  resultWithEmissions <- withFreshBinder hint binding \b -> do
    ab <- locallyMutableInplaceT do
      fmap toPairE $ flip runStateT1 (sink s) $ runDestM' $ cont $ sink $ binderName b
    refreshAbs ab \emissions result -> do
      PairB emissions' b' <- liftHoistExcept $ exchangeBs $ PairB b emissions
      return $ Abs emissions' $ Abs b' result
  Abs b (PairE e s') <- extendInplaceT resultWithEmissions
  s'' <- hoistState s b s'
  return (Abs (b:>binding) e, s'')

buildTabLamDest
  :: Mut n
  => NameHint -> Type n
  -> (forall l. (Emits l, DExt n l) => AtomName l -> DestM l (Atom l))
  -> DestM n (Atom n)
buildTabLamDest hint ty cont = do
  Abs (b:>_) body <- buildAbsDest hint (LamBinding TabArrow ty) \v ->
    buildBlockDest $ sinkM v >>= cont
  return $ Lam $ LamExpr (LamBinder b ty TabArrow Pure) body

instance EnvExtender DestM where
  refreshAbs ab cont = DestM $ StateT1 \s -> do
    (ans, (Abs b s')) <- refreshAbs ab \b e -> do
      (ans, s') <- flip runStateT1 (sink s) $ runDestM' $ cont b e
      return (ans, Abs b s')
    s'' <- hoistState s b s'
    return (ans, s'')

instance EnvReader DestM where
  unsafeGetEnv = DestM $ lift11 $ getOutMapInplaceT

instance Builder DestM where
  emitDecl hint ann expr = do
    ty <- getType expr
    Abs b v <- newNameM hint
    let decl = Let b $ DeclBinding ann ty expr
    let emissions = DestEmissions [] Empty $ Nest decl Empty
    DestM $ StateT1 \s -> fmap (,s) $ extendInplaceT $ Abs emissions v

instance ExtOutMap Env DestEmissions where
  extendOutMap bindings (DestEmissions ptrInfo ptrs decls) =
    withSubscopeDistinct decls $
      (bindings `extendOutMap` ptrBindersToEnvFrag ptrInfo ptrs)
                `extendOutMap` decls
   where
     ptrBindersToEnvFrag :: Distinct l => [DestPtrInfo n] -> Nest AtomNameBinder n l -> EnvFrag n l
     ptrBindersToEnvFrag [] Empty = emptyOutFrag
     ptrBindersToEnvFrag (DestPtrInfo ty _ : rest) (Nest b restBs) =
       withSubscopeDistinct restBs do
         let frag1 = toEnvFrag $ b :> PtrTy ty
         let frag2 = withExtEvidence (toExtEvidence b) $
                        ptrBindersToEnvFrag (map sink rest) restBs
         frag1 `catEnvFrags` frag2
     ptrBindersToEnvFrag _ _ = error "mismatched indices"


instance GenericE DestPtrInfo where
  type RepE DestPtrInfo = PairE (LiftE PtrType) Block
  fromE (DestPtrInfo ty n) = PairE (LiftE ty) n
  toE   (PairE (LiftE ty) n) = DestPtrInfo ty n

instance SinkableE DestPtrInfo
instance HoistableE  DestPtrInfo
instance SubstE Name DestPtrInfo
instance SubstE AtomSubstVal DestPtrInfo

-- === Destination builder ===

-- TODO: use a dedicated type (e.g. a tree of ImpExpr) instead of using Atom
newtype Dest (n::S) = Dest { fromDest :: Atom n }   -- has type `Ref a` for some a
        deriving ( Show, SinkableE, SubstE Name
                 , SubstE AtomSubstVal, HoistableE)
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
makeDest :: (ImpBuilder m, EnvReader m)
         => ImpSubst i o -> AllocInfo -> Type i -> m o (AbsPtrs Dest o)
makeDest subst allocInfo ty = do
   cache <- get
   (result, cache') <- liftDestM allocInfo cache $
                         buildLocalDest $ makeSingleDest ty
   put cache'
   return result

makeSingleDest :: Mut o => Type i -> DestM o (Dest o)
makeSingleDest ty = do
  Abs decls dest <- buildDeclsDest $ makeDestRec ty
  case decls of
    Empty -> return dest
    _ -> error
     $ "shouldn't need to emit decls if we're not working with indices"
     ++ pprint decls

extendIdxsTy
  :: EnvReader m
  => DestIdxs n -> Type n -> m n (EmptyAbs IdxNest n)
extendIdxsTy (idxsTy, idxs) new = do
  let newAbs = abstractFreeVarsNoAnn idxs new
  Abs bs (Abs b UnitE) <- liftBuilder $ buildNaryAbs idxsTy \idxs' -> do
    ty' <- applyNaryAbs (sink newAbs) idxs'
    singletonBinderNest NoHint ty'
  return $ Abs (bs >>> b) UnitE

type Idxs n = [AtomName n]
type IdxNest = Nest Binder
type DestIdxs n = (EmptyAbs IdxNest n, Idxs n)
type DepVars n = [AtomName n]

-- TODO: make `DestIdxs` a proper E-kinded thing
sinkDestIdxs :: DExt n l => DestIdxs n -> DestIdxs l
sinkDestIdxs (idxsTy, idxs) = (sink idxsTy, map sink idxs)

-- dest for the args and the result
-- TODO: de-dup some of the plumbing stuff here with the ordinary makeDest path
type NaryLamDest = Abs (Nest (BinderP AtomNameC Dest)) Dest

makeNaryLamDest :: (ImpBuilder m, EnvReader m)
                => ImpSubst i o -> NaryPiType i -> m o (AbsPtrs NaryLamDest o)
makeNaryLamDest subst piTy = do
  cache <- get
  let allocInfo = (LLVM, CPU, Unmanaged) -- TODO! This is just a placeholder
  (result, cache') <- liftDestM allocInfo cache $ buildLocalDest do
    Abs decls dest <- buildDeclsDest $ makeNaryLamDestRec piTy
    case decls of
      Empty -> return dest
      _ -> error "shouldn't have decls if we have empty indices"
  put cache'
  return result

makeNaryLamDestRec
  :: forall i o. Emits o
  => NaryPiType i -> DestM o (NaryLamDest o)
makeNaryLamDestRec (NaryPiType (NonEmptyNest b bs) Pure resultTy) = undefined
-- makeNaryLamDestRec (NaryPiType (NonEmptyNest b bs) Pure resultTy) = do
--   let argTy = binderType b
--   argDest <- makeDestRec argTy
--   Abs (b':>_) (Abs bs' resultDest) <-
--     buildDepDest (getNameHint b) argTy \v -> do
--       case bs of
--         Empty -> do
--           resultTy' <- applySubst (b@>v) resultTy
--           Abs Empty <$> makeDestRec resultTy'
--         Nest b1 bsRest -> do
--           restPiTy <- applySubst (b@>v) $ NaryPiType (NonEmptyNest b1 bsRest) Pure resultTy
--           makeNaryLamDestRec restPiTy
--   return $ Abs (Nest (b':>argDest) bs') resultDest
-- makeNaryLamDestRec _ = error "effectful functions not implemented"

makeDestRec :: forall i o. Emits o => Type i -> DestM o (Dest o)
makeDestRec ty = case ty of
  TabTy _ _        -> error "not implemented"
  TypeCon _ _ _    -> error "not implemented"
  DepPairTy _      -> error "not implemented"
  StaticRecordTy _ -> error "not implemented"
  VariantTy _      -> error "not implemented"
  TC con -> case con of
    BaseType b -> do
      ptr <- makeBaseTypePtr (Abs Empty UnitE, []) b
      return $ Dest $ Con $ BaseTypeRef ptr
    _ -> error $ "not implemented: " ++ pprint con
  _ -> error $ "not implemented: " ++ pprint ty

makeBaseTypePtr :: Emits n => DestIdxs n -> BaseType -> DestM n (Atom n)
makeBaseTypePtr (idxsTy, idxs) ty = do
  offset <- computeOffset idxsTy idxs
  numel <- buildBlockDest $ computeElemCount (sink idxsTy)
  allocInfo <- getAllocInfo
  let addrSpace = chooseAddrSpace allocInfo numel
  let ptrTy = (addrSpace, ty)
  ptr <- Var <$> introduceNewPtr "ptr" ptrTy numel
  ptrOffset ptr offset

copyAtom :: (ImpBuilder m, Emits n) => Dest n -> ImpAtom n -> m n ()
copyAtom (Dest topDest) (ImpAtom topSrc) = copyRec topDest topSrc
  where
    copyRec :: (ImpBuilder m, Emits n) => Atom n -> Atom n -> m n ()
    copyRec dest src = case (dest, src) of
      (BoxedRef ptrsSizes absDest, _) -> do
        -- TODO: load old ptr and free (recursively)
        ptrs <- forM ptrsSizes \(ptrPtr, sizeBlock) -> do
          PtrTy (_, (PtrType ptrTy)) <- getType ptrPtr
          size <- liftBuilderImp $ emitBlock =<< sinkM sizeBlock
          ptr <- emitAlloc ptrTy =<< fromScalarAtom size
          ptrPtr' <- fromScalarAtom (ImpAtom ptrPtr)
          storeAnywhere ptrPtr' ptr
          toScalarAtom ptr
        dest' <- applyNaryAbs absDest (map (SubstVal . fromImpAtom) ptrs)
        copyRec dest' src
      (DepPairRef lRef rRefAbs _, DepPair l r _) -> do
        copyRec lRef l
        rRef <- applyAbs rRefAbs (SubstVal l)
        copyRec rRef r
      (DataConRef _ _ refs, DataCon _ _ _ _ vals) ->
        copyDataConArgs refs vals
      (Con destRefCon, _) -> case (destRefCon, src) of
        (RecordRef refs, Record vals)
          | fmap (const ()) refs == fmap (const ()) vals -> do
              zipWithM_ copyRec (toList refs) (toList vals)
        (TabRef _, Lam _) -> error "not implemented"
        (BaseTypeRef ptr, _) -> do
          ptr' <- fromScalarAtom $ ImpAtom ptr
          src' <- fromScalarAtom $ ImpAtom src
          storeAnywhere ptr' src'
        (ConRef (SumAsProd _ tag payload), _) -> case src of
          DataCon _ _ _ con x -> do
            copyRec tag $ TagRepVal $ fromIntegral con
            zipWithM_ copyRec (payload !! con) x
          Con (SumAsProd _ tagSrc payloadSrc) -> do
            copyRec tag tagSrc
            unless (all null payload) do -- optimization
              tagSrc' <- fromScalarAtom $ ImpAtom tagSrc
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
        (ConRef destCon, Con srcCon) ->
          zipWithRefConM copyRec destCon srcCon
        _ -> error "unexpected src/dest pair"
      _ -> error "unexpected src/dest pair"

zipWithRefConM :: Monad m => (Atom n -> Atom n -> m ()) -> Con n -> Con n -> m ()
zipWithRefConM f destCon srcCon = case (destCon, srcCon) of
  (ProdCon ds, ProdCon ss) -> zipWithM_ f ds ss
  (IntRangeVal     _ _ iRef, IntRangeVal     _ _ i) -> f iRef i
  (IndexRangeVal _ _ _ iRef, IndexRangeVal _ _ _ i) -> f iRef i
  _ -> error $ "Unexpected ref/val " ++ pprint (destCon, srcCon)

copyDataConArgs :: (ImpBuilder m, Emits n)
                => EmptyAbs (Nest DataConRefBinding) n -> [Atom n] -> m n ()
copyDataConArgs (Abs Empty UnitE) [] = return ()
copyDataConArgs (Abs (Nest (DataConRefBinding b ref) rest) UnitE) (x:xs) = do
  copyAtom (Dest ref) (ImpAtom x)
  rest' <- applySubst (b@>SubstVal x) (EmptyAbs rest)
  copyDataConArgs rest' xs
copyDataConArgs bindings args =
  error $ "Mismatched bindings/args: " ++ pprint (bindings, args)

loadAnywhere :: (ImpBuilder m, Emits n) => IExpr n -> m n (IExpr n)
loadAnywhere ptr = load ptr -- TODO: generalize to GPU backend

storeAnywhere :: (ImpBuilder m, Emits n) => IExpr n -> IExpr n -> m n ()
storeAnywhere ptr val = store ptr val

store :: (ImpBuilder m, Emits n) => IExpr n -> IExpr n -> m n ()
store dest src = emitStatement $ Store dest src

alloc :: (ImpBuilder m, Emits o) => ImpSubst i o -> Type i -> m o (Dest o)
alloc subst ty = makeAllocDest subst Managed ty

indexDest :: (Builder m, Emits n) => Dest n -> Atom n -> m n (Dest n)
indexDest (Dest (Con (TabRef (Lam (LamExpr b body))))) i = do
  body' <- applyAbs (Abs b body) $ SubstVal i
  Dest <$> emitBlock body'
indexDest dest _ = error $ pprint $ fromDest dest

loadDest :: (Builder m, Emits n) => Atom n -> m n (Atom n)
loadDest (DataConRef def params bs) = do
  DataDef _ _ cons <- lookupDataDef def
  let DataConDef conName _ = cons !! 0
  DataCon conName def params 0 <$> loadDataConArgs bs
loadDest (DepPairRef lr rra a) = do
  l <- loadDest lr
  r <- loadDest =<< applyAbs rra (SubstVal l)
  return $ DepPair l r a
loadDest (BoxedRef ptrsSizes absDest) = do
  ptrs <- forM ptrsSizes \(ptrPtr, _) -> unsafePtrLoad ptrPtr
  dest <- applyNaryAbs absDest (map SubstVal ptrs)
  loadDest dest
loadDest (Con dest) = do
 case dest of
   BaseTypeRef ptr -> unsafePtrLoad ptr
   TabRef (Lam (LamExpr b body)) ->
     liftEmitBuilder $ buildLam (getNameHint b) TabArrow (binderType b) Pure \i -> do
       body' <- applySubst (b@>i) body
       result <- emitBlock body'
       loadDest result
   RecordRef xs -> Record <$> traverse loadDest xs
   ConRef con -> Con <$> case con of
     ProdCon ds -> ProdCon <$> traverse loadDest ds
     SumAsProd ty tag xss -> SumAsProd ty <$> loadDest tag <*> mapM (mapM loadDest) xss
     IntRangeVal     l h iRef -> IntRangeVal     l h <$> loadDest iRef
     IndexRangeVal t l h iRef -> IndexRangeVal t l h <$> loadDest iRef
     _        -> error $ "Not a valid dest: " ++ pprint dest
   _ -> error $ "not implemented" ++ pprint dest
loadDest dest = error $ "not implemented" ++ pprint dest

loadDataConArgs :: (Builder m, Emits n) => EmptyAbs (Nest DataConRefBinding) n
                -> m n [Atom n]
loadDataConArgs (Abs bs UnitE) = case bs of
  Empty -> return []
  Nest (DataConRefBinding b ref) rest -> do
    val <- loadDest ref
    rest' <- applySubst (b @> SubstVal val) $ EmptyAbs rest
    (val:) <$> loadDataConArgs rest'

_emitWhen :: (ImpBuilder m, Emits n)
         => IExpr n
         -> (forall l. (Emits l, DExt n l) => m l ())
         -> m n ()
_emitWhen cond doIfTrue =
  emitSwitch cond [False, True] \case False -> return ()
                                      True  -> doIfTrue

-- TODO: Consider targeting LLVM's `switch` instead of chained conditionals.
emitSwitch :: forall m n a.
              (ImpBuilder m, Emits n)
           => IExpr n
           -> [a]
           -> (forall l. (Emits l, DExt n l) => a -> m l ())
           -> m n ()
emitSwitch testIdx args cont = do
  Distinct <- getDistinct
  rec 0 args
  where
    rec :: forall l. (Emits l, DExt n l) => Int -> [a] -> m l ()
    rec _ [] = error "Shouldn't have an empty list of alternatives"
    rec _ [arg] = cont arg
    rec curIdx (arg:rest) = do
      curTag     <- fromScalarAtom $ ImpAtom $ TagRepVal $ fromIntegral curIdx
      cond       <- emitInstr $ IPrimOp $ ScalarBinOp (ICmp Equal) (sink testIdx) curTag
      thisCase   <- buildBlockImp $ cont arg >> return []
      otherCases <- buildBlockImp $ rec (curIdx + 1) rest >> return []
      emitStatement $ ICond cond thisCase otherCases

emitLoop :: (ImpBuilder m, Emits n)
         => NameHint -> Direction -> IExpr n
         -> (forall l. (DExt n l, Emits l) => IExpr l -> m l ())
         -> m n ()
emitLoop hint d n cont = do
  loopBody <- do
    withFreshIBinder hint (getIType n) \b@(IBinder _ ty)  -> do
      let i = IVar (binderName b) ty
      body <- buildBlockImp do
                cont =<< sinkM i
                return []
      return $ Abs b body
  emitStatement $ IFor d n loopBody

restructureScalarOrPairType :: EnvReader m => Type i -> [IExpr o] -> m o (ImpAtom o)
restructureScalarOrPairType ty xs =
  restructureScalarOrPairTypeRec ty xs >>= \case
    (atom, []) -> return atom
    _ -> error "Wrong number of scalars"

restructureScalarOrPairTypeRec
  :: EnvReader m => Type i -> [IExpr o] -> m o (ImpAtom o, [IExpr o])
restructureScalarOrPairTypeRec (PairTy t1 t2) xs = do
  (ImpAtom atom1, rest1) <- restructureScalarOrPairTypeRec t1 xs
  (ImpAtom atom2, rest2) <- restructureScalarOrPairTypeRec t2 rest1
  return (ImpAtom (PairVal atom1 atom2), rest2)
restructureScalarOrPairTypeRec (BaseTy _) (x:xs) = do
  x' <- toScalarAtom x
  return (x', xs)
restructureScalarOrPairTypeRec ty _ = error $ "Not a scalar or pair: " ++ pprint ty

buildBlockImp
  :: ImpBuilder m
  => (forall l. (Emits l, DExt n l) => m l [IExpr l])
  -> m n (ImpBlock n)
buildBlockImp cont = do
  Abs decls (ListE results) <- buildScopedImp $ ListE <$> cont
  return $ ImpBlock decls results

destToAtom :: (ImpBuilder m, Emits n) => Dest n -> m n (ImpAtom n)
destToAtom (Dest dest) = liftBuilderImp $ loadDest =<< sinkM dest

destToRefAtom :: Dest n -> ImpAtom n
destToRefAtom (Dest atom) = ImpAtom atom

refAtomToDest :: ImpAtom n -> Dest n
refAtomToDest (ImpAtom atom) = Dest atom

destGet :: (ImpBuilder m, Emits n) => Dest n -> ImpAtom n -> m n (Dest n)
destGet dest (ImpAtom i) = liftM (Dest . fromImpAtom) $ liftBuilderImp $ do
  Distinct <- getDistinct
  fromDest <$> indexDest (sink dest) (sink i)

destPairUnpack :: Dest n -> (Dest n, Dest n)
destPairUnpack (Dest (Con (ConRef (ProdCon [l, r])))) = (Dest l, Dest r)
destPairUnpack d = error $ "Not a pair destination: " ++ show d

makeAllocDest :: (ImpBuilder m, Emits o) => ImpSubst i o -> AllocType -> Type i -> m o (Dest o)
makeAllocDest subst allocTy ty = fst <$> makeAllocDestWithPtrs subst allocTy ty

backend_TODO_DONT_HARDCODE :: Backend
backend_TODO_DONT_HARDCODE = LLVM

curDev_TODO_DONT_HARDCODE :: Device
curDev_TODO_DONT_HARDCODE = CPU

makeAllocDestWithPtrs :: (ImpBuilder m, Emits o)
                      => ImpSubst i o -> AllocType -> Type i -> m o (Dest o, [IExpr o])
makeAllocDestWithPtrs subst allocTy ty = do
  let backend = backend_TODO_DONT_HARDCODE
  let curDev  = curDev_TODO_DONT_HARDCODE
  AbsPtrs absDest ptrDefs <- makeDest subst (backend, curDev, allocTy) ty
  ptrs <- forM ptrDefs \(DestPtrInfo ptrTy sizeBlock) -> do
    Distinct <- getDistinct
    size <- liftBuilderImp $ emitBlock $ sink sizeBlock
    ptr <- emitAlloc ptrTy =<< fromScalarAtom size
    case ptrTy of
      (Heap _, _) | allocTy == Managed -> extendAllocsToFree ptr
      _ -> return ()
    return ptr
  ptrAtoms <- mapM toScalarAtom ptrs
  dest' <- applyNaryAbs absDest $ map SubstVal (map fromImpAtom ptrAtoms)
  return (dest', ptrs)

allocDest :: (ImpBuilder m, Emits o)
          => ImpSubst i o -> Maybe (Dest o) -> Type i -> m o (Dest o)
allocDest subst maybeDest t = case maybeDest of
  Nothing   -> alloc subst t
  Just dest -> return dest

type AllocInfo = (Backend, Device, AllocType)

data AllocType = Managed | Unmanaged  deriving (Show, Eq)

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
          MLIR      -> error "Shouldn't be compiling to Imp with MLIR backend"
          Interpreter -> error "Shouldn't be compiling to Imp with interpreter backend"

isSmall :: Block n -> Bool
isSmall numel = case numel of
  Block _ Empty (Atom (Con (Lit l))) | getIntLit l <= 256 -> True
  _ -> False

-- TODO: separate these concepts in IFunType?
_deviceFromCallingConvention :: CallingConvention -> Device
_deviceFromCallingConvention cc = case cc of
  CEntryFun         -> CPU
  CInternalFun      -> CPU
  EntryFun _        -> CPU
  FFIFun            -> CPU
  FFIMultiResultFun -> CPU
  MCThreadLaunch    -> CPU
  CUDAKernelLaunch  -> GPU

-- === Determining buffer sizes and offsets using polynomials ===

type IndexStructure = EmptyAbs IdxNest :: E

computeElemCount :: (Emits n, Builder m, MonadIxCache1 m) => IndexStructure n -> m n (Atom n)
computeElemCount (EmptyAbs Empty) =
  -- XXX: this optimization is important because we don't want to emit any decls
  -- in the case that we don't have any indices. The more general path will
  -- still compute `1`, but it might emit decls along the way.
  return $ IdxRepVal 1
computeElemCount idxNest' = do
  let (idxList, idxNest) = indexStructureSplit idxNest'
  listSize <- foldM imul (IdxRepVal 1) =<< forM idxList \ty -> do
    appSimplifiedIxMethod ty simpleIxSize UnitVal
  nestSize <- A.emitCPoly =<< elemCountCPoly idxNest
  imul listSize nestSize

-- Split the index structure into a prefix of non-dependent index types
-- and a trailing nest of indices that can contain inter-dependencies.
indexStructureSplit :: IndexStructure n -> ([Type n], IndexStructure n)
indexStructureSplit (Abs Empty UnitE) = ([], EmptyAbs Empty)
indexStructureSplit s@(Abs (Nest b rest) UnitE) =
  case hoist b (EmptyAbs rest) of
    HoistFailure _     -> ([], s)
    HoistSuccess rest' -> (binderType b:ans1, ans2)
      where (ans1, ans2) = indexStructureSplit rest'

dceApproxBlock :: Block n -> Block n
dceApproxBlock block@(Block _ decls expr) = case hoist decls expr of
  HoistSuccess expr' -> Block NoBlockAnn Empty expr'
  HoistFailure _     -> block

computeOffset :: forall n m. (Emits n, Builder m, MonadIxCache1 m)
              => IndexStructure n -> [AtomName n] -> m n (Atom n)
computeOffset idxNest' idxs = do
  let (idxList , idxNest ) = indexStructureSplit idxNest'
  let (listIdxs, nestIdxs) = splitAt (length idxList) idxs
  nestOffset   <- rec idxNest nestIdxs
  nestSize     <- computeElemCount idxNest
  listOrds     <- forM listIdxs \i -> do
    ty <- getType i
    appSimplifiedIxMethod ty simpleToOrdinal $ Var i
  -- We don't compute the first size (which we don't need!) to avoid emitting unnecessary decls.
  idxListSizes <- case idxList of
    [] -> return []
    _  -> fmap (IdxRepVal (-1):) $ forM (tail idxList) \ty -> do
      appSimplifiedIxMethod ty simpleIxSize UnitVal
  listOffset   <- fst <$> foldM accumStrided (IdxRepVal 0, nestSize) (reverse $ zip idxListSizes listOrds)
  iadd listOffset nestOffset
  where
   accumStrided (total, stride) (size, i) = (,) <$> (iadd total =<< imul i stride) <*> imul stride size
   -- Recursively process the dependent part of the nest
   rec :: IndexStructure n -> [AtomName n] -> m n (Atom n)
   rec (Abs Empty UnitE) [] = return $ IdxRepVal 0
   rec (Abs (Nest b bs) UnitE) (i:is) = do
     rhsElemCounts <- refreshBinders b \(b':>_) s -> do
       rest' <- applySubst s $ EmptyAbs bs
       Abs b' <$> elemCountCPoly rest'
     significantOffset <- A.emitCPoly $ A.sumC i rhsElemCounts
     remainingIdxStructure <- applySubst (b@>i) (EmptyAbs bs)
     otherOffsets <- rec remainingIdxStructure is
     iadd significantOffset otherOffsets
   rec _ _ = error "zip error"

emitSimplified
  :: (Emits n, Builder m)
  => (forall l. (Emits l, DExt n l) => BuilderM l (Atom l))
  -> m n (Atom n)
emitSimplified m = emitBlock . dceApproxBlock =<< buildBlockSimplified m

elemCountCPoly :: (EnvExtender m, EnvReader m, Fallible1 m, MonadIxCache1 m)
               => IndexStructure n -> m n (A.ClampPolynomial n)
elemCountCPoly (Abs bs UnitE) = case bs of
  Empty -> return $ A.liftPoly $ A.emptyMonomial
  Nest b rest -> do
    -- TODO: Use the simplified version here!
    sizeBlock <- liftBuilder $ buildBlock $ emitSimplified $ indexSetSize $ sink $ binderType b
    msize <- A.blockAsCPoly sizeBlock
    case msize of
      Just size -> do
        rhsElemCounts <- refreshBinders b \(b':>_) s -> do
          rest' <- applySubst s $ Abs rest UnitE
          Abs b' <$> elemCountCPoly rest'
        withFreshBinder NoHint IdxRepTy \b' -> do
          let sumPoly = A.sumC (binderName b') (sink rhsElemCounts)
          return $ A.psubst (Abs b' sumPoly) size
      _ -> throw NotImplementedErr $
        "Algebraic simplification failed to model index computations: " ++ pprint sizeBlock

-- === Imp IR builder ===

class (EnvReader m, EnvExtender m, Fallible1 m, MonadIxCache1 m)
       => ImpBuilder (m::MonadKind1) where
  emitMultiReturnInstr :: Emits n => ImpInstr n -> m n [IExpr n]
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

emitCall :: (Emits n, ImpBuilder m)
         => NaryPiType n -> ImpFunName n -> [ImpAtom n] -> m n (ImpAtom n)
emitCall piTy f xs = undefined
-- emitCall piTy f xs = do
--   AbsPtrs absDest ptrDefs <- makeNaryLamDest piTy
--   ptrs <- forM ptrDefs \(DestPtrInfo ptrTy sizeBlock) -> do
--     Distinct <- getDistinct
--     size <- liftBuilderImp $ emitBlock $ sink sizeBlock
--     emitAlloc ptrTy =<< fromScalarAtom size
--   ptrAtoms <- mapM toScalarAtom ptrs
--   dest <- applyNaryAbs absDest $ map SubstVal ptrAtoms
--   resultDest <- storeArgDests dest xs
--   _ <- emitMultiReturnInstr $ ICall f ptrs
--   destToAtom resultDest

buildImpFunction
  :: ImpBuilder m
  => CallingConvention
  -> [(NameHint, IType)]
  -> (forall l. (Emits l, DExt n l) => [AtomName l] -> m l [IExpr l])
  -> m n (ImpFunction n)
buildImpFunction cc argHintsTys body = do
  Abs bs (Abs decls (ListE results)) <-
    buildImpNaryAbs argHintsTys \vs -> ListE <$> body vs
  let resultTys = map getIType results
  let impFun = IFunType cc (map snd argHintsTys) resultTys
  return $ ImpFunction impFun $ Abs bs $ ImpBlock decls results

buildImpNaryAbs
  :: (ImpBuilder m, SinkableE e, HasNamesE e, SubstE Name e, HoistableE e)
  => [(NameHint, IType)]
  -> (forall l. (Emits l, DExt n l) => [AtomName l] -> m l (e l))
  -> m n (Abs (Nest IBinder) (Abs (Nest ImpDecl) e) n)
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
    [x] -> return x
    _ -> error "unexpected numer of return values"

emitStatement :: (ImpBuilder m, Emits n) => ImpInstr n -> m n ()
emitStatement instr = do
  xs <- emitMultiReturnInstr instr
  case xs of
    [] -> return ()
    _ -> error "unexpected numer of return values"

emitAlloc :: (ImpBuilder m, Emits n) => PtrType -> IExpr n -> m n (IExpr n)
emitAlloc (addr, ty) n = emitInstr $ Alloc addr ty n

buildBinOp
  :: (ImpBuilder m, Emits n)
  => (forall l. (Emits l, DExt n l) => Atom l -> Atom l -> BuilderM l (Atom l))
  -> IExpr n -> IExpr n -> m n (IExpr n)
buildBinOp f x y = fromScalarAtom =<< liftBuilderImp do
  Distinct <- getDistinct
  x' <- fromImpAtom <$> toScalarAtom (sink x)
  y' <- fromImpAtom <$> toScalarAtom (sink y)
  f x' y'

iaddI :: (ImpBuilder m, Emits n) => IExpr n -> IExpr n -> m n (IExpr n)
iaddI = buildBinOp iadd

_isubI :: (ImpBuilder m, Emits n) => IExpr n -> IExpr n -> m n (IExpr n)
_isubI = buildBinOp isub

_imulI :: (ImpBuilder m, Emits n) => IExpr n -> IExpr n -> m n (IExpr n)
_imulI = buildBinOp imul

_idivI :: (ImpBuilder m, Emits n) => IExpr n -> IExpr n -> m n (IExpr n)
_idivI = buildBinOp idiv

_iltI :: (ImpBuilder m, Emits n) => IExpr n -> IExpr n -> m n (IExpr n)
_iltI = buildBinOp ilt

_ieqI :: (ImpBuilder m, Emits n) => IExpr n -> IExpr n -> m n (IExpr n)
_ieqI = buildBinOp ieq

_bandI :: (ImpBuilder m, Emits n) => IExpr n -> IExpr n -> m n (IExpr n)
_bandI x y = emitInstr $ IPrimOp $ ScalarBinOp BAnd x y

impOffset :: (ImpBuilder m, Emits n) => IExpr n -> IExpr n -> m n (IExpr n)
impOffset ref off = emitInstr $ IPrimOp $ PtrOffset ref off

cast :: (ImpBuilder m, Emits n) => IExpr n -> BaseType -> m n (IExpr n)
cast x bt = emitInstr $ ICastOp bt x

load :: (ImpBuilder m, Emits n) => IExpr n -> m n (IExpr n)
load x = emitInstr $ IPrimOp $ PtrLoad x

-- === Atom <-> IExpr conversions ===

fromScalarAtom :: HasCallStack => EnvReader m => ImpAtom n -> m n (IExpr n)
fromScalarAtom (ImpAtom atom) = case atom of
  Var v -> do
    ~(BaseTy b) <- getType $ Var v
    return $ IVar v b
  Con (Lit x) -> return $ ILit x
  _ -> error $ "Expected scalar, got: " ++ pprint atom

toScalarAtom :: EnvReader m => IExpr n -> m n (ImpAtom n)
toScalarAtom ie = return $ ImpAtom case ie of
  ILit l   -> Con $ Lit l
  IVar v _ -> Var v

getTypeI :: (EnvReaderI m, HasType e) => e i -> m i o (Type i)
getTypeI e = liftEnvReaderI $ getType e

atomToImpAtom :: forall m i o. Imper m => ImpSubst i o -> Atom i -> m i o (ImpAtom o)
atomToImpAtom subst e = ImpAtom <$> fmapNamesM f e
  where
    f :: Color c => Name c i -> AtomSubstVal c o
    f v = case subst ! v of
            Rename v'  -> Rename v'
            SubstVal x -> SubstVal (fromImpAtom x)

impAtomType :: EnvReader m => ImpAtom n -> m n (Type n)
impAtomType (ImpAtom x) = getType x

-- === Type classes ===

-- TODO: we shouldn't need the rank-2 type here because ImpBuilder and Builder
-- are part of the same conspiracy.
liftBuilderImp :: (Emits n, ImpBuilder m)
               => (forall l. (Emits l, DExt n l) => BuilderM l (Atom l))
               -> m n (ImpAtom n)
liftBuilderImp cont = do
  ab <- liftBuilder $ buildScoped cont
  Distinct <- getDistinct
  env <- unsafeGetEnv
  runEnvReaderIT env $ translateDeclNest idSubst ab \subst result' ->
    atomToImpAtom subst result'

-- TODO: should we merge this with `liftBuilderImp`? Not much harm in
-- simplifying even if it's not needed.
liftBuilderImpSimplify
  :: (Emits n, ImpBuilder m)
  => (forall l. (Emits l, DExt n l) => BuilderM l (Atom l))
  -> m n (ImpAtom n)
liftBuilderImpSimplify cont = do
  block <- dceApproxBlock <$> liftSimplifyM do
    block <- liftBuilder $ buildBlock cont
    buildBlock $ simplifyBlock block
  Distinct <- getDistinct
  env <- unsafeGetEnv
  runEnvReaderIT env $ translateBlock idSubst Nothing block

appSimplifiedIxMethodImp
  :: (Emits n, ImpBuilder m)
  => Type n -> (SimpleIxInstance n -> Abs (Nest Decl) LamExpr n)
  -> ImpAtom n -> m n (ImpAtom n)
appSimplifiedIxMethodImp ty method x = undefined
-- appSimplifiedIxMethodImp ty method x = do
--   -- TODO: Is this safe? Shouldn't I use x' here? It errors then!
--   Abs decls f <- method <$> simplifiedIxInstance ty
--   let decls' = decls
--   case f of
--     LamExpr fx' fb' ->
--       runSubstReaderT idSubst $ translateDeclNest decls' $
--         extendSubst (fx'@>SubstVal x) $ translateBlock Nothing fb'

intToIndexImp :: (ImpBuilder m, Emits o)
              => ImpSubst i o -> Type i -> IExpr o -> m o (ImpAtom o)
intToIndexImp ty i = undefined

indexToIntImp :: (ImpBuilder m, Emits n) => ImpAtom n -> m n (IExpr n)
indexToIntImp idx = do
  ty <- impAtomType idx
  fromScalarAtom =<< appSimplifiedIxMethodImp ty simpleToOrdinal  idx

indexSetSizeImp :: (ImpBuilder m, Emits n)
                => ImpSubst i o -> Type i -> m n (IExpr n)
indexSetSizeImp ty = undefined

-- === type checking imp programs ===

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
  IQueryParallelism _ _ -> return [IIdxRepTy, IIdxRepTy]
  ICall f _ -> do
    IFunType _ _ resultTys <- impFunType <$> lookupImpFun f
    return resultTys

-- TODO: reuse type rules in Type.hs
impOpType :: IPrimOp n -> IType
impOpType pop = case pop of
  ScalarBinOp op x y -> ignoreExcept $ checkBinOp op (getIType x) (getIType y)
  ScalarUnOp  op x   -> ignoreExcept $ checkUnOp  op (getIType x)
  VectorBinOp op x y -> ignoreExcept $ checkBinOp op (getIType x) (getIType y)
  Select  _ x  _     -> getIType x
  VectorPack xs      -> Vector ty  where Scalar ty = getIType $ head xs
  VectorIndex x _    -> Scalar ty  where Vector ty = getIType x
  PtrLoad ref        -> ty  where PtrType (_, ty) = getIType ref
  PtrOffset ref _    -> PtrType (addr, ty)  where PtrType (addr, ty) = getIType ref
  OutputStreamPtr -> hostPtrTy $ hostPtrTy $ Scalar Word8Type
    where hostPtrTy ty = PtrType (Heap CPU, ty)
  _ -> unreachable
  where unreachable = error $ "Not allowed in Imp IR: " ++ show pop

instance CheckableE ImpFunction where
  checkE = substM -- TODO!
