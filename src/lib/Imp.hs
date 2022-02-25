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

type AtomRecon = Abs (Nest (NameBinder ImpNameC)) Atom

type PtrBinder = IBinder

-- TODO: make it purely a function of the type and avoid the AtomRecon
toImpFunction :: EnvReader m
              => Backend -> CallingConvention
              -> Abs (Nest PtrBinder) Block n
              -> m n (ImpFunctionWithRecon n)
toImpFunction _ cc absBlock = undefined
-- toImpFunction _ cc absBlock = liftImpM $
--   translateTopLevel cc Nothing absBlock

toImpStandaloneFunction :: EnvReader m => NaryLamExpr n -> m n (ImpFunction n)
toImpStandaloneFunction lam =
  liftImpM $ toImpStandaloneFunction' idSubst lam

toImpStandaloneFunction' :: Imper m => ImpSubst i o -> NaryLamExpr i -> m i o (ImpFunction o)
toImpStandaloneFunction' subst lam@(NaryLamExpr bs Pure body) = undefined
-- toImpStandaloneFunction' lam@(NaryLamExpr bs Pure body) = do
--   ty <- naryLamExprType lam
--   AbsPtrs (Abs ptrBinders argResultDest) ptrsInfo <- makeNaryLamDest ty
--   let ptrHintTys = [("ptr"::NameHint, PtrType baseTy) | DestPtrInfo baseTy _ <- ptrsInfo]
--   dropSubst $ buildImpFunction CInternalFun ptrHintTys \vs -> do
--     argResultDest' <- applySubst (ptrBinders@@>vs) argResultDest
--     (args, resultDest) <- loadArgDests argResultDest'
--     extendSubst (bs @@> map SubstVal args) do
--       void $ translateBlock (Just $ sink resultDest) body
--       return []
-- toImpStandaloneFunction' (NaryLamExpr _ _ _) = error "effectful functions not implemented"

loadArgDests :: (Emits n, ImpBuilder m) => NaryLamDest n -> m n ([Atom n], Dest n)
loadArgDests = undefined
-- loadArgDests (Abs Empty resultDest) = return ([], resultDest)
-- loadArgDests (Abs (Nest (b:>argDest) bs) resultDest) = do
--   arg <- destToAtom argDest
--   restDest <- applySubst (b@>SubstVal arg) (Abs bs resultDest)
--   (args, resultDest') <- loadArgDests restDest
--   return (arg:args, resultDest')

storeArgDests :: (Emits n, ImpBuilder m) => NaryLamDest n -> [Atom n] -> m n (Dest n)
storeArgDests (Abs Empty resultDest) [] = return resultDest
-- storeArgDests (Abs (Nest (b:>argDest) bs) resultDest) (x:xs) = do
--   storeDest argDest x
--   restDest <- applySubst (b@>SubstVal x) (Abs bs resultDest)
--   storeArgDests restDest xs
-- storeArgDests _ _ = error "dest/args mismatch"

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
     makeImpBinders :: Nest (NameBinder ImpNameC) n l -> [IType] -> Nest IBinder n l
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
                  -> MaybeDest o
                  -> Abs (Nest PtrBinder) Block i
                  -> m i o (ImpFunctionWithRecon o)
translateTopLevel _ maybeDest (Abs bs body) = undefined
-- translateTopLevel _ maybeDest (Abs bs body) = do
--   let argTys = nestToList (\b -> (getNameHint b, iBinderType b)) bs
--   ab  <- buildImpNaryAbs argTys \vs ->
--     extendSubst (bs @@> map Rename vs) do
--       outDest <- case maybeDest of
--         Nothing   -> makeAllocDest Unmanaged =<< getType =<< substM body
--         Just dest -> sinkM dest
--       void $ translateBlock (Just outDest) body
--       destToAtom outDest
--   refreshAbs ab \bs' ab' -> refreshAbs ab' \decls resultAtom -> do
--     (results, recon) <- buildRecon (PairB bs' decls) resultAtom
--     let funImpl = Abs bs' $ ImpBlock decls results
--     let funTy   = IFunType (nestToList iBinderType bs') (map getIType results)
--     return $ ImpFunctionWithRecon (ImpFunction funTy funImpl) recon

buildRecon :: (HoistableB b, EnvReader m)
           => b n l
           -> Atom l
           -> m l ([IExpr l], AtomRecon n)
buildRecon b x = undefined
-- buildRecon b x = do
--   let (vs, recon) = captureClosure b x
--   xs <- forM vs \v -> do
--     ~(BaseTy ty) <- getType $ Var v
--     return $ IVar v ty
--   return (xs, recon)

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
  App f xs -> do
    xs' <- mapM toImp xs
    getTypeI f >>= \case
      TabTy _ _ -> error "not implemented"
      _ -> case f of
        Var v -> do
          let v' = substFVar subst v
          lookupAtomName v' >>= \case
            FFIFunBound _ v'' -> do
              resultTy <- getTypeI expr
              let scalarArgs = toList $ fmap fromScalarAtom xs'
              results <- emitMultiReturnInstr $ ICall v'' scalarArgs
              restructureScalarOrPairType resultTy results
            SimpLamBound piTy _ -> do
              if length (toList xs) /= numNaryPiArgs piTy
                then notASimpExpr
                else do
                  Just fImp <- queryImpCache v'
                  result <- emitCall piTy fImp $ toList xs'
                  returnVal result
            _ -> notASimpExpr
        _ -> notASimpExpr
  Atom x -> toImp x >>= returnVal
  Op op -> toImpOp subst maybeDest op
  -- Case e alts ty _ -> do
  --   dest <- allocDest subst maybeDest ty
  --   ImpAtomSum tag xss <- toImp e
  --   emitSwitch tag (zip xss alts) $
  --     \(xs, ab) -> refreshAbsI ab \bs body -> do
  --        let subst' = subst <>> bs @@> map SubstVal xs
  --        void $ translateBlock (sink subst') (Just $ sink dest) body
  --   loadDest dest
  where
    toImp atom = atomToImpAtom subst atom

    notASimpExpr = error $ "not a simplified expression: " ++ pprint expr

    returnVal:: ImpAtom o -> m i o (ImpAtom o)
    returnVal atom = case maybeDest of
      Nothing   -> return atom
      Just dest -> storeDest dest atom >> return atom

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
        ithDest <- indexDest dest =<< intToIndexImp subst ixTy (IIdxRepVal i)
        storeDest ithDest row'
      loadDest dest
    PrimEffect refDest m -> do
      refDest' <- refAtomToDest <$> toImp refDest
      case m of
        MAsk -> returnVal =<< loadDest refDest'
        -- MExtend (BaseMonoid _ combine) x -> do
        --   xTy <- getTypeI x
        --   refVal <- loadDest refDest'
        --   result <- liftBuilderImpSimplify $
        --               liftMonoidCombine (sink xTy) (sink combine) (sink refVal) (sink x)
        --   storeDest refDest' result
        --   returnVal UnitVal
        MPut x -> do
          x' <- toImp x
          storeDest refDest' x' >> returnVal impAtomUnitVal
        MGet -> do
          dest <- allocDest subst maybeDest resultTy
          copyDest dest refDest'
          loadDest dest
    UnsafeFromOrdinal n i -> do
      i' <- toIExpr i
      returnVal =<< intToIndexImp subst n i'
    IdxSetSize n -> returnIExpr =<< indexSetSizeImp subst n
    ToOrdinal idx -> case idx of
      Con (IntRangeVal   _ _   i) -> returnVal =<< toImp i
      Con (IndexRangeVal _ _ _ i) -> returnVal =<< toImp i
      _ -> returnIExpr =<< indexToIntImp subst idx
    Inject e -> case e of
      Con (IndexRangeVal t low _ restrictIdx) -> do
        offset <- case low of
          InclusiveLim a -> indexToIntImp subst a
          ExclusiveLim a -> indexToIntImp subst a >>= iaddI (IIdxRepVal 1)
          Unlimited      -> return $ IIdxRepVal 0
        restrictIdx' <- toIExpr restrictIdx
        returnVal =<< intToIndexImp subst t =<< iaddI restrictIdx' offset
      Con (ParIndexCon (TC (ParIndexRange realIdxTy _ _)) i) -> do
        i' <- toIExpr i
        returnVal =<< intToIndexImp subst realIdxTy i'
      _ -> error $ "Unsupported argument to inject: " ++ pprint e
    IndexRef ref i -> do
      ref' <- refAtomToDest <$> toImp ref
      i' <- toImp i
      newRef <- destToRefAtom <$> indexDest ref' i'
      returnVal newRef
    ProjRef i ~(Con (ConRef (ProdCon refs))) -> returnVal =<< toImp (refs !! i)
    IOAlloc ty n -> returnIExpr =<< emitAlloc (Heap CPU, ty) =<< toIExpr n
    IOFree ptr -> do
      ptr' <- toIExpr ptr
      emitStatement $ Free ptr'
      return $ impAtomUnitVal
    PtrOffset arr (IdxRepVal 0) -> returnVal =<< toImp arr
    PtrOffset arr off -> do
      arr' <- toIExpr arr
      off' <- toIExpr off
      buf <- impOffset arr' off'
      returnIExpr buf
    PtrLoad ptr -> do
      ptr' <-toIExpr ptr
      val <- loadAnywhere ptr'
      returnIExpr val
    PtrStore ptr x -> do
      ptr' <- toIExpr ptr
      x'   <- toIExpr x
      store ptr' x'
      return $ impAtomUnitVal
    SliceOffset ~(Con (IndexSliceVal n _ tileOffset)) idx -> do
      i' <- indexToIntImp subst idx
      tileOffset' <- toIExpr tileOffset
      i <- iaddI tileOffset' i'
      returnVal =<< intToIndexImp subst n i
    -- SliceCurry ~(Con (IndexSliceVal _ (PairTy _ v) tileOffset)) idx -> do
    --   vz <- intToIndexImp subst v $ IIdxRepVal 0
    --   extraOffset <- indexToIntImp subst (PairVal idx vz)
    --   tileOffset' <- toIExpr tileOffset
    --   tileOffset'' <- iaddI tileOffset' extraOffset
    --   returnIExpr tileOffset''
    ThrowError _ -> do
      dest <- allocDest subst maybeDest resultTy
      emitStatement IThrowError
      -- XXX: we'd be reading uninitialized data here but it's ok because control never reaches
      -- this point since we just threw an error.
      loadDest dest
    -- TODO: the validity of the case should already have been checked, but
    -- maybe we should do it again here to be sure?
    CastOp _ x -> toImp x
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
    --       emitSwitch p'' [y, x] (\arg -> storeDest (sink dest) (sink arg))
    --       loadDest dest
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
      instr <- IPrimOp <$> forM op \x -> toIExpr x
      returnIExpr =<< emitInstr instr
  where

    toImp :: Atom i -> m i o (ImpAtom o)
    toImp atom = atomToImpAtom subst atom

    toIExpr :: Atom i -> m i o (IExpr o)
    toIExpr atom = fromScalarAtom <$> toImp atom

    returnVal :: ImpAtom o -> m i o (ImpAtom o)
    returnVal atom = case maybeDest of
      Nothing   -> return atom
      Just dest -> storeDest dest atom >> return atom

    returnIExpr :: IExpr o -> m i o (ImpAtom o)
    returnIExpr x = returnVal $ toScalarAtom x

toImpHof :: (Imper m, Emits o)
         => ImpSubst i o -> Maybe (Dest o) -> PrimHof (Atom i) -> m i o (ImpAtom o)
toImpHof subst maybeDest hof = do
  resultTy <- getTypeI $ Hof hof
  case hof of
  --   For (RegularFor d) (Lam lam) -> do
  --     let idxTy = lamArgType lam
  --     refreshLamI lam \b body -> do
  --       case idxTy of
  --         _ -> do
  --           n <- indexSetSizeImp subst idxTy
  --           dest <- allocDest subst maybeDest resultTy
  --           emitLoop (getNameHint b) d n \i -> do
  --             idx <- intToIndexImp (sink subst) idxTy i
  --             ithDest <- destGet (sink dest) idx
  --             let subst' = sink subst <>> b @> SubstVal idx
  --             void $ translateBlock subst' (Just ithDest) body
  --           loadDest dest
  --   While (Lam lam) -> refreshLamI lam \b body -> do
  --     let subst' = subst <>> b @> SubstVal impAtomUnitVal
  --     body' <- buildBlockImp do
  --       ans <- fromScalarAtom <$> translateBlock (sink subst') Nothing body
  --       return [ans]
  --     emitStatement $ IWhile body'
  --     return $ impAtomUnitVal
  --   RunReader r (Lam (BinaryLamExpr h ref body)) -> do
  --     r' <- atomToImpAtom subst r
  --     rDest <- allocDestUnconditional subst =<< getTypeI r
  --     storeDest rDest r'
  --     refreshAbsI (Abs (PairB h ref) body) \(PairB h' ref') body' -> do
  --       let subst' = subst <>> (h'   @> SubstVal (ImpAtom UnitTy)
  --                          <.>  ref' @> SubstVal (destToRefAtom rDest))
  --       translateBlock subst' maybeDest body'
--     RunWriter (BaseMonoid e _) (Lam (BinaryLamExpr h ref body)) -> do
--       let PairTy _ accTy = resultTy
--       (aDest, wDest) <- destPairUnpack <$> allocDest maybeDest resultTy
--       e' <- substM e
--       emptyVal <- liftBuilderImp do
--         PairE accTy' e'' <- sinkM $ PairE accTy e'
--         liftMonoidEmpty accTy' e''
--       storeDest wDest emptyVal
--       void $ extendSubst (h @> SubstVal UnitTy <.> ref @> SubstVal wDest) $
--         translateBlock (Just aDest) body
--       PairVal <$> loadDest aDest <*> loadDest wDest
    -- RunState s (Lam (BinaryLamExpr h ref body)) -> do
    --   s' <- atomToImpAtom subst s
    --   (aDest, sDest) <- destPairUnpack <$> allocDest subst maybeDest resultTy
    --   storeDest sDest s'
    --   refreshAbsI (Abs (PairB h ref) body) \(PairB h' ref') body' -> do
    --     let subst' = subst <>> (h'   @> SubstVal (ImpAtom UnitTy)
    --                        <.>  ref' @> SubstVal (destToRefAtom sDest) )
    --     void $ translateBlock subst' (Just aDest) body'
    --   liftM ImpAtom $ PairVal <$> (fromImpAtom <$> loadDest aDest)
    --                           <*> (fromImpAtom <$> loadDest sDest)
    -- RunIO (Lam lam) -> refreshLamI lam \b body -> do
    --   let subst' = subst <>> b @> SubstVal impAtomUnitVal
    --   translateBlock subst' maybeDest body
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
type PtrBinders = Nest (NameBinder ImpNameC)
data DestEmissions n l where
  DestEmissions
    :: [DestPtrInfo n]   -- pointer types and allocation sizes
    -> PtrBinders n h    -- pointer binders for allocations we require
    ->   Nest Decl h l   -- decls to compute indexing offsets
    -> DestEmissions n l

instance GenericB DestEmissions where
  type RepB DestEmissions =         LiftB (ListE DestPtrInfo)
                            `PairB` Nest ImpNameBinder
                            `PairB` Nest Decl
  -- fromB (DestEmissions ps bs ds) = LiftB (ListE ps) `PairB` bs `PairB` ds
  -- toB   (LiftB (ListE ps) `PairB` bs `PairB` ds) = DestEmissions ps bs ds

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

introduceNewPtr :: Mut n => NameHint -> PtrType -> Block n -> DestM n (ImpName n)
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
  extendOutMap bindings (DestEmissions ptrInfo ptrs decls) = undefined
  -- extendOutMap bindings (DestEmissions ptrInfo ptrs decls) =
  --   withSubscopeDistinct decls $
  --     (bindings `extendOutMap` ptrBindersToEnvFrag ptrInfo ptrs)
  --               `extendOutMap` decls
  --  where
  --    ptrBindersToEnvFrag :: Distinct l => [DestPtrInfo n] -> Nest AtomNameBinder n l -> EnvFrag n l
  --    ptrBindersToEnvFrag [] Empty = emptyOutFrag
  --    ptrBindersToEnvFrag (DestPtrInfo ty _ : rest) (Nest b restBs) =
  --      withSubscopeDistinct restBs do
  --        let frag1 = toEnvFrag $ b :> PtrTy ty
  --        let frag2 = withExtEvidence (toExtEvidence b) $
  --                       ptrBindersToEnvFrag (map sink rest) restBs
  --        frag1 `catEnvFrags` frag2
  --    ptrBindersToEnvFrag _ _ = error "mismatched indices"


instance GenericE DestPtrInfo where
  type RepE DestPtrInfo = PairE (LiftE PtrType) Block
  fromE (DestPtrInfo ty n) = PairE (LiftE ty) n
  toE   (PairE (LiftE ty) n) = DestPtrInfo ty n

instance SinkableE DestPtrInfo
instance HoistableE  DestPtrInfo
instance SubstE Name DestPtrInfo
instance SubstE AtomSubstVal DestPtrInfo

-- === Destination builder ===

type Dest = ImpAtom  -- has type `Ref a` for some a
type MaybeDest n = Maybe (Dest n)

data AbsPtrs e n = AbsPtrs (Abs PtrBinders e n) [DestPtrInfo n]

instance GenericE (AbsPtrs e) where
  type RepE (AbsPtrs e) = PairE (NaryAbs ImpNameC e) (ListE DestPtrInfo)
  fromE (AbsPtrs ab ptrInfo) = PairE ab (ListE ptrInfo)
  toE   (PairE ab (ListE ptrInfo)) = AbsPtrs ab ptrInfo

instance SinkableE e => SinkableE (AbsPtrs e)
instance HoistableE e => HoistableE (AbsPtrs e)
instance SubstE Name e => SubstE Name (AbsPtrs e)
instance SubstE AtomSubstVal e => SubstE AtomSubstVal (AbsPtrs e)

-- builds a dest and a list of pointer binders along with their required allocation sizes
makeDest :: (ImpBuilder m, EnvReader m)
         => AllocInfo -> Type n -> m n (AbsPtrs Dest n)
makeDest allocInfo ty = do
   cache <- get
   (result, cache') <- liftDestM allocInfo cache $
                         buildLocalDest $ makeSingleDest [] $ sink ty
   put cache'
   return result

makeSingleDest :: Mut n => [AtomName n] -> Type n -> DestM n (Dest n)
makeSingleDest depVars ty = undefined

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
type NaryLamDest = Abs (Nest (BinderP ImpNameC Dest)) Dest

makeNaryLamDest :: (ImpBuilder m, EnvReader m)
                => NaryPiType n -> m n (AbsPtrs NaryLamDest n)
makeNaryLamDest piTy = do
  cache <- get
  let allocInfo = (LLVM, CPU, Unmanaged) -- TODO! This is just a placeholder
  (result, cache') <- liftDestM allocInfo cache $ buildLocalDest do
    Abs decls dest <- buildDeclsDest $
                        makeNaryLamDestRec (Abs Empty UnitE, []) [] (sink piTy)
    case decls of
      Empty -> return dest
      _ -> error "shouldn't have decls if we have empty indices"
  put cache'
  return result

makeNaryLamDestRec :: forall n. Emits n => DestIdxs n -> DepVars n
                   -> NaryPiType n -> DestM n (NaryLamDest n)
makeNaryLamDestRec idxs depVars (NaryPiType (NonEmptyNest b bs) Pure resultTy) = undefined

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

storeDest :: (ImpBuilder m, Emits n) => Dest n -> ImpAtom n -> m n ()
storeDest = undefined

loadAnywhere :: (ImpBuilder m, Emits n) => IExpr n -> m n (IExpr n)
loadAnywhere ptr = load ptr -- TODO: generalize to GPU backend

storeAnywhere :: (ImpBuilder m, Emits n) => IExpr n -> IExpr n -> m n ()
storeAnywhere ptr val = store ptr val

store :: (ImpBuilder m, Emits n) => IExpr n -> IExpr n -> m n ()
store dest src = emitStatement $ Store dest src

alloc :: (ImpBuilder m, Emits n) => Type n -> m n (Dest n)
alloc ty = makeAllocDest Managed ty

indexDest :: (ImpBuilder m, Emits n) => Dest n -> ImpAtom n -> m n (Dest n)
indexDest _ _ = undefined

loadDest :: (ImpBuilder m, Emits n) => Dest n -> m n (ImpAtom n)
loadDest dest = undefined -- loadDestWith load dest

-- TODO: Consider targeting LLVM's `switch` instead of chained conditionals.
emitSwitch :: forall m n a.
              (ImpBuilder m, Emits n)
           => IExpr n
           -> [a]
           -> (forall l. (Emits l, DExt n l) => a -> m l ())
           -> m n ()
emitSwitch testIdx args cont = undefined
-- emitSwitch testIdx args cont = do
--   Distinct <- getDistinct
--   rec 0 args
--   where
--     rec :: forall l. (Emits l, DExt n l) => Int -> [a] -> m l ()
--     rec _ [] = error "Shouldn't have an empty list of alternatives"
--     rec _ [arg] = cont arg
--     rec curIdx (arg:rest) = do
--       curTag     <- fromScalarAtom $ TagRepVal $ fromIntegral curIdx
--       cond       <- emitInstr $ IPrimOp $ ScalarBinOp (ICmp Equal) (sink testIdx) curTag
--       thisCase   <- buildBlockImp $ cont arg >> return []
--       otherCases <- buildBlockImp $ rec (curIdx + 1) rest >> return []
--       emitStatement $ ICond cond thisCase otherCases

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
  (atom1, rest1) <- restructureScalarOrPairTypeRec t1 xs
  (atom2, rest2) <- restructureScalarOrPairTypeRec t2 rest1
  return (ImpAtomProduct [atom1, atom2], rest2)
restructureScalarOrPairTypeRec (BaseTy _) (x:xs) = do
  return (toScalarAtom x, xs)
restructureScalarOrPairTypeRec ty _ = error $ "Not a scalar or pair: " ++ pprint ty

buildBlockImp
  :: ImpBuilder m
  => (forall l. (Emits l, DExt n l) => m l [IExpr l])
  -> m n (ImpBlock n)
buildBlockImp cont = do
  Abs decls (ListE results) <- buildScopedImp $ ListE <$> cont
  return $ ImpBlock decls results

destPairUnpack :: Dest n -> (Dest n, Dest n)
destPairUnpack = undefined
-- destPairUnpack (Con (ConRef (ProdCon [l, r]))) = (l, r)
-- destPairUnpack d = error $ "Not a pair destination: " ++ show d

makeAllocDest :: (ImpBuilder m, Emits n) => AllocType -> Type n -> m n (Dest n)
makeAllocDest allocTy ty = fst <$> makeAllocDestWithPtrs allocTy ty

backend_TODO_DONT_HARDCODE :: Backend
backend_TODO_DONT_HARDCODE = LLVM

curDev_TODO_DONT_HARDCODE :: Device
curDev_TODO_DONT_HARDCODE = CPU

makeAllocDestWithPtrs :: (ImpBuilder m, Emits n)
                      => AllocType -> Type n -> m n (Dest n, [IExpr n])
makeAllocDestWithPtrs allocTy ty = undefined
-- makeAllocDestWithPtrs allocTy ty = do
--   let backend = backend_TODO_DONT_HARDCODE
--   let curDev  = curDev_TODO_DONT_HARDCODE
--   AbsPtrs absDest ptrDefs <- makeDest (backend, curDev, allocTy) ty
--   ptrs <- forM ptrDefs \(DestPtrInfo ptrTy sizeBlock) -> do
--     Distinct <- getDistinct
--     size <- liftBuilderImp $ emitBlock $ sink sizeBlock
--     ptr <- emitAlloc ptrTy =<< fromScalarAtom size
--     case ptrTy of
--       (Heap _, _) | allocTy == Managed -> extendAllocsToFree ptr
--       _ -> return ()
--     return ptr
--   ptrAtoms <- mapM toScalarAtom ptrs
--   dest' <- applyNaryAbs absDest $ map SubstVal ptrAtoms
--   return (dest', ptrs)

allocDest :: (EnvReaderI m, ImpBuilder2 m, Emits o)
          => ImpSubst i o -> Maybe (Dest o) -> Type i -> m i o (Dest o)
allocDest subst maybeDest t = undefined
-- allocDest subst maybeDest t = case maybeDest of
--   Nothing   -> allocDestUnconditional subst t
--   Just dest -> return dest

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
withFreshIBinder hint ty cont = undefined
-- withFreshIBinder hint ty cont = do
--   withFreshBinder hint (MiscBound $ BaseTy ty) \b ->
--     cont $ IBinder b ty

emitCall :: (Emits n, ImpBuilder m)
         => NaryPiType n -> ImpFunName n -> [ImpAtom n] -> m n (ImpAtom n)
emitCall piTy f xs = undefined

buildImpFunction
  :: ImpBuilder m
  => CallingConvention
  -> [(NameHint, IType)]
  -> (forall l. (Emits l, DExt n l) => [AtomName l] -> m l [IExpr l])
  -> m n (ImpFunction n)
buildImpFunction cc argHintsTys body = undefined
-- buildImpFunction cc argHintsTys body = do
--   Abs bs (Abs decls (ListE results)) <-
--     buildImpNaryAbs argHintsTys \vs -> ListE <$> body vs
--   let resultTys = map getIType results
--   let impFun = IFunType cc (map snd argHintsTys) resultTys
--   return $ ImpFunction impFun $ Abs bs $ ImpBlock decls results

buildImpNaryAbs
  :: (ImpBuilder m, SinkableE e, HasNamesE e, SubstE Name e, HoistableE e)
  => [(NameHint, IType)]
  -> (forall l. (Emits l, DExt n l) => [AtomName l] -> m l (e l))
  -> m n (Abs (Nest IBinder) (Abs (Nest ImpDecl) e) n)
buildImpNaryAbs [] cont = undefined
-- buildImpNaryAbs [] cont = do
--   Distinct <- getDistinct
--   Abs Empty <$> buildScopedImp (cont [])
-- buildImpNaryAbs ((hint,ty) : rest) cont = do
--   withFreshIBinder hint ty \b -> do
--     ab <- buildImpNaryAbs rest \vs -> do
--       v <- sinkM $ binderName b
--       cont (v : vs)
--     Abs bs body <- return ab
--     return $ Abs (Nest b bs) body

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

buildBinOp :: (ImpBuilder m, Emits n)
           => (forall l. (Emits l, DExt n l) => Atom l -> Atom l -> BuilderM l (Atom l))
           -> IExpr n -> IExpr n -> m n (IExpr n)
buildBinOp f x y = undefined
-- buildBinOp f x y = fromScalarAtom =<< liftBuilderImp do
--   Distinct <- getDistinct
--   x' <- toScalarAtom $ sink x
--   y' <- toScalarAtom $ sink y
--   f x' y'

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

fromScalarAtom :: HasCallStack => ImpAtom n -> IExpr n
fromScalarAtom (ImpAtomScalar x) = x
fromScalarAtom atom = error $ "Expected scalar, got: " ++ show atom

toScalarAtom :: IExpr n -> ImpAtom n
toScalarAtom x = ImpAtomScalar x

substFVar :: ImpSubst i o -> AtomName i -> AtomName o
substFVar subst v = case subst ! v of
  Rename v' -> v'
  SubstVal _ -> error "Shouldn't happen. Functions aren't considered data"

atomToImpAtom :: forall m i o. Imper m => ImpSubst i o -> Atom i -> m i o (ImpAtom o)
atomToImpAtom _ _ = undefined

getTypeI :: (EnvReaderI m, HasType e) => e i -> m i o (Type i)
getTypeI e = liftEnvReaderI $ getType e

-- TODO: there might be ways to make this more efficient than load/store
copyDest :: (ImpBuilder m, Emits n) => Dest n -> Dest n -> m n ()
copyDest dest src = storeDest dest =<< loadDest src

destToRefAtom :: Dest n -> ImpAtom n
destToRefAtom = undefined

refAtomToDest :: ImpAtom n -> Dest n
refAtomToDest = undefined

impAtomUnitVal :: ImpAtom n
impAtomUnitVal = ImpAtomProduct []

-- === Type classes ===

-- TODO: we shouldn't need the rank-2 type here because ImpBuilder and Builder
-- are part of the same conspiracy.
liftBuilderImp :: (Emits n, ImpBuilder m, SubstE AtomSubstVal e, SinkableE e)
               => (forall l. (Emits l, DExt n l) => BuilderM l (e l))
               -> m n (e n)
liftBuilderImp cont = undefined
  -- Abs decls result <- liftBuilder $ buildScoped cont
  -- runSubstReaderT idSubst $ translateDeclNest decls $ substM result

-- TODO: should we merge this with `liftBuilderImp`? Not much harm in
-- simplifying even if it's not needed.
liftBuilderImpSimplify
  :: (Emits n, ImpBuilder m)
  => (forall l. (Emits l, DExt n l) => BuilderM l (ImpAtom l))
  -> m n (ImpAtom n)
liftBuilderImpSimplify cont = undefined
-- liftBuilderImpSimplify cont = do
--   block <- dceApproxBlock <$> liftSimplifyM do
--     block <- liftBuilder $ buildBlock cont
--     buildBlock $ simplifyBlock block
--   runSubstReaderT idSubst $ translateBlock Nothing block

-- appSimplifiedIxMethodImp
--   :: (Emits n, ImpBuilder m)
--   => Type n -> (SimpleIxInstance n -> Abs (Nest Decl) LamExpr n)
--   -> ImpAtom n -> m n (ImpAtom n)
-- appSimplifiedIxMethodImp ty method x = do
--   -- TODO: Is this safe? Shouldn't I use x' here? It errors then!
--   Abs decls f <- method <$> simplifiedIxInstance ty
--   let decls' = decls
--   case f of
--     LamExpr fx' fb' ->
--       runSubstReaderT idSubst $ translateDeclNest decls' $
--         extendSubst (fx'@>SubstVal x) $ translateBlock Nothing fb'

-- intToIndexImp :: (ImpBuilder m, Emits n) => Type n -> IExpr n -> m n (ImpAtom n)
-- intToIndexImp ty i =
--   appSimplifiedIxMethodImp ty simpleUnsafeFromOrdinal =<< toScalarAtom i

-- indexToIntImp :: (ImpBuilder m, Emits n) => ImpAtom n -> m n (IExpr n)
-- indexToIntImp idx = do
--   ty <- getType idx
--   fromScalarAtom =<< appSimplifiedIxMethodImp ty simpleToOrdinal  idx

-- indexSetSizeImp :: (ImpBuilder m, Emits n) => Type n -> m n (IExpr n)
-- indexSetSizeImp ty = do
--   fromScalarAtom =<< appSimplifiedIxMethodImp ty simpleIxSize impAtomUnitVal

intToIndexImp :: (ImpBuilder m, Emits o)
              => ImpSubst i o -> Type i -> IExpr o -> m o (ImpAtom o)
intToIndexImp ty i = undefined

indexToIntImp :: (ImpBuilder m, Emits n) => ImpSubst i o -> Atom i -> m n (IExpr n)
indexToIntImp _ idx = undefined

indexSetSizeImp :: (ImpBuilder m, Emits n)
                => ImpSubst i o -> Type i -> m n (IExpr n)
indexSetSizeImp ty = undefined

-- === type checking imp programs ===

impFunType :: ImpFunction n -> IFunType
impFunType (ImpFunction ty _) = ty
impFunType (FFIFunction ty _ _) = ty

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
    IFunType _ resultTys <- impFunType <$> lookupImpFun f
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
