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
  ( toImpFunction, fromLitIExpr
  , abstractPtrsImpFunction
  , impFunType, getIType, makeDestWith
  , loadDestWith, Dest, flattenDest) where

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

-- adds free pointer names as additional args at the beginning of the arg list
-- to avoid baking pointer literals into the function.
abstractPtrsImpFunction :: EnvReader m => ImpFunction n -> m n (ImpFunction n, [IExpr n])
abstractPtrsImpFunction = undefined

fromLitIExpr :: EnvReader m => IExpr n -> m n LitVal
fromLitIExpr (ILit l) = return l
fromLitIExpr (IVar _ _) = error "not a literal"
fromLitIExpr (IPtrVar p) = PtrLit <$> lookupPtr p

toImpFunction :: EnvReader m
              => Backend
              -> NaryLamExpr n
              -> m n (ImpFunction n)
toImpFunction _ lam = liftImpM $ toImpFunction' idSubst lam

toImpFunction' :: Imper m => ImpSubst i o -> NaryLamExpr i -> m i o (ImpFunction o)
toImpFunction' subst lam@(NaryLamExpr bs Pure body) = undefined

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
  Case e alts ty _ -> do
    dest <- allocDest subst maybeDest ty
    ImpAtomSum tag xss <- toImp e
    emitSwitch tag (zip xss alts) $
      \(xs, ab) -> refreshAbsI ab \bs body -> do
         let subst' = subst <>> bs @@> map SubstVal xs
         void $ translateBlock (sink subst') (Just $ sink dest) body
    loadDest dest
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

-- === Dests and ImpAtoms ===

-- TODO: this is currently exactly the same as ImpAtom. Should
-- we de-dup and use a newtype for safety?
data Dest (n::S) =
   DestScalar (IExpr n)     -- pointer to scalar cell
 | DestBuffer (Buffer n)
 | DestProduct [Dest n]
 | DestSum (IExpr n) [[Dest n]]
   deriving (Show)

loadDest :: (ImpBuilder m, Emits n) => Dest n -> m n (ImpAtom n)
loadDest dest = loadDestWith load dest

storeDest :: (ImpBuilder m, Emits n) => Dest n -> ImpAtom n -> m n ()
storeDest dest src = case (dest, src) of
  (DestScalar ptr, ImpAtomScalar val) -> store ptr val
  (DestBuffer d, ImpAtomBuffer s) -> do
    -- TODO: check that the buffer sizes are equal?
    memCopy (bufferPtr d) (bufferPtr s) (bufferNumel d)
  (DestProduct ds, ImpAtomProduct ss)
    | length ds == length ss -> mapM_ (uncurry storeDest) (zip ds ss)
  _ -> error "mismatched source and dest"

-- TODO: there might be ways to make this more efficient than load/store
copyDest :: (ImpBuilder m, Emits n) => Dest n -> Dest n -> m n ()
copyDest dest src = storeDest dest =<< loadDest src

destToRefAtom :: Dest n -> ImpAtom n
destToRefAtom = undefined

refAtomToDest :: ImpAtom n -> Dest n
refAtomToDest = undefined

destPairUnpack :: Dest n -> (Dest n, Dest n)
destPairUnpack (DestProduct [x, y]) = (x, y)
destPairUnpack d = error $ "Not a pair destination: " ++ show d

impAtomUnitVal :: ImpAtom n
impAtomUnitVal = ImpAtomProduct []

fromScalarAtom :: HasCallStack => ImpAtom n -> IExpr n
fromScalarAtom (ImpAtomScalar x) = x
fromScalarAtom atom = error $ "Expected scalar, got: " ++ show atom

toScalarAtom :: IExpr n -> ImpAtom n
toScalarAtom x = ImpAtomScalar x

getTypeI :: (EnvReaderI m, HasType e) => e i -> m i o (Type i)
getTypeI e = liftEnvReaderI $ getType e

substFVar :: ImpSubst i o -> AtomName i -> AtomName o
substFVar subst v = case subst ! v of
  Rename v' -> v'
  SubstVal _ -> error "Shouldn't happen. Functions aren't considered data"

atomToImpAtom :: forall m i o. Imper m => ImpSubst i o -> Atom i -> m i o (ImpAtom o)
atomToImpAtom _ _ = undefined

-- === the tricky bits: dest allocation and indexing ===

type AllocInfo = (Backend, Device, AllocType)
data AllocType = Managed | Unmanaged  deriving (Show, Eq)

allocDest :: (EnvReaderI m, ImpBuilder2 m, Emits o)
          => ImpSubst i o -> Maybe (Dest o) -> Type i -> m i o (Dest o)
allocDest subst maybeDest t = case maybeDest of
  Nothing   -> allocDestUnconditional subst t
  Just dest -> return dest

allocDestUnconditional
  :: (EnvReaderI m, ImpBuilder2 m, Emits o)
  => ImpSubst i o -> Type i -> m i o (Dest o)
allocDestUnconditional subst ty = makeDestWith allocBuffer subst ty

allocBuffer :: (ImpBuilder m, Emits n) => BaseType -> IExpr n -> m n (IExpr n)
allocBuffer ty numel = do
  let allocTy = Managed
  let allocInfo = (LLVM, CPU, allocTy) -- TODO! This is just a placeholder
  let addrSpace = chooseAddrSpace allocInfo numel
  let ptrTy = (addrSpace, ty)
  ptr <- emitAlloc ptrTy numel
  case ptrTy of
    (Heap _, _) | allocTy == Managed -> extendAllocsToFree ptr
    _ -> return ()
  return ptr

indexDest :: (ImpBuilder m, Emits n) => Dest n -> ImpAtom n -> m n (Dest n)
indexDest _ _ = undefined

chooseAddrSpace :: AllocInfo -> IExpr n -> AddressSpace
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

isSmall :: IExpr n -> Bool
isSmall numel = case numel of
  ILit l | getIntLit l <= 256 -> True
  _ -> False

type MaybeDest n = Maybe (Dest n)

makeDestWith
  :: (EnvReaderI m,  EnvReader2 m)
  => (BaseType -> IExpr o -> m i o (IExpr o)) -- allocate ptr (elty -> numel -> ptr)
  -> ImpSubst i o
  -> Type i
  -> m i o (Dest o)
makeDestWith allocPtr subst ty = case ty of
  TabTy (PiBinder b iTy _) bodyTy -> error "not implemented"
  TypeCon _ defName params -> do
    dcs <- liftEnvReaderI do
      def <- lookupDataDef defName
      instantiateDataDef def params
    case dcs of
      [] -> error "Void type not allowed"
      [DataConDef _ dataConBinders] -> error "not implemented"
      _ -> do
        tag <- allocScalarCell ITagRepTy
        contents <- forM dcs \dc -> case nonDepDataConTys dc of
          Nothing -> error
            "Dependent data constructors only allowed for single-constructor types"
          Just tys -> mapM rec tys
        return $ DestSum tag contents
  DepPairTy _ -> error "not implemented"
  StaticRecordTy types -> DestProduct <$> mapM rec (toList types)
  VariantTy (NoExt cases) -> do
    tag <- allocScalarCell ITagRepTy
    DestSum tag <$> map (\x->[x]) <$> mapM rec (toList cases)
  TC con -> case con of
    BaseType b -> do
      ptr <- allocScalarCell b
      return $ DestScalar ptr
    SumType cases -> do
      tag <- allocScalarCell ITagRepTy
      DestSum tag <$> map (\x->[x]) <$> mapM rec cases
    ProdType tys -> DestProduct <$> mapM rec tys
    IntRange _ _     -> rec IdxRepTy
    IndexRange _ _ _ -> rec IdxRepTy
    _ -> error $ "not implemented: " ++ pprint con
  _ -> error $ "not implemented: " ++ pprint ty
  where
    rec = makeDestWith allocPtr subst
    allocScalarCell b = allocPtr b (IIdxRepVal 1)

loadDestWith
  :: EnvReader m
  => (IExpr n -> m n (IExpr n)) -- dereference ptr
  -> Dest n
  -> m n (ImpAtom n)
loadDestWith loadPtr dest = case dest of
  DestScalar ptr -> ImpAtomScalar <$> loadPtr ptr
  DestBuffer buf -> ImpAtomBuffer <$> return buf
  DestProduct ds -> ImpAtomProduct <$> mapM rec ds
  DestSum tag contents ->
    ImpAtomSum <$> loadPtr tag <*> mapM (mapM rec) contents
  where rec = loadDestWith loadPtr

flattenDest :: Dest n -> [IExpr n]
flattenDest dest = case dest of
  DestScalar ptr -> [ptr]
  DestBuffer (Buffer ptr _) -> [ptr]
  DestProduct ds -> foldMap rec ds
  DestSum tag contents -> [tag] ++ foldMap (foldMap rec) contents
  where rec = flattenDest

type IdxNest = Nest Binder

-- dest for the args and the result
-- TODO: de-dup some of the plumbing stuff here with the ordinary makeDest path
type NaryLamDest = Abs (Nest (BinderP AtomNameC Dest)) Dest

-- === Imp builder helpers ===

copyDataConArgs :: (ImpBuilder m, Emits n)
                => EmptyAbs (Nest DataConRefBinding) n -> [Atom n] -> m n ()
copyDataConArgs (Abs Empty UnitE) [] = return ()
-- copyDataConArgs (Abs (Nest (DataConRefBinding b ref) rest) UnitE) (x:xs) = do
--   copyAtom (Dest ref) (ImpAtom x)
--   rest' <- applySubst (b@>SubstVal x) (EmptyAbs rest)
--   copyDataConArgs rest' xs
-- copyDataConArgs bindings args =
--   error $ "Mismatched bindings/args: " ++ pprint (bindings, args)

loadAnywhere :: (ImpBuilder m, Emits n) => IExpr n -> m n (IExpr n)
loadAnywhere ptr = load ptr -- TODO: generalize to GPU backend

storeAnywhere :: (ImpBuilder m, Emits n) => IExpr n -> IExpr n -> m n ()
storeAnywhere ptr val = store ptr val

store :: (ImpBuilder m, Emits n) => IExpr n -> IExpr n -> m n ()
store dest src = emitStatement $ Store dest src

memCopy :: (ImpBuilder m, Emits n) => IExpr n -> IExpr n -> IExpr n -> m n ()
memCopy dest src numel = emitStatement $ MemCopy dest src numel

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
      let curTag = ILit $ TagRepLit $ fromIntegral curIdx
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
  withFreshBinder hint ImpNameBinding \b ->
    cont $ IBinder b ty

emitCall :: (Emits n, ImpBuilder m)
         => NaryPiType n -> ImpFunName n -> [ImpAtom n] -> m n (ImpAtom n)
emitCall piTy f xs = undefined

buildImpFunction
  :: ImpBuilder m
  => [(NameHint, IType)]
  -> (forall l. (Emits l, DExt n l) => [ImpName l] -> m l [IExpr l])
  -> m n (ImpFunction n)
buildImpFunction argHintsTys body = do
  Abs bs (Abs decls (ListE results)) <-
    buildImpNaryAbs argHintsTys \vs -> ListE <$> body vs
  let resultTys = map getIType results
  let impFun = IFunType (map snd argHintsTys) resultTys
  return $ ImpFunction impFun $ Abs bs $ ImpBlock decls results

buildImpNaryAbs
  :: (ImpBuilder m, SinkableE e, HasNamesE e, SubstE Name e, HoistableE e)
  => [(NameHint, IType)]
  -> (forall l. (Emits l, DExt n l) => [ImpName l] -> m l (e l))
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
buildBinOp _ _ _ = undefined
-- buildBinOp f x y = fromScalarAtom <$> liftBuilderImp do
--   Distinct <- getDistinct
--   x' <- fromImpAtom <$> toScalarAtom (sink x)
--   y' <- fromImpAtom <$> toScalarAtom (sink y)
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

indexToIntImp :: (ImpBuilder m, Emits n) => ImpSubst i o -> Atom i -> m n (IExpr n)
indexToIntImp _ idx = undefined

indexSetSizeImp :: (ImpBuilder m, Emits n)
                => ImpSubst i o -> Type i -> m n (IExpr n)
indexSetSizeImp ty = undefined

-- === type checking imp programs ===

fromScalarType :: Type n -> IType
fromScalarType (BaseTy ty) = ty
fromScalarType ty = error $ "not a scalar type: " ++ pprint ty

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

-- === instances ===

instance GenericE Dest where
  type RepE Dest = UnitE

instance SinkableE Dest
instance HoistableE  Dest
instance SubstE Name Dest
instance SubstE AtomSubstVal Dest
