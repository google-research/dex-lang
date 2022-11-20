-- Copyright 2021 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE PartialTypeSignatures #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Imp
  ( blockToImpFunction, toImpFunction, ExportCC (..), toImpExportedFunction
  , impFunType, getIType, abstractLinktimeObjects, coreAtomFromRepValList
  , addImpTracing) where

import Prelude hiding ((.), id)
import Data.Functor
import Data.Foldable (toList)
import Data.Maybe (fromJust)
import Control.Category
import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.Writer.Strict
import Control.Monad.State.Strict hiding (State)
import qualified Control.Monad.State.Strict as MTL
import GHC.Exts (inline)

import Err
import MTL1
import Name
import Builder
import Syntax
import CheckType (CheckableE (..))
import Lower (DestBlock)
import LabeledItems
import QueryType
import Util (enumerate, forMFilter, forMZipped, Tree (..), zipTrees)
import Types.Primitives
import Types.Core
import Types.Imp
import Algebra

type SIAtom   = Atom  SimpToImpIR
type SIType   = Type  SimpToImpIR
type SIBlock  = Block SimpToImpIR
type SIExpr   = Expr  SimpToImpIR
type SIDecl   = Decl  SimpToImpIR
type SIRepVal = RepVal SimpToImpIR
type SIDecls  = Decls SimpToImpIR

toImpExportedFunction
  :: EnvReader m => ExportCC -> Abs (Nest (Binder SimpIR)) DestBlock n
  -> (Abs (Nest (Binder SimpIR)) (ListE SBlock) n) -> m n (ImpFunction n)
toImpExportedFunction = undefined

blockToImpFunction :: EnvReader m => Backend -> CallingConvention -> DestBlock n -> m n (ImpFunction n)
blockToImpFunction _ cc absBlock = liftImpM $ translateTopLevel cc absBlock

toImpFunction
  :: EnvReader m
  => CallingConvention -> NaryLamExpr SimpIR n -> m n (ImpFunction n)
toImpFunction _cc lam' = do
  lam@(NaryLamExpr bs effs body) <- return $ injectIRE lam'
  case effs of
    Pure -> return ()
    OneEffect IOEffect -> return ()
    _ -> error "effectful functions not implemented"
  ty <- unpackNaryPiType <$> naryLamExprType lam
  impArgTys <- getNaryLamImpArgTypes ty
  liftImpM $ buildImpFunction CInternalFun (zip (repeat noHint) impArgTys) \vs -> do
    (argAtoms, resultDest) <- interpretImpArgs (sink ty) vs
    extendSubst (bs @@> (SubstVal <$> argAtoms)) do
      void $ translateBlock (Just $ sink resultDest) body
      return []
  where
   getNaryLamImpArgTypes :: EnvReader m => NaryPiType' SimpToImpIR n -> m n [BaseType]
   getNaryLamImpArgTypes t = liftEnvReaderM $ go t where
     go :: NaryPiType' SimpToImpIR n -> EnvReaderM n [BaseType]
     go (Abs bs resultTy) = case bs of
       Nest piB rest -> do
         ts <- getRepBaseTypes $ binderType piB
         refreshAbs (Abs piB (Abs rest resultTy)) \_ restAb -> do
           tsRest <- go restAb
           return $ ts ++ tsRest
       Empty -> getDestBaseTypes resultTy

   interpretImpArgs :: EnvReader m => NaryPiType' SimpToImpIR n -> [IExpr n] -> m n ([SIAtom n], Dest n)
   interpretImpArgs t xsAll = liftEnvReaderM $ runSubstReaderT idSubst $ go t xsAll where
      go :: NaryPiType' SimpToImpIR i -> [IExpr o]
         -> SubstReaderT (AtomSubstVal SimpToImpIR) EnvReaderM i o ([SIAtom o], Dest o)
      go (Abs bs resultTy) xs = case bs of
        Nest (PiBinder b argTy _) rest -> do
          argTy' <- substM argTy
          (argTree, xsRest) <- listToTree argTy' xs
          let arg = RepValAtom $ toDRepVal $ RepVal argTy' argTree
          (args, dest) <- extendSubst (b @> SubstVal arg) $ go (Abs rest resultTy) xsRest
          return (arg:args, dest)
        Empty -> do
          resultTy' <- substM resultTy
          (destTree, xsRest) <- listToTree resultTy' xs
          case xsRest of
            [] -> return ()
            _  -> error "Shouldn't have any Imp arguments left"
          return ([], Dest resultTy' destTree)

-- This just drops the "nonempty" stuff, which makes the recursion easier. TODO: we
-- should drop the nonempty stuff everywhere. I don't think it helps us.
type NaryPiType' r = Abs (Nest (PiBinder r)) (Type r)
unpackNaryPiType :: NaryPiType r n -> NaryPiType' r n
unpackNaryPiType (NaryPiType bs _ resultTy) = Abs (nonEmptyToNest bs) resultTy

-- | Calling convention for exported function.
data ExportCC = FlatExportCC
              | XLAExportCC

data UnpackCC = FlatUnpackCC Int
              | XLAUnpackCC [FormalArg] [FormalArg]

type FormalArg = (NameHint, IType)
type ActualArg n = (ImpName n, IType)

_ccPrepareFormals :: ExportCC -> Nest (Binder SimpIR) n l -> [FormalArg] -> ([FormalArg], UnpackCC)
_ccPrepareFormals cc args destFormals = case cc of
  FlatExportCC -> do
    (argFormals ++ destFormals, FlatUnpackCC (length argFormals))
  XLAExportCC -> ( [(getNameHint @String "out", i8pp), (getNameHint @String "in", i8pp)]
                 , XLAUnpackCC argFormals destFormals )
  where
    argFormals = nestToList ((noHint,) . (\(BaseTy t) -> t) . binderType) args
    i8pp = PtrType (CPU, PtrType (CPU, Scalar Word8Type))

_ccUnpackActuals :: Emits n => UnpackCC -> [(ImpName n, BaseType)] -> SubstImpM i n ([ActualArg n], [ActualArg n])
_ccUnpackActuals cc actual = case cc of
  FlatUnpackCC n -> return $ splitAt n actual
  XLAUnpackCC argFormals destFormals -> case actual of
    [outsPtrName, insPtrName] -> do
      let (outsPtr, insPtr) = (IVar (fst outsPtrName) i8pp, IVar (fst insPtrName) i8pp)
      let loadPtr base i pointeeTy =
            flip cast (PtrType (CPU, pointeeTy)) =<< load =<< impOffset base (IIdxRepVal $ fromIntegral i)
      args <- forM (enumerate argFormals) \(i, (_, argTy)) ->
        toArg <$> case argTy of
          PtrType (_, pointeeTy) -> loadPtr insPtr i pointeeTy
          _ -> load =<< loadPtr insPtr i argTy
      -- outsPtr points to the buffer when there's one output, not to the pointer array.
      ptrs <- case destFormals of
        [(_, destTy)] -> (:[]) . toArg <$> cast outsPtr destTy
        _ ->
          forM (enumerate destFormals) \(i, (_, destTy)) ->
            toArg <$> case destTy of
              PtrType (_, pointeeTy) -> loadPtr outsPtr i pointeeTy
              _ -> error "Destination arguments should all have pointer types"
      return (args, ptrs)
    _ -> error "Expected two arguments for the XLA calling convention"
  where
    toArg = \case
      IVar v ty -> (v, ty)
      _ -> error "Expected a variable"
    i8pp = PtrType (CPU, PtrType (CPU, Scalar Word8Type))

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

type SubstImpM = SubstReaderT (AtomSubstVal SimpToImpIR) ImpM :: S -> S -> * -> *

instance ExtOutMap Env ImpBuilderEmissions where
  extendOutMap bindings emissions =
    bindings `extendOutMap` toEnvFrag emissions

class (ImpBuilder2 m, SubstReader (AtomSubstVal SimpToImpIR) m, EnvReader2 m, EnvExtender2 m)
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
     makeImpBinders :: Nest (NameBinder ImpNameC) n l -> [IType] -> Nest IBinder n l
     makeImpBinders Empty [] = Empty
     makeImpBinders (Nest b bs) (ty:tys) = Nest (IBinder b ty) $ makeImpBinders bs tys
     makeImpBinders _ _ = error "zip error"

  emitDeclsImp (Abs decls result) =
    ImpM $ lift11 $ extendInplaceT (Abs (toRNest decls) result)
  {-# INLINE emitDeclsImp #-}

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

instance ImpBuilder m => ImpBuilder (SubstReaderT (AtomSubstVal SimpToImpIR) m i) where
  emitMultiReturnInstr instr = SubstReaderT $ lift $ emitMultiReturnInstr instr
  {-# INLINE emitMultiReturnInstr #-}
  emitDeclsImp ab = SubstReaderT $ lift $ emitDeclsImp ab
  {-# INLINE emitDeclsImp #-}
  buildScopedImp cont = SubstReaderT $ ReaderT \env ->
    buildScopedImp $ runSubstReaderT (sink env) $ cont
  {-# INLINE buildScopedImp #-}
  extendAllocsToFree ptr = SubstReaderT $ lift $ extendAllocsToFree ptr
  {-# INLINE extendAllocsToFree #-}

instance ImpBuilder m => Imper (SubstReaderT (AtomSubstVal SimpToImpIR) m)

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
translateTopLevel :: CallingConvention -> DestBlock i -> SubstImpM i o (ImpFunction o)
translateTopLevel cc (Abs (destb:>destTy') body') = do
  destTy <- return $ injectIRE destTy'
  body   <- return $ injectIRE body'
  Abs decls (ListE results)  <- buildScopedImp do
    dest <- case destTy of
      RawRefTy ansTy -> allocDestUnmanaged =<< substM ansTy
      _ -> error "Expected a reference type for body destination"
    extendSubst (destb @> SubstVal (destToAtom dest)) $ void $ translateBlock Nothing body
    resultAtom <- loadAtom dest
    ListE <$> repValToList <$> atomToRepVal resultAtom
  let funImpl = Abs Empty $ ImpBlock decls results
  let funTy   = IFunType cc [] (map getIType results)
  return $ ImpFunction funTy funImpl

translateBlock :: forall i o. Emits o
               => MaybeDest o -> SIBlock i -> SubstImpM i o (SIAtom o)
translateBlock dest (Block _ decls result) = translateDeclNest decls $ translateExpr dest $ Atom result

translateDeclNestSubst
  :: Emits o => Subst (AtomSubstVal SimpToImpIR) l o
  -> Nest SIDecl l i' -> SubstImpM i o (Subst (AtomSubstVal SimpToImpIR) i' o)
translateDeclNestSubst !s = \case
  Empty -> return s
  Nest (Let b (DeclBinding _ _ expr)) rest -> do
    x <- withSubst s $ translateExpr Nothing expr
    translateDeclNestSubst (s <>> (b@>SubstVal x)) rest

translateDeclNest :: Emits o => Nest SIDecl i i' -> SubstImpM i' o a -> SubstImpM i o a
translateDeclNest decls cont = do
  s  <- getSubst
  s' <- translateDeclNestSubst s decls
  withSubst s' cont
{-# INLINE translateDeclNest #-}

translateExpr :: Emits o => MaybeDest o -> SIExpr i -> SubstImpM i o (SIAtom o)
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
        TopFunBound piTy (SpecializedTopFun specializationSpec) -> do
          if length (toList xs') /= numNaryPiArgs piTy
            then notASimpExpr
            else case specializationSpec of
              AppSpecialization _ _ -> do
                Just fImp <- queryImpCache v
                emitCall maybeDest piTy fImp $ toList xs
        _ -> notASimpExpr
      _ -> notASimpExpr
  TabApp f' xs' -> do
    xs <- mapM substM xs'
    f <- atomToRepVal =<< substM f'
    RepValAtom <$> toDRepVal <$> naryIndexRepVal f (toList xs)
  Atom x -> substM x >>= returnVal
  -- Inlining the traversal helps GHC sink the substM below the case inside toImpOp.
  Op op -> (inline traversePrimOp) substM op >>= toImpOp maybeDest
  Case e alts ty _ -> do
    e' <- substM e
    case trySelectBranch e' of
      Just (con, arg) -> do
        Abs b body <- return $ alts !! con
        extendSubst (b @> SubstVal arg) $ translateBlock maybeDest body
      Nothing -> case e' of
        -- This is awful, but it'll mostly disappear once we remove newtypes
        -- earlier so I'm not going to bother fixing it up now.
        Con (Newtype (VariantTy _) (Con (SumAsProd _ tag xss))) -> go tag xss
        Con (Newtype (TypeCon _ _ _) (Con (SumAsProd _ tag xss))) -> go tag xss
        Con (SumAsProd _ tag xss) -> go tag xss
        Con (Newtype (VariantTy _  ) (RepValAtom dRepVal)) -> goDRepVal dRepVal
        Con (Newtype (TypeCon _ _ _) (RepValAtom dRepVal)) -> goDRepVal dRepVal
        RepValAtom dRepVal                                 -> goDRepVal dRepVal
        _ -> error $ "unexpected case scrutinee: " ++ pprint e'
        where
          goDRepVal dRepVal = do
            RepVal sumTy (Branch (tag:xss)) <- forceDRepVal dRepVal
            ts <- caseAltsBinderTys sumTy
            let tag' = RepValAtom $ toDRepVal $ RepVal TagRepTy tag
            let xss' = zipWith (\t x -> RepValAtom $ toDRepVal $ RepVal t x) ts xss
            go tag' xss'
          go tag xss = do
            tag' <- fromScalarAtom tag
            dest <- maybeAllocDest maybeDest =<< substM ty
            emitSwitch tag' (zip xss alts) $
              \(xs, Abs b body) ->
                 void $ extendSubst (b @> SubstVal (sink xs)) $
                   translateBlock (Just $ sink dest) body
            loadAtom dest
  Handle _ _ _ -> error "handlers should be gone by now"
  where
    notASimpExpr = error $ "not a simplified expression: " ++ pprint expr
    returnVal atom = case maybeDest of
      Nothing   -> return atom
      Just dest -> storeAtom dest atom >> return atom

toImpOp :: forall i o .
           Emits o => MaybeDest o -> PrimOp (SIAtom o) -> SubstImpM i o (SIAtom o)
toImpOp maybeDest op = case op of
  TabCon ty rows -> do
    TabPi (TabPiType b _) <- return ty
    let ixTy = binderAnn b
    resultTy <- resultTyM
    dest <- maybeAllocDest maybeDest resultTy
    forM_ (zip [0..] rows) \(i, row) -> do
      ithDest <- indexDest dest =<< unsafeFromOrdinalImp ixTy (IIdxRepVal i)
      storeAtom ithDest row
    loadAtom dest
  PrimEffect refDest' m -> do
    refDest <- atomToDest refDest'
    case m of
      MAsk -> returnVal =<< loadAtom refDest
      MExtend (BaseMonoid _ combine) x -> do
        xTy <- getType x
        refVal <- loadAtom refDest
        result <- liftBuilderImp $
                    liftMonoidCombine (sink xTy) (sink combine) (sink refVal) (sink x)
        storeAtom refDest result
        returnVal UnitVal
      MPut x -> storeAtom refDest x >> returnVal UnitVal
      MGet -> do
        resultTy <- resultTyM
        dest <- maybeAllocDest maybeDest resultTy
        -- It might be more efficient to implement a specialized copy for dests
        -- than to go through a general purpose atom.
        storeAtom dest =<< loadAtom refDest
        loadAtom dest
    where
      liftMonoidCombine :: Emits n => SIType n -> SIAtom n -> SIAtom n -> SIAtom n -> SBuilderM n (SIAtom n)
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
  IndexRef refDestAtom i -> do
    refDest <- atomToDest refDestAtom
    returnVal =<< (destToAtom <$> indexDest refDest i)
  ProjRef i d -> do
    d' <- atomToDest d
    returnVal $ destToAtom $ projectDest i d'
  IOAlloc ty n -> do
    n' <- fromScalarAtom n
    ptr <- emitInstr $ Alloc CPU ty n'
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
    returnVal =<< toScalarAtom =<< load =<< fromScalarAtom arr
  PtrStore ptr x -> do
    ptr' <- fromScalarAtom ptr
    x'   <- fromScalarAtom x
    store ptr' x'
    return UnitVal
  ThrowError _ -> do
    resultTy <- resultTyM
    dest <- maybeAllocDest maybeDest resultTy
    emitStatement IThrowError
    -- XXX: we'd be reading uninitialized data here but it's ok because control never reaches
    -- this point since we just threw an error.
    loadAtom dest
  CastOp destTy x -> do
    sourceTy <- getType x
    case (sourceTy, destTy) of
      (BaseTy _, BaseTy bt) -> do
        x' <- fromScalarAtom x
        returnVal =<< toScalarAtom =<< cast x' bt
      _ -> error $ "Invalid cast: " ++ pprint sourceTy ++ " -> " ++ pprint destTy
  BitcastOp destTy x -> do
    case destTy of
      BaseTy bt -> do
        x' <- fromScalarAtom x
        ans <- emitInstr $ IBitcastOp bt x'
        returnVal =<< toScalarAtom ans
      _ -> error "Invalid bitcast"
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
  SumTag con -> case con of
    Con (SumCon _ tag _) -> returnVal $ TagRepVal $ fromIntegral tag
    Con (SumAsProd _ tag _) -> returnVal tag
    Con (Newtype _ (Con (SumCon _ tag _))) -> returnVal $ TagRepVal $ fromIntegral tag
    Con (Newtype _ (Con (SumAsProd _ tag _))) -> returnVal tag
    RepValAtom dRepVal -> go dRepVal
    Con (Newtype _ (RepValAtom dRepVal)) -> go dRepVal
    _ -> error $ "Not a data constructor: " ++ pprint con
    where go dRepVal = do
            RepVal _ (Branch (tag:_)) <- forceDRepVal dRepVal
            return $ RepValAtom $ toDRepVal $ RepVal TagRepTy tag
  ToEnum ty i -> returnVal =<< case ty of
    TypeCon _ defName _ -> do
      DataDef _ _ cons <- lookupDataDef defName
      return $ Con $ Newtype ty $
        Con $ SumAsProd (cons <&> const UnitTy) i (cons <&> const UnitVal)
    VariantTy (NoExt labeledItems) -> do
      let items = toList labeledItems
      return $ Con $ Newtype ty $
        Con $ SumAsProd (items <&> const UnitTy) i (items <&> const UnitVal)
    SumTy cases ->
      return $ Con $ SumAsProd cases i $ cases <&> const UnitVal
    _ -> error $ "Not an enum: " ++ pprint ty
  SumToVariant c -> do
    resultTy <- resultTyM
    return $ Con $ Newtype resultTy $ c
  AllocDest ty  -> returnVal =<< (destToAtom <$> allocDest ty)
  Place ref val -> do
    refDest <- atomToDest ref
    storeAtom refDest val >> returnVal UnitVal
  Freeze ref -> loadAtom =<< atomToDest ref
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
    refDest <- atomToDest ref
    refi <- destToAtom <$> indexDest refDest i
    refi' <- fromScalarAtom refi
    let PtrType (addrSpace, _) = getIType refi'
    returnVal =<< case vty of
      BaseTy vty'@(Vector _ _) -> do
        resultVal <- cast refi' (PtrType (addrSpace, vty'))
        return $ RepValAtom $ toDRepVal $ RepVal (RawRefTy vty) (Leaf resultVal)
      _ -> error "Expected a vector type"
  _ -> do
    instr <- IPrimOp <$> (inline traversePrimOp) fromScalarAtom op
    emitInstr instr >>= toScalarAtom >>= returnVal
  where
    unsupported = error $ "Unsupported PrimOp encountered in Imp" ++ pprint op
    resultTyM :: SubstImpM i o (SIType o)
    resultTyM = getType $ Op op
    returnVal atom = case maybeDest of
      Nothing   -> return atom
      Just dest -> storeAtom dest atom >> return atom

toImpFor
  :: Emits o => Maybe (Dest o) -> SIType o -> Direction
  -> IxDict SimpToImpIR i -> SIAtom i
  -> SubstImpM i o (SIAtom o)
toImpFor maybeDest resultTy d ixDict (Lam (LamExpr b body)) = do
  ixTy <- ixTyFromDict =<< substM ixDict
  n <- indexSetSizeImp ixTy
  dest <- maybeAllocDest maybeDest resultTy
  emitLoop (getNameHint b) d n \i -> do
    idx <- unsafeFromOrdinalImp (sink ixTy) i
    ithDest <- indexDest (sink dest) idx
    void $ extendSubst (b @> SubstVal idx) $
      translateBlock (Just ithDest) body
  loadAtom dest
toImpFor _ _ _ _ _ = error "expected a lambda as the atom argument"

toImpHof :: Emits o => Maybe (Dest o) -> PrimHof (SIAtom i) -> SubstImpM i o (SIAtom o)
toImpHof maybeDest hof = do
  resultTy <- getTypeSubst (Hof hof)
  case hof of
    For d ixDict lam -> toImpFor maybeDest resultTy d ixDict lam
    While (Lam (LamExpr b body)) -> do
      body' <- buildBlockImp $ extendSubst (b@>SubstVal UnitVal) do
        ans <- fromScalarAtom =<< translateBlock Nothing body
        return [ans]
      emitStatement $ IWhile body'
      return UnitVal
    RunReader r (Lam (BinaryLamExpr h ref body)) -> do
      r' <- substM r
      rDest <- allocDest =<< getType r'
      storeAtom rDest r'
      extendSubst (h @> SubstVal UnitTy <.> ref @> SubstVal (destToAtom rDest)) $
        translateBlock maybeDest body
    RunWriter d (BaseMonoid e _) (Lam (BinaryLamExpr h ref body)) -> do
      let PairTy ansTy accTy = resultTy
      (aDest, wDest) <- case d of
        Nothing -> destPairUnpack <$> maybeAllocDest maybeDest resultTy
        Just d' -> do
          aDest <- maybeAllocDest Nothing ansTy
          wDest <- atomToDest =<< substM d'
          return (aDest, wDest)
      e' <- substM e
      emptyVal <- liftBuilderImp do
        PairE accTy' e'' <- sinkM $ PairE accTy e'
        liftMonoidEmpty accTy' e''
      storeAtom wDest emptyVal
      void $ extendSubst (h @> SubstVal UnitTy <.> ref @> SubstVal (destToAtom wDest)) $
        translateBlock (Just aDest) body
      PairVal <$> loadAtom aDest <*> loadAtom wDest
    RunState d s (Lam (BinaryLamExpr h ref body)) -> do
      let PairTy ansTy _ = resultTy
      (aDest, sDest) <- case d of
        Nothing -> destPairUnpack <$> maybeAllocDest maybeDest resultTy
        Just d' -> do
          aDest <- maybeAllocDest Nothing ansTy
          sDest <- atomToDest =<< substM d'
          return (aDest, sDest)
      storeAtom sDest =<< substM s
      void $ extendSubst (h @> SubstVal UnitTy <.> ref @> SubstVal (destToAtom sDest)) $
        translateBlock (Just aDest) body
      PairVal <$> loadAtom aDest <*> loadAtom sDest
    RunIO (Lam (LamExpr b body)) ->
      extendSubst (b@>SubstVal UnitVal) $
        translateBlock maybeDest body
    RunInit (Lam (LamExpr b body)) ->
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
    RememberDest d (Lam (LamExpr b body)) -> do
      d' <- substM d
      void $ extendSubst (b @> SubstVal d') $ translateBlock Nothing body
      return d'
    _ -> error $ "not implemented: " ++ pprint hof
    where
      liftMonoidEmpty :: SIType n -> SIAtom n -> SBuilderM n (SIAtom n)
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

-- === Runtime representation of values and refs ===

data Dest (n::S) = Dest
     (SIType n)        -- type of stored value
     (Tree (IExpr n))  -- underlying scalar values
     deriving (Show)

type MaybeDest n = Maybe (Dest n)

data LeafType n where
  LeafType :: TypeCtx SimpToImpIR n l -> BaseType -> LeafType n

instance SinkableE LeafType where sinkingProofE = undefined

-- Gives the relevant context with which to interpret the leaves of a type tree.
type TypeCtx r = Nest (TypeCtxLayer r)

type IndexStructure r = EmptyAbs (IdxNest r) :: E
pattern Singleton :: IndexStructure r n
pattern Singleton = EmptyAbs Empty

type IdxNest r = Nest (IxBinder r)

data TypeCtxLayer (r::IR) (n::S) (l::S) where
 TabCtx     :: IxBinder r n l -> TypeCtxLayer r n l
 DepPairCtx :: MaybeB (Binder r) n l -> TypeCtxLayer r n l
 RefCtx     ::                   TypeCtxLayer r n n

instance SinkableE Dest where
  sinkingProofE = undefined

-- `ScalarDesc` describes how to interpret an Imp value in terms of the nest of
-- buffers that it points to
data BufferElementType = UnboxedValue BaseType | BoxedBuffer BufferElementType
data BufferType n = BufferType (IndexStructure SimpToImpIR n) BufferElementType
data IExprInterpretation n = BufferPtr (BufferType n) | RawValue BaseType

boxingDepth :: BufferElementType -> Int
boxingDepth = \case
  UnboxedValue _ -> 0
  BoxedBuffer eltTy -> 1 + boxingDepth eltTy

getRefBufferType :: LeafType n -> BufferType n
getRefBufferType fullLeafTy = case splitLeadingIxs fullLeafTy of
  Abs idxs restLeafTy ->
    BufferType (EmptyAbs idxs) (getElemType restLeafTy)

getIExprInterpretation :: LeafType n -> IExprInterpretation n
getIExprInterpretation fullLeafTy = case splitLeadingIxs fullLeafTy of
  Abs idxs restLeafTy -> case idxs of
    Empty -> RawValue (elemTypeToBaseType $ getElemType restLeafTy)
    _ -> BufferPtr (BufferType (EmptyAbs idxs) (getElemType restLeafTy))

getElemType :: LeafType n -> BufferElementType
getElemType leafTy = fst $ getElemTypeAndIdxStructure leafTy

getElemTypeAndIdxStructure :: LeafType n -> (BufferElementType, Maybe (IndexStructure SimpToImpIR n))
getElemTypeAndIdxStructure (LeafType ctxs baseTy) = case ctxs of
  Empty -> (UnboxedValue baseTy, Nothing)
  Nest b rest -> case b of
    TabCtx _ -> error "leading idxs should have been stripped off already"
    DepPairCtx depBinder ->
      case getIExprInterpretation (LeafType rest baseTy) of
        RawValue bt -> (UnboxedValue bt, Nothing)
        BufferPtr (BufferType ixs eltTy) -> do
          let ixs' = case depBinder of
                LeftB _      -> Nothing
                RightB UnitB -> Just ixs
          (BoxedBuffer eltTy, ixs')
    RefCtx -> (,Nothing) $ UnboxedValue $
      hostPtrTy $ iExprInterpretationToBaseType $
        getIExprInterpretation (LeafType rest baseTy)
    where hostPtrTy ty = PtrType (CPU, ty)

tryGetBoxIdxStructure :: LeafType n -> Maybe (IndexStructure SimpToImpIR n)
tryGetBoxIdxStructure leafTy = snd $ getElemTypeAndIdxStructure leafTy

iExprInterpretationToBaseType :: IExprInterpretation n -> BaseType
iExprInterpretationToBaseType = \case
  RawValue b -> b
  BufferPtr (BufferType _  elemTy) -> hostPtrTy $ elemTypeToBaseType elemTy
  where hostPtrTy ty = PtrType (CPU, ty)

splitLeadingIxs :: LeafType n -> Abs (IdxNest SimpToImpIR) LeafType n
splitLeadingIxs (LeafType (Nest (TabCtx ix) bs) t) =
  case splitLeadingIxs (LeafType bs t) of
    Abs ixs leafTy -> Abs (Nest ix ixs) leafTy
splitLeadingIxs (LeafType bs t) = Abs Empty $ LeafType bs t

elemTypeToBaseType :: BufferElementType -> BaseType
elemTypeToBaseType = \case
  UnboxedValue t -> t
  BoxedBuffer elemTy -> hostPtrTy $ elemTypeToBaseType elemTy
  where hostPtrTy ty = PtrType (CPU, ty)

typeToTree :: EnvReader m => SIType n -> m n (Tree (LeafType n))
typeToTree tyTop = go REmpty <$> liftEnvReaderM (stripNewtypes tyTop)
 where
  go :: RNest (TypeCtxLayer SimpToImpIR) n l -> SIType l -> Tree (LeafType n)
  go ctx = \case
    BaseTy b -> Leaf $ LeafType (unRNest ctx) b
    TabTy b bodyTy -> go (RNest ctx (TabCtx b)) bodyTy
    RawRefTy t -> go (RNest ctx RefCtx) t
    DepPairTy (DepPairType (b:>t1) (t2)) -> do
      let tree1 = rec t1
      let tree2 = go (RNest ctx (DepPairCtx (JustB (b:>t1)))) t2
      Branch [tree1, tree2]
    ProdTy ts -> Branch $ map rec ts
    SumTy ts -> do
      let tag = rec TagRepTy
      let xs = map rec ts
      Branch $ tag:xs
    ty -> error $ "not implemented " ++ pprint ty
    where rec = go ctx

-- TODO: do this in simplification instead
stripNewtypes :: SIType n -> EnvReaderM n (SIType n)
stripNewtypes = \case
  TabTy b bodyTy -> do
    refreshAbs (Abs b bodyTy) \b' bodyTy' ->
      TabTy b' <$> stripNewtypes bodyTy'
  RawRefTy t -> RawRefTy <$> stripNewtypes t
  TC con -> case con of
    BaseType b    -> return $ BaseTy b
    SumType cases -> (TC . SumType ) <$> mapM stripNewtypes cases
    ProdType tys  -> (TC . ProdType) <$> mapM stripNewtypes tys
    Nat           -> return IdxRepTy
    Fin _         -> return IdxRepTy
    _ -> error $ "not implemented: " ++ pprint con
  TypeCon _ defName params -> do
    def <- lookupDataDef defName
    dcs <- instantiateDataDef def params
    stripNewtypes (dataDefRep dcs)
  DepPairTy (DepPairType (b:>t1) (t2)) -> do
    t1' <- stripNewtypes t1
    Abs b' t2' <- buildAbs (getNameHint b) t1' \v -> do
      let x = Con (Newtype (sink t1) (Var v))
      t2' <- applySubst (b@>SubstVal x) t2
      stripNewtypes t2'
    return $ DepPairTy (DepPairType b' t2')
  VariantTy (NoExt ts) -> do
    ts' <- mapM stripNewtypes $ toList ts
    return $ SumTy ts'
  StaticRecordTy ts -> do
    ts' <- mapM stripNewtypes $ toList ts
    return $ ProdTy ts'
  ty -> error $ "not implemented: " ++ pprint ty

traverseScalarRepTys :: EnvReader m => SIType n -> (LeafType n -> m n a) -> m n (Tree a)
traverseScalarRepTys ty f = traverse f =<< typeToTree ty

storeRepVal :: Emits n => Dest n -> SIRepVal n -> SubstImpM i n ()
storeRepVal (Dest _ destTree) repVal@(RepVal _ valTree) = do
  leafTys <- valueToTree repVal
  forM_ (zipTrees (zipTrees leafTys destTree) valTree) \((leafTy, ptr), val) -> do
    storeLeaf leafTy ptr val

-- Like `typeToTree`, but when we additionally have the value, we can populate
-- the existentially-hidden fields.
valueToTree :: EnvReader m => SIRepVal n -> m n (Tree (LeafType n))
valueToTree (RepVal tyTop valTop) = do
  tyTop' <- liftEnvReaderM (stripNewtypes tyTop)
  go REmpty tyTop' valTop
 where
  go :: EnvReader m => RNest (TypeCtxLayer SimpToImpIR) n l -> SIType l -> Tree (IExpr n)
     -> m n (Tree (LeafType n))
  go ctx ty val = case ty of
    BaseTy b -> return $ Leaf $ LeafType (unRNest ctx) b
    TabTy b bodyTy -> go (RNest ctx (TabCtx b)) bodyTy val
    RawRefTy t -> go (RNest ctx RefCtx) t val
    DepPairTy (DepPairType (b:>t1) (t2)) -> case val of
      Branch [v1, v2] -> do
        case ctx of
          REmpty -> do
            tree1 <- rec t1 v1
            t2' <- applySubst (b@>SubstVal (RepValAtom $ toDRepVal $ RepVal t1 v1)) t2
            tree2 <- go (RNest ctx (DepPairCtx NothingB )) t2' v2
            return $ Branch [tree1, tree2]
          _ -> do
            tree1 <- rec t1 v1
            tree2 <- go (RNest ctx (DepPairCtx (JustB (b:>t1)))) t2 v2
            return $ Branch [tree1, tree2]
      _ -> error "expected a branch"
    ProdTy ts -> case val of
      Branch vals -> Branch <$> zipWithM rec ts vals
      _ -> error "expected a branch"
    SumTy ts -> case val of
      Branch (tagVal:vals) -> do
        tag <- rec TagRepTy tagVal
        results <- zipWithM rec ts vals
        return $ Branch $ tag : results
      _ -> error "expected a branch"
    _ -> error $ "not implemented " ++ pprint ty
    where rec = go ctx

storeLeaf :: Emits n => LeafType n -> IExpr n -> IExpr n -> SubstImpM i n ()
storeLeaf leafTy destPtr srcVal = do
  BufferType idxStructure elemTy <- return $ getRefBufferType leafTy
  case elemTy of
    UnboxedValue _ -> case idxStructure of
      Singleton -> store destPtr srcVal
      _ -> do
        numelem <- computeElemCountImp idxStructure
        emitStatement $ MemCopy destPtr srcVal numelem
    BoxedBuffer elemTy' -> case idxStructure of
      Singleton -> do
        -- In the singleton case our "value" is a buffer pointer, representing
        -- an object like `Fin 3 => Float`. We need to copy its data into a
        -- fresh buffer and store that pointer in the destination singleton
        -- buffer. For the copy, we handle the depth=0 case (the value buffer
        -- just contains raw values) using memcopy and otherwise call into deep
        -- copy.
        ifPtrNonNull srcVal do
          srcVal'  <- sinkM srcVal
          destPtr' <- sinkM destPtr
          Just boxIxStructure <- return $ tryGetBoxIdxStructure (sink leafTy)
          numelem <- computeElemCountImp boxIxStructure
          let baseTy = elemTypeToBaseType elemTy'
          newPtr <- emitInstr $ Alloc CPU baseTy numelem
          case elemTy' of
            UnboxedValue _ ->
              emitStatement $ MemCopy newPtr srcVal' numelem
            BoxedBuffer _ ->
              emitStatement $ DeepCopy (boxingDepth elemTy') newPtr srcVal' numelem
          store destPtr' newPtr
      _ -> do
        -- In the non-singleton case, our "value" is a buffer of boxed buffes,
        -- representing a value like `Fin 3 => List Float`. We use deep copy
        -- directly.
        let depth = boxingDepth elemTy
        numelem <- computeElemCountImp idxStructure
        emitStatement $ DeepCopy depth destPtr srcVal numelem

ifPtrNonNull
  :: Emits n
  => IExpr n
  -> (forall l. (Emits l, DExt n l) => SubstImpM i l ())
  -> SubstImpM i n ()
ifPtrNonNull p cont = do
  nullPtr <- emitInstr $ ICastOp (getIType p) (ILit (Word64Lit 0))
  cond <- emitInstr $ IPrimOp $ BinOp (ICmp Equal) p nullPtr
  body <- buildBlockImp $ cont >> return []
  void $ emitStatement $ ICond cond (ImpBlock Empty []) body

loadRepVal :: (ImpBuilder m, Emits n) => Dest n -> m n (SIRepVal n)
loadRepVal (Dest valTy destTree) = do
  leafTys <- typeToTree valTy
  RepVal valTy <$> forM (zipTrees leafTys destTree) \(leafTy, ptr) -> do
    BufferType size _ <- return $ getRefBufferType leafTy
    case size of
      Singleton -> load ptr
      _         -> return ptr

atomToRepVal :: Emits n => SIAtom n -> SubstImpM i n (SIRepVal n)
atomToRepVal x = RepVal <$> getType x <*> go x where
  go :: Emits n => SIAtom n -> SubstImpM i n (Tree (IExpr n))
  go atom = case atom of
    TabLam (TabLamExpr (b:>ixTy) body) -> do
      ty <- getType atom
      let lamExpr = LamExpr (LamBinder b (ixTypeType ixTy) PlainArrow Pure) body
      RepValAtom dRepVal <- dropSubst $ toImpFor Nothing ty Fwd (ixTypeDict ixTy) (Lam lamExpr)
      (RepVal _ tree) <- forceDRepVal dRepVal
      return tree
    RepValAtom dRepVal -> do
      (RepVal _ tree) <- forceDRepVal dRepVal
      return tree
    DepPair lhs rhs _ -> do
      lhsTree <- go lhs
      rhsTree <- go rhs
      return $ Branch [lhsTree, rhsTree]
    Con (Newtype _ v) -> go v
    Con (Lit l) -> return $ Leaf $ ILit l
    Con (ProdCon xs) -> Branch <$> mapM go xs
    Con (SumAsProd _ tag payload) -> do
      tag'     <- go tag
      payload' <- mapM go payload
      return $ Branch (tag':payload')
    Con (SumCon cases tag payload) -> do
      -- TODO: something better. Maybe we shouldn't have SumCon except during simplification?
      dest@(Dest _ (Branch (tagDest:dests))) <- allocDest (SumTy cases)
      storeAtom (Dest (cases!!tag) (dests!!tag)) payload
      storeAtom (Dest TagRepTy tagDest) (TagRepVal $ fromIntegral tag)
      RepValAtom dRepVal <- loadAtom dest
      (RepVal _ tree) <- forceDRepVal dRepVal
      return tree
    Var v -> lookupAtomName v >>= \case
      PtrLitBound t v' -> return $ Leaf $ IPtrVar v' t
      _ -> error "should only have pointer atom names left"
    _ -> error $ "not implemented: " ++ show atom

-- XXX: We used to have a function called `destToAtom` which loaded the value
-- from the dest. This version is not that. It just lifts a dest into an atom of
-- type `Ref _`.
destToAtom :: Dest n -> SIAtom n
destToAtom (Dest valTy tree) = RepValAtom $ toDRepVal $ RepVal (RawRefTy valTy) tree

atomToDest :: EnvReader m => SIAtom n -> m n (Dest n)
atomToDest (RepValAtom val) = do
  (RepVal ~(RawRefTy valTy) valTree) <- forceDRepVal val
  return $ Dest valTy valTree
atomToDest atom = error $ "Expected a non-var atom of type `RawRef _`, got: " ++ pprint atom

repValToList :: SIRepVal n -> [IExpr n]
repValToList (RepVal _ tree) = toList tree

-- TODO: augment with device, backend information as needed
data AllocContext = Managed | Unmanaged deriving (Show, Eq)
allocDestWithAllocContext :: Emits n => AllocContext -> SIType n -> SubstImpM i n (Dest n)
allocDestWithAllocContext ctx destValTy = do
  descTree <- typeToTree destValTy
  destTree <- forM descTree \leafTy -> do
    BufferType size elemTy <- return $ getRefBufferType leafTy
    numel <- case size of
      Singleton -> return $ IIdxRepVal 1
      idxStructure -> computeElemCountImp idxStructure
    emitAllocWithContext ctx (elemTypeToBaseType elemTy) numel
  return $ Dest destValTy $ destTree

emitAllocWithContext
  :: (Emits n, ImpBuilder m)
  => AllocContext -> BaseType -> IExpr n -> m n (IExpr n)
emitAllocWithContext ctx ty size = do
  if canUseStack ctx size
    then emitInstr $ StackAlloc ty size
    else do
      ptr <- emitInstr $ Alloc CPU ty size
      case ctx of
        Managed   -> extendAllocsToFree ptr
        Unmanaged -> return ()
      return ptr

canUseStack :: AllocContext -> IExpr n -> Bool
canUseStack Managed size | isSmall size  = True
canUseStack _ _ = False

isSmall :: IExpr n -> Bool
isSmall (ILit l) | getIntLit l <= 256 = True
isSmall _ = False

getRepBaseTypes :: EnvReader m => SIType n -> m n [BaseType]
getRepBaseTypes ty = do
  liftM snd $ runStreamWriterT1 $ traverseScalarRepTys ty \leafTy -> do
    writeStream $ iExprInterpretationToBaseType $ getIExprInterpretation leafTy

getDestBaseTypes :: EnvReader m => SIType n -> m n [BaseType]
getDestBaseTypes ty = do
  liftM snd $ runStreamWriterT1 $ traverseScalarRepTys ty \leafTy -> do
    writeStream $ iExprInterpretationToBaseType $ BufferPtr $ getRefBufferType leafTy

listToTree :: EnvReader m => SIType n -> [a] -> m n (Tree a, [a])
listToTree ty xs = runStreamReaderT1 xs $ traverseScalarRepTys ty \_ -> fromJust <$> readStream

allocDestUnmanaged :: Emits n => SIType n -> SubstImpM i n (Dest n)
allocDestUnmanaged = allocDestWithAllocContext Unmanaged

allocDest :: Emits n => SIType n -> SubstImpM i n (Dest n)
allocDest = allocDestWithAllocContext Managed

maybeAllocDest :: Emits n => Maybe (Dest n) -> SIType n -> SubstImpM i n (Dest n)
maybeAllocDest (Just d) _ = return d
maybeAllocDest Nothing t = allocDest t

storeAtom :: Emits n => Dest n -> SIAtom n -> SubstImpM i n ()
storeAtom dest x = storeRepVal dest =<< atomToRepVal x

loadAtom :: forall m n. (ImpBuilder m, Emits n) => Dest n -> m n (SIAtom n)
loadAtom d = RepValAtom <$> toDRepVal <$> loadRepVal d

coreAtomFromRepValList :: (Fallible1 m, EnvReader m) => SType n -> [CAtom n] -> m n (Atom CoreIR n)
coreAtomFromRepValList ty xs = do
  (tree, []) <- runStreamReaderT1 xs $ traverseScalarRepTys (injectIRE ty) \_ -> fromJust <$> readStream
  liftBuilder $ repValToCoreAtom ty tree

-- === Reconstructing core atoms ===

-- this whole section should disappear when we implement `Show` at the dex level.

data CoreRepVal n = CoreRepVal (Type CoreIR n) (Tree (Atom CoreIR n))

instance SinkableE CoreRepVal where
  sinkingProofE = undefined

repValToCoreAtom
  :: SType n -> Tree (CAtom n) -> BuilderM CoreIR n (Atom CoreIR n)
repValToCoreAtom topTy topTree = do
  Abs decls result <- buildScoped $ go True $
    CoreRepVal (sink topTy) (fmap sink topTree)
  case decls of
    Empty -> return result
    _ -> error $ "shouldn't emit decls at the top level"
 where
  -- We don't want to actually emit except under a table lambda.
  -- The `topLevel` flag tells us whether that condition holds.
  -- Ideally we'd pair it with `Emits`, and have a type-level
  -- `Maybe (Emits n)`.
  go :: Bool -> Emits n => CoreRepVal n -> BuilderM CoreIR n (Atom CoreIR n)
  go topLevel repVal@(CoreRepVal ty tree) = case (ty, tree) of
    (BaseTy _, Leaf x) -> return x
    (TabPi (TabPiType (_:>iTy) _), _) -> do
      buildTabLam noHint iTy \i -> do
        bodyRepVal <- indexCoreRepVal (sink repVal) (Var i)
        go False bodyRepVal
    (ProdTy ts, Branch xs) ->
      ProdVal <$> forMZipped ts xs  \t x -> rec $ CoreRepVal t x
    (SumTy  ts, Branch (tag:xs)) -> do
      tag' <- rec $ CoreRepVal TagRepTy tag
      if topLevel
        then do
          xs'  <- zipWithM (\t x -> rec $ CoreRepVal t x) ts xs
          return $ Con $ SumAsProd ts tag' xs'
        else do
          -- If we're under a table lambda, then we can't unconditionally recur
          -- into each branch because we might end up loading sizes from
          -- uninitialized memory and then generating `for` loops using them.
          let enumVal = Con $ SumAsProd (map (const UnitTy) ts) tag' (map (const UnitVal) ts)
          buildCase enumVal (SumTy ts) \i _ -> do
            xs' <- mapM (mapM sinkM) xs
            ts' <- mapM sinkM ts
            Con <$> SumCon ts' i <$> go topLevel (CoreRepVal (ts'!!i) (xs'!!i))
    (DepPairTy t, Branch [left, right]) -> do
      leftVal  <- rec $ CoreRepVal (depPairLeftTy t) left
      rightTy <- instantiateDepPairTy t leftVal
      rightVal <- rec $ CoreRepVal (rightTy) right
      return $ DepPair leftVal rightVal t
    (TypeCon _ defName params, _) -> do
      def <- lookupDataDef defName
      dcs <- instantiateDataDef def params
      goNewtype $ dataDefRep dcs
    (StaticRecordTy ts   , _) -> goNewtype (ProdTy $ toList ts)
    (VariantTy (NoExt ts), _) -> goNewtype (SumTy  $ toList ts)
    (NatTy, _)      -> goNewtype IdxRepTy
    (TC (Fin _), _) -> goNewtype NatTy
    _ -> error $ "unexpected type/tree pair: " ++ pprint ty ++ "\n" ++ show tree
    where
      goNewtype t = (Con . Newtype ty) <$> go topLevel (CoreRepVal t tree)
      rec = go topLevel

-- CoreIR version of `indexRepVal` (we could try to de-dup by thinking harder
-- about what they have in common, but wew plan to delete this soon anyway).
indexCoreRepVal :: Emits n => CoreRepVal n -> Atom CoreIR n -> BuilderM CoreIR n (CoreRepVal n)
indexCoreRepVal (CoreRepVal tabTy@(TabPi (TabPiType (b:>ixTy) eltTy)) vals) i = do
  eltTy' <- applySubst (b@>SubstVal i) eltTy
  ord <- ordinal ixTy i
  leafTys <- typeToTree (unsafeCoerceIRE tabTy)
  vals' <- forM (zipTrees leafTys vals) \(leafTy, ptr) -> do
    BufferPtr (BufferType (EmptyAbs ixStruct) _) <- return $ getIExprInterpretation leafTy
    ixStruct' <- return $ EmptyAbs (fmapNest (\(ib:>ann) -> ib:> unsafeCoerceIRE ann) ixStruct)
    offset <- computeOffsetCore ixStruct' ord
    ptr' <- ptrOffset ptr offset
    case ixStruct of
      Nest _ Empty -> unsafePtrLoad ptr'
      _            -> return ptr'
  return $ CoreRepVal eltTy' vals'
indexCoreRepVal _ _ = error "expected table type"

-- === Operations on dests ===

indexDest :: Emits n => Dest n -> SIAtom n -> SubstImpM i n (Dest n)
indexDest (Dest destValTy@(TabTy (b:>idxTy) eltTy) tree) i = do
  eltTy' <- applySubst (b@>SubstVal i) eltTy
  ord <- ordinalImp idxTy i
  leafTys <- typeToTree destValTy
  Dest eltTy' <$> forM (zipTrees leafTys tree) \(leafTy, ptr) -> do
    BufferType ixStruct _ <- return $ getRefBufferType leafTy
    offset <- computeOffsetImp ixStruct ord
    impOffset ptr offset
indexDest _ _ = error "expected a reference to a table"

-- TODO: direct n-ary version for efficiency?
naryIndexRepVal :: Emits n => RepVal SimpToImpIR n -> [SIAtom n] -> SubstImpM i n (RepVal SimpToImpIR n)
naryIndexRepVal x [] = return x
naryIndexRepVal x (ix:ixs) = do
  x' <- indexRepVal x ix
  naryIndexRepVal x' ixs

-- TODO: de-dup with indexDest?
indexRepVal :: Emits n => RepVal SimpToImpIR n -> SIAtom n -> SubstImpM i n (RepVal SimpToImpIR n)
indexRepVal (RepVal tabTy@(TabPi (TabPiType (b:>ixTy) eltTy)) vals) i = do
  eltTy' <- applySubst (b@>SubstVal i) eltTy
  ord <- ordinalImp ixTy i
  leafTys <- typeToTree tabTy
  vals' <- forM (zipTrees leafTys vals) \(leafTy, ptr) -> do
    BufferPtr (BufferType ixStruct _) <- return $ getIExprInterpretation leafTy
    offset <- computeOffsetImp ixStruct ord
    ptr' <- impOffset ptr offset
    -- we represent scalars by value, not by reference, so we do a load
    -- if this is the last index in the table nest.
    case ixStruct of
      EmptyAbs (Nest _ Empty) -> load ptr'
      _                       -> return ptr'
  return $ RepVal eltTy' vals'
indexRepVal _ _ = error "expected table type"

projectDest :: Int -> Dest n -> Dest n
projectDest i (Dest (ProdTy tys) (Branch ds)) =
  Dest (tys!!i) (ds!!i)
projectDest _ (Dest ty _) = error $ "Can't project dest: " ++ pprint ty

destPairUnpack :: Dest n -> (Dest n, Dest n)
destPairUnpack (Dest (PairTy t1 t2) (Branch [d1, d2])) =
  ( Dest t1 d1, Dest t2 d2 )
destPairUnpack (Dest ty tree) =
  error $ "Can't unpack dest: " ++ pprint ty ++ "\n" ++ show tree

-- === Determining buffer sizes and offsets using polynomials ===

type SBuilderM = BuilderM SimpToImpIR

computeElemCountImp :: Emits n => IndexStructure SimpToImpIR n -> SubstImpM i n (IExpr n)
computeElemCountImp idxs = do
  result <- coreToImpBuilder do
    idxs' <- sinkM idxs
    computeElemCount idxs'
  fromScalarAtom result

computeOffsetImp
  :: Emits n => IndexStructure SimpToImpIR n -> IExpr n -> SubstImpM i n (IExpr n)
computeOffsetImp idxs ixOrd = do
  ixOrd' <- toScalarAtom ixOrd
  result <- coreToImpBuilder do
    PairE idxs' ixOrd'' <- sinkM $ PairE idxs ixOrd'
    computeOffset idxs' ixOrd''
  fromScalarAtom result

computeElemCount :: Emits n => IndexStructure SimpToImpIR n -> SBuilderM n (Atom SimpToImpIR n)
computeElemCount (EmptyAbs Empty) =
  -- XXX: this optimization is important because we don't want to emit any decls
  -- in the case that we don't have any indices. The more general path will
  -- still compute `1`, but it might emit decls along the way.
  return $ IdxRepVal 1
computeElemCount idxNest' = do
  let (idxList, idxNest) = indexStructureSplit idxNest'
  sizes <- forM idxList indexSetSize
  listSize <- foldM imul (IdxRepVal 1) sizes
  nestSize <- elemCountPoly idxNest
  imul listSize nestSize

elemCountPoly :: Emits n => IndexStructure SimpToImpIR n -> SBuilderM n (Atom SimpToImpIR n)
elemCountPoly (Abs bs UnitE) = case bs of
  Empty -> return $ IdxRepVal 1
  Nest b@(_:>ixTy) rest -> do
   curSize <- indexSetSize ixTy
   restSizes <- computeSizeGivenOrdinal b $ EmptyAbs rest
   sumUsingPolysImp curSize restSizes

computeSizeGivenOrdinal
  :: EnvReader m
  => IxBinder SimpToImpIR n l -> IndexStructure SimpToImpIR l
  -> m n (Abs (Binder SimpToImpIR) (Block SimpToImpIR) n)
computeSizeGivenOrdinal (b:>idxTy) idxStruct = liftBuilder do
  withFreshBinder noHint IdxRepTy \bOrdinal ->
    Abs (bOrdinal:>IdxRepTy) <$> buildBlock do
      i <- unsafeFromOrdinal (sink idxTy) $ Var $ sink $ binderName bOrdinal
      idxStruct' <- applySubst (b@>SubstVal i) idxStruct
      elemCountPoly $ sink idxStruct'

-- Split the index structure into a prefix of non-dependent index types
-- and a trailing nest of indices that can contain inter-dependencies.
indexStructureSplit :: IndexStructure r n -> ([IxType r n], IndexStructure r n)
indexStructureSplit (Abs Empty UnitE) = ([], EmptyAbs Empty)
indexStructureSplit s@(Abs (Nest b rest) UnitE) =
  case hoist b (EmptyAbs rest) of
    HoistFailure _     -> ([], s)
    HoistSuccess rest' -> (binderAnn b:ans1, ans2)
      where (ans1, ans2) = indexStructureSplit rest'

computeOffset :: forall n. Emits n
              => IndexStructure SimpToImpIR n -> SIAtom n -> SBuilderM n (SIAtom n)
computeOffset (EmptyAbs (Nest _ Empty)) i = return i  -- optimization
computeOffset (EmptyAbs (Nest b idxs)) idxOrdinal = do
  case hoist b (EmptyAbs idxs) of
    HoistFailure _ -> do
     rhsElemCounts <- computeSizeGivenOrdinal b (EmptyAbs idxs)
     sumUsingPolysImp idxOrdinal rhsElemCounts
    HoistSuccess idxs' -> do
      stride <- computeElemCount idxs'
      idxOrdinal `imul` stride
computeOffset _ _ = error "Expected a nonempty nest of idx binders"

computeOffsetCore :: Emits n => IndexStructure CoreIR n -> CAtom n -> BuilderM CoreIR n (CAtom n)
computeOffsetCore (Abs nest UnitE) idx = do
  nest' <- return $ fmapNest (\(b:>t) -> b:>unsafeCoerceIRE t) nest
  idx'  <- return $ unsafeCoerceIRE idx
  block <- liftBuilder $ buildBlock $
    computeOffset (sink (EmptyAbs nest')) (sink idx')
  block' <- return $ unsafeCoerceIRE block
  emitBlock block'

sumUsingPolysImp
  :: Emits n => Atom SimpToImpIR n
  -> Abs (Binder SimpToImpIR) (Block SimpToImpIR) n -> BuilderM SimpToImpIR n (SIAtom n)
sumUsingPolysImp lim (Abs i body) = do
  ab <- hoistDecls i body
  sumUsingPolys lim ab

hoistDecls
  :: ( Builder SimpToImpIR m, EnvReader m, Emits n
     , BindsNames b, BindsEnv b, SubstB Name b, SinkableB b)
  => b n l -> SIBlock l -> m n (Abs b SIBlock n)
hoistDecls b block = do
  Abs hoistedDecls rest <- liftEnvReaderM $
    refreshAbs (Abs b block) \b' (Block _ decls result) ->
      hoistDeclsRec b' Empty decls result
  ab <- emitDecls hoistedDecls rest
  refreshAbs ab \b'' blockAbs' ->
    Abs b'' <$> absToBlockInferringTypes blockAbs'

hoistDeclsRec
  :: (BindsNames b, SinkableB b)
  => b n1 n2 -> SIDecls n2 n3 -> SIDecls n3 n4 -> SIAtom n4
  -> EnvReaderM n3 (Abs SIDecls (Abs b (Abs SIDecls SIAtom)) n1)
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
  emitDeclsImp :: (SubstE Name e, Emits n) => Abs (Nest ImpDecl) e n -> m n (e n)
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
  withFreshBinder hint (ImpNameBinding ty) \b ->
    cont $ IBinder b ty
{-# INLINE withFreshIBinder #-}

emitCall
  :: Emits n => MaybeDest n -> NaryPiType SimpToImpIR n
  -> ImpFunName n -> [SIAtom n] -> SubstImpM i n (SIAtom n)
emitCall maybeDest piTy f xs = do
  resultTy <- applyNaryAbs (unpackNaryPiType piTy) (map SubstVal xs)
  dest <- maybeAllocDest maybeDest resultTy
  argsImp <- forM xs \x -> repValToList <$> atomToRepVal x
  destImp <- repValToList <$> atomToRepVal (destToAtom dest)
  let impArgs = concat argsImp ++ destImp
  _ <- impCall f impArgs
  loadAtom dest

buildImpFunction
  :: CallingConvention
  -> [(NameHint, IType)]
  -> (forall l. (Emits l, DExt n l) => [IExpr l] -> SubstImpM i l [IExpr l])
  -> SubstImpM i n (ImpFunction n)
buildImpFunction cc argHintsTys body = do
  Abs bs (Abs decls (ListE results)) <-
    buildImpNaryAbs argHintsTys \vs -> ListE <$> body (map (uncurry IVar) vs)
  let resultTys = map getIType results
  let impFun = IFunType cc (map snd argHintsTys) resultTys
  return $ ImpFunction impFun $ Abs bs $ ImpBlock decls results

buildImpNaryAbs
  :: (SinkableE e, HasNamesE e, SubstE Name e, HoistableE e)
  => [(NameHint, IType)]
  -> (forall l. (Emits l, DExt n l) => [(Name ImpNameC l, BaseType)] -> SubstImpM i l (e l))
  -> SubstImpM i n (Abs (Nest IBinder) (Abs (Nest ImpDecl) e) n)
buildImpNaryAbs [] cont = do
  Distinct <- getDistinct
  Abs Empty <$> buildScopedImp (cont [])
buildImpNaryAbs ((hint,ty) : rest) cont = do
  withFreshIBinder hint ty \b -> do
    ab <- buildImpNaryAbs rest \vs -> do
      v <- sinkM $ binderName b
      cont ((v,ty) : vs)
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

impOffset :: Emits n => IExpr n -> IExpr n -> SubstImpM i n (IExpr n)
impOffset ref off = emitInstr $ IPrimOp $ PtrOffset ref off

cast :: Emits n => IExpr n -> BaseType -> SubstImpM i n (IExpr n)
cast x bt = emitInstr $ ICastOp bt x

load :: (ImpBuilder m, Emits n) => IExpr n -> m n (IExpr n)
load x = emitInstr $ IPrimOp $ PtrLoad x
{-# INLINE load #-}

store :: (ImpBuilder m, Emits n) => IExpr n -> IExpr n -> m n ()
store dest src = emitStatement $ Store dest src
{-# INLINE store #-}

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
                -- emitDebugPrint "Loop up to %d\n" (sink n)
                cont =<< sinkM i
                return []
      return $ Abs b body
  emitStatement $ IFor d n loopBody

_emitDebugPrint :: Emits n => String -> IExpr n -> SubstImpM i n ()
_emitDebugPrint fmt x = do
 x' <- cast x (Scalar Word64Type)
 emitStatement $ DebugPrint fmt x'

restructureScalarOrPairType :: SIType n -> [IExpr n] -> SubstImpM i n (SIAtom n)
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

-- === Atom <-> IExpr conversions ===

fromScalarAtom :: Emits n => SIAtom n -> SubstImpM i n (IExpr n)
fromScalarAtom atom = atomToRepVal atom >>= \case
  RepVal _ (Leaf x) -> return x
  _ -> error "Not a scalar atom"

toScalarAtom :: Monad m => IExpr n -> m (SIAtom n)
toScalarAtom x = return $ RepValAtom $ toDRepVal $ RepVal (BaseTy (getIType x)) (Leaf x)

-- TODO: we shouldn't need the rank-2 type here because ImpBuilder and Builder
-- are part of the same conspiracy.
liftBuilderImp :: (Emits n, SubstE (AtomSubstVal SimpToImpIR) e, SinkableE e)
               => (forall l. (Emits l, DExt n l) => BuilderM SimpToImpIR l (e l))
               -> SubstImpM i n (e n)
liftBuilderImp cont = do
  Abs decls result <- liftBuilder $ buildScoped cont
  dropSubst $ translateDeclNest decls $ substM result
{-# INLINE liftBuilderImp #-}

coreToImpBuilder
  :: (Emits n, ImpBuilder m, SinkableE e, SubstE Name e, SubstE (AtomSubstVal SimpToImpIR) e )
  => (forall l. (Emits l, DExt n l) => BuilderM SimpToImpIR l (e l))
  -> m n (e n)
coreToImpBuilder cont = do
  block <- liftBuilder $ buildScoped cont
  result <- liftImpM $ buildScopedImp $ dropSubst do
    Abs decls result <- sinkM block
    translateDeclNest decls $ substM result
  emitDeclsImp result
{-# INLINE coreToImpBuilder #-}

-- === Type classes ===

ordinalImp :: Emits n => IxType SimpToImpIR n -> SIAtom n -> SubstImpM i n (IExpr n)
ordinalImp (IxType _ dict) i = fromScalarAtom =<< do
  case dict of
    DictCon (IxFin _) -> return i
    DictCon (ExplicitMethods d params) -> do
      SpecializedDictBinding (SpecializedDict _ (Just fs)) <- lookupEnv d
      appSpecializedIxMethod (fs !! fromEnum Ordinal) (params ++ [i])
    _ -> error $ "Not a simplified dict: " ++ pprint dict

unsafeFromOrdinalImp :: Emits n => IxType SimpToImpIR n -> IExpr n -> SubstImpM i n (SIAtom n)
unsafeFromOrdinalImp (IxType _ dict) i = do
  i' <- (Con . Newtype NatTy) <$> toScalarAtom i
  case dict of
    DictCon (IxFin n) -> return $ Con $ Newtype (TC $ Fin n) i'
    DictCon (ExplicitMethods d params) -> do
      SpecializedDictBinding (SpecializedDict _ (Just fs)) <- lookupEnv d
      appSpecializedIxMethod (fs !! fromEnum UnsafeFromOrdinal) (params ++ [i'])
    _ -> error $ "Not a simplified dict: " ++ pprint dict

indexSetSizeImp :: Emits n => IxType SimpToImpIR n -> SubstImpM i n (IExpr n)
indexSetSizeImp (IxType _ dict) = do
  ans <- case dict of
    DictCon (IxFin n) -> return n
    DictCon (ExplicitMethods d params) -> do
      SpecializedDictBinding (SpecializedDict _ (Just fs)) <- lookupEnv d
      appSpecializedIxMethod (fs !! fromEnum Size) (params ++ [UnitVal])
    _ -> error $ "Not a simplified dict: " ++ pprint dict
  fromScalarAtom $ unwrapBaseNewtype ans

appSpecializedIxMethod :: Emits n => NaryLamExpr SimpIR n -> [SIAtom n] -> SubstImpM i n (SIAtom n)
appSpecializedIxMethod simpLam args = do
  NaryLamExpr bs _ body <- return $ injectIRE simpLam
  dropSubst $ extendSubst (bs @@> map SubstVal args) $ translateBlock Nothing body

-- === Abstracting link-time objects ===

abstractLinktimeObjects
  :: forall m n. EnvReader m
  => ImpFunction n -> m n (ClosedImpFunction n, [ImpFunName n], [PtrName n])
abstractLinktimeObjects f = do
  let allVars = freeVarsE f
  (funVars, funTys) <- unzip <$> forMFilter (nameSetToList @ImpFunNameC allVars) \v ->
    lookupImpFun v <&> \case
      ImpFunction ty _ -> Just (v, ty)
      FFIFunction _ _ -> Nothing
  (ptrVars, ptrTys) <- unzip <$> forMFilter (nameSetToList @PtrNameC allVars) \v -> do
    (ty, _) <- lookupPtrName v
    return $ Just (v, ty)
  Abs funBs (Abs ptrBs f') <- return $ abstractFreeVarsNoAnn funVars $
                                       abstractFreeVarsNoAnn ptrVars f
  let funBs' =  zipWithNest funBs funTys \b ty -> IFunBinder b ty
  let ptrBs' =  zipWithNest ptrBs ptrTys \b ty -> PtrBinder  b ty
  return (ClosedImpFunction funBs' ptrBs' f', funVars, ptrVars)

-- === type checking imp programs ===

toIVectorType :: SIType n -> IVectorType
toIVectorType = \case
  BaseTy vty@(Vector _ _) -> vty
  _ -> error "Not a vector type"

impFunType :: ImpFunction n -> IFunType
impFunType (ImpFunction ty _) = ty
impFunType (FFIFunction ty _) = ty

getIType :: IExpr n -> IType
getIType (ILit l) = litType l
getIType (IVar _ ty) = ty
getIType (IPtrVar _ ty) = PtrType ty

impInstrTypes :: EnvReader m => ImpInstr n -> m n [IType]
impInstrTypes instr = case instr of
  IPrimOp op      -> return [impOpType op]
  ICastOp t _     -> return [t]
  IBitcastOp t _  -> return [t]
  Alloc a ty _    -> return [PtrType (a  , ty)]
  StackAlloc ty _ -> return [PtrType (CPU, ty)]
  Store _ _       -> return []
  Free _          -> return []
  IThrowError     -> return []
  MemCopy _ _ _   -> return []
  DeepCopy _ _ _ _ -> return []
  IFor _ _ _      -> return []
  IWhile _        -> return []
  ICond _ _ _     -> return []
  ILaunch _ _ _   -> return []
  ISyncWorkgroup  -> return []
  IVectorBroadcast _ vty -> return [vty]
  IVectorIota vty        -> return [vty]
  DebugPrint _ _  -> return []
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
  OutputStream       -> hostPtrTy $ Scalar Word8Type
    where hostPtrTy ty = PtrType (CPU, ty)
  _ -> unreachable
  where unreachable = error $ "Not allowed in Imp IR: " ++ show pop

instance CheckableE ImpFunction where
  checkE = substM -- TODO!

-- TODO: Don't use Core Envs for Imp!
instance BindsEnv ImpDecl where
  toEnvFrag (ImpLet bs _) = toEnvFrag bs

instance BindsEnv IBinder where
  toEnvFrag (IBinder b ty) =  toEnvFrag $ b :> ImpNameBinding ty

instance SubstB (AtomSubstVal SimpToImpIR) IBinder

-- See Note [Confuse GHC] from Simplify.hs
confuseGHC :: EnvReader m => m n (DistinctEvidence n)
confuseGHC = getDistinct
{-# INLINE confuseGHC #-}

-- === debug instrumentation ===

-- Adds a `DebugPrint XXX` after each Imp instruction. It's a crude tracing
-- mechanism that's useful for debugging segfaults.
-- To use: put something like this in an appropriate place in `TopLevel.hs`
--    let fImp = addImpTracing (pprint fname ++ " %x\n") impFun' fImp'
addImpTracing :: String -> ImpFunction n -> ImpFunction n
addImpTracing _ f@(FFIFunction _ _) = f
addImpTracing fmt (ImpFunction ty (Abs bs body)) =
  ImpFunction ty (Abs bs (evalState (go REmpty body) 0))
 where
   go :: RNest ImpDecl n l -> ImpBlock l -> MTL.State Int (ImpBlock n)
   go accum (ImpBlock Empty result) = return $ ImpBlock (unRNest accum) result
   go accum (ImpBlock (Nest decl decls) result) = do
     n <- next
     let traceDecl = ImpLet Empty (DebugPrint fmt (ILit $ Word64Lit $ fromIntegral n))
     decl' <- traverseDeclBlocks (go REmpty) decl
     go (accum `RNest` traceDecl `RNest` decl') (ImpBlock decls result)

   next :: MTL.State Int Int
   next = do
     n <- get
     put $ n + 1
     return n

traverseDeclBlocks
  :: Monad m => (forall n'. ImpBlock n' -> m (ImpBlock n'))
  -> ImpDecl n l -> m (ImpDecl n l)
traverseDeclBlocks f (ImpLet bs instr) = ImpLet bs <$> case instr of
  IFor d n (Abs b block) -> IFor d n <$> (Abs b <$> f block)
  -- TODO: fill in the other cases as needed
  _ -> return instr

-- === notes ===

{-

Note [memory management]

Dex emphasizes flat array-like data structures unlike other functional languages
which tend to use trees of pointers. Instead of dynamically counting references
to heap-allocated objects we do all memory management at compile time based on
static scopes. The generated code uses malloc/free in a style similar to C
programming. We use destination-passing style to call functions.

Every function (or code block -- loop body, case body, etc.) is passed a
destination in which to store its final result. The function or block may
allocate memory for intermediate results but it must free anything it allocated
before returning. There's an important exception, to do with dependent pairs,
which we discuss soon.

The main unit of memory management is the fixed-size buffer, a contiguous chunk
of memory directly storing scalar base values, int32, float64 etc, with no
wasted space. The main Dex runtime data types -- tables, products, sums, base
types and mixtures of all these -- are all represented by some number of these.
We can determine the required size of the buffer based solely on the type, since
tables encode their size in their type. This lets us allocate buffers for
results before calling a function or starting a block.

A buffer is represented by a pointer which is guaranteed to have been generated
by a call to `malloc_dex` which means that it can be freed with a call to
`free_dex`. `malloc_dex` also stores the size of the buffer in the few bytes
before the data part, which lets us make copies of buffers without having to
keep track of their sizes (e.g. back in the Haskell runtime).

The destination-passing style, together with the free-before-returning style,
lets us generate as many views as we like of a buffer without having to count
references (dynamically or statically). For example, we use we use pointers to
interior memory locations in a buffer to represent array slices and subarrays.
We don't need to worry about use-after-free errors because we don't free the
buffer until the function/block returns, at which point those views will no
longer be available. The only thing that escapes the function is the data
written into the destination supplied by the caller.

Now back to the important exception, dependent pairs. When we have a dependent
pair, like `(n:Nat &^ Fin n => Float)`, we don't know the size of the `Fin n =>
Float` table because the `n` is given by the *value* of the (first element of
the) pair. We use these to encode dynamically-sized lists. We handle this case
by pretending that we can have an array of arbitrary-sized boxes. The
implementation is just an array of pointers. But these pointers behave quite
differently from either the pointers that point to standard buffers or the
pointers used as views of those buffers. We think of them as an implementation
detail modeling the interface of an array with variable-sized elements, stored
*as values* in the array. In particular, the buffer exclusively owns the memory
backing its boxes. When we free the buffer, we free its boxes. When we write to
a buffer at an index, allocate fresh memory for the new box and free the old box
(unless it's null, as for an uninitialized buffer). We can still take read-only
views of the data in the boxes, but only if we know the buffer itself is
immutable/frozen, because otherwise the box memory might be freed when it's
overwritten by another value, which could happen before exiting the scope (in
that sense it's no different from taking a slice of a buffer to represent a
subarray).

Separate from this memory system, we have user-facing references, `Ref h a`,
from the `State` effect. The memory for these is managed by a separate system,
the `runState` scope. The references are represented as pointers, and they may
appear in buffers if we happen to have a table of references in the user
program. But they are not boxes, and the memory they point to certainly isn't
owned by the buffer. For one thing, the same pointer can appear in multiple
tables, or multiple times in one table. To handle these references, we just
treat them as pointers to foreign memory. Once we've actually loaded one of
these pointers and we have it as a value, *then* we can interpret it as a buffer
so that we can read/write from it. Since the allocation and freeing is done by
`runState`, and the use of the references is guarded by the heap parameter, we
have the same sort of guarantee about having no use-after-free bugs.

-}
