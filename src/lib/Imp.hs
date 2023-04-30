-- Copyright 2021 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE PartialTypeSignatures #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Imp
  ( toImpFunction
  , impFunType, getIType, abstractLinktimeObjects
  , repValFromFlatList, addImpTracing
  -- These are just for the benefit of serialization/printing. otherwise we wouldn't need them
  , BufferType (..), IdxNest, IndexStructure, IExprInterpretation (..), typeToTree
  , computeOffset, getIExprInterpretation
  , isSingletonType, singletonTypeVal
  ) where

import Prelude hiding ((.), id)
import Data.Functor
import Data.Foldable (toList)
import Data.Maybe (fromJust, isJust)
import Data.Text.Prettyprint.Doc
import Control.Category
import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.Writer.Strict
import Control.Monad.State.Strict hiding (State)
import qualified Control.Monad.State.Strict as MTL

import Algebra
import Builder
import CheapReduction
import CheckType (CheckableE (..))
import Core
import Err
import IRVariants
import MTL1
import Name
import Subst
import QueryType
import Types.Core
import Types.Imp
import Types.Primitives
import Util (forMFilter, Tree (..), zipTrees, enumerate)

toImpFunction :: EnvReader m
  => CallingConvention -> DestLamExpr SimpIR n -> m n (ImpFunction n)
toImpFunction cc lam = do
  (DestLamExpr bs bodyAbs) <- return lam
  ty <- getNaryDestLamExprType lam
  impArgTys <- getNaryLamImpArgTypesWithCC cc ty
  liftImpM $ buildImpFunction cc (zip (repeat noHint) impArgTys) \vs -> do
    case cc of
      EntryFunCC _ -> do
        argAtoms <- interpretImpArgs (sink $ EmptyAbs bs) vs
        extendSubst (bs @@> (SubstVal <$> argAtoms)) do
          DestBlock (destb:>destTy) body <- return bodyAbs
          dest <- case destTy of
            RefTy _ ansTy -> allocDestUnmanaged =<< substM ansTy
            _ -> error "Expected a reference type for body destination"
          extendSubst (destb @> SubstVal (destToAtom dest)) do
            void $ translateBlock body
          resultAtom <- loadAtom dest
          repValToList <$> atomToRepVal resultAtom
      _ -> do
        (argAtoms, resultDest) <- interpretImpArgsWithCC cc (sink ty) vs
        extendSubst (bs @@> (SubstVal <$> argAtoms)) do
          (DestBlock destb body) <- return bodyAbs
          extendSubst (destb @> SubstVal (destToAtom (sink resultDest))) do
            void $ translateBlock body
            return []

getNaryLamImpArgTypesWithCC :: EnvReader m
  => CallingConvention -> PiType SimpIR n -> m n [BaseType]
getNaryLamImpArgTypesWithCC XLACC _ = return [i8pp, i8pp]
  where i8pp = PtrType (CPU, PtrType (CPU, Scalar Word8Type))
getNaryLamImpArgTypesWithCC (EntryFunCC _) t =
  concat . fst <$> getNaryLamImpArgTypes t
getNaryLamImpArgTypesWithCC _ t = do
  (argTyss, destTys) <- getNaryLamImpArgTypes t
  return $ concat argTyss ++ destTys

getImpFunType :: EnvReader m
  => CallingConvention -> PiType SimpIR n -> m n IFunType
getImpFunType StandardCC piTy = do
  argTys <- getNaryLamImpArgTypesWithCC StandardCC piTy
  return $ IFunType StandardCC argTys []
getImpFunType cc _ = error $ "unsupported calling convention: " ++ pprint cc

interpretImpArgsWithCC :: Emits n
  => CallingConvention -> PiType SimpIR n
  -> [IExpr n] -> SubstImpM i n ([SAtom n], Dest n)
interpretImpArgsWithCC XLACC t [outsPtr, insPtr] = do
  (argBaseTys, resultBaseTys) <- getNaryLamImpArgTypes t
  argVals <- forM (enumerate $ concat argBaseTys) \(i, ty) -> case ty of
    PtrType (_, pointeeTy) -> loadPtr insPtr i pointeeTy
    _ -> load =<< loadPtr insPtr i ty
  resultPtrs <- case resultBaseTys of
    -- outsPtr points directly to the buffer when there's one output, not to the pointer array.
    [ty] -> (:[]) <$> cast outsPtr ty
    _ ->
      forM (enumerate resultBaseTys) \(i, ty) -> case ty of
        PtrType (_, pointeeTy) -> loadPtr outsPtr i pointeeTy
        _ -> error "Destination arguments should all have pointer types"
  interpretImpArgsWithDest t (argVals ++ resultPtrs)
  where
    loadPtr base i pointeeTy = do
      ptr <- load =<< impOffset base (IIdxRepVal $ fromIntegral i)
      cast ptr (PtrType (CPU, pointeeTy))
interpretImpArgsWithCC _ t xsAll = interpretImpArgsWithDest t xsAll

getNaryLamImpArgTypes :: EnvReader m
  => PiType SimpIR n -> m n ([[BaseType]], [BaseType])
getNaryLamImpArgTypes t = liftEnvReaderM $ go t where
  go :: PiType SimpIR n -> EnvReaderM n ([[BaseType]], [BaseType])
  go (PiType bs effs resultTy) = case bs of
    Nest piB rest -> do
      ts <- getRepBaseTypes $ binderType piB
      refreshAbs (Abs piB (PiType rest effs resultTy)) \_ restPi -> do
        (argTys, resultTys) <- go restPi
        return (ts:argTys, resultTys)
    Empty -> ([],) <$> getDestBaseTypes resultTy

interpretImpArgsWithDest :: EnvReader m
  => PiType SimpIR n -> [IExpr n] -> m n ([SAtom n], Dest n)
interpretImpArgsWithDest t xs = do
  (PiType bs _ resultTy) <- return t
  (args, xsLeft) <- _interpretImpArgs (EmptyAbs bs) xs
  resultTy' <- applySubst (bs @@> (SubstVal <$> args)) resultTy
  (destTree, xsRest) <- listToTree resultTy' xsLeft
  case xsRest of
    [] -> return ()
    _  -> error "Shouldn't have any Imp arguments left"
  return (args, Dest resultTy' destTree)

interpretImpArgs :: EnvReader m
  => EmptyAbs (Nest SBinder) n -> [IExpr n] -> m n [SAtom n]
interpretImpArgs t args = do
  (args', xsLeft) <- _interpretImpArgs t args
  case xsLeft of
    [] -> return args'
    _  -> error "Shouldn't have any Imp arguments left"

_interpretImpArgs :: EnvReader m
  => EmptyAbs (Nest SBinder) n -> [IExpr n] -> m n ([SAtom n], [IExpr n])
_interpretImpArgs t args =
  liftEnvReaderM $ runSubstReaderT idSubst $ go t args where
    go :: EmptyAbs (Nest SBinder) i -> [IExpr o]
       -> SubstReaderT AtomSubstVal EnvReaderM i o ([SAtom o], [IExpr o])
    go (Abs bs UnitE) xs = case bs of
      Nest (b:>argTy) rest -> do
        argTy' <- substM argTy
        (argTree, xsRest) <- listToTree argTy' xs
        arg <- repValAtom $ RepVal argTy' argTree
        (args', xsLeft) <- extendSubst (b @> SubstVal arg) $ go (EmptyAbs rest) xsRest
        return (arg:args', xsLeft)
      Empty -> return ([], xs)

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

instance ImpBuilder m => ImpBuilder (SubstReaderT AtomSubstVal m i) where
  emitMultiReturnInstr instr = SubstReaderT $ lift $ emitMultiReturnInstr instr
  {-# INLINE emitMultiReturnInstr #-}
  emitDeclsImp ab = SubstReaderT $ lift $ emitDeclsImp ab
  {-# INLINE emitDeclsImp #-}
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

translateBlock :: forall i o. Emits o
  => SBlock i -> SubstImpM i o (SAtom o)
translateBlock (Block _ decls result) = translateDeclNest decls $ substM result

translateDeclNestSubst
  :: Emits o => Subst AtomSubstVal l o
  -> Nest SDecl l i' -> SubstImpM i o (Subst AtomSubstVal i' o)
translateDeclNestSubst !s = \case
  Empty -> return s
  Nest (Let b (DeclBinding _ _ expr)) rest -> do
    x <- withSubst s $ translateExpr expr
    translateDeclNestSubst (s <>> (b@>SubstVal x)) rest

translateDeclNest :: Emits o
  => Nest SDecl i i' -> SubstImpM i' o a -> SubstImpM i o a
translateDeclNest decls cont = do
  s  <- getSubst
  s' <- translateDeclNestSubst s decls
  withSubst s' cont
{-# INLINE translateDeclNest #-}

translateExpr :: forall i o. Emits o => SExpr i -> SubstImpM i o (SAtom o)
translateExpr expr = confuseGHC >>= \_ -> case expr of
  TopApp f' xs' -> do
    f <- substM f'
    xs <- mapM substM xs'
    lookupTopFun f >>= \case
      DexTopFun _ piTy _ _ -> emitCall piTy f $ toList xs
      FFITopFun _ _ -> do
        resultTy <- getType $ TopApp f xs
        scalarArgs <- liftM toList $ mapM fromScalarAtom xs
        results <- impCall f scalarArgs
        restructureScalarOrPairType resultTy results
  TabApp f' xs' -> do
    xs <- mapM substM xs'
    f <- atomToRepVal =<< substM f'
    repValAtom =<< naryIndexRepVal f (toList xs)
  Atom x -> substM x
  PrimOp op -> toImpOp op
  Case e alts unitResultTy _ -> do
    e' <- substM e
    case unitResultTy of
      UnitTy -> return ()
      _ -> error $ "Unexpected returning Case in Imp " ++ pprint expr
    case trySelectBranch e' of
      Just (con, arg) -> do
        Abs b body <- return $ alts !! con
        extendSubst (b @> SubstVal arg) $ translateBlock body
      Nothing -> do
        RepVal sumTy (Branch (tag:xss)) <- atomToRepVal e'
        ts <- caseAltsBinderTys sumTy
        tag' <- repValAtom $ RepVal TagRepTy tag
        xss' <- zipWithM (\t x -> repValAtom $ RepVal t x) ts xss
        go tag' xss'
        where
          go tag xss = do
            tag' <- fromScalarAtom tag
            emitSwitch tag' (zip xss alts) $
              \(xs, Abs b body) ->
                 extendSubst (b @> SubstVal (sink xs)) $
                   void $ translateBlock body
            return UnitVal
  TabCon _ _ _ -> error "Unexpected `TabCon` in Imp pass."

toImpRefOp :: Emits o
  => SAtom i -> RefOp SimpIR i -> SubstImpM i o (SAtom o)
toImpRefOp refDest' m = do
  refDest <- atomToDest =<< substM refDest'
  substM m >>= \case
    MAsk -> loadAtom refDest
    MExtend (BaseMonoid _ combine) x -> do
      xTy <- getType x
      refVal <- loadAtom refDest
      liftMonoidCombine refDest xTy combine refVal x
      return UnitVal
    MPut x -> storeAtom refDest x >> return UnitVal
    MGet -> do
      Dest resultTy _ <- return refDest
      dest <- allocDest resultTy
      -- It might be more efficient to implement a specialized copy for dests
      -- than to go through a general purpose atom.
      storeAtom dest =<< loadAtom refDest
      loadAtom dest
    IndexRef i -> destToAtom <$> indexDest refDest i
    ProjRef  ~(ProjectProduct i) -> return $ destToAtom $ projectDest i refDest
  where
    liftMonoidCombine :: Emits o
      => (Dest o) -> SType o -> LamExpr SimpIR o
      -> SAtom o -> SAtom o -> SubstImpM n o ()
    liftMonoidCombine accDest accTy bc x y = do
      LamExpr (Nest (_:>baseTy) _) _ <- return bc
      alphaEq accTy baseTy >>= \case
        -- Immediately beta-reduce, beacuse Imp doesn't reduce non-table applications.
        True -> do
          BinaryLamExpr xb yb body <- return bc
          body' <- applySubst (xb @> SubstVal x <.> yb @> SubstVal y) body
          ans <- liftBuilderImp $ emitBlock (sink body')
          storeAtom accDest ans
        False -> case accTy of
          TabTy (b:>ixTy) eltTy -> do
            n <- indexSetSizeImp ixTy
            emitLoop noHint Fwd n \i -> do
              idx <- unsafeFromOrdinalImp (sink ixTy) i
              xElt <- liftBuilderImp $ tabApp (sink x) (sink idx)
              yElt <- liftBuilderImp $ tabApp (sink y) (sink idx)
              eltTy' <- applySubst (b@>SubstVal idx) eltTy
              ithDest <- indexDest (sink accDest) idx
              liftMonoidCombine ithDest eltTy' (sink bc) xElt yElt
          _ -> error $ "Base monoid type mismatch: can't lift " ++
                 pprint baseTy ++ " to " ++ pprint accTy

toImpOp :: forall i o . Emits o => PrimOp SimpIR i -> SubstImpM i o (SAtom o)
toImpOp op = case op of
  Hof hof -> toImpHof hof
  RefOp refDest eff -> toImpRefOp refDest eff
  DAMOp damOp -> case damOp of
    Seq d ixDict carry f -> do
      UnaryLamExpr b body <- return f
      ixTy <- ixTyFromDict =<< substM ixDict
      carry' <- substM carry
      n <- indexSetSizeImp ixTy
      emitLoop (getNameHint b) d n \i -> do
        idx <- unsafeFromOrdinalImp (sink ixTy) i
        void $ extendSubst (b @> SubstVal (PairVal idx (sink carry'))) $
          translateBlock body
      return carry'
    RememberDest d f -> do
      UnaryLamExpr b body <- return f
      d' <- substM d
      void $ extendSubst (b @> SubstVal d') $ translateBlock body
      return d'
    Place ref val -> do
      val' <- substM val
      refDest <- atomToDest =<< substM ref
      storeAtom refDest val' >> return UnitVal
    Freeze ref -> loadAtom =<< atomToDest =<< substM ref
    AllocDest ty  -> do
      d <- liftM destToAtom $ allocDest =<< substM ty
      return d
  BinOp binOp x y -> returnIExprVal =<< emitInstr =<< (IBinOp binOp <$> fsa x <*> fsa y)
  UnOp  unOp  x   -> returnIExprVal =<< emitInstr =<< (IUnOp  unOp  <$> fsa x)
  MemOp    op' -> toImpMemOp    =<< substM op'
  MiscOp   op' -> toImpMiscOp   =<< substM op'
  VectorOp op' -> toImpVectorOp =<< substM op'
  where
    fsa x = substM x >>= fromScalarAtom
    returnIExprVal x = return $ toScalarAtom x

toImpVectorOp :: Emits o => VectorOp SimpIR o -> SubstImpM i o (SAtom o)
toImpVectorOp = \case
  VectorBroadcast val vty -> do
    val' <- fromScalarAtom val
    emitInstr (IVectorBroadcast val' $ toIVectorType vty) >>= returnIExprVal
  VectorIota vty -> emitInstr (IVectorIota $ toIVectorType vty) >>= returnIExprVal
  VectorSubref ref i vty -> do
    refDest <- atomToDest ref
    refi <- destToAtom <$> indexDest refDest i
    refi' <- fromScalarAtom refi
    let PtrType (addrSpace, _) = getIType refi'
    case vty of
      BaseTy vty'@(Vector _ _) -> do
        resultVal <- cast refi' (PtrType (addrSpace, vty'))
        repValAtom $ RepVal (RefTy (Con HeapVal) vty) (Leaf resultVal)
      _ -> error "Expected a vector type"
  where
    returnIExprVal x = return $ toScalarAtom x

toImpMiscOp :: Emits o => MiscOp SimpIR o -> SubstImpM i o (SAtom o)
toImpMiscOp op = case op of
  ThrowError resultTy -> do
    emitStatement IThrowError
    buildGarbageVal resultTy
  CastOp destTy x -> do
    BaseTy _  <- getType x
    BaseTy bt <- return destTy
    x' <- fsa x
    returnIExprVal =<< cast x' bt
  BitcastOp destTy x -> do
    BaseTy bt <- return destTy
    returnIExprVal =<< emitInstr =<< (IBitcastOp bt <$> fsa x)
  UnsafeCoerce resultTy x -> do
    srcTy <- getType x
    srcRep  <- getRepBaseTypes srcTy
    destRep <- getRepBaseTypes resultTy
    assertEq srcRep destRep $
      "representation types don't match: " ++ pprint srcRep ++ "  !=  " ++ pprint destRep
    RepVal _ tree <- atomToRepVal x
    repValAtom (RepVal resultTy tree)
  GarbageVal resultTy -> buildGarbageVal resultTy
  Select p x y -> do
    BaseTy _ <- getType x
    returnIExprVal =<< emitInstr =<< (ISelect <$> fsa p <*> fsa x <*> fsa y)
  SumTag con -> case con of
    Con (SumCon _ tag _) -> return $ TagRepVal $ fromIntegral tag
    RepValAtom dRepVal -> go dRepVal
    _ -> error $ "Not a data constructor: " ++ pprint con
    where go dRepVal = do
            RepVal _ (Branch (tag:_)) <- return dRepVal
            return $ RepValAtom $ RepVal TagRepTy tag
  ToEnum ty i -> case ty of
    SumTy cases -> do
      i' <- fromScalarAtom i
      return $ RepValAtom $ RepVal ty $ Branch $ Leaf i' : map (const (Branch [])) cases
    _ -> error $ "Not an enum: " ++ pprint ty
  OutputStream -> returnIExprVal =<< emitInstr IOutputStream
  ThrowException _ -> error "shouldn't have ThrowException left" -- also, should be replaced with user-defined errors
  ShowAny _ -> error "Shouldn't have ShowAny in simplified IR"
  ShowScalar x -> do
    resultTy <- getType $ PrimOp $ MiscOp op
    Dest (PairTy sizeTy tabTy) (Branch [sizeTree, tabTree@(Leaf tabPtr)]) <- allocDest resultTy
    xScalar <- fromScalarAtom x
    size <- emitInstr $ IShowScalar tabPtr xScalar
    let size' = toScalarAtom size
    storeAtom (Dest sizeTy sizeTree) size'
    tab <- loadAtom $ Dest tabTy tabTree
    return $ PairVal size' tab
  where
    fsa = fromScalarAtom
    returnIExprVal x = return $ toScalarAtom x

toImpMemOp :: forall i o . Emits o => MemOp SimpIR o -> SubstImpM i o (SAtom o)
toImpMemOp op = case op of
  IOAlloc n -> do
    n' <- fsa n
    ptr <- emitInstr $ Alloc CPU (Scalar Word8Type) n'
    returnIExprVal ptr
  IOFree ptr -> do
    ptr' <- fsa ptr
    emitStatement $ Free ptr'
    return UnitVal
  PtrOffset arr (IdxRepVal 0) -> return arr
  PtrOffset arr off -> do
    arr' <- fsa arr
    off' <- fsa off
    buf <- impOffset arr' off'
    returnIExprVal buf
  PtrLoad arr -> do
    result <- load =<< fsa arr
    returnIExprVal result
  PtrStore ptr x -> do
    ptr' <- fsa ptr
    x'   <- fsa x
    store ptr' x'
    return UnitVal
  where
    fsa = fromScalarAtom
    returnIExprVal x = return $ toScalarAtom x

toImpHof :: Emits o => Hof SimpIR i -> SubstImpM i o (SAtom o)
toImpHof hof = do
  resultTy <- getTypeSubst (Hof hof)
  case hof of
    For _ _ _ -> error $ "Unexpected `for` in Imp pass " ++ pprint hof
    While body -> do
      body' <- buildBlockImp do
        ans <- fromScalarAtom =<< translateBlock body
        return [ans]
      emitStatement $ IWhile body'
      return UnitVal
    RunReader r f -> do
      BinaryLamExpr h ref body <- return f
      r' <- substM r
      rDest <- allocDest =<< getType r'
      storeAtom rDest r'
      extendSubst (h @> SubstVal (Con HeapVal) <.> ref @> SubstVal (destToAtom rDest)) $
        translateBlock body
    RunWriter d (BaseMonoid e _) f -> do
      BinaryLamExpr h ref body <- return f
      let PairTy ansTy accTy = resultTy
      (aDest, wDest) <- case d of
        Nothing -> destPairUnpack <$> allocDest resultTy
        Just d' -> do
          aDest <- allocDest ansTy
          wDest <- atomToDest =<< substM d'
          return (aDest, wDest)
      e' <- substM e
      PairE accTy' e'' <- sinkM $ PairE accTy e'
      liftMonoidEmpty wDest accTy' e''
      extendSubst (h @> SubstVal (Con HeapVal) <.> ref @> SubstVal (destToAtom wDest)) $
        translateBlock body >>= storeAtom aDest
      PairVal <$> loadAtom aDest <*> loadAtom wDest
    RunState d s f -> do
      BinaryLamExpr h ref body <- return f
      let PairTy ansTy _ = resultTy
      (aDest, sDest) <- case d of
        Nothing -> destPairUnpack <$> allocDest resultTy
        Just d' -> do
          aDest <- allocDest ansTy
          sDest <- atomToDest =<< substM d'
          return (aDest, sDest)
      storeAtom sDest =<< substM s
      extendSubst (h @> SubstVal (Con HeapVal) <.> ref @> SubstVal (destToAtom sDest)) $
        translateBlock body >>= storeAtom aDest
      PairVal <$> loadAtom aDest <*> loadAtom sDest
    RunIO body -> translateBlock body
    RunInit body -> translateBlock body
    where
      liftMonoidEmpty :: Emits n => Dest n -> SType n -> SAtom n -> SubstImpM i n ()
      liftMonoidEmpty accDest accTy x = do
        xTy <- getType x
        alphaEq xTy accTy >>= \case
          True -> storeAtom accDest x
          False -> case accTy of
            TabTy (b:>ixTy) eltTy -> do
              n <- indexSetSizeImp ixTy
              emitLoop noHint Fwd n \i -> do
                idx <- unsafeFromOrdinalImp (sink ixTy) i
                x' <- sinkM x
                eltTy' <- applySubst (b@>SubstVal idx) eltTy
                ithDest <- indexDest (sink accDest) idx
                liftMonoidEmpty ithDest eltTy' x'
            _ -> error $ "Base monoid type mismatch: can't lift " ++
                  pprint xTy ++ " to " ++ pprint accTy

-- === Runtime representation of values and refs ===

data Dest (n::S) = Dest
     (SType n)        -- type of stored value
     (Tree (IExpr n))  -- underlying scalar values
     deriving (Show)

data LeafType n where
  LeafType :: TypeCtx SimpIR n l -> BaseType -> LeafType n

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
data BufferElementType = UnboxedValue BaseType | BoxedBuffer BufferElementType deriving (Show)
data BufferType n = BufferType (IndexStructure SimpIR n) BufferElementType deriving (Show)
data IExprInterpretation n = BufferPtr (BufferType n) | RawValue BaseType deriving (Show)

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

getElemTypeAndIdxStructure :: LeafType n -> (BufferElementType, Maybe (IndexStructure SimpIR n))
getElemTypeAndIdxStructure (LeafType ctxs baseTy) = case ctxs of
  Empty -> (UnboxedValue baseTy, Nothing)
  Nest b rest -> case b of
    TabCtx _ -> error "leading idxs should have been stripped off already"
    DepPairCtx depBinder -> case splitLeadingDepPairs rest of
      PairB depBinders rest' -> case getIExprInterpretation (LeafType rest' baseTy) of
        RawValue bt -> (UnboxedValue bt, Nothing)
        BufferPtr (BufferType ixs eltTy) -> do
          let ixs' = case allNothingBs (Nest depBinder depBinders) of
                Just UnitB -> Just ixs
                Nothing -> Nothing
          (BoxedBuffer eltTy, ixs')
    RefCtx -> (,Nothing) $ UnboxedValue $ hostPtrTy $ elemTypeToBaseType eltTy
      where BufferType _ eltTy = getRefBufferType (LeafType rest baseTy)
    where hostPtrTy ty = PtrType (CPU, ty)

allNothingBs :: Nest (MaybeB b) n l -> Maybe (UnitB n l)
allNothingBs Empty = Just UnitB
allNothingBs (Nest (LeftB _) _) = Nothing
allNothingBs (Nest (RightB UnitB) rest) = allNothingBs rest

splitLeadingDepPairs :: TypeCtx SimpIR n l -> PairB (Nest (MaybeB SBinder)) (TypeCtx SimpIR) n l
splitLeadingDepPairs = \case
  Empty -> PairB Empty Empty
  Nest (DepPairCtx b) rest -> case splitLeadingDepPairs rest of
    PairB bs rest' -> PairB (Nest b bs) rest'
  ctxs -> PairB Empty ctxs

tryGetBoxIdxStructure :: LeafType n -> Maybe (IndexStructure SimpIR n)
tryGetBoxIdxStructure leafTy = snd $ getElemTypeAndIdxStructure leafTy

iExprInterpretationToBaseType :: IExprInterpretation n -> BaseType
iExprInterpretationToBaseType = \case
  RawValue b -> b
  BufferPtr (BufferType _  elemTy) -> hostPtrTy $ elemTypeToBaseType elemTy
  where hostPtrTy ty = PtrType (CPU, ty)

splitLeadingIxs :: LeafType n -> Abs (IdxNest SimpIR) LeafType n
splitLeadingIxs (LeafType (Nest (TabCtx ix) bs) t) =
  case splitLeadingIxs (LeafType bs t) of
    Abs ixs leafTy -> Abs (Nest ix ixs) leafTy
splitLeadingIxs (LeafType bs t) = Abs Empty $ LeafType bs t

elemTypeToBaseType :: BufferElementType -> BaseType
elemTypeToBaseType = \case
  UnboxedValue t -> t
  BoxedBuffer elemTy -> hostPtrTy $ elemTypeToBaseType elemTy
  where hostPtrTy ty = PtrType (CPU, ty)

typeToTree :: EnvReader m => SType n -> m n (Tree (LeafType n))
typeToTree tyTop = return $ go REmpty tyTop
 where
  go :: RNest (TypeCtxLayer SimpIR) n l -> SType l -> Tree (LeafType n)
  go ctx = \case
    BaseTy b -> Leaf $ LeafType (unRNest ctx) b
    TabTy b bodyTy -> go (RNest ctx (TabCtx b)) bodyTy
    RefTy _ t -> go (RNest ctx RefCtx) t
    DepPairTy (DepPairType _ (b:>t1) (t2)) -> do
      let tree1 = rec t1
      let tree2 = go (RNest ctx (DepPairCtx (JustB (b:>t1)))) t2
      Branch [tree1, tree2]
    ProdTy ts -> Branch $ map rec ts
    SumTy ts -> do
      let tag = rec TagRepTy
      let xs = map rec ts
      Branch $ tag:xs
    TC HeapType -> Branch []
    ty -> error $ "not implemented " ++ pprint ty
    where rec = go ctx

traverseScalarRepTys :: EnvReader m => SType n -> (LeafType n -> m n a) -> m n (Tree a)
traverseScalarRepTys ty f = traverse f =<< typeToTree ty
{-# INLINE traverseScalarRepTys #-}

storeRepVal :: Emits n => Dest n -> SRepVal n -> SubstImpM i n ()
storeRepVal (Dest _ destTree) repVal@(RepVal _ valTree) = do
  leafTys <- valueToTree repVal
  forM_ (zipTrees (zipTrees leafTys destTree) valTree) \((leafTy, ptr), val) -> do
    storeLeaf leafTy ptr val
{-# INLINE storeRepVal #-}

-- Like `typeToTree`, but when we additionally have the value, we can populate
-- the existentially-hidden fields.
valueToTree :: EnvReader m => SRepVal n -> m n (Tree (LeafType n))
valueToTree (RepVal tyTop valTop) = do
  go REmpty tyTop valTop
 where
  go :: EnvReader m => RNest (TypeCtxLayer SimpIR) n l -> SType l -> Tree (IExpr n)
     -> m n (Tree (LeafType n))
  go ctx ty val = case ty of
    BaseTy b -> return $ Leaf $ LeafType (unRNest ctx) b
    TabTy b bodyTy -> go (RNest ctx (TabCtx b)) bodyTy val
    RefTy _ t -> go (RNest ctx RefCtx) t val
    DepPairTy (DepPairType _ (b:>t1) (t2)) -> case val of
      Branch [v1, v2] -> do
        case allDepPairCtxs (unRNest ctx) of
          Just UnitB -> do
            tree1 <- rec t1 v1
            x <- repValAtom $ RepVal t1 v1
            t2' <- applySubst (b@>SubstVal x) t2
            tree2 <- go (RNest ctx (DepPairCtx NothingB )) t2' v2
            return $ Branch [tree1, tree2]
          Nothing -> do
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
{-# INLINE valueToTree #-}

allDepPairCtxs :: TypeCtx SimpIR n l -> Maybe (UnitB n l)
allDepPairCtxs ctx = case splitLeadingDepPairs ctx of
  PairB bs Empty -> allNothingBs bs
  _ -> Nothing

storeLeaf :: Emits n => LeafType n -> IExpr n -> IExpr n -> SubstImpM i n ()
storeLeaf leafTy dest src = case getRefBufferType leafTy of
  BufferType Singleton (UnboxedValue _) -> store dest src
  BufferType idxStructure (UnboxedValue _) -> do
    numel <- computeElemCountImp idxStructure
    memcopy dest src numel
  BufferType Singleton (BoxedBuffer elemTy) -> do
    load dest >>= freeBox elemTy
    Just boxIxStructure <- return $ tryGetBoxIdxStructure leafTy
    boxSize <- computeElemCountImp boxIxStructure
    cloneBox dest elemTy (Just boxSize) src
  BufferType idxStructure (BoxedBuffer elemTy) -> do
    numelem <- computeElemCountImp idxStructure
    emitLoop "i" Fwd numelem \i -> do
      curDest <- impOffset (sink dest) i
      load curDest >>= freeBox elemTy
      srcBox <- impOffset (sink src) i >>= load
      cloneBox curDest elemTy Nothing srcBox
{-# INLINE storeLeaf #-}

freeBox :: Emits n => BufferElementType -> IExpr n -> SubstImpM i n ()
freeBox elemTy ptr = do
  ifNull ptr (return ()) do
    ptr' <- sinkM ptr
    case elemTy of
      UnboxedValue _ -> return ()
      BoxedBuffer innerBoxElemTy -> do
        numElem <- emitInstr $ GetAllocSize ptr'
        mapOffsetPtrs numElem [ptr'] \[offsetPtr] ->
          load offsetPtr  >>= freeBox innerBoxElemTy
    emitStatement $ Free ptr'

-- If the buffer size (in elements) is not provided, then it assumed to be
-- available by querying the runtime. This means that it must be a pointer
-- directly obtained by calling `malloc_alloc`, not an offset-derived pointer
-- thereof.
cloneBox :: Emits n => IExpr n -> BufferElementType -> Maybe (IExpr n) -> IExpr n -> SubstImpM i n ()
cloneBox dest elemTy maybeBufferNumElem srcPtr = do
  ifNull srcPtr
    (store (sink dest) (nullPtrIExpr $ elemTypeToBaseType elemTy))
    do
      numElem <- case maybeBufferNumElem of
        Just n -> sinkM n
        Nothing -> emitInstr $ GetAllocSize $ sink srcPtr
      -- It's "Unmanaged" by the scoped memory system because its lifetime is
      -- determined by the array it will appear in instead. (Also it has to be
      -- heap-allocated).
      newPtr <- emitAllocWithContext Unmanaged (elemTypeToBaseType elemTy) numElem
      store (sink dest) newPtr
      case elemTy of
        UnboxedValue _ -> memcopy newPtr (sink srcPtr) numElem
        BoxedBuffer elemTy' -> do
          mapOffsetPtrs numElem [newPtr, sink srcPtr] \[newPtrOffset, srcPtrOffset] -> do
            load srcPtrOffset >>= cloneBox newPtrOffset elemTy' Nothing

ifNull
  :: Emits n
  => IExpr n
  -> (forall l. (Emits l, DExt n l) => SubstImpM i l ())
  -> (forall l. (Emits l, DExt n l) => SubstImpM i l ())
  -> SubstImpM i n ()
ifNull p trueBranch falseBranch = do
  pIsNull <- isNull p
  trueBlock  <- buildBlockImp $ [] <$ trueBranch
  falseBlock <- buildBlockImp $ [] <$ falseBranch
  emitStatement $ ICond pIsNull trueBlock falseBlock

isNull :: (ImpBuilder m, Emits n) => IExpr n -> m n (IExpr n)
isNull p = do
  let PtrType (_, baseTy) = getIType p
  emitInstr $ IBinOp (ICmp Equal) p (nullPtrIExpr baseTy)
{-# INLINE isNull #-}

nullPtrIExpr :: BaseType -> IExpr n
nullPtrIExpr baseTy = ILit $ PtrLit (CPU, baseTy) NullPtr

loadRepVal :: (ImpBuilder m, Emits n) => Dest n -> m n (SRepVal n)
loadRepVal (Dest valTy destTree) = do
  leafTys <- typeToTree valTy
  RepVal valTy <$> forM (zipTrees leafTys destTree) \(leafTy, ptr) -> do
    BufferType size _ <- return $ getRefBufferType leafTy
    case size of
      Singleton -> load ptr
      _         -> return ptr
{-# INLINE loadRepVal #-}

atomToRepVal :: Emits n => SAtom n -> SubstImpM i n (SRepVal n)
atomToRepVal x = RepVal <$> getType x <*> go x where
  go :: Emits n => SAtom n -> SubstImpM i n (Tree (IExpr n))
  go atom = case atom of
    RepValAtom dRepVal -> do
      (RepVal _ tree) <- return dRepVal
      return tree
    DepPair lhs rhs _ -> do
      lhsTree <- go lhs
      rhsTree <- go rhs
      return $ Branch [lhsTree, rhsTree]
    Con (Lit l) -> return $ Leaf $ ILit l
    Con (ProdCon xs) -> Branch <$> mapM go xs
    Con (SumCon cases tag payload) -> do
      tag' <- go $ TagRepVal $ fromIntegral tag
      xs <- forM (enumerate cases) \(i, t) -> if i == tag
        then go payload
        else buildGarbageVal t <&> \(RepValAtom (RepVal _ tree)) -> tree
      return $ Branch $ tag':xs
    Con HeapVal -> return $ Branch []
    Var v -> lookupAtomName v >>= \case
      TopDataBound (RepVal _ tree) -> return tree
      _ -> error "should only have pointer and data atom names left"
    PtrVar p -> do
      PtrBinding ty _ <- lookupEnv p
      return $ Leaf $ IPtrVar p ty
    ProjectElt p val -> do
      (ps, v) <- return $ asNaryProj p val
      lookupAtomName v >>= \case
        TopDataBound (RepVal _ tree) -> applyProjection (toList ps) tree
        _ -> error "should only be projecting a data atom"
      where
        applyProjection :: [Projection] -> Tree (IExpr n) -> SubstImpM i n (Tree (IExpr n))
        applyProjection [] t = return t
        applyProjection (i:is) t = do
          t' <- applyProjection is t
          case i of
            UnwrapNewtype -> error "impossible"
            ProjectProduct idx    -> case t' of
              Branch ts -> return $ ts !! idx
              _ -> error "should only be projecting a branch"

-- XXX: We used to have a function called `destToAtom` which loaded the value
-- from the dest. This version is not that. It just lifts a dest into an atom of
-- type `Ref _`.
destToAtom :: Dest n -> SAtom n
destToAtom (Dest valTy tree) = RepValAtom $ RepVal (RefTy (Con HeapVal) valTy) tree

atomToDest :: EnvReader m => SAtom n -> m n (Dest n)
atomToDest (RepValAtom val) = do
  (RepVal ~(RefTy _ valTy) valTree) <- return val
  return $ Dest valTy valTree
atomToDest atom = error $ "Expected a non-var atom of type `RawRef _`, got: " ++ pprint atom
{-# INLINE atomToDest #-}

repValToList :: SRepVal n -> [IExpr n]
repValToList (RepVal _ tree) = toList tree

-- TODO: augment with device, backend information as needed
data AllocContext = Managed | Unmanaged deriving (Show, Eq)
allocDestWithAllocContext :: Emits n => AllocContext -> SType n -> SubstImpM i n (Dest n)
allocDestWithAllocContext ctx destValTy = do
  descTree <- typeToTree destValTy
  destTree <- forM descTree \leafTy -> allocBuffer ctx $ getRefBufferType leafTy
  return $ Dest destValTy $ destTree

allocBuffer :: Emits n => AllocContext -> BufferType n -> SubstImpM i n (IExpr n)
allocBuffer ctx (BufferType idxStructure elemTy) = do
  numel <- computeElemCountImp idxStructure
  let baseTy = elemTypeToBaseType elemTy
  ptr <- emitAllocWithContext ctx baseTy numel
  case elemTy of
    UnboxedValue _ -> return ()
    BoxedBuffer boxElemTy ->
      case numel of
        IIdxRepVal 1 -> store ptr (nullPtrIExpr $ elemTypeToBaseType boxElemTy)
        _ -> emitStatement $ InitializeZeros ptr numel
  return ptr

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
{-# INLINE emitAllocWithContext #-}

canUseStack :: AllocContext -> IExpr n -> Bool
canUseStack Managed size | isSmall size  = True
canUseStack _ _ = False

isSmall :: IExpr n -> Bool
isSmall (ILit l) | getIntLit l <= 256 = True
isSmall _ = False

getRepBaseTypes :: EnvReader m => SType n -> m n [BaseType]
getRepBaseTypes ty = do
  liftM snd $ runStreamWriterT1 $ traverseScalarRepTys ty \leafTy -> do
    writeStream $ iExprInterpretationToBaseType $ getIExprInterpretation leafTy
{-# INLINE getRepBaseTypes #-}

getDestBaseTypes :: EnvReader m => SType n -> m n [BaseType]
getDestBaseTypes ty = do
  liftM snd $ runStreamWriterT1 $ traverseScalarRepTys ty \leafTy -> do
    writeStream $ iExprInterpretationToBaseType $ BufferPtr $ getRefBufferType leafTy

listToTree :: EnvReader m => SType n -> [a] -> m n (Tree a, [a])
listToTree ty xs = runStreamReaderT1 xs $ traverseScalarRepTys ty \_ -> fromJust <$> readStream

allocDestUnmanaged :: Emits n => SType n -> SubstImpM i n (Dest n)
allocDestUnmanaged = allocDestWithAllocContext Unmanaged
{-# INLINE allocDestUnmanaged #-}

allocDest :: Emits n => SType n -> SubstImpM i n (Dest n)
allocDest = allocDestWithAllocContext Managed

storeAtom :: Emits n => Dest n -> SAtom n -> SubstImpM i n ()
storeAtom dest x = storeRepVal dest =<< atomToRepVal x

loadAtom :: Emits n => Dest n -> SubstImpM i n (SAtom n)
loadAtom d = repValAtom =<< loadRepVal d

repValFromFlatList :: (TopBuilder m, Mut n) => SType n -> [LitVal] -> m n (SRepVal n)
repValFromFlatList ty xs = do
  (litValTree, []) <- runStreamReaderT1 xs $ traverseScalarRepTys ty \_ ->
    fromJust <$> readStream
  iExprTree <- mapM litValToIExpr litValTree
  return $ RepVal ty iExprTree

litValToIExpr :: (TopBuilder m, Mut n) => LitVal -> m n (IExpr n)
litValToIExpr litval = case litval of
  PtrLit ty ptr -> do
    ptrName <- emitBinding "ptr" $ PtrBinding ty ptr
    return $ IPtrVar ptrName ty
  _ -> return $ ILit litval

buildGarbageVal :: Emits n => SType n -> SubstImpM i n (SAtom n)
buildGarbageVal ty =
  RepValAtom <$> RepVal ty <$> traverseScalarRepTys ty \leafTy -> do
    case getIExprInterpretation leafTy of
      BufferPtr bufferTy -> allocBuffer Managed bufferTy
      RawValue b -> return $ ILit $ emptyLit b

-- === Operations on dests ===

indexDest :: Emits n => Dest n -> SAtom n -> SubstImpM i n (Dest n)
indexDest (Dest destValTy@(TabTy (b:>idxTy) eltTy) tree) i = do
  eltTy' <- applySubst (b@>SubstVal i) eltTy
  ord <- ordinalImp idxTy i
  leafTys <- typeToTree destValTy
  Dest eltTy' <$> forM (zipTrees leafTys tree) \(leafTy, ptr) -> do
    BufferType ixStruct _ <- return $ getRefBufferType leafTy
    offset <- computeOffsetImp ixStruct ord
    impOffset ptr offset
indexDest _ _ = error "expected a reference to a table"
{-# INLINE indexDest #-}

-- TODO: direct n-ary version for efficiency?
naryIndexRepVal :: Emits n => RepVal SimpIR n -> [SAtom n] -> SubstImpM i n (RepVal SimpIR n)
naryIndexRepVal x [] = return x
naryIndexRepVal x (ix:ixs) = do
  x' <- indexRepVal x ix
  naryIndexRepVal x' ixs
{-# INLINE naryIndexRepVal #-}

-- TODO: de-dup with indexDest?
indexRepVal :: Emits n => RepVal SimpIR n -> SAtom n -> SubstImpM i n (RepVal SimpIR n)
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
{-# INLINE indexRepVal #-}

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

type SBuilderM = BuilderM SimpIR

computeElemCountImp :: Emits n => IndexStructure SimpIR n -> SubstImpM i n (IExpr n)
computeElemCountImp Singleton = return $ IIdxRepVal 1
computeElemCountImp idxs = do
  result <- coreToImpBuilder do
    idxs' <- sinkM idxs
    computeElemCount idxs'
  fromScalarAtom result

computeOffsetImp
  :: Emits n => IndexStructure SimpIR n -> IExpr n -> SubstImpM i n (IExpr n)
computeOffsetImp idxs ixOrd = do
  let ixOrd' = toScalarAtom ixOrd
  result <- coreToImpBuilder do
    PairE idxs' ixOrd'' <- sinkM $ PairE idxs ixOrd'
    computeOffset idxs' ixOrd''
  fromScalarAtom result

computeElemCount :: Emits n => IndexStructure SimpIR n -> SBuilderM n (Atom SimpIR n)
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

elemCountPoly :: Emits n => IndexStructure SimpIR n -> SBuilderM n (Atom SimpIR n)
elemCountPoly (Abs bs UnitE) = case bs of
  Empty -> return $ IdxRepVal 1
  Nest b@(_:>ixTy) rest -> do
   curSize <- indexSetSize ixTy
   restSizes <- computeSizeGivenOrdinal b $ EmptyAbs rest
   sumUsingPolysImp curSize restSizes

computeSizeGivenOrdinal
  :: EnvReader m
  => IxBinder SimpIR n l -> IndexStructure SimpIR l
  -> m n (Abs (Binder SimpIR) (Block SimpIR) n)
computeSizeGivenOrdinal (b:>idxTy) idxStruct = liftBuilder do
  withFreshBinder noHint IdxRepTy \bOrdinal ->
    Abs bOrdinal <$> buildBlock do
      i <- unsafeFromOrdinal (sink idxTy) $ Var $ sink $ binderName bOrdinal
      idxStruct' <- applySubst (b@>SubstVal i) idxStruct
      elemCountPoly $ sink idxStruct'

-- Split the index structure into a prefix of non-dependent index types
-- and a trailing nest of indices that can contain inter-dependencies.
indexStructureSplit :: IndexStructure SimpIR n -> ([IxType SimpIR n], IndexStructure SimpIR n)
indexStructureSplit (Abs Empty UnitE) = ([], EmptyAbs Empty)
indexStructureSplit s@(Abs (Nest b rest) UnitE) =
  case hoist b (EmptyAbs rest) of
    HoistFailure _     -> ([], s)
    HoistSuccess rest' -> (binderAnn b:ans1, ans2)
      where (ans1, ans2) = indexStructureSplit rest'

computeOffset :: forall n. Emits n
              => IndexStructure SimpIR n -> SAtom n -> SBuilderM n (SAtom n)
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

sumUsingPolysImp
  :: Emits n => Atom SimpIR n
  -> Abs (Binder SimpIR) (Block SimpIR) n -> BuilderM SimpIR n (SAtom n)
sumUsingPolysImp lim (Abs i body) = do
  ab <- hoistDecls i body
  sumUsingPolys lim ab

hoistDecls
  :: ( Builder SimpIR m, EnvReader m, Emits n
     , BindsNames b, BindsEnv b, RenameB b, SinkableB b)
  => b n l -> SBlock l -> m n (Abs b SBlock n)
hoistDecls b block = do
  Abs hoistedDecls rest <- liftEnvReaderM $
    refreshAbs (Abs b block) \b' (Block _ decls result) ->
      hoistDeclsRec b' Empty decls result
  ab <- emitDecls hoistedDecls rest
  refreshAbs ab \b'' blockAbs' ->
    Abs b'' <$> absToBlockInferringTypes blockAbs'
{-# INLINE hoistDecls #-}

hoistDeclsRec
  :: (BindsNames b, SinkableB b)
  => b n1 n2 -> SDecls n2 n3 -> SDecls n3 n4 -> SAtom n4
  -> EnvReaderM n3 (Abs SDecls (Abs b (Abs SDecls SAtom)) n1)
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
{-# INLINE hoistDeclsRec #-}

-- === Imp IR builder ===

data ImpInstrResult (n::S) = NoResults | OneResult !(IExpr n) | MultiResult !([IExpr n])

class (EnvReader m, EnvExtender m, Fallible1 m) => ImpBuilder (m::MonadKind1) where
  emitMultiReturnInstr :: Emits n => ImpInstr n -> m n (ImpInstrResult n)
  emitDeclsImp :: (RenameE e, Emits n) => Abs (Nest ImpDecl) e n -> m n (e n)
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
  withFreshBinder hint (ImpNameBinding ty) \(b:>_) ->
    cont $ IBinder b ty
{-# INLINE withFreshIBinder #-}

emitCall
  :: Emits n => PiType SimpIR n
  -> ImpFunName n -> [SAtom n] -> SubstImpM i n (SAtom n)
emitCall (PiType bs _ resultTy) f xs = do
  resultTy' <- applySubst (bs @@> map SubstVal xs) resultTy
  dest <- allocDest resultTy'
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
  :: (SinkableE e, HasNamesE e, RenameE e, HoistableE e)
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
{-# INLINE impCall #-}

impOffset :: Emits n => IExpr n -> IExpr n -> SubstImpM i n (IExpr n)
impOffset ref (IIdxRepVal 0) = return ref
impOffset ref off = emitInstr $ IPtrOffset ref off
{-# INLINE impOffset #-}

memcopy :: (ImpBuilder m, Emits n) => IExpr n -> IExpr n -> IExpr n -> m n ()
memcopy new src numElem = emitStatement $ MemCopy new src numElem
{-# INLINE memcopy #-}

cast :: Emits n => IExpr n -> BaseType -> SubstImpM i n (IExpr n)
cast x bt = emitInstr $ ICastOp bt x

load :: (ImpBuilder m, Emits n) => IExpr n -> m n (IExpr n)
load x = emitInstr $ IPtrLoad x
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
      cond       <- emitInstr $ IBinOp (ICmp Equal) (sink testIdx) curTag
      thisCase   <- buildBlockImp $ cont arg >> return []
      otherCases <- buildBlockImp $ rec (curIdx + 1) rest >> return []
      emitStatement $ ICond cond thisCase otherCases

mapOffsetPtrs
  :: Emits n
  => IExpr n -> [IExpr n]
  -> (forall l. (DExt n l, Emits l) => [IExpr l] -> SubstImpM i l ())
  -> SubstImpM i n ()
mapOffsetPtrs numelem basePtrs cont = do
  emitLoop "i" Fwd numelem \i -> do
    offsetPtrs <- forM basePtrs \basePtr -> impOffset (sink basePtr) i
    cont offsetPtrs

emitLoop :: Emits n
         => NameHint -> Direction -> IExpr n
         -> (forall l. (DExt n l, Emits l) => IExpr l -> SubstImpM i l ())
         -> SubstImpM i n ()
emitLoop _ _ (IIdxRepVal 0) _ = return ()
emitLoop _ _ (IIdxRepVal 1) cont = do
  Distinct <- getDistinct
  cont (IIdxRepVal 0)
emitLoop hint d n cont = do
  loopBody <- do
    withFreshIBinder hint (getIType n) \b@(IBinder _ ty)  -> do
      let i = IVar (binderName b) ty
      body <- buildBlockImp do
                cont =<< sinkM i
                return []
      return $ Abs b body
  emitStatement $ IFor d n loopBody

_emitDebugPrint :: (ImpBuilder m, Emits n) => String -> IExpr n -> m n ()
_emitDebugPrint fmt x = do
 x' <- emitInstr $ ICastOp (Scalar Int64Type) x
 emitStatement $ DebugPrint fmt x'

restructureScalarOrPairType :: SType n -> [IExpr n] -> SubstImpM i n (SAtom n)
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
      let x' = toScalarAtom x
      return (x', xs)
    go ty _ = error $ "Not a scalar or pair: " ++ pprint ty

buildBlockImp
  :: (forall l. (Emits l, DExt n l) => SubstImpM i l [IExpr l])
  -> SubstImpM i n (ImpBlock n)
buildBlockImp cont = do
  Abs decls (ListE results) <- buildScopedImp $ ListE <$> cont
  return $ ImpBlock decls results

-- === Atom <-> IExpr conversions ===

fromScalarAtom :: Emits n => SAtom n -> SubstImpM i n (IExpr n)
fromScalarAtom atom = atomToRepVal atom >>= \case
  RepVal ty tree -> case tree of
    Leaf x -> return x
    _ -> error $ "Not a scalar atom:" ++ pprint ty

toScalarAtom :: IExpr n -> SAtom n
toScalarAtom x = RepValAtom $ RepVal (BaseTy (getIType x)) (Leaf x)

-- TODO: we shouldn't need the rank-2 type here because ImpBuilder and Builder
-- are part of the same conspiracy.
liftBuilderImp :: (Emits n, SubstE AtomSubstVal e, SinkableE e)
               => (forall l. (Emits l, DExt n l) => BuilderM SimpIR l (e l))
               -> SubstImpM i n (e n)
liftBuilderImp cont = do
  Abs decls result <- liftBuilder $ buildScoped cont
  dropSubst $ translateDeclNest decls $ substM result
{-# INLINE liftBuilderImp #-}

coreToImpBuilder
  :: (Emits n, ImpBuilder m, SinkableE e, RenameE e, SubstE AtomSubstVal e )
  => (forall l. (Emits l, DExt n l) => BuilderM SimpIR l (e l))
  -> m n (e n)
coreToImpBuilder cont = do
  block <- liftBuilder $ buildScoped cont
  result <- liftImpM $ buildScopedImp $ dropSubst do
    Abs decls result <- sinkM block
    translateDeclNest decls $ substM result
  emitDeclsImp result
{-# INLINE coreToImpBuilder #-}

-- === Type classes ===

ordinalImp :: Emits n => IxType SimpIR n -> SAtom n -> SubstImpM i n (IExpr n)
ordinalImp (IxType _ dict) i = fromScalarAtom =<< case dict of
  IxDictRawFin _ -> return i
  IxDictSpecialized _ d params -> do
    SpecializedDict _ (Just fs) <- lookupSpecDict d
    appSpecializedIxMethod (fs !! fromEnum Ordinal) (params ++ [i])

unsafeFromOrdinalImp :: Emits n => IxType SimpIR n -> IExpr n -> SubstImpM i n (SAtom n)
unsafeFromOrdinalImp (IxType _ dict) i = do
  let i' = toScalarAtom i
  case dict of
    IxDictRawFin _ -> return i'
    IxDictSpecialized _ d params -> do
      SpecializedDict _ (Just fs) <- lookupSpecDict d
      appSpecializedIxMethod (fs !! fromEnum UnsafeFromOrdinal) (params ++ [i'])

indexSetSizeImp :: Emits n => IxType SimpIR n -> SubstImpM i n (IExpr n)
indexSetSizeImp (IxType _ dict) = do
  ans <- case dict of
    IxDictRawFin n -> return n
    IxDictSpecialized _ d params -> do
      SpecializedDict _ (Just fs) <- lookupSpecDict d
      appSpecializedIxMethod (fs !! fromEnum Size) (params ++ [])
  fromScalarAtom ans

appSpecializedIxMethod :: Emits n => LamExpr SimpIR n -> [SAtom n] -> SubstImpM i n (SAtom n)
appSpecializedIxMethod simpLam args = do
  LamExpr bs body <- return simpLam
  dropSubst $ extendSubst (bs @@> map SubstVal args) $ translateBlock body

-- === Abstracting link-time objects ===

abstractLinktimeObjects
  :: forall m n. EnvReader m
  => ImpFunction n -> m n (ClosedImpFunction n, [TopFunName n], [PtrName n])
abstractLinktimeObjects f = do
  let allVars = freeVarsE f
  (funVars, funTys) <- unzip <$> forMFilter (nameSetToList @TopFunNameC allVars) \v ->
    lookupTopFun v >>= \case
      DexTopFun _ piTy _ _ -> do
        ty' <- getImpFunType StandardCC piTy
        return $ Just (v, ty')
      FFITopFun _ _ -> return Nothing
  (ptrVars, ptrTys) <- unzip <$> forMFilter (nameSetToList @PtrNameC allVars) \v -> do
    (ty, _) <- lookupPtrName v
    return $ Just (v, ty)
  Abs funBs (Abs ptrBs f') <- return $ abstractFreeVarsNoAnn funVars $
                                       abstractFreeVarsNoAnn ptrVars f
  let funBs' =  zipWithNest funBs funTys \b ty -> IFunBinder b ty
  let ptrBs' =  zipWithNest ptrBs ptrTys \b ty -> PtrBinder  b ty
  return (ClosedImpFunction funBs' ptrBs' f', funVars, ptrVars)

-- === singleton types ===

-- The following implementation should be valid:
--   isSingletonType :: EnvReader m => Type n -> m n Bool
--   isSingletonType ty =
--     singletonTypeVal ty >>= \case
--       Nothing -> return False
--       Just _  -> return True
-- But a separate implementation doesn't have to go under binders,
-- because it doesn't have to reconstruct the singleton value (which
-- may be type annotated and whose type may refer to names).

isSingletonType :: Type SimpIR n -> Bool
isSingletonType topTy = isJust $ checkIsSingleton topTy
  where
    checkIsSingleton :: Type r n -> Maybe ()
    checkIsSingleton ty = case ty of
      TabPi (TabPiType _ body) -> checkIsSingleton body
      TC (ProdType tys) -> mapM_ checkIsSingleton tys
      _ -> Nothing

singletonTypeVal :: (EnvReader m)
  => Type SimpIR n -> m n (Maybe (Atom SimpIR n))
singletonTypeVal ty = do
  tree <- typeToTree ty
  if length tree == 0 then do
    -- The tree has 0 of these if the type is empty
    let tree' = fmap (const $ ILit $ Int32Lit 0) tree
    return $ Just $ RepValAtom $ RepVal ty tree'
  else
    return Nothing
{-# INLINE singletonTypeVal #-}

-- === type checking imp programs ===

toIVectorType :: SType n -> IVectorType
toIVectorType = \case
  BaseTy vty@(Vector _ _) -> vty
  _ -> error "Not a vector type"

impFunType :: ImpFunction n -> IFunType
impFunType (ImpFunction ty _) = ty

getIType :: IExpr n -> IType
getIType (ILit l) = litType l
getIType (IVar _ ty) = ty
getIType (IPtrVar _ ty) = PtrType ty

impInstrTypes :: EnvReader m => ImpInstr n -> m n [IType]
impInstrTypes instr = case instr of
  IBinOp op x _   -> return [typeBinOp op (getIType x)]
  IUnOp  op x     -> return [typeUnOp  op (getIType x)]
  ICastOp t _     -> return [t]
  IBitcastOp t _  -> return [t]
  Alloc a ty _    -> return [PtrType (a  , ty)]
  StackAlloc ty _ -> return [PtrType (CPU, ty)]
  Store _ _       -> return []
  Free _          -> return []
  IThrowError     -> return []
  MemCopy _ _ _   -> return []
  InitializeZeros _ _ -> return []
  GetAllocSize _  -> return [IIdxRepTy]
  IFor _ _ _      -> return []
  IWhile _        -> return []
  ICond _ _ _     -> return []
  ILaunch _ _ _   -> return []
  ISyncWorkgroup  -> return []
  IVectorBroadcast _ vty -> return [vty]
  IVectorIota vty        -> return [vty]
  DebugPrint _ _  -> return []
  IQueryParallelism _ _ -> return [IIdxRepTy, IIdxRepTy]
  ICall f _ -> lookupTopFun f >>= \case
    DexTopFun _ piTy _ _ -> do
      IFunType _ _ resultTys <- getImpFunType StandardCC piTy
      return resultTys
    FFITopFun _ (IFunType _ _ resultTys) -> return resultTys
  ISelect  _ x  _  -> return [getIType x]
  IPtrLoad ref -> return [ty]  where PtrType (_, ty) = getIType ref
  IPtrOffset ref _ -> return [PtrType (addr, ty)]  where PtrType (addr, ty) = getIType ref
  IOutputStream    -> return [hostPtrTy $ Scalar Word8Type]
  IShowScalar _ _  -> return [Scalar Word32Type]
  where hostPtrTy ty = PtrType (CPU, ty)

instance CheckableE SimpIR ImpFunction where
  checkE _ = return () -- TODO

-- TODO: Don't use Core Envs for Imp!
instance BindsEnv ImpDecl where
  toEnvFrag (ImpLet bs _) = toEnvFrag bs

instance BindsEnv IBinder where
  toEnvFrag (IBinder b ty) =  toEnvFrag $ b :> ImpNameBinding ty

instance Pretty (LeafType n) where
  pretty (LeafType ctx base) = pretty ctx <+> pretty base

instance Pretty (TypeCtxLayer SimpIR n l) where
  pretty = \case
    TabCtx ix            -> pretty ix
    DepPairCtx (RightB UnitB) -> "dep-pair-instantiated"
    DepPairCtx (LeftB b)      -> "dep-pair" <+> pretty b
    RefCtx               -> "refctx"

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
  ICond cond block1 block2 -> ICond cond <$> f block1 <*> f block2
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
references (dynamically or statically). For example, we use pointers to
interior memory locations in a buffer to represent array slices and subarrays.
We don't need to worry about use-after-free errors because we don't free the
buffer until the function/block returns, at which point those views will no
longer be available. The only thing that escapes the function is the data
written into the destination supplied by the caller.

Now back to the important exception, dependent pairs. When we have a dependent
pair, like `(n:Nat &> Fin n => Float)`, we don't know the size of the `Fin n =>
Float` table because the `n` is given by the *value* of the (first element of
the) pair. We use these to encode dynamically-sized lists.

We handle having an array of these by pretending that we can have an array of
arbitrary-sized boxes. The implementation is just an array of pointers. But
these pointers behave quite differently from either the pointers that point to
standard buffers or the pointers used as views of those buffers. We think of
them as an implementation detail modeling the interface of an array with
variable-sized elements, stored *as values* in the array. In particular, the
outer buffer exclusively owns the memory backing its boxes. When we free the
buffer, we free its boxes. When we write to a buffer at an index, allocate fresh
memory for the new box and free the old box (unless it's null, as for an
uninitialized buffer). We can still take read-only views of the data in the
boxes, but only if we know the buffer itself is immutable/frozen, because
otherwise the box memory might be freed when it's overwritten by another value,
which could happen before exiting the scope (in that sense it's no different
from taking a slice of a buffer to represent a subarray).

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
