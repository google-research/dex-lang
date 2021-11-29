-- Copyright 2021 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}

module SaferNames.Imp (toImpModule, PtrBinder, impFunType, getIType) where

import Control.Applicative
import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.Except hiding (Except)
import Data.Either

import Err
import Syntax (CallingConvention (..), Backend (..))

import SaferNames.Name
import SaferNames.Builder
import SaferNames.Syntax
import SaferNames.Type

type AtomRecon = Abs (Nest (NameBinder AtomNameC)) Atom

type PtrBinder = IBinder

toImpModule :: Distinct n
            => Bindings n -> Backend -> CallingConvention
            -> SourceName
            -> Maybe (Dest n)
            -> Abs (Nest PtrBinder) Block n
            -> (ImpFunction n, ImpModule n, AtomRecon n)
toImpModule bindings _ cc mainFunName maybeDest absBlock =
  (f', ImpModule [f'], recon')
  where
    PairE recon' f' = runImpM bindings do
      (recon, f) <- translateTopLevel cc mainFunName (fmap inject maybeDest) $
                      inject absBlock
      return $ PairE recon f

-- === ImpM monad ===

type ImpBuilderEmissions = Nest ImpDecl

newtype ImpM (n::S) (a:: *) =
  ImpM { runImpM' :: InplaceT Bindings ImpBuilderEmissions Identity n a }
  deriving ( Functor, Applicative, Monad, ScopeReader)

type SubstImpM = EnvReaderT AtomSubstVal ImpM :: S -> S -> * -> *

instance ExtOutMap Bindings ImpBuilderEmissions where
  extendOutMap bindings emissions =
    bindings `extendOutMap` toBindingsFrag emissions

class ( ImpBuilder2 m, EnvReader AtomSubstVal m
      , BindingsReader2 m, BindingsExtender2 m)
      => Imper (m::MonadKind2) where

instance BindingsReader ImpM where
  getBindings = ImpM $ getOutMapInplaceT

instance BindingsExtender ImpM where
  extendBindings frag cont = ImpM $
    extendInplaceTLocal (\bindings -> extendOutMap bindings frag) $
      withExtEvidence (toExtEvidence frag) $ runImpM' cont

instance ImpBuilder ImpM where
  emitMultiReturnInstr instr = do
    let tys = impInstrTypes instr
    ListE vs <- ImpM $
      extendInplaceT do
        scope <- getScope
        let hints = map (const "v") tys
        withManyFresh hints AtomNameRep scope \bs -> do
          let vs = nestToList (inject . nameBinderName) bs
          let impBs = makeImpBinders bs tys
          let decl = ImpLet impBs $ inject instr
          return $ DistinctAbs (Nest decl Empty) (ListE vs)
    return $ zipWith IVar vs tys
    where
     makeImpBinders :: Nest (NameBinder AtomNameC) n l -> [IType] -> Nest IBinder n l
     makeImpBinders Empty [] = Empty
     makeImpBinders (Nest b bs) (ty:tys) = Nest (IBinder b ty) $ makeImpBinders bs tys
     makeImpBinders _ _ = error "zip error"

  buildScopedImp cont = ImpM $
    locallyMutableInplaceT $ runImpM' do
      Emits <- fabricateEmitsEvidenceM
      Distinct <- getDistinct
      cont

instance ImpBuilder m => ImpBuilder (EnvReaderT AtomSubstVal m i) where
  emitMultiReturnInstr instr = EnvReaderT $ lift $ emitMultiReturnInstr instr
  buildScopedImp cont = EnvReaderT $ ReaderT \env ->
    buildScopedImp $ runEnvReaderT (inject env) $ cont

instance ImpBuilder m => Imper (EnvReaderT AtomSubstVal m)

runImpM
  :: Distinct n
  => Bindings n
  -> (Immut n => SubstImpM n n (e n))
  -> e n
runImpM bindings cont =
  withImmutEvidence (toImmutEvidence bindings) $
    case runIdentity $ runInplaceT bindings $ runImpM' $ runEnvReaderT idEnv $ cont of
      (Empty, result) -> result

-- === the actual pass ===

translateTopLevel :: (Immut o, Imper m)
                  => CallingConvention
                  -> SourceName
                  -> MaybeDest o
                  -> Abs (Nest PtrBinder) Block i
                  -> m i o (AtomRecon o, ImpFunction o)
translateTopLevel cc mainFunName maybeDest (Abs bs body) = do
  let argTys = nestToList (\b -> (getNameHint b, iBinderType b)) bs
  DistinctAbs bs' (DistinctAbs decls resultAtom) <-
    buildImpNaryAbs argTys \vs ->
      extendEnv (bs @@> map Rename vs) do
        maybeDest' <- mapM injectM maybeDest
        translateBlock maybeDest' body
  let localBindings = toBindingsFrag $ PairB bs' decls
  (results, recon) <- extendBindings localBindings $
                        buildRecon localBindings resultAtom
  let funImpl = Abs bs' $ ImpBlock decls results
  let funTy   = IFunType cc (nestToList iBinderType bs') (map getIType results)
  return (recon, ImpFunction mainFunName funTy funImpl)

buildRecon :: (HoistableB b, BindingsReader m)
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
               => MaybeDest o -> Block i -> m i o (Atom o)
translateBlock dest (Block _ decls result) = translateDeclNest decls $ translateExpr dest result

translateDeclNest :: (Imper m, Emits o) => Nest Decl i i' -> m i' o a -> m i o a
translateDeclNest Empty cont = cont
translateDeclNest (Nest decl rest) cont =
  translateDecl decl $ translateDeclNest rest cont

translateDecl :: (Imper m, Emits o) => Decl i i' -> m i' o a -> m i o a
translateDecl (Let b (DeclBinding _ _ expr)) cont = do
  ans <- translateExpr Nothing expr
  extendEnv (b @> SubstVal ans) $ cont

translateExpr :: (Imper m, Emits o) => MaybeDest o -> Expr i -> m i o (Atom o)
translateExpr maybeDest expr = case expr of
  Hof hof -> toImpHof maybeDest hof
  Atom x -> substM x >>= returnVal
  Op op -> mapM substM op >>= toImpOp maybeDest
  _ -> error $ "not implemented: " ++ pprint expr
  where
    returnVal atom = case maybeDest of
      Nothing   -> return atom
      Just dest -> copyAtom dest atom >> return atom

toImpOp :: forall m i o .
           (Imper m, Emits o) => MaybeDest o -> PrimOp (Atom o) -> m i o (Atom o)
toImpOp maybeDest op = case op of
  TabCon ~(Pi tabTy) rows -> do
    let ixTy = piArgType tabTy
    resultTy <- resultTyM
    dest <- allocDest maybeDest resultTy
    forM_ (zip [0..] rows) \(i, row) -> do
      ithDest <- destGet dest =<< intToIndexImp ixTy (IIdxRepVal i)
      copyAtom ithDest row
    destToAtom dest
  PrimEffect refDest m -> do
    case m of
      MAsk      -> returnVal =<< destToAtom refDest
  --     MExtend ~(Lam f) -> do
  --       -- TODO: Update in-place?
  --       refValue <- destToAtom refDest
  --       result <- translateBlock mempty (Nothing, snd $ applyAbs f refValue)
  --       copyAtom refDest result
  --       returnVal UnitVal
      MPut x    -> copyAtom  refDest x >> returnVal UnitVal
      MGet -> do
        resultTy <- resultTyM
        dest <- allocDest maybeDest resultTy
        -- It might be more efficient to implement a specialized copy for dests
        -- than to go through a general purpose atom.
        copyAtom dest =<< destToAtom refDest
        destToAtom dest
  UnsafeFromOrdinal n i -> returnVal =<< intToIndexImp n =<< fromScalarAtom i
  IdxSetSize n -> returnVal =<< toScalarAtom  =<< indexSetSizeImp n
  ToOrdinal idx -> case idx of
    Con (IntRangeVal   _ _   i) -> returnVal $ i
    Con (IndexRangeVal _ _ _ i) -> returnVal $ i
    _ -> returnVal =<< toScalarAtom =<< indexToIntImp idx
  Inject e -> case e of
    Con (IndexRangeVal t low _ restrictIdx) -> do
      offset <- case low of
        InclusiveLim a -> indexToIntImp a
        ExclusiveLim a -> indexToIntImp a >>= iaddI (IIdxRepVal 1)
        Unlimited      -> return (IIdxRepVal 0)
      restrictIdx' <- fromScalarAtom restrictIdx
      returnVal =<< intToIndexImp t =<< iaddI restrictIdx' offset
    Con (ParIndexCon (TC (ParIndexRange realIdxTy _ _)) i) -> do
      i' <- fromScalarAtom i
      returnVal =<< intToIndexImp realIdxTy i'
    _ -> error $ "Unsupported argument to inject: " ++ pprint e
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
  SliceOffset ~(Con (IndexSliceVal n _ tileOffset)) idx -> do
    i' <- indexToIntImp idx
    tileOffset' <- fromScalarAtom tileOffset
    i <- iaddI tileOffset' i'
    returnVal =<< intToIndexImp n i
  SliceCurry ~(Con (IndexSliceVal _ (PairTy _ v) tileOffset)) idx -> do
    vz <- intToIndexImp v $ IIdxRepVal 0
    extraOffset <- indexToIntImp (PairVal idx vz)
    tileOffset' <- fromScalarAtom tileOffset
    tileOffset'' <- iaddI tileOffset' extraOffset
    returnVal =<< toScalarAtom tileOffset''
  ThrowError _ -> undefined
  CastOp destTy x -> do
    xTy <- getType x
    case (xTy, destTy) of
      (BaseTy _, BaseTy bt) -> do
        x' <- fromScalarAtom x
        returnVal =<< toScalarAtom =<< cast x' bt
      _ -> error $ "Invalid cast: " ++ pprint xTy ++ " -> " ++ pprint destTy
  Select p x y -> do
    xTy <- getType x
    case xTy of
      BaseTy _ -> do
        p' <- fromScalarAtom p
        x' <- fromScalarAtom x
        y' <- fromScalarAtom y
        ans <- emitInstr $ IPrimOp $ Select p' x' y'
        returnVal =<< toScalarAtom ans
      _ -> do
        resultTy <- resultTyM
        dest <- allocDest maybeDest resultTy
        p' <- fromScalarAtom p
        p'' <- cast p' tagBT
        emitSwitch p'' [copyAtom dest y, copyAtom dest x]
        destToAtom dest
        where (BaseTy tagBT) = TagRepTy
  RecordCons   _ _ -> error "Unreachable: should have simplified away"
  RecordSplit  _ _ -> error "Unreachable: should have simplified away"
  VariantLift  _ _ -> error "Unreachable: should have simplified away"
  VariantSplit _ _ -> error "Unreachable: should have simplified away"
  DataConTag con -> undefined
  ToEnum ty i -> undefined
  FFICall name returnTy xs -> undefined
  SumToVariant ~(Con c) -> do
    ~resultTy@(VariantTy labs) <- resultTyM
    returnVal $ case c of
      SumCon    _ tag payload -> Variant labs "c" tag payload
      SumAsProd _ tag payload -> Con $ SumAsProd resultTy tag payload
      _ -> error $ "Not a sum type: " ++ pprint (Con c)
  _ -> do
    instr <- IPrimOp <$> mapM fromScalarAtom op
    emitInstr instr >>= toScalarAtom >>= returnVal
  where
    resultTyM :: m i o (Type o)
    resultTyM = getType $ Op op
    returnVal atom = case maybeDest of
      Nothing   -> return atom
      Just dest -> copyAtom dest atom >> return atom

toImpHof :: (Imper m, Emits o) => Maybe (Dest o) -> PrimHof (Atom i) -> m i o (Atom o)
toImpHof maybeDest hof = do
  -- TODO: it's a shame to have to substitute the whole expression just to get its type.
  -- Laziness *might* save us, but we should check.
  resultTy <- getType =<< substM (Hof hof)
  case hof of
    For (RegularFor d) (Lam (LamExpr b body)) -> do
      idxTy <- substM $ binderType b
      case idxTy of
        _ -> do
          n <- indexSetSizeImp idxTy
          dest <- allocDest maybeDest resultTy
          emitLoop (getNameHint b) d n \i -> do
            idx <- intToIndexImp (inject idxTy) i
            ithDest <- destGet (inject dest) idx
            void $ extendEnv (b @> SubstVal idx) $
              translateBlock (Just ithDest) body
          destToAtom dest

-- === Destination type ===

type Dest = Atom  -- has type `Ref a` for some a
type MaybeDest n = Maybe (Dest n)

copyAtom :: (ImpBuilder m, Emits n) => Dest n -> Atom n -> m n ()
copyAtom topDest topSrc = copyRec topDest topSrc
  where
    copyRec dest src = case (dest, src) of
      (Con destRefCon, _) -> case (destRefCon, src) of
        (BaseTypeRef ptr, _) -> do
          ptr' <- fromScalarAtom ptr
          src' <- fromScalarAtom src
          storeAnywhere ptr' src'

loadAnywhere :: (ImpBuilder m, Emits n) => IExpr n -> m n (IExpr n)
loadAnywhere _ = undefined

storeAnywhere :: (ImpBuilder m, Emits n) => IExpr n -> IExpr n -> m n ()
storeAnywhere ptr val = store ptr val

store :: (ImpBuilder m, Emits n) => IExpr n -> IExpr n -> m n ()
store dest src = emitStatement $ Store dest src

alloc :: (ImpBuilder m, Emits n) => Type n -> m n (Dest n)
alloc ty = makeAllocDest Managed ty

emitWhen :: (ImpBuilder m, Emits n)
         => IExpr n
         -> m n ()
         -> m n ()
emitWhen cond doIfTrue = emitSwitch cond [return (), doIfTrue]

-- TODO: Consider targeting LLVM's `switch` instead of chained conditionals.
emitSwitch :: (ImpBuilder m, Emits n)
           => IExpr n
           -> [m n ()]  -- <-- Need to figure out what to do here! No impredicative polymorphism
           -> m n ()
emitSwitch _ = undefined

emitLoop :: (ImpBuilder m, Emits n)
         => NameHint -> Direction -> IExpr n
         -> (forall l. (Ext n l, Distinct l, Emits l) => IExpr l -> m l ())
         -> m n ()
emitLoop hint d n body = undefined

destToAtom :: (ImpBuilder m, Emits n) => Dest n -> m n (Atom n)
destToAtom (Con dest) = do
 case dest of
   BaseTypeRef ptr -> fromScalarAtom ptr >>= load >>= toScalarAtom

destGet :: (ImpBuilder m, Emits n) => Dest n -> Atom n -> m n (Dest n)
destGet _ _ = undefined

destPairUnpack :: Dest n -> (Dest n, Dest n)
destPairUnpack (Con (ConRef (ProdCon [l, r]))) = (l, r)
destPairUnpack d = error $ "Not a pair destination: " ++ show d

fromDestConsList :: Dest n -> [Dest n]
fromDestConsList dest = case dest of
  Con (ConRef (ProdCon [h, t])) -> h : fromDestConsList t
  Con (ConRef (ProdCon []))     -> []
  _ -> error $ "Not a dest cons list: " ++ pprint dest

makeAllocDest :: (ImpBuilder m, Emits n) => AllocType -> Type n -> m n (Dest n)
makeAllocDest allocTy ty = fst <$> makeAllocDestWithPtrs allocTy ty

makeAllocDestWithPtrs :: (ImpBuilder m, Emits n)
                      => AllocType -> Type n -> m n (Dest n, [IExpr n])
makeAllocDestWithPtrs _ _ = undefined

copyDest :: (ImpBuilder m, Emits n) => Maybe (Dest n) -> Atom n -> m n (Atom n)
copyDest maybeDest atom = case maybeDest of
  Nothing   -> return atom
  Just dest -> copyAtom dest atom >> return atom

allocDest :: (ImpBuilder m, Emits n) => Maybe (Dest n) -> Type n -> m n (Dest n)
allocDest maybeDest t = case maybeDest of
  Nothing   -> alloc t
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
isSmall _ = undefined

allocateBuffer :: (ImpBuilder m, Emits n)
               => AddressSpace -> Bool -> BaseType -> IExpr n -> m n (IExpr n)
allocateBuffer _ _ _ _ = undefined

-- TODO: separate these concepts in IFunType?
deviceFromCallingConvention :: CallingConvention -> Device
deviceFromCallingConvention cc = case cc of
  CEntryFun         -> CPU
  EntryFun _        -> CPU
  FFIFun            -> CPU
  FFIMultiResultFun -> CPU
  MCThreadLaunch    -> CPU
  CUDAKernelLaunch  -> GPU

-- === Imp IR builder ===

class (BindingsReader m, BindingsExtender m) => ImpBuilder (m::MonadKind1) where
  emitMultiReturnInstr :: Emits n => ImpInstr n -> m n [IExpr n]
  buildScopedImp
    :: (InjectableE e, Immut n)
    => (forall l. (Emits l, Ext n l, Distinct l) => m l (e l))
    -> m n (DistinctAbs (Nest ImpDecl) e n)

type ImpBuilder2 (m::MonadKind2) = forall i. ImpBuilder (m i)

withFreshIBinder
  :: (Immut n, ImpBuilder m)
  => NameHint -> IType
  -> (forall l. (Immut l, Distinct l, Ext n l) => IBinder n l -> m l a)
  -> m n a
withFreshIBinder _ _ _ = undefined

buildImpAbs
  :: ( Immut n, ImpBuilder m
     , InjectableE e, HasNamesE e, SubstE Name e, HoistableE e)
  => NameHint -> IType
  -> (forall l. (Emits l, Ext n l) => AtomName l -> m l (e l))
  -> m n (DistinctAbs IBinder (DistinctAbs (Nest ImpDecl) e) n)
buildImpAbs hint ty body =
  withFreshIBinder hint ty \b -> do
    ab <- buildScopedImp $ injectM (binderName b) >>= body
    return $ DistinctAbs b ab

buildImpNaryAbs
  :: ( Immut n, ImpBuilder m
     , InjectableE e, HasNamesE e, SubstE Name e, HoistableE e)
  => [(NameHint, IType)]
  -> (forall l. (Emits l, Ext n l) => [AtomName l] -> m l (e l))
  -> m n (DistinctAbs (Nest IBinder) (DistinctAbs (Nest ImpDecl) e) n)
buildImpNaryAbs [] body = do
  Distinct <- getDistinct
  DistinctAbs Empty <$> buildScopedImp (body [])

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

extendAlloc :: (ImpBuilder m, Emits n) => IExpr n -> m n ()
extendAlloc _ = undefined

emitAlloc :: (ImpBuilder m, Emits n) => PtrType -> IExpr n -> m n (IExpr n)
emitAlloc (addr, ty) n = emitInstr $ Alloc addr ty n

buildBinOp :: (ImpBuilder m, Emits n)
           => (Atom n -> Atom n -> BuilderM n (Atom n))
           -> IExpr n -> IExpr n -> m n (IExpr n)
buildBinOp _ _ _ = undefined

iaddI :: (ImpBuilder m, Emits n) => IExpr n -> IExpr n -> m n (IExpr n)
iaddI = buildBinOp iadd

isubI :: (ImpBuilder m, Emits n) => IExpr n -> IExpr n -> m n (IExpr n)
isubI = buildBinOp isub

imulI :: (ImpBuilder m, Emits n) => IExpr n -> IExpr n -> m n (IExpr n)
imulI = buildBinOp imul

idivI :: (ImpBuilder m, Emits n) => IExpr n -> IExpr n -> m n (IExpr n)
idivI = buildBinOp idiv

iltI :: (ImpBuilder m, Emits n) => IExpr n -> IExpr n -> m n (IExpr n)
iltI = buildBinOp ilt

ieqI :: (ImpBuilder m, Emits n) => IExpr n -> IExpr n -> m n (IExpr n)
ieqI = buildBinOp ieq

bandI :: (ImpBuilder m, Emits n) => IExpr n -> IExpr n -> m n (IExpr n)
bandI x y = emitInstr $ IPrimOp $ ScalarBinOp BAnd x y

impOffset :: (ImpBuilder m, Emits n) => IExpr n -> IExpr n -> m n (IExpr n)
impOffset ref off = emitInstr $ IPrimOp $ PtrOffset ref off

cast :: (ImpBuilder m, Emits n) => IExpr n -> BaseType -> m n (IExpr n)
cast x bt = emitInstr $ ICastOp bt x

load :: (ImpBuilder m, Emits n) => IExpr n -> m n (IExpr n)
load x = emitInstr $ IPrimOp $ PtrLoad x

-- === Atom <-> IExpr conversions ===

fromScalarAtom :: BindingsReader m => Atom n -> m n (IExpr n)
fromScalarAtom atom = case atom of
  Var v -> do
    ~(BaseTy b) <- getType $ Var v
    return $ IVar v b
  Con (Lit x) -> return $ ILit x
  _ -> error $ "Expected scalar, got: " ++ pprint atom

toScalarAtom :: BindingsReader m => IExpr n -> m n (Atom n)
toScalarAtom ie = case ie of
  ILit l   -> return $ Con $ Lit l
  IVar v _ -> return $ Var v

fromScalarType :: Type n -> IType
fromScalarType (BaseTy b) =  b
fromScalarType ty = error $ "Not a scalar type: " ++ pprint ty

toScalarType :: IType -> Type n
toScalarType b = BaseTy b

-- === Type classes ===

liftBuilderImp :: (Emits n, ImpBuilder m, SubstE AtomSubstVal e, InjectableE e)
               => (forall l. (Emits l, Ext n l, Distinct l) => BuilderM l (e l))
               -> m n (e n)
liftBuilderImp cont = do
  Abs decls result <- liftImmut do
    DB bindings <- getDB
    DistinctAbs decls result <- return $ runBuilderM bindings $ buildScoped cont
    return $ Abs decls result
  runEnvReaderT idEnv $ translateDeclNest decls $ substM result

intToIndexImp :: (ImpBuilder m, Emits n) => Type n -> IExpr n -> m n (Atom n)
intToIndexImp ty i = liftBuilderImp $ intToIndex (inject ty) =<< toScalarAtom (inject i)

indexToIntImp :: (ImpBuilder m, Emits n) => Atom n -> m n (IExpr n)
indexToIntImp idx = fromScalarAtom =<< liftBuilderImp (indexToInt $ inject idx)

indexSetSizeImp :: (ImpBuilder m, Emits n) => Type n -> m n (IExpr n)
indexSetSizeImp ty = fromScalarAtom =<< liftBuilderImp (indexSetSize $ inject ty)

-- === type checking imp programs ===

instance CheckableE ImpModule where
  checkE m = substM m  -- TODO

impFunType :: ImpFunction n -> IFunType
impFunType (ImpFunction _ ty _) = ty

getIType :: IExpr n -> IType
getIType (ILit l) = litType l
getIType (IVar _ ty) = ty

impInstrTypes :: ImpInstr n -> [IType]
impInstrTypes instr = case instr of
  IPrimOp op      -> [impOpType op]
  ICastOp t _     -> [t]
  Alloc a ty _    -> [PtrType (a, ty)]
  Store _ _       -> []
  Free _          -> []
  IThrowError     -> []
  MemCopy _ _ _   -> []
  IFor _ _ _      -> []
  IWhile _        -> []
  ICond _ _ _     -> []
  ILaunch _ _ _   -> []
  ISyncWorkgroup  -> []
  IQueryParallelism _ _ -> [IIdxRepTy, IIdxRepTy]
  ICall (_, IFunType _ _ resultTys) _ -> resultTys

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
