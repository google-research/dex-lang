-- Copyright 2021 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}

module SaferNames.Imp (toImpModule, PtrBinder, impFunType, getIType) where

import Control.Category ((>>>))
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
  App f' x' -> do
    f <- substM f'
    x <- substM x'
    getType f >>= \case
      TabTy _ _ -> do
        case f of
          Lam (LamExpr b body) -> do
            body' <- applyAbs (Abs b body) (SubstVal x)
            dropSubst $ translateBlock maybeDest body'
          _ -> error $ "Invalid Imp atom: " ++ pprint f
  Atom x -> substM x >>= returnVal
  Op op -> mapM substM op >>= toImpOp maybeDest
  Case e alts ty -> do
    e' <- substM e
    case trySelectBranch e' of
      Just (con, args) -> do
        Abs bs body <- return $ alts !! con
        extendEnv (bs @@> map SubstVal args) $ translateBlock maybeDest body
      Nothing -> case e' of
        Con (SumAsProd _ tag xss) -> do
          tag' <- fromScalarAtom tag
          dest <- allocDest maybeDest =<< substM ty
          emitSwitch tag' (zip xss alts) $
            \(xs, Abs bs body) ->
               void $ extendEnv (bs @@> map (SubstVal . inject) xs) $
                 translateBlock (Just $ inject dest) body
          destToAtom dest
        _ -> error "not possible"
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
        emitSwitch p'' [x, y] (\arg -> copyAtom (inject dest) (inject arg))
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
    RunIO (Lam (LamExpr b body)) ->
      extendEnv (b@>SubstVal UnitVal) $
        translateBlock maybeDest body
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
type DestEmission = EitherE DeclBinding DestPtrInfo
data DestEmissions n l where
  DestEmissions
    :: [DestPtrInfo n]          -- pointer types and allocation sizes
    -> Nest AtomNameBinder n h  -- pointer binders
    ->   Nest Decl h l          -- decls to compute indexing offsets
    -> DestEmissions n l

instance GenericB DestEmissions where
  type RepB DestEmissions =         LiftB (ListE DestPtrInfo)
                            `PairB` Nest AtomNameBinder
                            `PairB` Nest Decl
  fromB (DestEmissions ps bs ds) = LiftB (ListE ps) `PairB` bs `PairB` ds
  toB   (LiftB (ListE ps) `PairB` bs `PairB` ds) = DestEmissions ps bs ds

instance ProvesExt   DestEmissions
instance BindsNames  DestEmissions
instance InjectableB DestEmissions
instance HoistableB  DestEmissions

instance OutFrag DestEmissions where
  emptyOutFrag = DestEmissions [] Empty Empty
  catOutFrags _ (DestEmissions p1 b1 d1) de2@(DestEmissions p2 b2 d2) =
    ignoreHoistFailure do
      ListE p2' <- hoist (PairB b1 d1) (ListE p2)
      PairB b2' d1' <- withSubscopeDistinct d2 $exchangeBs $ PairB d1 b2
      return $ DestEmissions (p1 <> p2') (b1 >>> b2') (d1' >>> d2)

newtype DestM (n::S) (a:: *) =
  DestM { runDestM' :: InplaceT Bindings DestEmissions
                         (ReaderT AllocInfo HardFailM) n a }
  deriving ( Functor, Applicative, Monad
           , ScopeReader, MonadFail, Fallible)

-- TODO: actually plumb this through the Imp monad
allocInfo :: AllocInfo
allocInfo = (LLVM, CPU, Managed)

runDestM :: (Immut n, Distinct n, InjectableE e)
         => Bindings n
         -> (forall l. (Emits l, Ext n l, Distinct l) => DestM l (e l))
         -> DistinctAbs DestEmissions e n
runDestM bindings m = do
  let result = runHardFail $ flip runReaderT allocInfo $
                 runInplaceT bindings $ locallyMutableInplaceT do
                   Emits <- fabricateEmitsEvidenceM
                   runDestM' m
  case result of
    (DestEmissions _ Empty Empty, result') -> result'

getAllocInfo :: DestM n AllocInfo
getAllocInfo = DestM $ lift1 ask

introduceNewPtr :: Mut n => NameHint -> PtrType -> Block n -> DestM n (AtomName n)
introduceNewPtr hint ptrTy numel =
  DestM $ emitInplaceT hint (DestPtrInfo ptrTy numel) \b ptrInfo ->
    DestEmissions [ptrInfo] (Nest b Empty) Empty

-- TODO: this is mostly copy-paste from Inference
buildDeclsDest
  :: (Mut n, InjectableE e)
  => (forall l. (Emits l, Ext n l, Distinct l) => DestM l (e l))
  -> DestM n (Abs (Nest Decl) e n)
buildDeclsDest cont =
  DestM $ extendInplaceT do
    resultWithEmissions <- locallyMutableInplaceT do
      Emits    <- fabricateEmitsEvidenceM
      runDestM' cont
    DistinctAbs (DestEmissions ptrInfo ptrBs decls) result <- return resultWithEmissions
    withSubscopeDistinct decls $
      return $ DistinctAbs (DestEmissions ptrInfo ptrBs Empty) $ Abs decls result

buildBlockDest
  :: Mut n
  => (forall l. (Emits l, Ext n l, Distinct l) => DestM l (Atom l))
  -> DestM n (Block n)
buildBlockDest cont = do
  Abs decls (PairE result ty) <- buildDeclsDest do
    result <- cont
    ty <- getType result
    return $ result `PairE` ty
  ty' <- liftHoistExcept $ hoist decls ty
  return $ Block ty' decls $ Atom result

-- TODO: this is mostly copy-paste from Inference
buildAbsDest
  :: (InjectableE e, HoistableE e, NameColor c, ToBinding binding c)
  => Mut n
  => NameHint -> binding n
  -> (forall l. (Mut l, Distinct l, Ext n l) => Name c l -> DestM l (e l))
  -> DestM n (Abs (BinderP c binding) e n)
buildAbsDest hint binding cont =
  DestM $ extendInplaceT do
    scope <- getScope
    withFresh hint nameColorRep scope \b -> do
      let b' = b :> inject binding
      let bExt = toBindingsFrag b'
      extendInplaceTLocal (\bindings -> extendOutMap bindings bExt) do
        DistinctAbs emissions result <- locallyMutableInplaceT do
          runDestM' $ cont $ inject $ binderName b
        PairB emissions' b'' <- liftHoistExcept $ exchangeBs $ PairB b' emissions
        withSubscopeDistinct b'' $
          return $ DistinctAbs emissions' (Abs b'' result)

buildTabLamDest
  :: Mut n
  => NameHint -> Type n
  -> (forall l. (Emits l, Ext n l, Distinct l) => AtomName l -> DestM l (Atom l))
  -> DestM n (Atom n)
buildTabLamDest hint ty body = do
  Abs (b:>_) body <- buildAbsDest hint (LamBinding TabArrow ty) \v ->
    buildBlockDest $ injectM v >>= body
  return $ Lam $ LamExpr (LamBinder b ty TabArrow Pure) body

instance BindingsExtender DestM where
  extendBindings frag cont = DestM $
    extendInplaceTLocal (\bindings -> extendOutMap bindings frag) $
      withExtEvidence (toExtEvidence frag) $
        runDestM' cont

instance BindingsReader DestM where
  getBindings = DestM $ getOutMapInplaceT

instance Builder DestM where
  emitDecl hint ann expr = do
    ty <- getType expr
    DestM $ emitInplaceT hint (DeclBinding ann ty expr) \b binding ->
      DestEmissions [] Empty $ Nest (Let b binding) Empty

  -- We can't implement this because we'd have to throw away the pointer
  -- binders. Maybe we should split builder into a separate decl-emitting thing
  -- and a scoping thing.
  buildScoped _ = error "not implemented"

instance ExtOutMap Bindings DestEmissions where
  extendOutMap bindings (DestEmissions ptrInfo ptrs decls) =
    withSubscopeDistinct decls $
      (bindings `extendOutMap` ptrBindersToBindingsFrag ptrInfo ptrs)
                `extendOutMap` decls
   where
     ptrBindersToBindingsFrag :: Distinct l => [DestPtrInfo n] -> Nest AtomNameBinder n l -> BindingsFrag n l
     ptrBindersToBindingsFrag [] Empty = emptyOutFrag
     ptrBindersToBindingsFrag (DestPtrInfo ty _ : rest) (Nest b restBs) =
       withSubscopeDistinct restBs do
         let frag1 = toBindingsFrag $ b :> PtrTy ty
         let frag2 = withExtEvidence (toExtEvidence b) $
                        ptrBindersToBindingsFrag (map inject rest) restBs
         frag1 `catBindingsFrags` frag2


instance GenericE DestPtrInfo where
  type RepE DestPtrInfo = PairE (LiftE PtrType) Block
  fromE (DestPtrInfo ty n) = PairE (LiftE ty) n
  toE   (PairE (LiftE ty) n) = DestPtrInfo ty n

instance InjectableE DestPtrInfo
instance HoistableE  DestPtrInfo
instance SubstE Name DestPtrInfo
instance SubstE AtomSubstVal DestPtrInfo

-- === Destination builder ===

type Dest = Atom  -- has type `Ref a` for some a
type MaybeDest n = Maybe (Dest n)

type IdxNest = Nest Binder
type Idxs n = [AtomName n]

data AbsPtrs e n = AbsPtrs (NaryAbs AtomNameC e n) [DestPtrInfo n]

instance GenericE (AbsPtrs e) where
  type RepE (AbsPtrs e) = PairE (NaryAbs AtomNameC e) (ListE DestPtrInfo)
  fromE (AbsPtrs ab ptrInfo) = PairE ab (ListE ptrInfo)
  toE   (PairE ab (ListE ptrInfo)) = AbsPtrs ab ptrInfo

instance InjectableE e => InjectableE (AbsPtrs e)
instance SubstE Name e => SubstE Name (AbsPtrs e)
instance SubstE AtomSubstVal e => SubstE AtomSubstVal (AbsPtrs e)

-- builds a dest and a list of pointer binders along with their required allocation sizes
makeDest :: (Emits n, ImpBuilder m, BindingsReader m)
         => AllocInfo -> Type n -> m n (AbsPtrs Dest n)
makeDest allocInfo ty = do
  Abs decls result <- liftImmut do
    DB bindings <- getDB
    DistinctAbs (DestEmissions ptrInfo ptrBs decls) result <-
      return $ runDestM bindings do
        makeDestRec [] Empty =<< injectM ty
    case exchangeBs $ PairB ptrBs decls of
      HoistFailure _ -> error "shouldn't happen"
      HoistSuccess (PairB decls' ptrBs') ->
        withExtEvidence (toExtEvidence decls') $ withSubscopeDistinct ptrBs' $
          return $ Abs decls' $ AbsPtrs (Abs ptrBs' result) (map inject ptrInfo)
  runEnvReaderT idEnv $ translateDeclNest decls $ substM result

makeDestRec :: forall n l.
               Emits n => Idxs n -> IdxNest n l -> Type l -> DestM n (Dest n)
makeDestRec idxs idxBinders ty = case ty of
  TabTy (PiBinder b iTy _) bodyTy -> do
    Distinct <- getDistinct
    iTy' <- applyCurIdxs iTy
    lam <- buildTabLamDest "i" (inject iTy') \v -> do
      let idxs' = map inject idxs <> [v]
      Abs idxBinders' bodyTy' <- injectM $ Abs (idxBinders >>> Nest (b:>iTy) Empty) bodyTy
      makeDestRec idxs' idxBinders' bodyTy'
    return $ Con $ TabRef lam
  TypeCon _ _ -> do
    Abs idxBinders' (ListE dcs) <- liftImmut do
      refreshAbsM (inject $ Abs idxBinders ty) \idxBinders' (TypeCon def params) -> do
        dcs <- applyDataDefParams (snd def) params
        return $ Abs idxBinders' $ ListE dcs
    case dcs of
      [] -> error "Void type not allowed"
      [_] -> error "not implemented"
      _ -> do
        tag <- rec TagRepTy
        ty' <- applyCurIdxs ty
        contents <- forM dcs \dc -> case nonDepDataConTys dc of
          Nothing -> error "Dependent data constructors only allowed for single-constructor types"
          Just tys -> mapM (makeDestRec idxs idxBinders') tys
        return $ Con $ ConRef $ SumAsProd ty' tag contents
  TC con -> case con of
    BaseType b -> do
      ptr <- makeBaseTypePtr idxs idxBinders b
      return $ Con $ BaseTypeRef ptr
    ProdType tys  -> (Con . ConRef) <$> (ProdCon <$> traverse rec tys)
    IntRange l h -> do
      l' <- applyCurIdxs l
      h' <- applyCurIdxs h
      x <- rec IdxRepTy
      return $ Con $ ConRef $ IntRangeVal l' h' x
    IndexRange t l h -> do
      t' <- applyCurIdxs t
      l' <- mapM applyCurIdxs l
      h' <- mapM applyCurIdxs h
      x <- rec IdxRepTy
      return $ Con $ ConRef $ IndexRangeVal t' l' h' x
    _ -> error $ "not implemented: " ++ pprint con
  _ -> error $ "not implemented: " ++ pprint ty
  where
    applyCurIdxs :: (InjectableE e, SubstE Name e) => e l -> DestM n (e n)
    applyCurIdxs x = applyNaryAbs (Abs idxBinders x) idxs

    rec = makeDestRec idxs idxBinders

makeBaseTypePtr :: Emits n => Idxs n -> IdxNest n l -> BaseType -> DestM n (Atom n)
makeBaseTypePtr idxs idxBinders ty = do
  numel <- buildBlockDest do
    elemCount =<< injectM (Abs idxBinders UnitE)
  allocInfo <- getAllocInfo
  let addrSpace = chooseAddrSpace allocInfo numel
  let ptrTy = (addrSpace, ty)
  ptr <- introduceNewPtr "ptr" ptrTy numel
  applyIdxs idxs idxBinders $ Var ptr

elemCount :: (Emits n, Builder m) => EmptyAbs IdxNest n -> m n (Atom n)
elemCount (Abs idxs UnitE) = case idxs of
  Empty -> return $ IdxRepVal 1
  Nest (b:>ixTy) rest -> case hoist b $ Abs rest UnitE of
    HoistSuccess rest' -> do
      n1 <- indexSetSize ixTy
      n2 <- elemCount rest'
      imul n1 n2
    HoistFailure _ -> error "can't handle dependent tables"

applyIdxs :: (Emits n, Builder m) => Idxs n -> IdxNest n l -> Atom n -> m n (Atom n)
applyIdxs [] Empty ptr = return ptr
applyIdxs (ix:ixs) (Nest b rest) ptr =
  case hoist b (Abs rest UnitE) of
    HoistSuccess (Abs rest' UnitE) -> do
      stride <- elemCount $ Abs rest' UnitE
      ordinal <- indexToInt $ Var ix
      offset <- imul stride ordinal
      ptr' <- ptrOffset ptr offset
      applyIdxs ixs rest' ptr'
    HoistFailure _ -> error "can't handle dependent tables"

copyAtom :: (ImpBuilder m, Emits n) => Dest n -> Atom n -> m n ()
copyAtom topDest topSrc = copyRec topDest topSrc
  where
    copyRec :: (ImpBuilder m, Emits n) => Dest n -> Atom n -> m n ()
    copyRec dest src = case (dest, src) of
      (Con destRefCon, _) -> case (destRefCon, src) of
        (BaseTypeRef ptr, _) -> do
          ptr' <- fromScalarAtom ptr
          src' <- fromScalarAtom src
          storeAnywhere ptr' src'
        (ConRef (SumAsProd _ tag payload), DataCon _ _ _ con x) -> do
          rec tag $ TagRepVal $ fromIntegral con
          zipWithM_ rec (payload !! con) x
        _ -> error $ "not implemented " ++ pprint dest
      (DataConRef _ _ refs, DataCon _ _ _ _ vals) -> copyDataConArgs refs vals
      _ -> error $ "not implemented " ++ pprint dest
      where
        rec = copyRec

copyDataConArgs :: (ImpBuilder m, Emits n)
                => EmptyAbs (Nest DataConRefBinding) n -> [Atom n] -> m n ()
copyDataConArgs (Abs Empty UnitE) [] = return ()
copyDataConArgs (Abs (Nest (DataConRefBinding b ref) rest) UnitE) (x:xs) = do
  copyAtom ref x
  rest' <- applyAbs (Abs b $ EmptyAbs rest) (SubstVal x)
  copyDataConArgs rest' xs
copyDataConArgs bindings args =
  error $ "Mismatched bindings/args: " ++ pprint (bindings, args)

loadAnywhere :: (ImpBuilder m, Emits n) => IExpr n -> m n (IExpr n)
loadAnywhere ptr = load ptr -- TODO: generalize to GPU backend

storeAnywhere :: (ImpBuilder m, Emits n) => IExpr n -> IExpr n -> m n ()
storeAnywhere ptr val = store ptr val

store :: (ImpBuilder m, Emits n) => IExpr n -> IExpr n -> m n ()
store dest src = emitStatement $ Store dest src

alloc :: (ImpBuilder m, Emits n) => Type n -> m n (Dest n)
alloc ty = makeAllocDest Managed ty

indexDest :: (Builder m, Emits n) => Dest n -> Atom n -> m n (Dest n)
indexDest (Con (TabRef (Lam (LamExpr b body)))) i = do
  body' <- applyAbs (Abs b body) $ SubstVal i
  emitBlock body'
indexDest dest _ = error $ pprint dest

loadDest :: (Builder m, Emits n) => Dest n -> m n (Atom n)
loadDest (Con dest) = do
 case dest of
   BaseTypeRef ptr -> unsafePtrLoad ptr
   TabRef (Lam (LamExpr b body)) ->
     buildLam (getNameHint b) TabArrow (binderType b) Pure \i -> do
       Distinct <- getDistinct
       body' <- applyAbs (inject $ Abs b body) i
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

emitWhen :: (ImpBuilder m, Emits n)
         => IExpr n
         -> (forall l. (Emits l, Ext n l, Distinct l) => m l ())
         -> m n ()
emitWhen cond doIfTrue =
  emitSwitch cond [False, True] \case False -> return ()
                                      True  -> doIfTrue

-- TODO: Consider targeting LLVM's `switch` instead of chained conditionals.
emitSwitch :: forall m n a.
              (ImpBuilder m, Emits n)
           => IExpr n
           -> [a]
           -> (forall l. (Emits l, Ext n l, Distinct l) => a -> m l ())
           -> m n ()
emitSwitch testIdx args cont = do
  Distinct <- getDistinct
  rec 0 args
  where
    rec :: forall l. (Emits l, Ext n l, Distinct l) => Int -> [a] -> m l ()
    rec _ [] = error "Shouldn't have an empty list of alternatives"
    rec _ [arg] = cont arg
    rec curIdx (arg:rest) = do
      curTag     <- fromScalarAtom $ TagRepVal $ fromIntegral curIdx
      cond       <- emitInstr $ IPrimOp $ ScalarBinOp (ICmp Equal) (inject testIdx) curTag
      thisCase   <- buildBlockImp $ cont arg >> return []
      otherCases <- buildBlockImp $ rec (curIdx + 1) rest >> return []
      emitStatement $ ICond cond thisCase otherCases

emitLoop :: (ImpBuilder m, Emits n)
         => NameHint -> Direction -> IExpr n
         -> (forall l. (Ext n l, Distinct l, Emits l) => IExpr l -> m l ())
         -> m n ()
emitLoop hint d n cont = do
  loopBody <- liftImmut do
    withFreshIBinder hint (getIType n) \b@(IBinder _ ty)  -> do
      let i = IVar (binderName b) ty
      body <- buildBlockImp do
                cont =<< injectM i
                return []
      return $ Abs b body
  emitStatement $ IFor d n loopBody

buildBlockImp
  :: ImpBuilder m
  => (forall l. (Emits l, Ext n l, Distinct l) => m l [IExpr l])
  -> m n (ImpBlock n)
buildBlockImp cont = liftImmut do
  DistinctAbs decls (ListE results) <- buildScopedImp $ ListE <$> cont
  return $ ImpBlock decls results

destToAtom :: (ImpBuilder m, Emits n) => Dest n -> m n (Atom n)
destToAtom dest = liftBuilderImp $ loadDest $ inject dest

destGet :: (ImpBuilder m, Emits n) => Dest n -> Atom n -> m n (Dest n)
destGet dest i = liftBuilderImp $ indexDest (inject dest) (inject i)

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
makeAllocDestWithPtrs allocTy ty = do
  let backend = undefined
  let curDev = undefined
  AbsPtrs absDest ptrDefs <- makeDest (backend, curDev, allocTy) ty
  ptrs <- forM ptrDefs \(DestPtrInfo ptrTy sizeBlock) -> do
    size <- liftBuilderImp $ emitBlock $ inject sizeBlock
    emitAlloc ptrTy =<< fromScalarAtom size
  ptrAtoms <- mapM toScalarAtom ptrs
  dest' <- applyNaryAbs absDest $ map SubstVal ptrAtoms
  return (dest', ptrs)

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
isSmall numel = case numel of
  Block _ Empty (Atom (Con (Lit l))) | getIntLit l <= 256 -> True
  _ -> False

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
withFreshIBinder hint ty cont = do
  scope    <- getScope
  Distinct <- getDistinct
  withFresh hint nameColorRep scope \b -> do
    extendBindings (toBindingsFrag (b :> (toBinding $ MiscBound $ BaseTy ty))) $
      cont $ IBinder b ty

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
