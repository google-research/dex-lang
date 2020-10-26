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

import Embed
import Syntax
import Env
import Type
import PPrint
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
data ImpCtx = ImpCtx { impBackend :: Backend
                     , curDevice  :: Device
                     , curLevel   :: ParallelismLevel }
data ImpCatEnv = ImpCatEnv
  { envPtrsToFree :: [IExpr]
  , envScope      :: Scope
  , envDecls      :: [ImpDecl]
  , envFunctions  :: Env ImpFunction }

type ImpM = ExceptT () (ReaderT ImpCtx (Cat ImpCatEnv))
type AtomRecon = Abs (Nest Binder) Atom

toImpModule :: Backend -> CallingConvention -> Name
            -> [IBinder] -> Maybe Dest -> Block
            -> (ImpFunction, ImpModule, AtomRecon)
toImpModule backend cc entryName argBinders maybeDest block =
  runImpM initOpts inVarScope $ do
    (reconAtom, impBlock) <- scopedBlock $ translateTopLevel (maybeDest, block)
    functions <- toList <$> looks envFunctions
    let ty = IFunType cc (map binderAnn argBinders) (impBlockType impBlock)
    let mainFunction = ImpFunction (entryName:>ty) argBinders impBlock
    return (mainFunction, ImpModule (functions ++ [mainFunction]), reconAtom)
  where
    inVarScope :: Scope  -- TODO: fix (shouldn't use UnitTy)
    inVarScope = binderScope <> destScope
    binderScope = foldMap binderAsEnv $ fmap (fmap $ const (UnitTy, UnknownBinder)) argBinders
    destScope = fromMaybe mempty $ fmap freeVars maybeDest
    initOpts = ImpCtx backend CPU TopLevel

-- We don't emit any results when a destination is provided, since they are already
-- going to be available through the dest.
translateTopLevel :: WithDest Block -> ImpM (AtomRecon, [IExpr])
translateTopLevel (maybeDest, block) = do
  outDest <- case maybeDest of
        Nothing   -> allocKind Unmanaged $ getType block
        Just dest -> return dest
  handleErrors $ void $ translateBlock mempty (Just outDest, block)
  resultAtom <- destToAtom outDest
  let vsOut = envAsVars $ freeVars resultAtom
  let reconAtom = Abs (toNest $ [Bind (v:>ty) | (v:>(ty, _)) <- vsOut]) resultAtom
  let resultIExprs = case maybeDest of
        Nothing -> [IVar (v:>fromScalarType ty) | (v:>(ty, _)) <- vsOut]
        Just _  -> []
  return (reconAtom, resultIExprs)

runImpM :: ImpCtx -> Scope -> ImpM a -> a
runImpM opts inVarScope m =
  fromRight (error "Unexpected top level error") $
    fst $ runCat (runReaderT (runExceptT m) opts) $ mempty {envScope = inVarScope}

translateBlock :: SubstEnv -> WithDest Block -> ImpM Atom
translateBlock env destBlock = do
  let (decls, result, copies) = splitDest destBlock
  env' <- (env<>) <$> catFoldM translateDecl env decls
  forM_ copies $ \(dest, atom) -> copyAtom dest =<< impSubst env' atom
  translateExpr env' result

translateDecl :: SubstEnv -> WithDest Decl -> ImpM SubstEnv
translateDecl env (maybeDest, (Let _ b bound)) = do
  b' <- traverse (impSubst env) b
  ans <- translateExpr env (maybeDest, bound)
  return $ b' @> ans
translateDecl env (maybeDest, (Unpack bs bound)) = do
  bs' <- mapM (traverse (impSubst env)) bs
  expr <- translateExpr env (maybeDest, bound)
  case expr of
    DataCon _ _ _ ans -> return $ newEnv bs' ans
    Record items -> return $ newEnv bs $ toList items
    _ -> error "Unsupported type in an Unpack binding"

translateExpr :: SubstEnv -> WithDest Expr -> ImpM Atom
translateExpr env (maybeDest, expr) = case expr of
  Hof hof     -> toImpHof env (maybeDest, hof)
  App x' idx' -> case getType x' of
    TabTy _ _ -> do
      x <- impSubst env x'
      idx <- impSubst env idx'
      case x of
        Lam a@(Abs _ (TabArrow, _)) ->
          translateBlock mempty (maybeDest, snd $ applyAbs a idx)
        _ -> error $ "Invalid Imp atom: " ++ pprint x
    _ -> error $ "shouldn't have non-table app left"
  Atom x   -> copyDest maybeDest =<< impSubst env x
  Op   op  -> toImpOp . (maybeDest,) =<< traverse (impSubst env) op
  Case e alts _ -> do
    e' <- impSubst env e
    case e' of
      DataCon _ _ con args -> do
        let Abs bs body = alts !! con
        translateBlock (env <> newEnv bs args) (maybeDest, body)
      Variant (NoExt types) label i x -> do
        let LabeledItems ixtypes = enumerate types
        let index = fst $ ixtypes M.! label NE.!! i
        let Abs bs body = alts !! index
        translateBlock (env <> newEnv bs [x]) (maybeDest, body)
      Con (SumAsProd _ tag xss) -> do
        let tag' = fromScalarAtom tag
        dest <- allocDest maybeDest $ getType expr
        emitSwitch tag' $ flip map (zip xss alts) $
          \(xs, Abs bs body) ->
             void $ translateBlock (env <> newEnv bs xs) (Just dest, body)
        destToAtom dest
      _ -> error $ "Unexpected scrutinee: " ++ pprint e'

launchKernel :: SubstEnv -> WithDest Atom -> ImpM Atom
launchKernel env (maybeDest, ~lbody@(LamVal b body)) = do
  opts  <- ask
  idxTy <- impSubst env $ binderType b
  n     <- indexSetSize idxTy
  dest  <- allocDest maybeDest $ getType $ Hof $ For ParallelFor lbody
  i     <- freshVar $ binderNameHint b:>getIType n
  tid   <- freshVar $ "tid":>getIType n
  let (cc, dev) = case impBackend opts of
        LLVMCUDA -> (CUDAKernelLaunch, GPU)
        LLVMMC   -> (MCThreadLaunch  , CPU)
        backend -> error $ "Shouldn't be launching kernels from " ++ show backend
  kernelBody <- withDevice dev $ withLevel ThreadLevel $ scopedErrBlock $ do
    idx <- intToIndex idxTy $ IVar i
    ithDest <- destGet dest idx
    void $ translateBlock (env <> b @> idx) (Just ithDest, body)
  let args = envAsVars $ freeIVars kernelBody `envDiff` (i @> ())
  f <- emitFunction cc (map Bind (tid:i:args)) kernelBody
  emitStatement $ ILaunch f n $ map IVar args
  destToAtom dest

emitFunction :: CallingConvention -> [IBinder] -> ImpBlock -> ImpM IFunVar
emitFunction cc bs body = do
  funEnv <- looks envFunctions
  let name = genFresh (Name TopFunctionName "kernel" 0) funEnv
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
    forM_ (zip [0..] rows) $ \(i, row) -> do
      ithDest <- destGet dest =<< intToIndex (binderType b) (IIdxRepVal i)
      copyAtom ithDest row
    destToAtom dest
  Fst ~(PairVal x _) -> returnVal x
  Snd ~(PairVal _ y) -> returnVal y
  PrimEffect refDest m -> do
    case m of
      MAsk    -> returnVal =<< destToAtom refDest
      MTell x -> addToAtom refDest x >> returnVal UnitVal
      MPut x  -> copyAtom  refDest x >> returnVal UnitVal
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
  Inject e -> do
    let (TC (IndexRange t low _)) = getType e
    offset <- case low of
      InclusiveLim a -> indexToInt a
      ExclusiveLim a -> indexToInt a >>= iaddI (IIdxRepVal 1)
      Unlimited      -> return (IIdxRepVal 0)
    restrictIdx <- indexToInt e
    idx <- iaddI restrictIdx offset
    returnVal =<< intToIndex t idx
  IndexRef refDest i -> returnVal =<< destGet refDest i
  FstRef ~(Con (ConRef (PairCon ref _  ))) -> returnVal ref
  SndRef ~(Con (ConRef (PairCon _   ref))) -> returnVal ref
  PtrOffset arr off -> do
    buf <- impOffset (fromScalarAtom arr) (fromScalarAtom off)
    returnVal $ toScalarAtom buf
  PtrLoad arr -> returnVal . toScalarAtom =<< loadAnywhere (fromScalarAtom arr)
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
  FFICall name returnTy xs -> do
    let returnTys = fromScalarOrPairType returnTy
    let xTys = map (fromScalarType . getType) xs
    f <- emitFFIFunction name xTys returnTys
    results <- emitMultiReturnInstr $ ICall f $ map fromScalarAtom xs
    returnVal $ restructureScalarOrPairType returnTy results
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
    For ParallelFor body -> do
      backend <- asks impBackend
      level   <- asks curLevel
      unless (  level == TopLevel
             && backend `elem` [LLVMCUDA, LLVMMC]
             && isPure (Hof hof)) $ error "Invalid kernel launch"
      launchKernel env (maybeDest, body)
    For (RegularFor d) (LamVal b body) -> do
      idxTy <- impSubst env $ binderType b
      n' <- indexSetSize idxTy
      dest <- allocDest maybeDest resultTy
      emitLoop (binderNameHint b) d n' $ \i -> do
        idx <- intToIndex idxTy i
        ithDest <- destGet dest idx
        void $ translateBlock (env <> b @> idx) (Just ithDest, body)
      destToAtom dest
    Tile d (LamVal tb tBody) (LamVal sb sBody) -> do
      ~(TC (IndexSlice idxTy tileIdxTy)) <- impSubst env $ binderType tb
      n <- indexSetSize idxTy
      dest <- allocDest maybeDest resultTy
      tileLen <- indexSetSize tileIdxTy
      nTiles      <- n `idivI` tileLen
      epilogueOff <- nTiles `imulI` tileLen
      nEpilogue   <- n `isubI` epilogueOff
      emitLoop (binderNameHint tb) Fwd nTiles $ \iTile -> do
        tileOffset <- toScalarAtom <$> iTile `imulI` tileLen
        let tileAtom = Con $ IndexSliceVal idxTy tileIdxTy tileOffset
        tileDest <- fromEmbed $ sliceDestDim d dest tileOffset tileIdxTy
        void $ translateBlock (env <> tb @> tileAtom) (Just tileDest, tBody)
      emitLoop (binderNameHint sb) Fwd nEpilogue $ \iEpi -> do
        i <- iEpi `iaddI` epilogueOff
        idx <- intToIndex idxTy i
        sDest <- fromEmbed $ indexDestDim d dest idx
        void $ translateBlock (env <> sb @> idx) (Just sDest, sBody)
      destToAtom dest
    While (Lam (Abs _ (_, cond))) (Lam (Abs _ (_, body))) -> do
      cond' <- liftM snd $ scopedBlock $ do
                 ans <- translateBlock env (Nothing, cond)
                 return ((), [fromScalarAtom ans])
      body' <- scopedErrBlock $ void $ translateBlock env (Nothing, body)
      emitStatement $ IWhile cond' body'
      return UnitVal
    RunReader r (BinaryFunVal _ ref _ body) -> do
      rDest <- alloc $ getType r
      copyAtom rDest =<< impSubst env r
      translateBlock (env <> ref @> rDest) (maybeDest, body)
    RunWriter (BinaryFunVal _ ref _ body) -> do
      (aDest, wDest) <- destPairUnpack <$> allocDest maybeDest resultTy
      let RefTy _ wTy = getType ref
      copyAtom wDest (zeroAt wTy)
      void $ translateBlock (env <> ref @> wDest) (Just aDest, body)
      PairVal <$> destToAtom aDest <*> destToAtom wDest
    RunState s (BinaryFunVal _ ref _ body) -> do
      (aDest, sDest) <- destPairUnpack <$> allocDest maybeDest resultTy
      copyAtom sDest =<< impSubst env s
      void $ translateBlock (env <> ref @> sDest) (Just aDest, body)
      PairVal <$> destToAtom aDest <*> destToAtom sDest
    _ -> error $ "Invalid higher order function primitive: " ++ pprint hof

-- === Destination type ===

type Dest = Atom  -- has type `Ref a` for some a
type WithDest a = (Maybe Dest, a)

data DestEnv = DestEnv
       { _allocationInfo :: AllocInfo
       , enclosingIdxs :: IndexStructure
       , destDepVars :: Env () }

-- The Cat env carries names for the pointers needed, along with their types and
-- blocks that compute allocation sizes needed
type DestM = ReaderT DestEnv (CatT (Env (Type, Block)) Embed)

-- builds a dest and a list of pointer binders along with their required allocation sizes
makeDest :: AllocInfo -> Type -> Embed ([(Binder, Atom)], Dest)
makeDest allocInfo ty = do
  (dest, ptrs) <- flip runCatT mempty $ flip runReaderT env $ makeDestRec ty
  ptrs' <- forM (envPairs ptrs) $ \(v, (ptrTy, numel)) -> do
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
        lam <- buildLam (Bind ("i":> binderAnn b)) TabArrow $ \(Var i) -> do
          bodyTy' <- substEmbed (b@>Var i) bodyTy
          withEnclosingIdxs (Bind i) $ makeDestRec bodyTy'
        return $ Con $ TabRef lam
  TypeCon def params -> do
    let dcs = applyDataDefParams def params
    case dcs of
      [] -> error "Void type not allowed"
      [DataConDef _ bs] -> do
        dests <- makeDataConDest bs
        return $ DataConRef def params dests
      _ -> do
        when (any isDependent dcs) $ error
          "Dependent data constructors only allowed for single-constructor types"
        tag <- rec TagRepTy
        let dcs' = applyDataDefParams def params
        contents <- forM dcs' $ \(DataConDef _ bs) -> forM (toList bs) (rec . binderType)
        return $ Con $ ConRef $ SumAsProd ty tag contents
  RecordTy (NoExt types) -> (Con . RecordRef) <$> forM types rec
  VariantTy (NoExt types) -> do
    tag <- rec TagRepTy
    contents <- forM (toList types) rec
    return $ Con $ ConRef $ SumAsProd ty tag $ map (\x->[x]) contents
  TC con -> case con of
    BaseType b -> do
      ptr <- makeBaseTypePtr b
      return $ Con $ BaseTypeRef ptr
    PairType a b -> (Con . ConRef) <$> (PairCon <$> rec a <*> rec b)
    UnitType     -> (Con . ConRef) <$> return UnitCon
    CharType     -> (Con . ConRef . CharCon) <$> rec (BaseTy $ Scalar Int8Type)
    IntRange     l h -> (Con . ConRef . IntRangeVal     l h) <$> rec IdxRepTy
    IndexRange t l h -> (Con . ConRef . IndexRangeVal t l h) <$> rec IdxRepTy
    _ -> error $ "not implemented: " ++ pprint con
  _ -> error $ "not implemented: " ++ pprint ty
  where rec = makeDestRec

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
  ptrScope <- fmap (const (UnitTy, UnknownBinder)) <$> look
  scope <- getScope
  -- We use a different namespace because these will be hoisted to the top
  -- where they could cast shadows
  let addrSpace = chooseAddrSpace allocInfo numel
  let ptrName = genFresh (Name AllocPtrName "ptr" 0) (scope <> ptrScope)
  let ptrTy = PtrTy (AllocatedPtr, addrSpace, ty)
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
  v <- freshVarE UnknownBinder b  -- TODO: scope names more carefully
  rest'  <- substEmbed (b @> Var v) rest
  rest'' <- withDepVar (Bind v) $ makeDataConDest rest'
  return $ Nest (DataConRefBinding (Bind v) dest) rest''

copyAtom :: Dest -> Atom -> ImpM ()
copyAtom (BoxedRef b ptrPtr size body) src = do
  -- TODO: load old ptr and free (recursively)
  let PtrTy ptrTy = binderAnn b
  size' <- translateBlock mempty (Nothing, size)
  ptr <- emitAlloc ptrTy $ fromScalarAtom size'
  body' <- impSubst (b@>toScalarAtom ptr) body
  copyAtom body' src
  storeAnywhere (fromScalarAtom ptrPtr) ptr
copyAtom (DataConRef _ _ refs) (DataCon _ _ _ vals) = copyDataConArgs refs vals
copyAtom (Con dest) src = case (dest, src) of
  (BaseTypeRef ptr, _) -> storeAnywhere (fromScalarAtom ptr) (fromScalarAtom src)
  (TabRef _, TabVal _ _) -> zipTabDestAtom copyAtom (Con dest) src
  (ConRef (SumAsProd _ tag payload), DataCon _ _ con x) -> do
    copyAtom tag (TagRepVal $ fromIntegral con)
    zipWithM_ copyAtom (payload !! con) x
  (ConRef destCon, Con srcCon) -> zipWithRefConM copyAtom destCon srcCon
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

copyDataConArgs :: Nest DataConRefBinding -> [Atom] -> ImpM ()
copyDataConArgs Empty [] = return ()
copyDataConArgs (Nest (DataConRefBinding b ref) rest) (x:xs) = do
  copyAtom ref x
  rest' <- impSubst (b@>x) rest
  copyDataConArgs rest' xs
copyDataConArgs bindings args =
  error $ "Mismatched bindings/args: " ++ pprint (bindings, args)

loadDest :: MonadEmbed m => Dest -> m Atom
loadDest (BoxedRef b ptrPtr _ body) = do
  ptr <- ptrLoad ptrPtr
  body' <- substEmbed (b@>ptr) body
  loadDest body'
loadDest (DataConRef def params bs) = do
  DataCon def params 0 <$> loadDataConArgs bs
loadDest (Con dest) = do
 case dest of
  BaseTypeRef ptr -> ptrLoad ptr
  TabRef (TabVal b body) -> buildLam b TabArrow $ \i -> do
    body' <- substEmbed (b@>i) body
    result <- emitBlock body'
    loadDest result
  RecordRef xs -> Record <$> traverse loadDest xs
  ConRef con -> Con <$> case con of
    PairCon d1 d2 -> PairCon <$> loadDest d1 <*> loadDest d2
    UnitCon -> return UnitCon
    SumAsProd ty tag xss -> SumAsProd ty <$> loadDest tag <*> mapM (mapM loadDest) xss
    IntRangeVal     l h iRef -> IntRangeVal     l h <$> loadDest iRef
    IndexRangeVal t l h iRef -> IndexRangeVal t l h <$> loadDest iRef
    CharCon d -> CharCon <$> loadDest d
    _        -> error $ "Not a valid dest: " ++ pprint dest
  _          -> error $ "Not a valid dest: " ++ pprint dest
loadDest dest = error $ "Not a valid dest: " ++ pprint dest

loadDataConArgs :: MonadEmbed m => Nest DataConRefBinding -> m [Atom]
loadDataConArgs Empty = return []
loadDataConArgs (Nest (DataConRefBinding b ref) rest) = do
  val <- loadDest ref
  rest' <- substEmbed (b@>val) rest
  (val:) <$> loadDataConArgs rest'

indexDestDim :: MonadEmbed m => Int->Dest -> Atom -> m Dest
indexDestDim 0 dest i = indexDest dest i
indexDestDim d dest i = buildFor Fwd (Bind ("i":>idxTy)) $ \j -> do
  dest' <- indexDest dest j
  indexDestDim (d-1) dest' i
  where
    RawRefTy (TabTy idxBinder _) = dest
    idxTy = binderType idxBinder

indexDest :: MonadEmbed m => Dest -> Atom -> m Dest
indexDest (Con (TabRef tabVal)) i = appReduce tabVal i
indexDest dest _ = error $ pprint dest

sliceDestDim :: MonadEmbed m => Int -> Dest -> Atom -> Type -> m Dest
sliceDestDim 0 dest i sliceIdxTy = sliceDest dest i sliceIdxTy
sliceDestDim d dest i sliceIdxTy = buildFor Fwd (Bind ("i":>idxTy)) $ \j -> do
  dest' <- indexDest dest j
  sliceDestDim (d-1) dest' i sliceIdxTy
  where
    RawRefTy (TabTy idxBinder _) = dest
    idxTy = binderType idxBinder

sliceDest :: MonadEmbed m => Dest -> Atom -> Type -> m Dest
sliceDest ~(Con (TabRef tab@(TabVal b _))) i sliceIdxTy = (Con . TabRef) <$> do
  buildFor Fwd (Bind ("j" :> sliceIdxTy)) $ \j -> do
    j' <- indexToIntE j
    ioff <- iadd j' i
    vidx <- intToIndexE (binderType b) ioff
    appReduce tab vidx

destToAtom :: Dest -> ImpM Atom
destToAtom dest = fromEmbed $ loadDest dest

destGet :: Dest -> Atom -> ImpM Dest
destGet dest i = fromEmbed $ indexDest dest i

destPairUnpack :: Dest -> (Dest, Dest)
destPairUnpack (Con (ConRef (PairCon l r))) = (l, r)
destPairUnpack d = error $ "Not a pair destination: " ++ show d

makeAllocDest :: AllocType -> Type -> ImpM Dest
makeAllocDest allocTy ty = do
  backend <- asks impBackend
  curDev <- asks curDevice
  (ptrsSizes, dest) <- fromEmbed $ makeDest (backend, curDev, allocTy) ty
  env <- flip foldMapM ptrsSizes $ \(Bind (ptr:>PtrTy ptrTy), size) -> do
    ptr' <- emitAlloc ptrTy $ fromScalarAtom size
    case ptrTy of
      (_, Heap _, _) | allocTy == Managed -> extendAlloc ptr'
      _ -> return ()
    return (ptr @> toScalarAtom ptr')
  impSubst env dest

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

      let destDecls = flip fmap (toList decls) $ \d -> case d of
                        Let _ b _  -> (fst <$> varDests `envLookup` b, d)
                        Unpack _ _ -> (Nothing, d)
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
      -- If the result is a table lambda then there is nothing we can do, except for a copy.
      (_, TabVal _ _)  -> tell [(dest, result)]
      (_, Con (Lit _)) -> tell [(dest, result)]
      -- This is conservative, in case the type is dependent. We could do better.
      (DataConRef _ _ _, DataCon _ _ _ _) -> tell [(dest, result)]
      (Con (ConRef destCon), Con srcCon) ->
        zipWithRefConM gatherVarDests destCon srcCon
      (Con (RecordRef items), Record items')
        | fmap (const ()) items == fmap (const ()) items' -> do
            zipWithM_ gatherVarDests (toList items) (toList items')
      (Con (ConRef (SumAsProd _ _ _)), _) -> tell [(dest, result)]  -- TODO
      _ -> unreachable
      where
        unreachable = error $ "Invalid dest-result pair:\n"
                        ++ pprint dest ++ "\n  and:\n" ++ pprint result

letBoundVars :: Decl -> Env ()
letBoundVars (Let _ b _) = b @> ()
letBoundVars (Unpack _ _) = mempty

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
          LLVM     -> CPU
          LLVMMC   -> CPU
          LLVMCUDA -> GPU
          Interp   -> error "Shouldn't be compiling with interpreter backend"

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
  buffer <- emitAlloc (AllocatedPtr, addrSpace, b) numel
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

fromScalarType :: Type -> IType
fromScalarType (BaseTy b) =  b
fromScalarType ty = error $ "Not a scalar type: " ++ pprint ty

toScalarType :: IType -> Type
toScalarType b = BaseTy b

-- === Type classes ===

fromEmbed :: Subst a => Embed a -> ImpM a
fromEmbed m = do
  scope <- variableScope
  let (ans, (_, decls)) = runEmbed m scope
  env <- catFoldM translateDecl mempty $ fmap (Nothing,) decls
  impSubst env ans

intToIndex :: Type -> IExpr -> ImpM Atom
intToIndex ty i = fromEmbed (intToIndexE ty (toScalarAtom i))

indexToInt :: Atom -> ImpM IExpr
indexToInt idx = fromScalarAtom <$> fromEmbed (indexToIntE idx)

indexSetSize :: Type -> ImpM IExpr
indexSetSize ty = fromScalarAtom <$> fromEmbed (indexSetSizeE ty)

zipTabDestAtom :: HasCallStack => (Dest -> Atom -> ImpM ()) -> Dest -> Atom -> ImpM ()
zipTabDestAtom f ~dest@(Con (TabRef (TabVal b _))) ~src@(TabVal b' _) = do
  unless (binderType b == binderType b') $ error $ "Mismatched dimensions"
  let idxTy = binderType b
  n <- indexSetSize idxTy
  emitLoop "i" Fwd n $ \i -> do
    idx <- intToIndex idxTy i
    destIndexed <- destGet dest idx
    srcIndexed  <- translateExpr mempty (Nothing, App src idx)
    f destIndexed srcIndexed

zipWithRefConM :: Monad m => (Dest -> Atom -> m ()) -> Con -> Con -> m ()
zipWithRefConM f destCon srcCon = case (destCon, srcCon) of
  (PairCon d1 d2, PairCon s1 s2) -> f d1 s1 >> f d2 s2
  (UnitCon, UnitCon) -> return ()
  (SumAsProd _ tagRef xssRef, SumAsProd _ tag xss) ->
    f tagRef tag >> zipWithM_ (zipWithM f) xssRef xss
  (IntRangeVal     _ _ iRef, IntRangeVal     _ _ i) -> f iRef i
  (IndexRangeVal _ _ _ iRef, IndexRangeVal _ _ _ i) -> f iRef i
  (CharCon d, CharCon x) -> f d x
  _ -> error $ "Unexpected ref/val " ++ pprint (destCon, srcCon)

-- TODO: put this in userspace using type classes
addToAtom :: Dest -> Atom -> ImpM ()
addToAtom dest src = case (dest, src) of
  (Con (BaseTypeRef ptr), x) -> do
    let ptr' = fromScalarAtom ptr
    let x'   = fromScalarAtom x
    cur <- loadAnywhere ptr'
    let op = case getIType cur of
               Scalar _ -> ScalarBinOp
               Vector _ -> VectorBinOp
               _ -> error $ "The result of load cannot be a reference"
    updated <- emitInstr $ IPrimOp $ op FAdd cur x'
    storeAnywhere ptr' updated
  (Con (TabRef _), TabVal _ _) -> zipTabDestAtom addToAtom dest src
  (Con (ConRef destCon), Con srcCon) -> zipWithRefConM addToAtom destCon srcCon
  (Con (RecordRef dests), Record srcs) ->
    zipWithM_ addToAtom (toList dests) (toList srcs)
  _ -> error $ "Not implemented " ++ pprint (dest, src)

loadAnywhere :: IExpr -> ImpM IExpr
loadAnywhere ptr = do
  curDev <- asks curDevice
  let (PtrType (_, addrSpace, ty)) = getIType ptr
  case addrSpace of
    Heap ptrDev | ptrDev /= curDev -> do
      localPtr <- allocateStackSingleton ty
      memcopy localPtr ptr (IIdxRepVal 1)
      load localPtr
    _ -> load ptr

storeAnywhere :: IExpr -> IExpr -> ImpM ()
storeAnywhere ptr val = do
  curDev <- asks curDevice
  let (PtrType (_, addrSpace, ty)) = getIType ptr
  case addrSpace of
    Heap ptrDev | ptrDev /= curDev -> do
      localPtr <- allocateStackSingleton ty
      store localPtr val
      memcopy ptr localPtr (IIdxRepVal 1)
    _ -> store ptr val

allocateStackSingleton :: IType -> ImpM IExpr
allocateStackSingleton ty = allocateBuffer Stack False ty (IIdxRepVal 1)

-- === Imp embedding ===

embedBinOp :: (Atom -> Atom -> Embed Atom) -> (IExpr -> IExpr -> ImpM IExpr)
embedBinOp f x y =
  fromScalarAtom <$> fromEmbed (f (toScalarAtom x) (toScalarAtom y))

iaddI :: IExpr -> IExpr -> ImpM IExpr
iaddI = embedBinOp iadd

isubI :: IExpr -> IExpr -> ImpM IExpr
isubI = embedBinOp isub

imulI :: IExpr -> IExpr -> ImpM IExpr
imulI = embedBinOp imul

idivI :: IExpr -> IExpr -> ImpM IExpr
idivI = embedBinOp idiv

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

alloc :: Type -> ImpM Dest
alloc ty = allocKind Managed ty

handleErrors :: ImpM () -> ImpM ()
handleErrors m = m `catchError` (const $ emitStatement IThrowError)

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
  vs <- forM (impInstrTypes instr) $ \ty -> freshVar ("v":>ty)
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

allocKind :: AllocType -> Type -> ImpM Dest
allocKind allocTy ty = makeAllocDest allocTy ty

extendAlloc :: IExpr -> ImpM ()
extendAlloc v = extend $ mempty { envPtrsToFree = [v] }

emitAlloc :: HasCallStack => PtrType -> IExpr -> ImpM IExpr
emitAlloc (_, addr, ty) n = emitInstr $ Alloc addr ty n

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
  extend $ mempty { envScope = v @> (UnitTy, UnknownBinder) }
  return $ v:>t

withLevel :: ParallelismLevel -> ImpM a -> ImpM a
withLevel level = local (\opts -> opts {curLevel = level })

withDevice :: Device -> ImpM a -> ImpM a
withDevice device = local (\opts -> opts {curDevice = device })

-- === type checking imp programs ===

-- TODO: track parallelism level and current device and add validity checks like
-- "shouldn't launch a kernel from device/thread code"

-- State keeps track of _all_ names used in the program, Reader keeps the type env.
type ImpCheckM a = StateT (Env ()) (ReaderT (Env IType, Device) (Either Err)) a

instance Checkable ImpModule where
  -- TODO: check main function defined
  checkValid (ImpModule fs) = mapM_ checkValid fs

instance Checkable ImpFunction where
  checkValid f@(ImpFunction (_:> IFunType cc _ _) bs block) = addContext ctx $ do
    let scope = foldMap (binderAsEnv . fmap (const ())) bs
    let env   = foldMap (binderAsEnv                  ) bs
    void $ flip runReaderT (env, deviceFromCallingConvention cc) $
      flip runStateT scope $ checkBlock block
    where ctx = "Checking:\n" ++ pprint f
  checkValid (FFIFunction _) = return ()

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
    checkInt size
    checkBinder i
    assertEq (binderAnn i) (getIType size) $ "Mismatch between the loop iterator and upper bound type"
    [] <- withTypeEnv (i @> getIType size) $ checkBlock block
    return []
  IWhile cond body -> do
    [condTy] <- checkBlock cond
    assertEq (Scalar Int8Type) condTy $ "Not a bool: " ++ pprint cond
    [] <- checkBlock body
    return []
  ICond predicate consequent alternative -> do
    predTy <- checkIExpr predicate
    assertEq (Scalar Int8Type) predTy "Type mismatch in predicate"
    [] <- checkBlock consequent
    [] <- checkBlock alternative
    return []
  IQueryParallelism _ _ -> return [Scalar Int32Type]
  ILaunch _ n args -> [] <$ do
    -- TODO: check args against type of function
    assertHost
    checkInt n
    mapM_ checkIExpr args
  IPrimOp op -> (:[]) <$> checkImpOp op
  ICastOp dt x -> (:[]) <$> do
    case getIType x of
      Scalar _ -> return ()
      _ -> throw CompilerErr $ "Invalid cast source type: " ++ pprint dt
    case dt of
      Scalar _ -> return ()
      _ -> throw CompilerErr $ "Invalid cast destination type: " ++ pprint dt
    return dt
  Alloc a ty _ -> (:[]) <$> do
    when (a /= Stack) assertHost
    return $ PtrType (AllocatedPtr, a, ty)
  MemCopy dest src numel -> [] <$ do
    PtrType (_, _, destTy) <- checkIExpr dest
    PtrType (_, _, srcTy)  <- checkIExpr src
    assertEq destTy srcTy "pointer type mismatch"
    checkInt numel
  Store dest val -> [] <$ do
    PtrType (_, addr, ty) <- checkIExpr dest
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
      PtrType (_, addr, ty) <- return ref
      checkAddrAccessible addr
      return ty
    PtrOffset ref _ -> do  -- TODO: check offset too
      PtrType (_, addr, ty) <- return ref
      return $ PtrType (DerivedPtr, addr, ty)
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
  Alloc a ty _    -> [PtrType (AllocatedPtr, a, ty)]
  Store _ _       -> []
  Free _          -> []
  IThrowError     -> []
  MemCopy _ _ _   -> []
  IFor _ _ _ _    -> []
  IWhile _ _      -> []
  ICond _ _ _     -> []
  ILaunch _ _ _   -> []
  IQueryParallelism _ _ -> [Scalar Int32Type]
  ICall (_:>IFunType _ _ resultTys) _ -> resultTys

checkImpBinOp :: MonadError Err m => BinOp -> IType -> IType -> m IType
checkImpBinOp op x y = do
  retTy <- checkBinOp op (BaseTy x) (BaseTy y)
  case retTy of
    BaseTy bt -> return bt
    _         -> throw CompilerErr $ "Unexpected BinOp return type: " ++ pprint retTy

checkImpUnOp :: MonadError Err m => UnOp -> IType -> m IType
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
  PtrLoad ref        -> ty  where PtrType (_, _, ty) = getIType ref
  PtrOffset ref _    -> PtrType (DerivedPtr, addr, ty)  where PtrType (_, addr, ty) = getIType ref
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
