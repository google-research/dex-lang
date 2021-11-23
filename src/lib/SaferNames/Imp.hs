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
import Syntax (CallingConvention, Backend)

import SaferNames.Name
import SaferNames.Builder (Emits, EmitsEvidence (..), fabricateEmitsEvidenceM)
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
  (f', ImpModule [], recon')
  where
    PairE recon' f' = runImpM bindings do
      (recon, f) <- translateTopLevel cc (fmap inject maybeDest) $
                      inject absBlock
      return $ PairE recon f

-- === ImpM monad ===

type ImpBuilderEmissions = Nest ImpDecl

newtype ImpM (i::S) (o::S) (a:: *) =
  ImpM { runImpM' ::
           EnvReaderT AtomSubstVal
             (InplaceT Bindings ImpBuilderEmissions Identity) i o a }
  deriving ( Functor, Applicative, Monad, ScopeReader, EnvReader AtomSubstVal)

instance ExtOutMap Bindings ImpBuilderEmissions where
  extendOutMap bindings emissions =
    bindings `extendOutMap` toBindingsFrag emissions

class ( ImpBuilder2 m, EnvReader AtomSubstVal m
      , BindingsReader2 m, BindingsExtender2 m)
      => Imper (m::MonadKind2) where

instance BindingsReader (ImpM i) where
  getBindings = ImpM $ EnvReaderT $ lift $ getOutMapInplaceT

instance BindingsExtender (ImpM i) where
  extendBindings frag cont = ImpM $ EnvReaderT $ ReaderT \env ->
    extendInplaceTLocal (\bindings -> extendOutMap bindings frag) $
      withExtEvidence (toExtEvidence frag) $
        runEnvReaderT (inject env) $ runImpM' cont

instance ImpBuilder (ImpM i) where
  emitMultiReturnInstr instr = do
    let tys = impInstrTypes instr
    ListE vs <- ImpM $ EnvReaderT $ ReaderT \env ->
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

  buildScopedImp cont = ImpM $ EnvReaderT $ ReaderT \env ->
    locallyMutableInplaceT $
      runEnvReaderT (inject env) $ runImpM' do
        Emits <- fabricateEmitsEvidenceM
        Distinct <- getDistinct
        cont

instance Imper ImpM

runImpM
  :: Distinct n
  => Bindings n
  -> (Immut n => ImpM n n (e n))
  -> e n
runImpM bindings cont =
  withImmutEvidence (toImmutEvidence bindings) $
    case runIdentity $ runInplaceT bindings $ runEnvReaderT idEnv $ runImpM' $ cont of
      (Empty, result) -> result

-- === the actual pass ===

translateTopLevel :: (Immut o, Imper m)
                  => CallingConvention
                  -> MaybeDest o
                  -> Abs (Nest PtrBinder) Block i
                  -> m i o (AtomRecon o, ImpFunction o)
translateTopLevel cc maybeDest (Abs bs body) = do
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
  return (recon, ImpFunction "mainFn" funTy funImpl)

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
translateBlock dest (Block _ decls result) = go decls result
  where
    go :: Nest Decl i' i'' -> Expr i'' -> m i' o (Atom o)
    go Empty result = translateExpr dest result
    go (Nest decl decls) result = translateDecl Nothing decl $ go decls result

translateDecl :: (Imper m, Emits o) => MaybeDest o -> Decl i i' -> (m i' o a) -> m i o a
translateDecl maybeDest (Let b (DeclBinding _ _ expr)) cont = do
  ans <- translateExpr maybeDest expr
  extendEnv (b @> SubstVal ans) $ cont

translateExpr :: (Imper m, Emits o) => MaybeDest o -> Expr i -> m i o (Atom o)
translateExpr maybeDest expr = case expr of
  Atom x -> substM x >>= returnVal
  Op op -> mapM substM op >>= toImpOp maybeDest
  _ -> error $ "not implemented: " ++ pprint expr
  where
    returnVal atom = case maybeDest of
      Nothing   -> return atom
      Just dest -> copyAtom dest atom >> return atom

toImpOp :: (Imper m, Emits o) => MaybeDest o -> PrimOp (Atom o) -> m i o (Atom o)
toImpOp maybeDest op = case op of
  _ -> do
    instr <- IPrimOp <$> mapM fromScalarAtom op
    emitInstr instr >>= toScalarAtom >>= returnVal
  where
    returnVal atom = case maybeDest of
      Nothing   -> return atom
      Just dest -> copyAtom dest atom >> return atom

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

storeAnywhere :: (ImpBuilder m, Emits n) => IExpr n -> IExpr n -> m n ()
storeAnywhere ptr val = store ptr val

store :: (ImpBuilder m, Emits n) => IExpr n -> IExpr n -> m n ()
store dest src = emitStatement $ Store dest src

destToAtom :: (ImpBuilder m, Emits n) => Dest n -> m n (Atom n)
destToAtom (Con dest) = do
 case dest of
   BaseTypeRef ptr -> fromScalarAtom ptr >>= load >>= toScalarAtom

-- === Imp IR builder ===

class BindingsReader m => ImpBuilder (m::MonadKind1) where
  emitMultiReturnInstr :: Emits n => ImpInstr n -> m n [IExpr n]
  buildScopedImp
    :: (InjectableE e, Immut n)
    => (forall l. (Emits l, Ext n l) => m l (e l))
    -> m n (DistinctAbs (Nest ImpDecl) e n)

type ImpBuilder2 (m::MonadKind2) = forall i. ImpBuilder (m i)

withFreshIBinder
  :: (Immut n, ImpBuilder m)
  => NameHint -> IType
  -> (forall l. (Immut l, Distinct l, Ext n l) => IBinder n l -> m l a)
  -> m n a
withFreshIBinder hint ty cont = undefined

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
-- buildImpNaryAbs ((hint, ty):args) body = do
--   Abs b (Abs bs body) <- withFreshIBinder hint ty \v ->
--     buildImpNaryAbs args \vs -> do
--       v' <- injectM v
--       body (v':vs)
--   return $ Abs (Nest b bs) body

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

-- === type checking imp programs ===

impFunType :: ImpFunction n -> IFunType
impFunType (ImpFunction _ ty _) = ty

getIType :: IExpr n -> IType
getIType (ILit l) = litType l

impInstrTypes :: ImpInstr n -> [IType]
impInstrTypes instr = case instr of
  IPrimOp op      -> [impOpType op]

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
