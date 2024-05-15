-- Copyright 2022 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE UndecidableInstances #-}

module DPS (dpsPass) where

import Prelude hiding ((.))
import Data.Functor
import Data.Maybe (fromJust)
import Control.Category
import Control.Monad.Reader
import Unsafe.Coerce

import Builder
import Core
import Imp
import CheapReduction
import IRVariants
import Name
import Subst
import PPrint
import QueryType
import Types.Core
import Types.Top
import Types.Primitives
import Util (enumerate, popList, SMaybe (..), Not)

dpsPass :: EnvReader m => STopLam n -> m n (STopLam n)
dpsPass (TopLam False piTy (LamExpr bs body)) = do
  liftEnvReaderM $ liftAtomSubstBuilder do
    dpsPiTy <- computeDPSPiTy piTy
    buildTopDestLamFromPi dpsPiTy \args dest -> do
      extendSubst (bs @@> (SubstVal . toAtom <$> args)) do
        SNothing <- dpsExpr (SJust (toAtom dest)) body
        return UnitVal
dpsPass (TopLam True _ _) = error "already in destination style"

computeDPSPiTy :: PiType SimpIR i -> DestM i o (PiType SimpIR o)
computeDPSPiTy (PiType bs resultTy) = case bs of
  Empty -> do
    destTy <- computeDestTy =<< dpsSubstType resultTy
    withFreshBinder "ans" destTy \bDest ->
      return $ PiType (UnaryNest bDest) UnitTy
  Nest (b:>ty) bsRest -> do
    repTy <- computeRepTy =<< dpsSubstType ty
    withFreshBinder (getNameHint b) repTy \b' ->
      extendSubst (b@>Rename (binderName b')) do
        PiType bsRest' resultTy' <- computeDPSPiTy (PiType bsRest resultTy)
        return $ PiType (Nest b' bsRest') resultTy'

type Dest = SAtom
type MaybeDest   d n = SMaybe d (Dest n)
type MaybeResult d n = SMaybe (Not d) (SAtom n)

data DPSTag
type DestM = AtomSubstBuilder DPSTag SimpIR

computeRepTy :: EnvReader m => SType n -> m n (SType n)
computeRepTy ty = case ty of
  TyCon con -> case con of
    BaseType _ -> return ty

computeDestTy :: EnvReader m => SType n -> m n (SType n)
computeDestTy ty = case ty of
  TyCon con -> case con of
    BaseType _ -> return $ RefTy ty

lowerAtom :: SAtom i -> DestM i o (SAtom o)
lowerAtom = substM

getDPSFun :: TopFunName o -> DestM i o (TopFunName o)
getDPSFun = undefined

loadIfScalar :: Emits o => SAtom o -> DestM i o (SAtom o)
loadIfScalar = undefined

loadDest :: Emits o => SAtom o -> DestM i o (SAtom o)
loadDest = undefined

storeDest :: Emits o => Dest o -> SAtom o -> DestM i o ()
storeDest dest val = do
  RefTy (TyCon tycon) <- return $ getType dest
  case tycon of
    BaseType _ -> undefined -- void $ emit $ RefOp dest $ MPut val

-- The dps pass carries a non-type-preserving substitution in which arrays are
-- replaced with refs to arrays. So it's incorrect to directly apply the
-- substitution as we do here. It's fine as long as arrays don't appear in types
-- but it's not clear what we should otherwise. Maybe it's ok to dereference an
-- read-only ref inside a type? reference?
dpsSubstType :: SType i -> DestM i o (SType o)
dpsSubstType = substM

dpsExpr
  :: forall i o d. Emits o
  => MaybeDest d o
  -> SExpr i
  -> DestM i o (MaybeResult d o)
dpsExpr maybeDest expr = case expr of
  Block _ block -> dpsBlock maybeDest block
  TopApp _ f args -> withDest \dest -> do
    f' <- substM f >>= getDPSFun
    args' <- mapM lowerAtom args
    void $ topApp f' (args' ++ [dest]) >>= emit
  TabApp _ xs i -> do
    xs' <- lowerAtom xs
    i' <- lowerAtom i
    x <- indexRef xs' i'
    returnResult =<< loadIfScalar x
  Case scrut alts _ -> withDest \dest -> do
    scrut' <- lowerAtom scrut
    void $ buildCase scrut' UnitTy \i x -> do
      Abs b body <- return $ alts!!i
      extendSubst (b@>SubstVal x) do
        SNothing <- dpsExpr (SJust $ sink dest) body
        return ()
      return UnitVal
  Atom x ->  lowerAtom x >>= returnResult
  TabCon _ _ -> undefined
  PrimOp _ _ -> undefined
  Project _ _ _ -> undefined

  where
    returnResult :: SAtom o -> DestM i o (MaybeResult d o)
    returnResult result = do
      case maybeDest of
        SJust dest -> storeDest dest result >> return SNothing
        SNothing -> return $ SJust result

    withDest :: (Dest o -> DestM i o ()) -> DestM i o (MaybeResult d o)
    withDest cont = do
      case maybeDest of
        SJust dest -> cont dest >> return SNothing
        SNothing -> do
          destTy <- dpsSubstType $ RefTy (getType expr)
          dest <- newUninitializedRef destTy
          cont dest
          result <- loadDest dest
          return $ SJust result

dpsBlock :: Emits o => MaybeDest d o -> SBlock i -> DestM i o (MaybeResult d o)
dpsBlock maybeDest (Abs decls result) = case decls of
  Empty -> dpsExpr maybeDest result
  Nest (Let b (DeclBinding _ expr)) declsRest -> do
    SJust x <- dpsExpr SNothing expr
    extendSubst (b@>SubstVal x) $
      dpsBlock maybeDest (Abs declsRest result)
