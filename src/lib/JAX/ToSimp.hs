-- Copyright 2023 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module JAX.ToSimp where

import GHC.Base (NonEmpty(..))

import Builder
import Core
import Err
import IRVariants
import Name
import JAX.Concrete
import Subst
import Types.Core
import Types.Primitives qualified as P

newtype JaxSimpM (i::S) (o::S) a = JaxSimpM
  { runJaxSimpM :: SubstReaderT AtomSubstVal (BuilderM SimpIR) i o a }
  deriving ( Functor, Applicative, Monad, MonadFail
           , ScopeReader, EnvReader, EnvExtender
           , SubstReader AtomSubstVal, Fallible
           , Builder SimpIR, ScopableBuilder SimpIR)

simplifyEqn :: Emits o => JEqn i i' -> JaxSimpM i' o a -> JaxSimpM i o a
simplifyEqn eqn cont = do
  s  <- getSubst
  s' <- simplifyEqnSubst s eqn
  withSubst s' cont
{-# INLINE simplifyEqn #-}

simplifyEqnSubst :: Emits o
  => Subst AtomSubstVal l o -> JEqn l i' -> JaxSimpM i o (Subst AtomSubstVal i' o)
simplifyEqnSubst !s JEqn{..} = do
  simpIn <- withSubst s $ mapM simplifyAtom invars
  simpOut <- simplifyPrim simpIn primitive
  return $ s <>> (outvars @@> (map SubstVal simpOut))

simplifyAtom :: JAtom i -> JaxSimpM i o (SAtom o, JVarType)
simplifyAtom = \case
  JVariable (JVar {..}) -> case sourceName of
    SourceName _ -> error "Unexpected source name during compilation"
    InternalName _ nm -> do
      env <- getSubst
      case env ! nm of
        -- TODO Assuming the subst is not type-changing
        SubstVal x -> return (x, ty)
        Rename nm' -> return (Var nm', ty)
  -- TODO In Jax, literals can presumably include (large) arrays.  How should we
  -- represent them here?
  JLiteral (JLit {..}) -> return (Con (P.Lit (P.Float32Lit 0.0)), ty)

simplifyPrim :: Emits o
  => [(SAtom o, JVarType)] -> Primitive -> JaxSimpM i o [SAtom o]
simplifyPrim args prim = case (prim, args) of
  (Sin, [(arg, ty)]) -> do
    res <- unary_expand_rank P.Sin arg ty
    return [res]
  _ -> undefined

unary_expand_rank :: forall i o. Emits o
  => P.UnOp -> SAtom o -> JVarType -> JaxSimpM i o (SAtom o)
unary_expand_rank op arg JArrayName {..} = go arg shape where
  go :: Emits l => SAtom l -> [DimSizeName] -> JaxSimpM i l (SAtom l)
  go arg' = \case
    [] -> emitExprToAtom $ PrimOp (P.UnOp op arg')
    (DimSize sz:rest) -> buildFor noHint P.Fwd (finIxTy sz) \i -> do
      ixed <- emitExprToAtom $ TabApp (sink arg') (Var i :| [])
      go ixed rest

finIxTy :: Int -> IxType r n
finIxTy n = IxType IdxRepTy (IxDictRawFin (IdxRepVal $ fromIntegral n))
