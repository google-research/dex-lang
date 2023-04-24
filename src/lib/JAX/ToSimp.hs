-- Copyright 2023 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module JAX.ToSimp (liftJaxSimpM, simplifyJaxpr, simplifyClosedJaxpr) where

import Control.Category ((>>>))

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

liftJaxSimpM :: (EnvReader m) => JaxSimpM n n (e n) -> m n (e n)
liftJaxSimpM act = liftBuilder $ runSubstReaderT idSubst $ runJaxSimpM act
{-# INLINE liftJaxSimpM #-}

simplifyClosedJaxpr :: ClosedJaxpr i -> JaxSimpM i o (LamExpr SimpIR o)
simplifyClosedJaxpr ClosedJaxpr{jaxpr, consts=[]} = simplifyJaxpr jaxpr
simplifyClosedJaxpr _ = error "TODO Support consts"

simplifyJaxpr :: Jaxpr i -> JaxSimpM i o (LamExpr SimpIR o)
simplifyJaxpr (Jaxpr invars constvars eqns outvars) = do
  simplifyJBinders invars \invarsB -> do
    simplifyJBinders constvars \constvarsB -> do
      body <- buildBlock do
        simplifyEqns eqns do
          outs <- (map fst) <$> mapM simplifyAtom outvars
          return $ Con $ ProdCon $ outs
      return $ LamExpr (invarsB >>> constvarsB) body

simplifyJBinders
  :: Nest JBinder i i'
  -> (forall o'. DExt o o' => Nest SBinder o o' -> JaxSimpM i' o' a)
  -> JaxSimpM i o a
simplifyJBinders Empty cont = getDistinct >>= \Distinct -> cont Empty
simplifyJBinders (Nest jb jbs) cont = case jb of
  JBindSource _ _ -> error "Unexpected source name after resolution"
  JBind (JSourceName {suffix=suffix}) jTy b -> do
    ty <- simplifyJTy jTy
    withFreshBinder (getNameHint suffix) ty \b' -> do
      extendSubst (b @> Rename (binderName b')) do
        simplifyJBinders jbs \bs' -> cont (Nest b' bs')

simplifyJTy :: JVarType -> JaxSimpM i o (SType o)
simplifyJTy JArrayName{shape, dtype} = go shape $ simplifyDType dtype where
  go [] ty = return ty
  go ((DimSize sz):rest) ty = do
    rest' <- go rest ty
    finIxTy sz ==> rest'

simplifyDType :: DType -> Type r n
simplifyDType = \case
  F64 -> BaseTy $ P.Scalar P.Float64Type
  F32 -> BaseTy $ P.Scalar P.Float32Type
  I64 -> BaseTy $ P.Scalar P.Int64Type
  I32 -> BaseTy $ P.Scalar P.Int32Type

simplifyEqns :: Emits o => Nest JEqn i i' -> JaxSimpM i' o a -> JaxSimpM i o a
simplifyEqns eqn cont = do
  s  <- getSubst
  s' <- simplifyEqnsSubst s eqn
  withSubst s' cont
{-# INLINE simplifyEqns #-}

simplifyEqnsSubst :: Emits o
  => Subst AtomSubstVal l o -> Nest JEqn l i'
  -> JaxSimpM i o (Subst AtomSubstVal i' o)
simplifyEqnsSubst !s Empty = return s
simplifyEqnsSubst !s (Nest eqn rest) = do
  s' <- simplifyEqnSubst s eqn
  simplifyEqnsSubst s' rest

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
  JLiteral (JLit {..}) -> return (Con (Lit (P.Float32Lit 0.0)), ty)

simplifyPrim :: Emits o
  => [(SAtom o, JVarType)] -> Primitive -> JaxSimpM i o [SAtom o]
simplifyPrim args prim = case (prim, args) of
  (Sin, [(arg, ty)]) -> do
    res <- unaryExpandRank P.Sin arg ty
    return [res]
  _ -> undefined

unaryExpandRank :: forall i o. Emits o
  => P.UnOp -> SAtom o -> JVarType -> JaxSimpM i o (SAtom o)
unaryExpandRank op arg JArrayName{shape} = go arg shape where
  go :: Emits l => SAtom l -> [DimSizeName] -> JaxSimpM i l (SAtom l)
  go arg' = \case
    [] -> emitExprToAtom $ PrimOp (UnOp op arg')
    (DimSize sz:rest) -> buildFor noHint P.Fwd (finIxTy sz) \i -> do
      ixed <- emitExprToAtom $ TabApp (sink arg') [Var i]
      go ixed rest
