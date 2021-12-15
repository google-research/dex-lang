-- Copyright 2021 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE TypeFamilies #-}

module Linearize (linearize) where

import Control.Applicative
import Control.Monad
import Control.Monad.Reader
import Control.Monad.State.Strict
import qualified Data.List.NonEmpty as NE
import Data.Maybe
import Data.Foldable
import qualified Data.Set as S
import GHC.Stack

import Name
import Builder
import Syntax
import Type
import PPrint

-- === linearization monad ===

data PrimalTangentPair c n =
  -- XXX: we use the Nothing case when there isn't a meaningful tangent, for
  -- example, when we're differentiating a function with free variables.
  -- TODO: the tangent component, if present, should be an atom name. We could
  -- enforce this with a GADT.
  PTPair (Name c n) (Maybe (Name c n))
 | ZeroTangentWithPrimal (Name c n)

type PrimalM  = SubstReaderT Name BuilderM        :: MonadKind2
type TangentM = SubstReaderT PrimalTangentPair BuilderM :: MonadKind2

data WithTangent (i::S) (o::S) (e1::E) (e2::E) =
  WithTangent (e1 o) (forall o'. (Emits o', DExt o o') => TangentM i o' (e2 o'))

type LinM i o e1 e2 = PrimalM i o (WithTangent i o e1 e2)

-- === TODO: move these elsewhere ===


zeroAt :: (Emits n ,Builder m) => Type n -> m n (Atom n )
zeroAt ty = case ty of
  BaseTy bt  -> return $ Con $ Lit $ zeroLit bt
  _          -> unreachable
  where
    unreachable :: a
    unreachable = error $ "Missing zero case for a tangent type: " ++ pprint ty
    zeroLit bt = case bt of
      Scalar Float64Type -> Float64Lit 0.0
      Scalar Float32Type -> Float32Lit 0.0
      Vector st          -> VecLit $ replicate vectorWidth $ zeroLit $ Scalar st
      _                  -> unreachable

zeroLike :: (HasType e, Emits n, Builder m) => e n -> m n (Atom n )
zeroLike x = zeroAt =<< getType x

-- === actual linearization passs ===

-- main API entrypoint
linearize :: EnvReader m => Atom n -> m n (Atom n)
linearize x = liftImmut do
  DB env <- getDB
  return $ runBuilderM env $ runSubstReaderT idSubst $ linearizeLambda' x

-- reify the tangent builder as a lambda
linearizeLambda' :: Atom i -> PrimalM i o (Atom o)
linearizeLambda' (Lam (LamExpr (LamBinder b ty PlainArrow Pure) body)) = do
  ty' <- substM ty
  buildLam (getNameHint b) PlainArrow ty' Pure \vp -> do
    WithTangent primalResult tangentAction <- extendSubst (b@>vp) $ linearizeBlock body
    let tangentTy = sink $ tangentType ty'
    tangentLam <- buildLam (getNameHint b) LinArrow tangentTy Pure \vt ->
      liftTangentM $ extendSubst (b @> PTPair (sink vp) (Just vt)) $ tangentAction
    return $ PairVal primalResult tangentLam
linearizeLambda' _ = error "not implemented"

tangentType :: Type n -> Type n
tangentType ty = ty -- TODO!

liftTangentM :: TangentM i o a -> PrimalM i o a
liftTangentM m = do
  subst <- getSubst
  SubstReaderT $ lift $
    runSubstReaderT (newSubst \v -> ZeroTangentWithPrimal (subst ! v)) m

linearizeAtom :: Atom i -> LinM i o Atom Atom
linearizeAtom atom = case atom of
  Var v -> do
    v' <- substM v
    return $ WithTangent (Var v') do
      PTPair p maybeT <- lookupSubstM v
      case maybeT of
        Just t -> return $ Var t
        Nothing -> zeroLike $ Var p
  Con con -> linearizePrimCon con

linearizeBlock :: Emits o => Block i -> LinM i o Atom Atom
linearizeBlock (Block _ decls result) =
  linearizeDecls decls $ linearizeExpr result

linearizeDecls :: Emits o => Nest Decl i i' -> LinM i' o e1 e2 -> LinM i  o e1 e2
linearizeDecls Empty cont = cont
linearizeDecls (Nest (Let b (DeclBinding ann _ expr)) rest) cont = do
  WithTangent p tf <- linearizeExpr expr
  v <- emitDecl (getNameHint b) ann (Atom p)
  extendSubst (b@>v) do
    WithTangent pRest tfRest <- linearizeDecls rest cont
    return $ WithTangent pRest do
      t <- tf
      vt <- emitDecl (getNameHint b) ann (Atom t)
      extendSubst (b@>PTPair (sink v) (Just vt)) do
        tfRest

linearizeExpr :: Expr i -> LinM i o Atom Atom
linearizeExpr expr = case expr of
  Atom e     -> linearizeAtom e

linearizePrimCon :: Con i -> LinM i o Atom Atom
linearizePrimCon con = case con of
  Lit _                 -> atomWithZero $ Con con

atomWithZero :: Atom i -> LinM i o Atom Atom
atomWithZero x = do
  x' <- substM x
  return $ WithTangent x' (zeroLike $ sink x')

-- === instances ===

instance GenericE (PrimalTangentPair c) where
  type RepE (PrimalTangentPair c) = EitherE (Name c) (MaybeE (Name c))
  fromE = undefined
  toE = undefined

instance HoistableE (PrimalTangentPair c)
instance SinkableE  (PrimalTangentPair c)
instance SinkableV  PrimalTangentPair
