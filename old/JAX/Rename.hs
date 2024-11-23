-- Copyright 2023 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module JAX.Rename (liftRenameM, renameClosedJaxpr, renameJaxpr) where

import Control.Monad.Reader
import Data.Map qualified as M

import Core
import IRVariants
import JAX.Concrete
import MTL1
import Name

newtype RenamerM (n::S) (a:: *) =
  RenamerM { runRenamerM :: ReaderT1 SourceMap (ScopeReaderM) n a }
  deriving ( Functor, Applicative, Monad
           , ScopeReader, ScopeExtender)

newtype SourceMap (n::S) = SourceMap
  (M.Map JSourceName (Name (AtomNameC SimpIR) n))
  deriving (Semigroup, Monoid)

instance SinkableE SourceMap where
  sinkingProofE = undefined

askSourceMap :: RenamerM n (SourceMap n)
askSourceMap = RenamerM ask

extendSourceMap :: JSourceName -> (Name (AtomNameC SimpIR)) n
  -> RenamerM n a -> RenamerM n a
extendSourceMap sname name (RenamerM cont) = RenamerM do
  let ext = SourceMap $ M.singleton sname name
  local (<> ext) cont

liftRenameM :: EnvReader m => RenamerM n (e n) -> m n (e n)
liftRenameM act = liftScopeReaderM $ runReaderT1 mempty $ runRenamerM act

renameClosedJaxpr :: Distinct o => ClosedJaxpr i -> RenamerM o (ClosedJaxpr o)
renameClosedJaxpr ClosedJaxpr{jaxpr, consts} = do
  jaxpr' <- renameJaxpr jaxpr
  return ClosedJaxpr{jaxpr=jaxpr', consts}

renameJaxpr :: Distinct o => Jaxpr i -> RenamerM o (Jaxpr o)
renameJaxpr (Jaxpr invars constvars eqns outvars) =
  renameJBinders invars \invars' ->
    renameJBinders constvars \constvars' ->
      renameJEqns eqns \eqns' -> do
        outvars' <- mapM renameJAtom outvars
        return $ Jaxpr invars' constvars' eqns' outvars'

renameJBinder :: Distinct o
  => JBinder i i'
  -> (forall o'. DExt o o' => JBinder o o' -> RenamerM o' a)
  -> RenamerM o a
renameJBinder binder cont = case binder of
  JBindSource sname ty -> do
    withFreshM (getNameHint sname) \freshName -> do
      Distinct <- getDistinct
      extendSourceMap sname (binderName freshName) $
        cont $ JBind sname ty freshName
  JBind _ _ _ -> error "Shouldn't be source-renaming internal names"

renameJBinders :: Distinct o
  => Nest JBinder i i'
  -> (forall o'. DExt o o' => Nest JBinder o o' -> RenamerM o' a)
  -> RenamerM o a
renameJBinders Empty cont = cont Empty
renameJBinders (Nest b bs) cont =
  renameJBinder b \b' ->
    renameJBinders bs \bs' ->
      cont $ Nest b' bs'

renameJAtom :: JAtom i -> RenamerM o (JAtom o)
renameJAtom = \case
  JVariable jvar -> JVariable <$> renameJVar jvar
  JLiteral jlit -> return $ JLiteral jlit

renameJVar :: JVar i -> RenamerM o (JVar o)
renameJVar JVar{sourceName, ty} = do
  sourceName' <- renameJSourceNameOr sourceName
  return $ JVar sourceName' ty

renameJSourceNameOr :: JSourceNameOr (Name (AtomNameC SimpIR)) i
  -> RenamerM o (JSourceNameOr (Name (AtomNameC SimpIR)) o)
renameJSourceNameOr = \case
  SourceName sname -> do
    SourceMap sm <- askSourceMap
    case M.lookup sname sm of
      (Just name) -> return $ InternalName sname name
      Nothing -> error $ "Unbound variable " ++ show sname
  InternalName _ _ -> error "Shouldn't be source-renaming internal names"

renameJEqn :: Distinct o
  => JEqn i i'
  -> (forall o'. DExt o o' => JEqn o o' -> RenamerM o' a)
  -> RenamerM o a
renameJEqn JEqn{outvars, primitive, invars} cont = do
  invars' <- mapM renameJAtom invars
  renameJBinders outvars \outvars' -> cont $ JEqn outvars' primitive invars'

renameJEqns :: Distinct o
  => Nest JEqn i i'
  -> (forall o'. DExt o o' => Nest JEqn o o' -> RenamerM o' a)
  -> RenamerM o a
renameJEqns Empty cont = cont Empty
renameJEqns (Nest b bs) cont =
  renameJEqn b \b' ->
    renameJEqns bs \bs' ->
      cont $ Nest b' bs'

