-- Copyright 2021 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleInstances #-}

module SaferNames.CheapReduction
  ( cheapReduceBlockToAtom, cheapReduce, CheaplyReducible (..)
  , cheapReduceDecls) where

import Control.Monad.Identity

import SaferNames.Name
import SaferNames.Syntax
import Err

-- === api ===

cheapReduceBlockToAtom :: (BindingsReader m, Scopable m)
                       => Block n -> m n (Maybe (Atom n))
cheapReduceBlockToAtom block = fromAtomicBlock <$> cheapReduce block

fromAtomicBlock :: Block n -> Maybe (Atom n)
fromAtomicBlock (Block _ Empty expr) = fromAtomicExpr expr
fromAtomicBlock _ = Nothing

fromAtomicExpr :: Expr n -> Maybe (Atom n)
fromAtomicExpr (Atom atom) = Just atom
fromAtomicExpr _ = Nothing

cheapReduce :: (CheaplyReducible e, BindingsReader m, Scopable m)
            => e n -> m n (e n)
cheapReduce x = runEnvReaderT idEnv $ cheapReduceE x

cheapReduceDecls
  :: ( SubstE AtomSubstVal e, MonadFail1 m, BindingsReader m, Scopable m
     , CheaplyReducible e, HoistableE e, InjectableE e, SubstE Name e, SubstE AtomSubstVal e)
  => Abs (Nest Decl) e n -> m n (e n)
cheapReduceDecls ab = runEnvReaderT idEnv $ cheapReduceDeclsE ab >>= liftMaybe

-- === internal ===

cheapReduceFreeVars
  :: ( EnvReader Name m, BindingsReader2 m, Scopable2 m
     , InjectableE e, SubstE AtomSubstVal e)
  => e i -> m i o (e o)
cheapReduceFreeVars e = do
  env <- getEnv
  WithBindings bindings env' <- addBindings env
  injectM $ fmapNames (toScope bindings) (cheapReduceName env' bindings) e
  where
    cheapReduceName :: Distinct o
                    => Env Name i o -> Bindings o -> Name c i -> AtomSubstVal c o
    cheapReduceName env bindings v =
      case getNameColor v of
      AtomNameRep ->
        SubstVal $
          runIdentity $ runBindingsReaderT bindings $ runEnvReaderT env $
            cheapReduceAtomName v
      _ ->
        Rename $ env ! v

cheapReduceAtomName
  :: (EnvReader Name m, BindingsReader2 m, Scopable2 m)
  => AtomName i -> m i o (Atom o)
cheapReduceAtomName v = do
  v' <- substM v
  lookupBindings v' >>= \case
    -- TODO: worry about effects!
    AtomNameBinding (LetBound (DeclBinding PlainLet _ expr)) -> do
      expr' <- dropSubst $ cheapReduceE expr
      case fromAtomicExpr expr' of
        Nothing -> return $ Var v'
        Just x' -> return x'
    _ -> return $ Var v'

class CheaplyReducible (e::E) where
  cheapReduceE :: (EnvReader Name m, BindingsReader2 m, Scopable2 m)
               => e i -> m i o (e o)

instance CheaplyReducible Atom where
  cheapReduceE = cheapReduceFreeVars

instance CheaplyReducible (EffectRowP AtomName) where
  cheapReduceE = cheapReduceFreeVars

instance CheaplyReducible Expr where
  cheapReduceE expr = case expr of
    Atom atom -> Atom <$> cheapReduceE atom
    App f x -> do
      f' <- cheapReduceE f
      x' <- cheapReduceE x
      -- TODO: Worry about variable capture. Should really carry a substitution.
      case f' of
        Lam (LamExpr (LamBinder b _ arr Pure) body)
          | arr == PlainArrow || arr == ImplicitArrow -> do
              body' <- applyAbs (Abs b body) (SubstVal x')
              body'' <- dropSubst $ cheapReduceE body'
              case fromAtomicBlock body'' of
                Just reduced -> return $ Atom reduced
                Nothing -> substM expr
        TypeCon con xs -> return $ Atom $ TypeCon con $ xs ++ [x']
        _ -> substM expr
    _ -> substM expr

instance CheaplyReducible Block where
  -- This path is just an optimized special case
  cheapReduceE (Block ty Empty result) = do
    ty' <- substM ty
    result' <- cheapReduceE result
    return $ Block ty' Empty result'
  cheapReduceE (Block ty decls result) = do
    ty' <- substM ty
    Abs decls' result' <-
      refreshBinders2 decls do
        cheapReduceE result
    case hoist decls' result' of
      Just result'' -> return $ Block ty' Empty result''
      Nothing       -> return $ Block ty' decls' result'

instance (CheaplyReducible e1, CheaplyReducible e2)
         => CheaplyReducible (PairE e1 e2) where
  cheapReduceE (PairE e1 e2) = PairE <$> cheapReduceE e1 <*> cheapReduceE e2

cheapReduceDeclsE
  :: ( EnvReader Name m, BindingsReader2 m, Scopable2 m
     , CheaplyReducible e, HoistableE e, InjectableE e, SubstE Name e, SubstE AtomSubstVal e)
  => Abs (Nest Decl) e i -> m i o (Maybe (e o))
cheapReduceDeclsE (Abs decls e) =
  liftM fromConstAbs $ refreshBinders2 decls $ cheapReduceE e
