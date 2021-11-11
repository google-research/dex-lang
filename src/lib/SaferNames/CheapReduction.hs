-- Copyright 2021 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleInstances #-}

module SaferNames.CheapReduction (
  CheaplyReducibleE (..), cheapReduce, cheapReduceWithDecls, cheapReduceToAtom) where

import Control.Monad.Identity

import SaferNames.Name
import SaferNames.Syntax
import SaferNames.PPrint ()
import {-# SOURCE #-} SaferNames.Inference (trySynthDictBlock)
import Err

-- === api ===

cheapReduce :: (BindingsReader m, SubstE AtomSubstVal e, InjectableE e)
            => e n -> m n (e n)
cheapReduce e = do
  WithBindings bindings e' <- addBindings e
  injectM $ runCheapReducerM idEnv bindings $ cheapReduceFromSubst e'

cheapReduceWithDecls :: (BindingsReader m, SubstE AtomSubstVal e, InjectableE e)
                     => Nest Decl n l -> e l -> m n (Maybe (e n))
cheapReduceWithDecls decls result = do
  WithBindings bindings (Abs decls' result') <- addBindings $ Abs decls result
  let reduced = runCheapReducerM idEnv bindings $
                 cheapReduceWithDeclsB decls' $ cheapReduceFromSubst result'
  case reduced of
    Nothing -> return Nothing
    Just x -> Just <$> injectM x

cheapReduceToAtom :: (BindingsReader m, CheaplyReducibleE e, InjectableE e)
                  => e n -> m n (Maybe (Atom n))
cheapReduceToAtom e = do
  WithBindings bindings e' <- addBindings e
  case runCheapReducerM idEnv bindings (cheapReduceE e') of
    Nothing -> return Nothing
    Just x -> Just <$> injectM x

-- === internal ===

type CheapReducerM = EnvReaderT AtomSubstVal BindingsReaderM

runCheapReducerM :: Distinct o
                 => Env AtomSubstVal i o -> Bindings o -> CheapReducerM i o a -> a
runCheapReducerM env bindings m =
  runBindingsReaderM bindings $ runEnvReaderT env m

cheapReduceFromSubst
  :: ( EnvReader AtomSubstVal m, BindingsGetter2 m
     , InjectableE e, SubstE AtomSubstVal e)
  => e i -> m i o (e o)
cheapReduceFromSubst e = do
  e' <- substM e
  bindings <- getBindingsM
  Distinct <- getDistinct
  return $ fmapNames (toScope bindings) (cheapReduceName bindings) e'

cheapReduceName :: Distinct n
                => Bindings n -> Name c n -> AtomSubstVal c n
cheapReduceName bindings v =
  runBindingsReaderM bindings $ withNameColorRep (getNameColor v) do
    lookupBindings v >>= \case
      AtomNameBinding (LetBound (DeclBinding _ _ (Atom x))) ->
        SubstVal <$> cheapReduce x
      _ -> return $ Rename v

cheapReduceWithDeclsB :: (EnvReader AtomSubstVal m, BindingsGetter2 m)
                      => Nest Decl i i'
                      -> m i' o a
                      -> m i  o (Maybe a)
cheapReduceWithDeclsB decls cont = case decls of
    Empty -> Just <$> cont
    Nest (Let b (DeclBinding _ _ expr)) rest -> do
      cheapReduceE expr >>= \case
        Nothing -> return Nothing
        Just x -> extendEnv (b@>SubstVal x) $
                    cheapReduceWithDeclsB rest cont

class CheaplyReducibleE (e::E) where
  cheapReduceE :: (EnvReader AtomSubstVal m, BindingsGetter2 m)
               => e i -> m i o (Maybe (Atom o))

instance CheaplyReducibleE e => CheaplyReducibleE (Abs (Nest Decl) e) where
  cheapReduceE (Abs decls result) =
    join <$> (cheapReduceWithDeclsB decls $ cheapReduceE result)

instance CheaplyReducibleE Block where
  cheapReduceE (Block _ decls result) = cheapReduceE $ Abs decls result

instance CheaplyReducibleE Expr where
  cheapReduceE expr = cheapReduceFromSubst expr >>= \case
    Atom atom -> return $ Just atom
    App f x -> do
      case f of
        Lam (LamExpr (LamBinder b _ arr Pure) body)
          | arr == PlainArrow || arr == ImplicitArrow || arr == ClassArrow -> do
              dropSubst $ extendEnv (b@>SubstVal x) $ cheapReduceE body
        TypeCon con xs -> return $ Just $ TypeCon con $ xs ++ [x]
        _ -> return Nothing
    Op (SynthesizeDict _ ty) -> do
      runFallibleT1 (trySynthDictBlock ty) >>= \case
        Success (Block _ Empty (Atom d)) -> return $ Just d
        _ -> return Nothing
    -- TODO: Make sure that this wraps correctly
    -- TODO: Other casts?
    Op (CastOp (BaseTy (Scalar Int32Type)) (Con (Lit (Int64Lit v)))) ->
      return $ Just $ Con $ Lit $ Int32Lit $ fromIntegral v
    _ -> return Nothing
