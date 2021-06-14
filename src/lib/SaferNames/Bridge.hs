-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}

module SaferNames.Bridge
  ( BridgeState (..), EnvDS, EnvSD, HasSafeVersionE (..)
  , HasSafeVersionB (..)) where

import Data.Maybe (fromJust)

import qualified            Syntax as D  -- D for Danger
import qualified            Env    as D

import SaferNames.Name (S (..), FreshBinder (..))
import qualified SaferNames.Syntax as S
import qualified SaferNames.Name   as S

type EnvDS n = D.Env   (S.Name n)
type EnvSD n = S.Env n  D.Name

data BridgeState n = BridgeState
  { envSD :: S.Env n  D.Name
  , envDS :: D.Env   (S.Name n)
  , sBindings :: S.Bindings n
  , dBindings :: D.Bindings }

class HasSafeVersionE (e:: *) where
  type SafeVersionE e :: S.E
  toSafeE   :: S.Scope n -> EnvDS n -> e -> SafeVersionE e n
  fromSafeE :: D.Scope   -> EnvSD n -> SafeVersionE e n -> e

class HasSafeVersionB (b:: *) where
  type SafeVersionB b :: S.B
  toSafeB   :: S.Scope n -> EnvDS n -> b
            -> (forall l. (SafeVersionB b n l, EnvSD l) -> a)
            -> a
  fromSafeB :: D.Scope   -> EnvSD n -> SafeVersionB b n l -> (b, EnvSD (n:-:l))

instance HasSafeVersionE D.Module where
  type SafeVersionE D.Module = S.Module
  toSafeE = undefined
  fromSafeE = undefined

instance HasSafeVersionE D.Atom where
  type SafeVersionE D.Atom = S.Atom

  toSafeE scope env atom = case atom of
    D.Var (v D.:> ty) -> S.Var (S.AnnVar (fromJust $ D.envLookup env v) (toSafeE scope env ty))
    D.Lam (D.Abs b (arr, body)) -> S.Lam $ toSafeE scope env (D.Abs b (DWithArrow arr body))
    D.Pi  (D.Abs b (arr, body)) -> S.Pi  $ toSafeE scope env (D.Abs b (DWithArrow arr body))
    D.Con con -> S.Con $ fmap (toSafeE scope env) con
    D.TC  tc  -> S.TC  $ fmap (toSafeE scope env) tc

  fromSafeE scope env atom = case atom of
    S.Var (S.AnnVar v ty) -> D.Var $ S.envLookup env v D.:> fromSafeE scope env ty
    S.Con con -> D.Con $ fmap (fromSafeE scope env) con

instance HasSafeVersionE D.Block where
  type SafeVersionE D.Block = S.Block
  toSafeE = undefined
  fromSafeE = undefined

instance HasSafeVersionB D.Decl where
  type SafeVersionB D.Decl = S.Decl
  toSafeB _ _ _ _ = undefined
  fromSafeB _ _ _ = undefined

instance HasSafeVersionE e => HasSafeVersionB (D.BinderP e) where
  type SafeVersionB (D.BinderP e) = S.AnnBinderP S.PlainBinder (SafeVersionE e)
  toSafeB _ _ _ _ = undefined
  fromSafeB _ _ _ = undefined

instance HasSafeVersionE D.EffectRow where
  type SafeVersionE D.EffectRow = S.EffectRow
  toSafeE = undefined
  fromSafeE = undefined

data DWithArrow (e :: *) = DWithArrow D.Arrow e

instance HasSafeVersionE e => HasSafeVersionE (DWithArrow e) where
  type SafeVersionE (DWithArrow e) = S.WithArrow (SafeVersionE e)
  toSafeE = undefined
  fromSafeE = undefined

instance (HasSafeVersionB b, HasSafeVersionE e)
         => HasSafeVersionE (D.Abs b e) where
  type SafeVersionE (D.Abs b e) = S.Abs (SafeVersionB b) (SafeVersionE e)
  toSafeE = undefined
  fromSafeE = undefined

instance HasSafeVersionB b => HasSafeVersionB (D.Nest b) where
  type SafeVersionB (D.Nest b) = S.Nest (SafeVersionB b)
  toSafeB _ _ _ _ = undefined
  fromSafeB _ _ _ = undefined
