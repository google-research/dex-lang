-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module SaferNames.Bridge
  ( BridgeNameMap, EnvDS, EnvSD, HasSafeVersionE (..)
  , HasSafeVersionB (..), DEvaluatedModule (..), SEvaluatedModule (..)
  , TopBindings (..), toSafeETop, fromSafeETop, extendTopBindings
  , UnsafeTopBindings, unsafeExtendTopBindings) where

import Data.Maybe (fromJust)

import Syntax
import Env

import SaferNames.Name
import SaferNames.Syntax

import qualified Syntax as D  -- D for Danger
import qualified Env    as D

import qualified SaferNames.Syntax as S
import qualified SaferNames.Name   as S

type EnvDS n = D.Env   (S.Name n)
type EnvSD n = S.Env n  D.Name

type BridgeNameMap n = ( S.Env n D.Name
                       , D.Env  (S.Name n))

class HasSafeVersionE (e:: *) where
  type SafeVersionE e :: S.E
  toSafeE   :: S.Scope n -> EnvDS n -> e -> SafeVersionE e n
  fromSafeE :: D.Scope   -> EnvSD n -> SafeVersionE e n -> e

class HasSafeVersionB (b:: *) where
  type SafeVersionB b :: S.B
  toSafeB   :: S.Scope n -> EnvDS n -> b
            -> (forall l. SafeVersionB b n l -> EnvDS l -> a)
            -> a
  fromSafeB :: D.Scope -> EnvSD n -> SafeVersionB b n l -> (b, EnvSD (n:-:l))

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

instance HasSafeVersionE D.Expr where
  type SafeVersionE D.Expr = S.Expr

instance HasSafeVersionE D.Block where
  type SafeVersionE D.Block = S.Block
  toSafeE scope env (D.Block decls result) =
    case toSafeE scope env $ D.Abs decls result of
      S.Abs decls' result' -> S.Block decls' result'
  fromSafeE scope env (S.Block decls result) =
    case fromSafeE scope env $ S.Abs decls result of
      D.Abs decls' result' -> D.Block decls' result'

instance HasSafeVersionB D.Decl where
  type SafeVersionB D.Decl = S.Decl
  toSafeB scope env (D.Let ann b expr) cont =
    let expr' = toSafeE scope env expr
    in toSafeB scope env b \b' env' ->
      cont (S.Let ann b' expr') env'
  fromSafeB scope env (S.Let ann b expr) =
    let expr' = fromSafeE scope env expr
        (b', env') = fromSafeB scope env b
    in (D.Let ann b' expr', env')

instance HasSafeVersionE e => HasSafeVersionB (D.BinderP e) where
  type SafeVersionB (D.BinderP e) = S.AnnBinderP S.PlainBinder (SafeVersionE e)
  toSafeB scope env b cont = case b of
    D.Ignore ann ->
      let ann' = toSafeE scope env ann
      in cont (S.Ignore S.:> ann') mempty
    -- we drop the inliner hint here, but that's ok because this should only be
    -- used at the top level
    D.BindWithHint _ b@(v D.:> ann) ->
      let ann' = toSafeE scope env ann
      in withFresh scope \_ b' v' ->
        cont (b' S.:> ann') (b D.@> v')

  fromSafeB _ _ _ = undefined

instance HasSafeVersionE D.EffectRow where
  type SafeVersionE D.EffectRow = S.EffectRow
  toSafeE = undefined
  fromSafeE = undefined

data DWithArrow (e :: *) = DWithArrow D.Arrow e

instance HasSafeVersionE e => HasSafeVersionE (DWithArrow e) where
  type SafeVersionE (DWithArrow e) = S.WithArrow (SafeVersionE e)
  toSafeE scope env (DWithArrow arr body) =
    S.WithArrow (fmap (toSafeE scope env) arr) (toSafeE scope env body)
  fromSafeE scope env (S.WithArrow arr body) =
    DWithArrow (fmap (fromSafeE scope env) arr) (fromSafeE scope env body)

instance (BindsVars b, HasNamesB (SafeVersionB b), HasSafeVersionB b, HasSafeVersionE e)
         => HasSafeVersionE (D.Abs b e) where
  type SafeVersionE (D.Abs b e) = S.Abs (SafeVersionB b) (SafeVersionE e)
  toSafeE scope env (D.Abs b e) =
    toSafeB scope env b \b' env' ->
      S.Abs b' $ toSafeE (extendScope scope b') env' e
  fromSafeE scope env (S.Abs b e) =
    let (b', env') = fromSafeB scope env b
        e' = fromSafeE (scope <> undefined) (env <>> env') e
    in D.Abs b' e'

instance HasSafeVersionB b => HasSafeVersionB (D.Nest b) where
  type SafeVersionB (D.Nest b) = S.Nest (SafeVersionB b)
  toSafeB _ _ _ _ = undefined
  fromSafeB _ _ _ = undefined

data DEvaluatedModule        = DEvaluatedModule D.Bindings
data SEvaluatedModule (n::S) = SEvaluatedModule (EvaluatedModule n)

instance HasSafeVersionE DEvaluatedModule where
  type SafeVersionE DEvaluatedModule = SEvaluatedModule
  toSafeE   _ = undefined
  fromSafeE _ = undefined

-- === working with top-level bindings ===

data TopBindings n = TopBindings
  { topSourceMap :: S.SourceNameMap n
  , sBindings :: S.Bindings n
  , dBindings :: D.Bindings
  , bridgeMap :: BridgeNameMap n }

toSafeETop :: HasSafeVersionE e => TopBindings n -> e -> SafeVersionE e n
toSafeETop env x = let
  scope =  envAsScope $ fromRecEnv $ sBindings env
  toSafeMap = snd $ bridgeMap env
  in toSafeE scope toSafeMap x

fromSafeETop :: HasSafeVersionE e => TopBindings n -> SafeVersionE e n -> e
fromSafeETop env x = let
  scope = dBindings $ env
  fromSafeMap = fst $ bridgeMap $ env
  in fromSafeE scope fromSafeMap x

extendTopBindings :: TopBindings n -> S.EvaluatedModule n
                  -> (forall l. TopBindings l -> a) -> a
extendTopBindings _ _ _ = undefined

-- Used for Live and Export, which don't work with safe names yet
type UnsafeTopBindings = TopBindings UnsafeMakeS

instance Semigroup UnsafeTopBindings where
  (<>) = undefined

instance Monoid UnsafeTopBindings where
  mempty = undefined

unsafeExtendTopBindings :: UnsafeTopBindings -> D.Name -> (D.Type, D.BinderInfo) -> UnsafeTopBindings
unsafeExtendTopBindings = undefined
