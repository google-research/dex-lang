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
import qualified Data.Set as Set
import Unsafe.Coerce

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

-- like FreshBinder, but the renaming fragment takes dangerous names as input
data FreshBinderD (b::S.B) (n::S.S) where
  FreshBinderD :: FreshExt o o' -> b o o' -> EnvDS o' -> FreshBinderD b o

injectDEnvNamesL :: FreshExt n l -> EnvDS n -> EnvDS l
injectDEnvNamesL _ env = unsafeCoerce env

class HasSafeVersionE (e:: *) where
  type SafeVersionE e :: S.E
  toSafeE   :: S.Scope n -> EnvDS n -> e -> SafeVersionE e n
  fromSafeE :: D.Scope   -> EnvSD n -> SafeVersionE e n -> e

class HasSafeVersionB (b:: *) where
  type SafeVersionB b :: S.B
  toSafeB   :: S.Scope n -> EnvDS n -> b -> FreshBinderD (SafeVersionB b) n
  fromSafeB :: D.Scope -> EnvSD n -> SafeVersionB b n l -> (b, EnvSD (n:=>:l))

instance HasSafeVersionE D.Name where
  type SafeVersionE D.Name = S.Name
  toSafeE _ env name =
    case D.envLookup env name of
      Nothing -> error "oops"
      Just name' -> name'
  fromSafeE _ env name = S.envLookup env name

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
  toSafeB scope env (D.Let ann b expr) = do
    let expr' = toSafeE scope env expr
    case toSafeB scope env b of
      FreshBinderD ext b' env' ->
        FreshBinderD ext (S.Let ann b' expr') env'
  fromSafeB scope env (S.Let ann b expr) =
    let expr' = fromSafeE scope env expr
        (b', env') = fromSafeB scope env b
    in (D.Let ann b' expr', env')

instance HasSafeVersionE e => HasSafeVersionB (D.BinderP e) where
  type SafeVersionB (D.BinderP e) = S.AnnBinderP S.PlainBinder (SafeVersionE e)
  toSafeB scope env b = case b of
    D.Ignore ann ->
      let ann' = toSafeE scope env ann
      in FreshBinderD emptyFreshExt (S.Ignore S.:> ann') mempty
    -- we drop the inliner hint here, but that's ok because this should only be
    -- used at the top level
    D.BindWithHint _ (v D.:> ann) -> do
      let ann' = toSafeE scope env ann
      withFresh scope \ext b' v' ->
        FreshBinderD ext (b' S.:> ann') (v D.@> v')

  fromSafeB scope env (v S.:> ann) =
    let ann' = fromSafeE scope env ann
        v' = genFresh "v" scope
    in (Bind (v' D.:> ann'), v S.@> v')

instance HasSafeVersionE D.Effect where
  type SafeVersionE D.Effect = S.Effect
  toSafeE scope env eff = case eff of
    D.RWSEffect rws h -> S.RWSEffect rws $ toSafeE scope env h
    D.ExceptionEffect -> S.ExceptionEffect
    D.IOEffect -> S.IOEffect
  fromSafeE scope env eff = case eff of
    S.RWSEffect rws h -> D.RWSEffect rws $ fromSafeE scope env h
    S.ExceptionEffect -> D.ExceptionEffect
    S.IOEffect -> D.IOEffect

instance HasSafeVersionE D.EffectRow where
  type SafeVersionE D.EffectRow = S.EffectRow
  toSafeE scope env (D.EffectRow effs v) =
    S.EffectRow (Set.map (toSafeE scope env) effs) (fmap (toSafeE scope env) v)
  fromSafeE scope env (S.EffectRow effs v) =
    D.EffectRow (Set.map (fromSafeE scope env) effs) (fmap (fromSafeE scope env) v)

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
    case toSafeB scope env b of
      FreshBinderD ext b' frag -> do
        let scope' = extendScope scope b'
        let env' = injectDEnvNamesL ext env <> frag
        S.Abs b' $ toSafeE scope' env' e
  fromSafeE scope env (S.Abs b e) =
    let (b', env') = fromSafeB scope env b
        e' = fromSafeE (scope <> D.boundVars b') (env <>> env') e
    in D.Abs b' e'

data DNestPair b1 b2 = DNestPair b1 b2

instance (BindsVars b1, HasSafeVersionB b1, HasNamesB (SafeVersionB b1),
          BindsVars b2, HasSafeVersionB b2, HasNamesB (SafeVersionB b2))
       => HasSafeVersionB (DNestPair b1 b2) where
  type SafeVersionB (DNestPair b1 b2) = S.NestPair (SafeVersionB b1) (SafeVersionB b2)
  toSafeB scope env (DNestPair b1 b2) =
    case toSafeB scope env b1 of
      FreshBinderD ext1 b1' frag1 -> do
        let scope' = extendScope scope b1'
        let env' = injectDEnvNamesL ext1 env <> frag1
        case toSafeB scope' env' b2 of
          FreshBinderD ext2 b2' frag2 -> do
            let fragOut = injectDEnvNamesL ext2 frag1 <> frag2
            FreshBinderD (composeFreshExt ext1 ext2) (S.NestPair b1' b2') fragOut
  fromSafeB scope env (S.NestPair b1 b2) = do
    let (b1', frag1) = fromSafeB scope env b1
    let scope' = scope <> D.boundVars b1'
    let env' = env <>> frag1
    let (b2', frag2) = fromSafeB scope' env' b2
    (DNestPair b1' b2', frag1 <.> frag2)

instance (BindsVars b, HasSafeVersionB b, HasNamesB (SafeVersionB b))
         => HasSafeVersionB (D.Nest b) where
  type SafeVersionB (D.Nest b) = S.Nest (SafeVersionB b)
  toSafeB scope env nest = case nest of
    D.Empty -> FreshBinderD emptyFreshExt S.Empty mempty
    D.Nest b rest ->
      case toSafeB scope env (DNestPair b rest) of
        FreshBinderD ext (S.NestPair b' rest') renamer ->
          FreshBinderD ext (S.Nest b' rest') renamer
  fromSafeB scope env nest = case nest of
    S.Empty -> (D.Empty, S.emptyEnv)
    S.Nest b rest -> do
      let (DNestPair b' rest', frag) = fromSafeB scope env (S.NestPair b rest)
      (D.Nest b' rest', frag)

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
