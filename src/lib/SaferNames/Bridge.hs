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

module SaferNames.Bridge (HasSafeVersionE (..), HasSafeVersionB (..))  where

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

class HasSafeVersionE (e:: *) where
  type SafeVersionE e :: S.E
  toSafeE   :: e -> SafeVersionE e n
  fromSafeE :: SafeVersionE e n -> e

class HasSafeVersionB (b:: *) where
  type SafeVersionB b :: S.B
  toSafeB   :: b -> SafeVersionB b n l
  fromSafeB :: SafeVersionB b n l -> b

instance HasSafeVersionE D.Name where
  type SafeVersionE D.Name = S.Name
  toSafeE name = UnsafeMakeName name
  fromSafeE (UnsafeMakeName name) = name

instance HasSafeVersionE D.Atom where
  type SafeVersionE D.Atom = S.Atom

  toSafeE atom = case atom of
    D.Lam (D.Abs b (arr, body)) -> S.Lam $ toSafeE (D.Abs b (DWithArrow arr body))
    D.Pi  (D.Abs b (arr, body)) -> S.Pi  $ toSafeE (D.Abs b (DWithArrow arr body))
    D.Con con -> S.Con $ fmap toSafeE con
    D.TC  tc  -> S.TC  $ fmap toSafeE tc

  fromSafeE atom = case atom of
    S.Con con -> D.Con $ fmap fromSafeE con

instance HasSafeVersionE D.Expr where
  type SafeVersionE D.Expr = S.Expr

instance HasSafeVersionE D.Block where
  type SafeVersionE D.Block = S.Block
  toSafeE (D.Block decls result) =
    case toSafeE $ D.Abs decls result of
      S.Abs decls' result' -> S.Block decls' result'
  fromSafeE (S.Block decls result) =
    case fromSafeE $ S.Abs decls result of
      D.Abs decls' result' -> D.Block decls' result'

instance HasSafeVersionB D.Decl where
  type SafeVersionB D.Decl = S.Decl
  toSafeB   (D.Let ann b expr) = S.Let ann (toSafeB   b) (toSafeE   expr)
  fromSafeB (S.Let ann b expr) = D.Let ann (fromSafeB b) (fromSafeE expr)

instance HasSafeVersionE e => HasSafeVersionB (D.BinderP e) where
  type SafeVersionB (D.BinderP e) = S.AnnBinderP S.PlainBinder (SafeVersionE e)

instance HasSafeVersionE D.Effect where
  type SafeVersionE D.Effect = S.Effect
  toSafeE eff = case eff of
    D.RWSEffect rws h -> S.RWSEffect rws $ toSafeE h
    D.ExceptionEffect -> S.ExceptionEffect
    D.IOEffect -> S.IOEffect
  fromSafeE eff = case eff of
    S.RWSEffect rws h -> D.RWSEffect rws $ fromSafeE h
    S.ExceptionEffect -> D.ExceptionEffect
    S.IOEffect -> D.IOEffect

instance HasSafeVersionE D.EffectRow where
  type SafeVersionE D.EffectRow = S.EffectRow
  toSafeE (D.EffectRow effs v) = S.EffectRow (Set.map toSafeE effs) (fmap toSafeE v)
  fromSafeE (S.EffectRow effs v) = D.EffectRow (Set.map fromSafeE effs) (fmap fromSafeE v)

data DWithArrow (e :: *) = DWithArrow D.Arrow e

instance HasSafeVersionE e => HasSafeVersionE (DWithArrow e) where
  type SafeVersionE (DWithArrow e) = S.WithArrow (SafeVersionE e)
  toSafeE   (DWithArrow  arr body) = S.WithArrow (fmap toSafeE   arr) (toSafeE   body)
  fromSafeE (S.WithArrow arr body) = DWithArrow  (fmap fromSafeE arr) (fromSafeE body)

instance (BindsVars b, HasNamesB (SafeVersionB b), HasSafeVersionB b, HasSafeVersionE e)
         => HasSafeVersionE (D.Abs b e) where
  type SafeVersionE (D.Abs b e) = S.Abs (SafeVersionB b) (SafeVersionE e)
  toSafeE (D.Abs b e) = S.Abs (toSafeB b) (toSafeE e)
  fromSafeE (S.Abs b e) = D.Abs (fromSafeB b) (fromSafeE e)

instance (BindsVars b, HasSafeVersionB b, HasNamesB (SafeVersionB b))
         => HasSafeVersionB (D.Nest b) where
  type SafeVersionB (D.Nest b) = S.Nest (SafeVersionB b)
  toSafeB nest = case nest of
    D.Empty -> unsafeCoerceB $ S.Empty
    D.Nest b rest -> S.Nest (toSafeB b) (toSafeB rest)

  fromSafeB nest = case nest of
    S.Empty -> D.Empty
    S.Nest b rest -> D.Nest (fromSafeB b) (fromSafeB rest)

data DEvaluatedModule        = DEvaluatedModule D.Bindings
data SEvaluatedModule (n::S) = SEvaluatedModule (EvaluatedModule n)

instance HasSafeVersionE DEvaluatedModule where
  type SafeVersionE DEvaluatedModule = SEvaluatedModule
  toSafeE   _ = undefined
  fromSafeE _ = undefined
