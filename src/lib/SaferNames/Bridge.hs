-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -w #-}

module SaferNames.Bridge (HasSafeVersionE (..), HasSafeVersionB (..),
                          toSafeBindings)  where

import Data.Foldable (toList)
import qualified Data.Set as Set

import LabeledItems
import Syntax
import Env
import Type
import Data.Maybe (fromJust)

import qualified Data.Map.Strict as M

import SaferNames.NameCore
import SaferNames.Name
import SaferNames.Syntax
import SaferNames.LazyMap as LM

import qualified Syntax as D  -- D for Danger
import qualified Env    as D

import qualified SaferNames.NameCore  as S
import qualified SaferNames.Name      as S
import qualified SaferNames.Syntax    as S

toSafeBindings :: D.Bindings -> S.Scope n
toSafeBindings = undefined
-- toSafeBindings (Env bindings) = undefined
--   S.RecEnv $ S.UnsafeMakeEnv $ LM.newLazyMap (M.keysSet bindings) \v ->
--     toSafeBinderInfo $ fromJust (M.lookup v bindings)

toSafeBinderInfo :: (D.Type, D.BinderInfo) -> S.TypedBinderInfo n
toSafeBinderInfo (ty, info) = S.TypedBinderInfo (toSafeE ty) (toSafeE info)

class HasSafeVersionE (e:: *) where
  type SafeVersionE e :: S.E
  toSafeE   :: e -> SafeVersionE e n
  fromSafeE :: SafeVersionE e n -> e

class HasSafeVersionB (b:: *) where
  type SafeVersionB b :: S.B
  toSafeB   :: b -> SafeVersionB b n l
  fromSafeB :: SafeVersionB b n l -> b

instance HasSafeVersionE D.Name where
  type SafeVersionE D.Name = S.AtomName
  toSafeE name = UnsafeMakeName name
  fromSafeE (UnsafeMakeName name) = name

instance HasSafeVersionE D.Atom where
  type SafeVersionE D.Atom = S.Atom

  toSafeE atom = case atom of
    D.Var v -> S.Var $ toSafeE v
    -- D.Lam (D.Abs b (arr, body)) ->
    --   S.Lam $ S.Abs (toSafeB b) (S.WithArrow (fmap toSafeE arr) (toSafeE body))
    -- D.Pi  (D.Abs b (arr, body)) ->
    --   S.Pi  $ S.Abs (toSafeB b) (S.WithArrow (fmap toSafeE arr) (toSafeE body))
    -- D.DataCon dataDef params con args ->
    --   S.DataCon (toSafeE dataDef) (map toSafeE params) con (map toSafeE args)
    -- D.TypeCon dataDef params ->
    --   S.TypeCon (toSafeE dataDef) (map toSafeE params)
    D.LabeledRow (Ext items t) -> S.LabeledRow $ Ext (fmap toSafeE items) (fmap toSafeE t)
    D.Record items -> S.Record $ fmap toSafeE items
    D.RecordTy (Ext items t) -> S.RecordTy $ Ext (fmap toSafeE items) (fmap toSafeE t)
    D.Variant (Ext items t) label idx val ->
      S.Variant (Ext (fmap toSafeE items) (fmap toSafeE t)) label idx (toSafeE val)
    D.VariantTy (Ext items t) -> S.VariantTy $ Ext (fmap toSafeE items) (fmap toSafeE t)
    D.Con con -> S.Con $ fmap toSafeE con
    D.TC  tc  -> S.TC  $ fmap toSafeE tc
    D.Eff effs -> S.Eff $ toSafeE effs
    -- D.ACase scrut alts ty -> S.ACase (toSafeE scrut) (map toSafeE alts) (toSafeE ty)
    -- D.DataConRef dataDef params args ->
    --   S.DataConRef (toSafeE dataDef) (map toSafeE params) (S.Abs (toSafeB args) S.UnitE)
    -- D.BoxedRef b ptr size body ->
    --   S.BoxedRef (toSafeE ptr) (toSafeE size) (S.Abs (toSafeB b) (toSafeE body))
    D.ProjectElt idxs (v D.:> _) -> S.ProjectElt idxs $ (S.UnsafeMakeName v)
  fromSafeE atom = case atom of
    S.Var v -> D.Var $ fromSafeE v
    -- S.Lam (S.Abs b (S.WithArrow arr body)) ->
    --   D.Lam $ D.Abs (fromSafeB b) (fmap fromSafeE arr, fromSafeE body)
    -- S.Pi  (S.Abs b (S.WithArrow arr body)) ->
    --   D.Pi  $ D.Abs (fromSafeB b) (fmap fromSafeE arr, fromSafeE body)
    -- S.DataCon dataDef params con args ->
    --   D.DataCon (fromSafeE dataDef) (map fromSafeE params) con (map fromSafeE args)
    -- S.TypeCon dataDef params ->
    --   D.TypeCon (fromSafeE dataDef) (map fromSafeE params)
    S.LabeledRow (Ext items t) -> D.LabeledRow $ Ext (fmap fromSafeE items) (fmap fromSafeE t)
    S.Record items -> D.Record $ fmap fromSafeE items
    S.RecordTy (Ext items t) -> D.RecordTy $ Ext (fmap fromSafeE items) (fmap fromSafeE t)
    S.Variant (Ext items t) label idx val ->
      D.Variant (Ext (fmap fromSafeE items) (fmap fromSafeE t)) label idx (fromSafeE val)
    S.VariantTy (Ext items t) -> D.VariantTy $ Ext (fmap fromSafeE items) (fmap fromSafeE t)
    S.Con con -> D.Con $ fmap fromSafeE con
    S.TC  tc  -> D.TC  $ fmap fromSafeE tc
    S.Eff effs -> D.Eff $ fromSafeE effs
    -- S.ACase scrut alts ty -> D.ACase (fromSafeE scrut) (map fromSafeE alts) (fromSafeE ty)
    -- S.DataConRef dataDef params (S.Abs args S.UnitE) ->
    --   D.DataConRef (fromSafeE dataDef) (map fromSafeE params) (fromSafeB args)
    -- S.BoxedRef ptr size (S.Abs b body) ->
    --   D.BoxedRef (fromSafeB b) (fromSafeE ptr) (fromSafeE size) (fromSafeE body)
    S.ProjectElt idxs v -> D.ProjectElt idxs $ fromSafeE v

instance HasSafeVersionE e => HasSafeVersionE (VarP e) where
  type SafeVersionE (VarP e) = AtomName
  toSafeE (name D.:> _) = UnsafeMakeName name
  fromSafeE (UnsafeMakeName name) = undefined -- name D.:> fromSafeE ty

instance HasSafeVersionE D.DataDef where
  type SafeVersionE D.DataDef = S.DataDef
  -- toSafeE (D.DataDef name paramBinders cons) =
  --     S.DataDef name paramBinders' $ map toSafeE cons
  --     where paramBinders' = dBinderListToSBinderList $ toList paramBinders
  -- fromSafeE (S.DataDef name paramBinders cons) =
  --   D.DataDef name (D.toNest $ sBinderListToDBinderList paramBinders) (map fromSafeE cons)

instance HasSafeVersionE D.BinderInfo where
  type SafeVersionE D.BinderInfo = S.AtomBinderInfo
  toSafeE = undefined
  fromSafeE = undefined

unsafeToNest :: [b n' l'] -> S.Nest b n l
unsafeToNest [] = unsafeCoerceB S.Empty
unsafeToNest (b:bs) = S.Nest (unsafeCoerceB b) (unsafeCoerceB (unsafeToNest bs))

unsafeFromNest :: S.Nest b n l -> [b n' l']
unsafeFromNest S.Empty = []
unsafeFromNest (S.Nest b bs) = unsafeCoerceB b : unsafeFromNest (unsafeCoerceB bs)

-- dBinderListToSBinderList :: [D.Binder] -> S.BinderList n l
-- dBinderListToSBinderList = undefined
-- dBinderListToSBinderList bs = unsafeToNest vs S.:> ListE tys
--   where (vs, tys) = unzip [ (v,ty) | (v S.:> ty) <- map toSafeB bs]

-- sBinderListToDBinderList :: S.BinderList n l -> [D.Binder]
-- sBinderListToDBinderList = undefined
-- sBinderListToDBinderList (vs S.:> ListE tys) =
--   map fromSafeB $ zipWith (S.:>) (unsafeFromNest vs) tys

instance HasSafeVersionE D.DataConDef where
  type SafeVersionE D.DataConDef = S.DataConDef
  -- toSafeE (D.DataConDef name bs) = S.DataConDef name $ S.Abs (toSafeB bs) S.UnitE
  -- fromSafeE (S.DataConDef name (S.Abs bs S.UnitE)) = D.DataConDef name $ fromSafeB bs

instance HasSafeVersionB D.DataConRefBinding where
  type SafeVersionB D.DataConRefBinding = S.DataConRefBinding
  toSafeB = undefined
  fromSafeB = undefined

instance HasSafeVersionE D.Expr where
  type SafeVersionE D.Expr = S.Expr
  toSafeE expr = case expr of
    D.App f x -> S.App (toSafeE f) (toSafeE x)
    -- D.Case scrut alts ty -> S.Case (toSafeE scrut) (map toSafeE alts) (toSafeE ty)
    D.Atom x -> S.Atom (toSafeE x)
    D.Op op -> S.Op (fmap toSafeE op)
    D.Hof hof -> S.Hof (fmap toSafeE hof)

  fromSafeE expr = case expr of
    S.App f x -> D.App (fromSafeE f) (fromSafeE x)
    -- S.Case scrut alts ty -> D.Case (fromSafeE scrut) (map fromSafeE alts) (fromSafeE ty)
    S.Atom x -> D.Atom (fromSafeE x)
    S.Op op -> D.Op (fmap fromSafeE op)
    S.Hof hof -> D.Hof (fmap fromSafeE hof)

instance HasSafeVersionE D.Block where
  type SafeVersionE D.Block = S.Block
  toSafeE (D.Block decls result) =
    case toSafeE $ D.Abs decls result of
      S.Abs decls' result' -> S.Block (toSafeE (getType result)) decls' result'
  fromSafeE (S.Block _ decls result) =
    case fromSafeE $ S.Abs decls result of
      D.Abs decls' result' -> D.Block decls' result'

instance HasSafeVersionB D.Decl where
  type SafeVersionB D.Decl = S.Decl
  -- toSafeB   (D.Let ann b expr) = S.Let ann (toSafeB   b) (toSafeE   expr)
  -- fromSafeB (S.Let ann b expr) = D.Let ann (fromSafeB b) (fromSafeE expr)

instance HasSafeVersionE e => HasSafeVersionB (D.BinderP e) where
  -- type SafeVersionB (D.BinderP e) = S.AnnBinderP (S.NameBinder S.TypedBinderInfo) (SafeVersionE e)
  -- toSafeB b = case b of
  --   D.Bind (v D.:> ann) -> UnsafeMakeBinder v S.:> toSafeE ann
  -- fromSafeB (b S.:> ann) = case b of
  --   UnsafeMakeBinder v -> D.Bind (v D.:> fromSafeE ann)

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

instance (HasSafeVersionB b, HasSafeVersionE e) => HasSafeVersionE (D.Abs b e) where
  type SafeVersionE (D.Abs b e) = S.Abs (SafeVersionB b) (SafeVersionE e)
  toSafeE (D.Abs b e) = S.Abs (toSafeB b) (toSafeE e)
  fromSafeE (S.Abs b e) = D.Abs (fromSafeB b) (fromSafeE e)

instance HasSafeVersionB b => HasSafeVersionB (D.Nest b) where
  type SafeVersionB (D.Nest b) = S.Nest (SafeVersionB b)
  toSafeB nest = case nest of
    D.Empty -> unsafeCoerceB $ S.Empty
    D.Nest b rest -> S.Nest (toSafeB b) (toSafeB rest)

  fromSafeB nest = case nest of
    S.Empty -> D.Empty
    S.Nest b rest -> D.Nest (fromSafeB b) (fromSafeB rest)
