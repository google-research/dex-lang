-- Copyright 2020 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE DerivingVia #-}

module MDImp (impToMDImp) where

import Control.Monad
import qualified Data.Set as S

import Env
import Syntax
import PPrint
import Cat


import Debug.Trace

impToMDImp :: ImpFunction -> MDImpFunction ImpKernel
impToMDImp (ImpFunction dests args prog) = MDImpFunction dests args $ progToMD prog

-- Set of variables allocated on the host
type TranslationState = S.Set Name
type Translate = Cat TranslationState

isHostPtr :: IVar -> Translate Bool
isHostPtr v = looks $ S.member (varName v)

progToMD :: ImpProg -> MDImpProg ImpKernel
progToMD (ImpProg stmts) = MDImpProg $ evalCat $ forM stmts (\s@(d, _) -> (d,) <$> stmtToMDInstr s)

-- TODO: Collapse loops, hoist allocations, etc.
stmtToMDInstr :: ImpStatement -> Translate (MDImpInstr ImpKernel)
stmtToMDInstr (~(Just d), instr) = case traceShowId instr of
  Alloc t s -> case t of
    BaseTy _ -> extend (S.singleton $ varName d) >> keep
    _        -> return $ MDAlloc t s
  Free v    -> do
    isHost <- isHostPtr v
    if isHost then keep else return $ MDFree v
  IPrimOp _ -> keep
  -- XXX: This is super unsafe! We have no guarantee that different iterations won't race!
  --      Now that Imp is not necessarily the last stop before codegen, we should make it
  --      emit some extra loop tags to ensure that transforms like this one are safe!
  Loop Fwd v s p     -> do
    -- I think that this should never happen, because the only reason why we might allocate
    -- a destination for a scalar value (and we only allow scalar references in host memory)
    -- is when it is an output of the Imp function. However, in that case the kernel should
    -- close over the value and not the reference, so it should work out fine.
    -- Anyway, if this ends up crashing the compiler at some point, then we will simply have
    -- to host some loads outside of the kernel.
    forM_ args (assertRef False)
    return $ MDLaunch s args $ ImpKernel args v p
    where args = envAsVars $ (freeIVars p `envDiff` (v @> ()))
  Load  ~(IVar v)    -> assertRef True v >> keep
  Store ~(IVar v) _  -> assertRef True v >> keep
  IOffset _ _ _      -> notAllowed -- Shouldn't need to offset pointers on the host.
  IWhile _ _         -> notAllowed -- TODO: Allow while loops? Those are not paralellizable anyway.
  If _ _ _           -> notAllowed
  Loop _ _ _ _       -> notAllowed
  IThrowError        -> notAllowed
  where
    keep :: Translate (MDImpInstr ImpKernel)
    keep = return $ MDHostInstr instr
    assertRef onHost v = do
      isHost <- isHostPtr v
      if isHost == onHost then return () else error "Dereferencing a device pointer on the host!"
    notAllowed = error $ "Not allowed in multi-device program: " ++ pprint instr
