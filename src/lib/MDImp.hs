-- Copyright 2020 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DuplicateRecordFields #-}

module MDImp (impToMDImp) where

import Env
import Syntax
import PPrint

impToMDImp :: ImpFunction -> MDImpFunction ImpKernel
impToMDImp (ImpFunction dests args prog) = MDImpFunction dests args $ progToMD prog

progToMD :: ImpProg -> MDImpProg ImpKernel
progToMD (ImpProg stmts) = MDImpProg $ fmap (\(b, instr) -> (b, instrToMD instr)) stmts

-- TODO: Collapse loops, hoist allocations, etc.
instrToMD :: ImpInstr -> MDImpInstr ImpKernel
instrToMD instr = case instr of
  Alloc t s      -> MDAlloc t s
  Free v         -> MDFree v
  IPrimOp op     -> MDPrimOp op
  -- XXX: This is super unsafe! We have no guarantee that different iterations won't race!
  --      Now that Imp is not necessarily the last stop before codegen, we should make it
  --      emit some extra loop tags to ensure that transforms like this one are safe!
  Loop Fwd v s p -> MDLaunch s args $ ImpKernel args v p
    where args = envAsVars $ (freeIVars p `envDiff` (v @> ()))
  Load _         -> notAllowed
  Store _ _      -> notAllowed
  IOffset _ _ _  -> notAllowed
  IWhile _ _     -> notAllowed -- TODO: Allow while loops? Those are not paralellizable anyway.
  Loop _ _ _ _   -> notAllowed
  where notAllowed = error $ "Not allowed in multi-device program: " ++ pprint instr
