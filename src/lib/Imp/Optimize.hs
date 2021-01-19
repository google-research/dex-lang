-- Copyright 2020 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module Imp.Optimize (liftCUDAAllocations) where

import Control.Monad

import PPrint
import Env
import Cat
import Syntax
import Imp.Builder

-- TODO: DCE!

type AllocInfo    = (BaseType, Int)
type FuncAllocEnv = [(IBinder, AllocInfo)]
type ModAllocEnv  = Env [AllocInfo]

liftCUDAAllocations :: ImpModule -> ImpModule
liftCUDAAllocations m =
    fst $ runCat (traverseImpModule liftFunc m) mempty
  where
    liftFunc :: Env IFunVar -> ImpFunction -> Cat ModAllocEnv ImpFunction
    liftFunc fenv f = case f of
      FFIFunction _ -> return f
      ImpFunction (fname:>IFunType cc argTys retTys) argBs' body' -> case cc of
        CUDAKernelLaunch -> do
          let ((argBs, body), fAllocEnv) =
                flip runCat mempty $ runISubstBuilderT (ISubstEnv mempty fenv) $ do
                  ~args@(tid:wid:wsz:_) <- traverse freshIVar argBs'
                  newBody <- extendValSubst (newEnv argBs' $ fmap IVar args) $ buildScoped $ do
                    gtid <- iadd (IVar tid) =<< imul (IVar wid) (IVar wsz)
                    evalImpBlock (liftAlloc gtid) body'
                  return (fmap Bind args, newBody)
          let (allocBs, allocs) = unzip fAllocEnv
          extend $ fname @> allocs
          let newFunTy = IFunType cc (argTys ++ fmap binderAnn allocBs) retTys
          return $ ImpFunction (fname :> newFunTy) (argBs ++ allocBs) body
        _ -> traverseImpFunction amendLaunch fenv f

    liftAlloc :: IExpr -> ITraversalDef (Cat FuncAllocEnv)
    liftAlloc gtid = (liftAllocDecl, traverseImpInstr rec)
      where
        rec = liftAlloc gtid
        liftAllocDecl decl = case decl of
          ImpLet [b] (Alloc addrSpace ty (IIdxRepVal size)) ->
            case addrSpace of
              Stack    -> traverseImpDecl rec decl
              Heap CPU -> error "Unexpected CPU allocation in a CUDA kernel"
              Heap GPU -> do
                bArg <- freshIVar b
                liftSE $ extend $ [(Bind bArg, (ty, fromIntegral size))]
                ptr <- ptrOffset (IVar bArg) =<< imul gtid (IIdxRepVal size)
                return $ b @> ptr
          ImpLet _ (Alloc _ _ _) ->
            error $ "Failed to lift an allocation out of a CUDA kernel: " ++ pprint decl
          ImpLet _ (Free _) -> return mempty
          _                 -> traverseImpDecl rec decl

    amendLaunch :: ITraversalDef (Cat ModAllocEnv)
    amendLaunch = (traverseImpDecl amendLaunch, amendLaunchInstr)
      where
        amendLaunchInstr :: ImpInstr -> ISubstBuilderT (Cat ModAllocEnv) ImpInstr
        amendLaunchInstr instr = case instr of
          ILaunch f' s' args' -> do
            s <- traverseIExpr s'
            args <- traverse traverseIExpr args'
            liftedAllocs <- liftSE $ looks (!f')
            f <- traverseIFunVar f'
            extraArgs <- case null liftedAllocs of
              True -> return []
              False -> do
                ~[numWorkgroups, workgroupSize] <- emit $ IQueryParallelism f s
                nthreads <- imul numWorkgroups workgroupSize
                forM liftedAllocs $ \(ty, size) -> do
                  totalSize <- imul (IIdxRepVal $ fromIntegral size) nthreads
                  alloc (Heap GPU) ty totalSize
            return $ ILaunch f s (args ++ extraArgs)
          _ -> traverseImpInstr amendLaunch instr
