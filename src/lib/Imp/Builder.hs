-- Copyright 2020 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module Imp.Builder ( ISubstBuilderT, ISubstEnv (..)
                   , runISubstBuilderT, liftSE
                   , emit, freshIVar, extendValSubst
                   , buildScoped
                   -- IR builders
                   , iadd, imul
                   , alloc, ptrOffset
                   -- traversal
                   , traverseImpModule, traverseImpFunction
                   , traverseImpBlock, evalImpBlock
                   , traverseImpDecl, traverseImpInstr
                   , traverseIExpr, traverseIFunVar
                   , ITraversalDef, substTraversalDef
                   ) where

import Control.Monad.Reader

import Env
import Cat
import Syntax
import Imp
import Util (bindM2)

-- XXX: Scope is actually global within each function
data IBuilderEnv = IBuilderEnv
  { scope :: Env ()
  , blockDecls :: Nest ImpDecl
  }
data ISubstEnv = ISubstEnv
  { valSubst  :: Env IExpr
  , funcSubst :: Env IFunVar
  }

type IBuilderT      m = CatT IBuilderEnv m
type ISubstT      m = ReaderT ISubstEnv m
type ISubstBuilderT m = IBuilderT (ISubstT m)

runIBuilderT :: Monad m => IBuilderT m a -> m a
runIBuilderT m = fst <$> runCatT m mempty

runISubstT :: Monad m => ISubstEnv -> ISubstT m a -> m a
runISubstT env m = runReaderT m env

runISubstBuilderT :: Monad m => ISubstEnv -> ISubstBuilderT m a -> m a
runISubstBuilderT env = (runISubstT env) . runIBuilderT

liftSE :: Monad m => m a -> ISubstBuilderT m a
liftSE = lift . lift

extendScope :: Monad m => Env a -> IBuilderT m ()
extendScope s = extend $ IBuilderEnv (fmap (const ()) s) mempty

emit :: Monad m => ImpInstr -> IBuilderT m [IExpr]
emit instr = do
  vs <- traverse (freshIVar . Ignore) $ impInstrTypes instr
  emitTo vs instr

emitTo :: Monad m => [IVar] -> ImpInstr -> IBuilderT m [IExpr]
emitTo bs instr = do
  extend $ mempty { blockDecls = (Nest (ImpLet (fmap Bind bs) instr) Empty) }
  return $ fmap IVar bs

instance Semigroup IBuilderEnv where
  (IBuilderEnv s d) <> (IBuilderEnv s' d') = IBuilderEnv (s <> s') (d <> d')

instance Monoid IBuilderEnv where
  mempty = IBuilderEnv mempty mempty

instance Semigroup ISubstEnv where
  (ISubstEnv v f) <> (ISubstEnv v' f') = ISubstEnv (v <> v') (f <> f')

instance Monoid ISubstEnv where
  mempty = ISubstEnv mempty mempty

-- === Imp IR builders ===

ptrOffset :: Monad m => IExpr -> IExpr -> IBuilderT m IExpr
ptrOffset ptr off = liftM head $ emit $ IPrimOp $ PtrOffset ptr off

imul :: Monad m => IExpr -> IExpr -> IBuilderT m IExpr
imul x y = liftM head $ emit $ IPrimOp $ ScalarBinOp IMul x y

iadd :: Monad m => IExpr -> IExpr -> IBuilderT m IExpr
iadd x y = liftM head $ emit $ IPrimOp $ ScalarBinOp IAdd x y

alloc :: Monad m => AddressSpace -> IType -> IExpr -> IBuilderT m IExpr
alloc addrSpc ty size = liftM head $ emit $ Alloc addrSpc ty size

-- === Imp IR traversal ===

type ITraversalDef m = ( ImpDecl  -> ISubstBuilderT m (Env IExpr)
                       , ImpInstr -> ISubstBuilderT m ImpInstr
                       )

substTraversalDef :: Monad m => ITraversalDef m
substTraversalDef = ( traverseImpDecl  substTraversalDef
                    , traverseImpInstr substTraversalDef )

traverseImpModule :: forall m. Monad m
                  => (Env IFunVar -> ImpFunction -> m ImpFunction) -> ImpModule -> m ImpModule
traverseImpModule fTrav (ImpModule funcs) = ImpModule . fst <$> runCatT (traverse go funcs) mempty
  where
    go :: ImpFunction -> CatT (Env IFunVar) m ImpFunction
    go f = do
      fenv <- look
      f' <- lift $ fTrav fenv f
      extend $ impFunVar f @> impFunVar f'
      return f'

traverseImpFunction :: Monad m => ITraversalDef m -> Env IFunVar -> ImpFunction -> m ImpFunction
traverseImpFunction _   _    (FFIFunction f             ) = return $ FFIFunction f
traverseImpFunction def fenv (ImpFunction name args body) = runISubstBuilderT env $ do
  extendScope $ foldMap binderAsEnv args
  body' <- extendValSubst (foldMap argSub args) $ traverseImpBlock def body
  return $ ImpFunction name args body'
  where
    argSub b = case b of
      Ignore _ -> mempty
      Bind   v -> v @> IVar v
    env = ISubstEnv mempty fenv

traverseImpBlock :: Monad m => ITraversalDef m -> ImpBlock -> ISubstBuilderT m ImpBlock
traverseImpBlock def block = buildScoped $ evalImpBlock def block

evalImpBlock :: Monad m => ITraversalDef m -> ImpBlock -> ISubstBuilderT m [IExpr]
evalImpBlock def@(fDecl, _) (ImpBlock decls results) = do
  case decls of
    Nest decl rest -> do
      env' <- fDecl decl
      extendValSubst env' $ evalImpBlock def $ ImpBlock rest results
    Empty -> traverse traverseIExpr results

traverseImpDecl :: Monad m => ITraversalDef m -> ImpDecl -> ISubstBuilderT m (Env IExpr)
traverseImpDecl (_, fInstr) (ImpLet bs instr) = do
  vs <- bindM2 emitTo (traverse freshIVar bs) (fInstr instr)
  return $ newEnv bs vs

traverseImpInstr :: Monad m => ITraversalDef m -> ImpInstr -> ISubstBuilderT m ImpInstr
traverseImpInstr def instr = case instr of
  IFor dir b size body -> do
    b' <- freshIVar b
    IFor dir (Bind b') <$> traverseIExpr size
                       <*> (extendValSubst (b @> IVar b') $ traverseImpBlock def body)
  IWhile body -> IWhile <$> traverseImpBlock def body
  ICond cond tb fb -> ICond <$> traverseIExpr cond
                            <*> traverseImpBlock def tb
                            <*> traverseImpBlock def fb
  IQueryParallelism f s -> IQueryParallelism <$> traverseIFunVar f
                                             <*> traverseIExpr s
  ISyncWorkgroup   -> return ISyncWorkgroup
  ILaunch f s args -> ILaunch <$> traverseIFunVar f
                              <*> traverseIExpr s
                              <*> traverse traverseIExpr args
  ICall f args  -> ICall <$> traverseIFunVar f <*> traverse traverseIExpr args
  Store dst val -> Store <$> traverseIExpr dst <*> traverseIExpr val
  Alloc addrSpace ty size -> Alloc addrSpace ty <$> traverseIExpr size
  MemCopy dst src n       -> MemCopy <$> traverseIExpr dst
                                     <*> traverseIExpr src
                                     <*> traverseIExpr n
  Free dst       -> Free <$> traverseIExpr dst
  IThrowError    -> return IThrowError
  ICastOp ty val -> ICastOp ty <$> traverseIExpr val
  IPrimOp op     -> IPrimOp <$> traverse traverseIExpr op

traverseIExpr :: Monad m => IExpr -> ISubstBuilderT m IExpr
traverseIExpr (ILit l) = return $ ILit l
traverseIExpr (IVar v) = (!v) <$> asks valSubst

traverseIFunVar :: Monad m => IFunVar -> ISubstBuilderT m IFunVar
traverseIFunVar fv = (!fv) <$> asks funcSubst

freshIVar :: Monad m => IBinder -> IBuilderT m IVar
freshIVar b = do
  let nameHint = case b of
                   Bind (name:>_) -> name
                   Ignore _       -> "v"
  name <- genFresh nameHint <$> looks scope
  extendScope $ name @> ()
  return $ name :> binderAnn b

buildScoped :: Monad m => IBuilderT m [IExpr] -> IBuilderT m ImpBlock
buildScoped m = do
  (results, IBuilderEnv scopeExt decls) <- scoped m
  extend $ IBuilderEnv scopeExt mempty  -- Names are global in Imp IR
  return $ ImpBlock decls results

extendValSubst :: Monad m => Env IExpr -> ISubstBuilderT m a -> ISubstBuilderT m a
extendValSubst s = local (\env -> env { valSubst = valSubst env <> s })
