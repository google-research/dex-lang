-- Copyright 2020 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module Imp.Builder () where
-- module Imp.Builder ( ISubstBuilderT, ISubstEnv (..)
--                    , runISubstBuilderT, liftSE
--                    , emit, freshIVar, extendValSubst
--                    , buildScoped
--                    -- IR builders
--                    , iadd, imul
--                    , alloc, ptrOffset
--                    -- traversal
--                    , traverseImpModule, traverseImpFunction
--                    , traverseImpBlock, evalImpBlock
--                    , traverseImpDecl, traverseImpInstr
--                    , traverseIExpr, traverseIFunVar
--                    , ITraversalDef, substTraversalDef
--                    ) where

import Preamble
import Base
import Core

-- -- XXX: Scope is actually global within each function
-- data IBuilderEnv = IBuilderEnv
--   { scope :: Scope ()
--   , blockDecls :: [ImpDecl]
--   }
-- data ISubstEnv = ISubstEnv
--   { valSubst  :: SimpleEnv () IExpr
--   , funcSubst :: SimpleEnv () IFunVar
--   }

-- type IBuilderT      m = CatT IBuilderEnv m
-- type ISubstT        m = ReaderT ISubstEnv m
-- type ISubstBuilderT m = IBuilderT (ISubstT m)

-- runIBuilderT :: Monad m => IBuilderT m a -> m a
-- runIBuilderT m = fst <$> runCatT m mempty

-- runISubstT :: Monad m => ISubstEnv -> ISubstT m a -> m a
-- runISubstT env m = runReaderT m env

-- runISubstBuilderT :: Monad m => ISubstEnv -> ISubstBuilderT m a -> m a
-- runISubstBuilderT env = (runISubstT env) . runIBuilderT

-- liftSE :: Monad m => m a -> ISubstBuilderT m a
-- liftSE = lift . lift

-- extendScope :: Monad m => SimpleEnv () a -> IBuilderT m ()
-- extendScope s = undefined -- extend $ IBuilderEnv (fmap (const ()) s) mempty

-- emit :: Monad m => ImpInstr -> IBuilderT m [IExpr]
-- emit = undefined
-- -- emit instr = do
-- --   vs <- traverse (freshIVar . ("v"::NameStr,)) $ impInstrTypes instr
-- --   emitTo vs instr

-- emitTo :: Monad m => [IVar] -> ImpInstr -> IBuilderT m [IExpr]
-- emitTo = undefined
-- -- emitTo bs instr = do
-- --   extend $ mempty { blockDecls = [ImpLet bs instr] }
-- --   return $ fmap IVar bs

-- instance Semigroup IBuilderEnv where
--   (IBuilderEnv s d) <> (IBuilderEnv s' d') = IBuilderEnv (s <> s') (d <> d')

-- instance Monoid IBuilderEnv where
--   mempty = IBuilderEnv mempty mempty

-- instance Semigroup ISubstEnv where
--   (ISubstEnv v f) <> (ISubstEnv v' f') = ISubstEnv (v <> v') (f <> f')

-- instance Monoid ISubstEnv where
--   mempty = ISubstEnv mempty mempty

-- -- === Imp IR builders ===

-- ptrOffset :: Monad m => IExpr -> IExpr -> IBuilderT m IExpr
-- ptrOffset ptr off = liftM head $ emit $ IPrimOp $ PtrOffset ptr off

-- imul :: Monad m => IExpr -> IExpr -> IBuilderT m IExpr
-- imul x y = liftM head $ emit $ IPrimOp $ ScalarBinOp IMul x y

-- iadd :: Monad m => IExpr -> IExpr -> IBuilderT m IExpr
-- iadd x y = liftM head $ emit $ IPrimOp $ ScalarBinOp IAdd x y

-- alloc :: Monad m => AddressSpace -> IType -> IExpr -> IBuilderT m IExpr
-- alloc addrSpc ty size = liftM head $ emit $ Alloc addrSpc ty size

-- -- === Imp IR traversal ===

-- type ITraversalDef m = ( ImpDecl  -> ISubstBuilderT m (SimpleEnv () IExpr)
--                        , ImpInstr -> ISubstBuilderT m ImpInstr
--                        )

-- substTraversalDef :: Monad m => ITraversalDef m
-- substTraversalDef = ( traverseImpDecl  substTraversalDef
--                     , traverseImpInstr substTraversalDef )

-- traverseImpModule :: forall m. Monad m
--                   => (SimpleEnv () IFunVar -> ImpFunction -> m ImpFunction) -> ImpModule -> m ImpModule
-- traverseImpModule fTrav (ImpModule funcs) = ImpModule . fst <$> runCatT (traverse go funcs) mempty
--   where
--     go :: ImpFunction -> CatT (SimpleEnv () IFunVar) m ImpFunction
--     go f = do
--       fenv <- look
--       f' <- lift $ fTrav fenv f
--       extend $ fst (impFunVar f) @> HLift (impFunVar f')
--       return f'

-- traverseImpFunction :: Monad m => ITraversalDef m -> SimpleEnv () IFunVar -> ImpFunction -> m ImpFunction
-- traverseImpFunction _   _    (FFIFunction f             ) = return $ FFIFunction f
-- traverseImpFunction def fenv (ImpFunction name args body) = runISubstBuilderT env $ do
--   extendScope $ foldMap (\(v,ty)->v@>HLift ty) args
--   body' <- extendValSubst (foldMap argSub args) $ traverseImpBlock def body
--   return $ ImpFunction name args body'
--   where
--     argSub (v,_) = v @> HLift (IVar v)
--     env = ISubstEnv mempty fenv

-- traverseImpBlock :: Monad m => ITraversalDef m -> ImpBlock -> ISubstBuilderT m ImpBlock
-- traverseImpBlock def block = buildScoped $ evalImpBlock def block

-- evalImpBlock :: Monad m => ITraversalDef m -> ImpBlock -> ISubstBuilderT m [IExpr]
-- evalImpBlock def@(fDecl, _) (ImpBlock decls results) = do
--   case decls of
--     decl:rest -> do
--       env' <- fDecl decl
--       extendValSubst env' $ evalImpBlock def $ ImpBlock rest results
--     [] -> traverse traverseIExpr results

-- traverseImpDecl :: Monad m => ITraversalDef m -> ImpDecl -> ISubstBuilderT m (SimpleEnv () IExpr)
-- traverseImpDecl (_, fInstr) (ImpLet bs instr) = do
--   vs <- bindM2 emitTo (traverse freshIVar bs) (fInstr instr)
--   return $ newSubst bs vs

-- traverseImpInstr :: Monad m => ITraversalDef m -> ImpInstr -> ISubstBuilderT m ImpInstr
-- traverseImpInstr def instr = case instr of
--   IFor dir (v,ty) size body -> do
--     v' <- freshIVar (v,ty)
--     IFor dir (v', ty) <$> traverseIExpr size
--                 <*> (extendValSubst (v @> HLift (IVar v')) $ traverseImpBlock def body)
--   IWhile body -> IWhile <$> traverseImpBlock def body
--   ICond cond tb fb -> ICond <$> traverseIExpr cond
--                             <*> traverseImpBlock def tb
--                             <*> traverseImpBlock def fb
--   IQueryParallelism f s -> IQueryParallelism <$> traverseIFunVar f
--                                              <*> traverseIExpr s
--   ISyncWorkgroup   -> return ISyncWorkgroup
--   ILaunch f s args -> ILaunch <$> traverseIFunVar f
--                               <*> traverseIExpr s
--                               <*> traverse traverseIExpr args
--   ICall f args  -> ICall <$> traverseIFunVar f <*> traverse traverseIExpr args
--   Store dst val -> Store <$> traverseIExpr dst <*> traverseIExpr val
--   Alloc addrSpace ty size -> Alloc addrSpace ty <$> traverseIExpr size
--   MemCopy dst src n       -> MemCopy <$> traverseIExpr dst
--                                      <*> traverseIExpr src
--                                      <*> traverseIExpr n
--   Free dst       -> Free <$> traverseIExpr dst
--   IThrowError    -> return IThrowError
--   ICastOp ty val -> ICastOp ty <$> traverseIExpr val
--   IPrimOp op     -> IPrimOp <$> traverse traverseIExpr op

-- traverseIExpr :: Monad m => IExpr -> ISubstBuilderT m IExpr
-- traverseIExpr (ILit l) = return $ ILit l
-- traverseIExpr (IVar v) = fromHLift . (!v) <$> asks valSubst

-- traverseIFunVar :: Monad m => IFunVar -> ISubstBuilderT m IFunVar
-- traverseIFunVar fv = fromHLift . (!fst fv) <$> asks funcSubst

-- freshIVar :: (HasNameStr hint, Monad m) => (hint, IType) -> IBuilderT m IVar
-- freshIVar (nameHint, ty) = do
--   name <- genFresh NormalName (getNameStr nameHint) <$> looks scope
--   extendScope $ name @> HUnit
--   return name

-- buildScoped :: Monad m => IBuilderT m [IExpr] -> IBuilderT m ImpBlock
-- buildScoped m = do
--   (results, IBuilderEnv scopeExt decls) <- scoped m
--   extend $ IBuilderEnv scopeExt mempty  -- Names are global in Imp IR
--   return $ ImpBlock decls results

-- extendValSubst :: Monad m => SimpleEnv () IExpr
--                -> ISubstBuilderT m a -> ISubstBuilderT m a
-- extendValSubst s = local (\env -> env { valSubst = valSubst env <> s })

-- newSubst ::[IBinder] -> [IExpr] -> SimpleEnv i IExpr
-- newSubst = undefined
