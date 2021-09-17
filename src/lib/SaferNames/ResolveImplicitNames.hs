-- Copyright 2021 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module SaferNames.ResolveImplicitNames (resolveImplicitTopDecl) where

import Control.Monad.Except hiding (Except)
import Control.Monad.Reader
import Control.Monad.Writer
import Data.Char (isLower)
import Data.List (nub)
import qualified Data.Set as S
import Data.String

import LabeledItems
import SaferNames.Name hiding (extendEnv)
import SaferNames.Syntax

resolveImplicitTopDecl :: UDecl VoidS VoidS -> UDecl VoidS VoidS
resolveImplicitTopDecl (ULet ann (UPatAnn pat (Just ty)) expr) =
  ULet ann (UPatAnn pat (Just ty')) expr' where
    implicitArgs = findImplicitArgNames ty
    ty'   = foldr addImplicitPiArg  ty   implicitArgs
    expr' = foldr addImplicitLamArg expr implicitArgs
resolveImplicitTopDecl (UInstance className argBinders params methods maybeName) =
  UInstance className argBinders' params methods maybeName where
    implicitArgs = findImplicitArgNames $ PairE className $ Abs argBinders (ListE params)
    argBinders' = foldr Nest argBinders $ map nameAsImplicitBinder implicitArgs
resolveImplicitTopDecl decl = decl

-- === WithEnv Monad transformer ===

-- The idea is to be able to monoidally accumulate (with the
-- `extendEnv` action) some piece of state, which is made
-- automatically available to downstream actions in their Reader
-- environment.

-- XXX: we deliberately avoid implementing the instance
--   MonadReader env m => MonadReader env (WithEnv env m a)
-- because we want to make lifting explicit, to avoid performance issues due
-- to too many `WithEnv` wrappers.
newtype WithEnv env m a = WithEnv { runWithEnv :: m (a, env) }

extendEnv :: (Monad m) => env -> WithEnv env m ()
extendEnv env = WithEnv $ return ((), env)

instance (Monoid env, MonadReader env m) => Functor (WithEnv env m) where
  fmap = liftM

instance (Monoid env, MonadReader env m) => Applicative (WithEnv env m) where
  (<*>) = ap
  pure x = WithEnv $ pure (x, mempty)

instance (Monoid env, MonadReader env m) => Monad (WithEnv env m) where
  return = pure
  -- TODO: Repeated bind will get expensive here. An implementation like Cat
  -- might be more efficient
  WithEnv m1 >>= f = WithEnv do
    (x, env1) <- m1
    let WithEnv m2 = f x
    (y, env2) <- local (<> env1) m2
    return (y, env1 <> env2)

instance Monoid env => MonadTrans (WithEnv env) where
  lift m = WithEnv $ fmap (,mempty) m

instance (Monoid env, MonadError e m, MonadReader env m)
         => MonadError e (WithEnv env m) where
  throwError e = lift $ throwError e
  catchError (WithEnv m) handler =
    WithEnv $ catchError m (runWithEnv . handler)

-- === Traversal to find implicit names

nameAsImplicitBinder :: SourceName -> UPatAnnArrow VoidS VoidS
nameAsImplicitBinder v = UPatAnnArrow (fromString v) ImplicitArrow

addImplicitPiArg :: SourceName -> UType VoidS -> UType VoidS
addImplicitPiArg v vTy = WithSrcE Nothing $ UPi $ UPiExpr ImplicitArrow (fromString v) Pure vTy

addImplicitLamArg :: SourceName -> UExpr VoidS -> UExpr VoidS
addImplicitLamArg v e = WithSrcE Nothing $ ULam $ ULamExpr ImplicitArrow (fromString v) e

findImplicitArgNames :: HasImplicitArgNamesE e => e n -> [SourceName]
findImplicitArgNames expr =
  nub $ flip runReader mempty $ execWriterT $ implicitArgsE expr

-- TODO: de-deuplicate with SourceRename by making a class for traversals
--       parameterized by the base cases on UBinder and UVar.
class HasImplicitArgNamesE (e::E) where
  implicitArgsE :: MonadReader (S.Set SourceName) m
                => MonadWriter [SourceName] m
                => e n
                -> m ()

class HasImplicitArgNamesB (b::B) where
  implicitArgsB :: MonadReader (S.Set SourceName) m
                => MonadWriter [SourceName] m
                => b n l
                -> WithEnv (S.Set SourceName) m ()

instance HasImplicitArgNamesE (SourceNameOr e) where
  implicitArgsE (SourceName v) = do
    isFree <- asks \boundNames -> not $ v `S.member` boundNames
    when (isFree && isLower (head v)) $ tell [v]
  implicitArgsE _ = error "Unexpected internal name"

instance HasImplicitArgNamesB (UBinder (color::C)) where
  implicitArgsB ubinder = case ubinder of
    UBindSource b -> extendEnv (S.singleton b)
    UBind _ -> error "Unexpected internal name"
    UIgnore -> return ()

instance HasImplicitArgNamesB UPatAnn where
  implicitArgsB (UPatAnn b ann) = do
    lift $ mapM_ implicitArgsE ann
    implicitArgsB b

instance HasImplicitArgNamesB UPatAnnArrow where
  implicitArgsB (UPatAnnArrow b _) = implicitArgsB b

instance HasImplicitArgNamesE UExpr' where
  implicitArgsE expr = case expr of
    UVar v -> implicitArgsE v
    UPi (UPiExpr _ pat eff body) -> implicitArgsE $ Abs pat (PairE eff body)
    -- specifically exclude vars on the lhs of an application
    UApp _ (WithSrcE _ (UVar _)) x -> implicitArgsE x
    UApp _ f x -> implicitArgsE f >> implicitArgsE x
    UHole -> return ()
    UTypeAnn v ty -> implicitArgsE v >> implicitArgsE ty
    UIndexRange low high -> mapM_ implicitArgsE low >> mapM_ implicitArgsE high
    UPrimExpr e -> mapM_ implicitArgsE e
    URecord (Ext ulr _) ->  mapM_ implicitArgsE ulr  -- TODO Not scanning `rest`?
    UVariant _ _   val -> implicitArgsE val
    UVariantLift _ val -> implicitArgsE val
    URecordTy  (Ext tys ext) -> mapM_ implicitArgsE tys >> mapM_ implicitArgsE ext
    UVariantTy (Ext tys ext) -> mapM_ implicitArgsE tys >> mapM_ implicitArgsE ext
    UIntLit   _ -> return ()
    UFloatLit _ -> return ()
    ULam _    -> error "Unexpected lambda in type annotation"
    UDecl _   -> error "Unexpected let binding in type annotation"
    UFor _ _  -> error "Unexpected for in type annotation"
    UCase _ _ -> error "Unexpected case in type annotation"
    UTabCon _ ->  error "Unexpected table constructor in type annotation"

instance HasImplicitArgNamesB UPat' where
  implicitArgsB pat = case pat of
    UPatBinder b -> implicitArgsB b
    UPatCon _ bs -> implicitArgsB bs
    UPatPair p -> implicitArgsB p
    UPatUnit _ -> return ()
    UPatRecord _ ps -> implicitArgsB ps
    UPatVariant _ _ p -> implicitArgsB p
    UPatVariantLift _ p -> implicitArgsB p
    UPatTable ps -> implicitArgsB ps

instance HasImplicitArgNamesB b => HasImplicitArgNamesB (Nest b) where
  implicitArgsB Empty = return ()
  implicitArgsB (Nest b bs) = implicitArgsB b >> implicitArgsB bs

instance (HasImplicitArgNamesB b1, HasImplicitArgNamesB b2)
         => HasImplicitArgNamesB (PairB b1 b2) where
  implicitArgsB (PairB b1 b2) = implicitArgsB b1 >> implicitArgsB b2

instance HasImplicitArgNamesB UnitB where
  implicitArgsB UnitB = return ()

instance (HasImplicitArgNamesB b1, HasImplicitArgNamesB b2)
         => HasImplicitArgNamesB (EitherB b1 b2) where
  implicitArgsB (LeftB  b) = implicitArgsB b
  implicitArgsB (RightB b) = implicitArgsB b

instance (HasImplicitArgNamesB b, HasImplicitArgNamesE e)
         => HasImplicitArgNamesE (Abs b e) where
  implicitArgsE (Abs b e) = do
    ((), vs) <- runWithEnv $ implicitArgsB b
    local (<>vs) $ implicitArgsE e

instance (HasImplicitArgNamesE e1, HasImplicitArgNamesE e2)
         => HasImplicitArgNamesE (PairE e1 e2) where
  implicitArgsE (PairE x y) = implicitArgsE x >> implicitArgsE y

instance ((forall n. Ord (a n)), HasImplicitArgNamesE a)
         => HasImplicitArgNamesE (EffectRowP a) where
  implicitArgsE (EffectRow row tailVar) = do
    mapM_ implicitArgsE $ S.toList row
    mapM_ implicitArgsE tailVar

instance HasImplicitArgNamesE a => HasImplicitArgNamesE (EffectP a) where
  implicitArgsE (RWSEffect _ name) = implicitArgsE name
  implicitArgsE _ = return ()

instance HasImplicitArgNamesE e => HasImplicitArgNamesE (WithSrcE e) where
  implicitArgsE (WithSrcE _ x) = implicitArgsE x

instance HasImplicitArgNamesB b => HasImplicitArgNamesB (WithSrcB b) where
  implicitArgsB (WithSrcB _ x) = implicitArgsB x

instance HasImplicitArgNamesE e => HasImplicitArgNamesE (ListE e) where
  implicitArgsE (ListE xs) = mapM_ implicitArgsE xs

