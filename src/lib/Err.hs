-- Copyright 2021 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveAnyClass #-}

module Err (
  Err (..), Except, ErrType (..), SrcCtx, SrcPos, MonadErr,
  throw, throwIf, addContext, addSrcContext, catchIOExcept,
  liftEitherIO, modifyErr, assertEq, ignoreExcept, WithSrc (..),
  ) where

import Control.Exception hiding (throw)

import Preamble
import Util (pprint)

data Err = Err ErrType SrcCtx String  deriving (Show, Generic, Store)
instance Exception Err

type Except = Either Err
type MonadErr m = (MonadError Err m, MonadFail m)

data ErrType = NoErr
             | ParseErr
             | TypeErr
             | KindErr
             | LinErr
             | UnboundVarErr
             | RepeatedVarErr
             | CompilerErr
             | IRVariantErr
             | NotImplementedErr
             | DataIOErr
             | MiscErr
             | RuntimeErr
               deriving (Show, Generic, Store)

type SrcCtx = Maybe SrcPos
type SrcPos = (Int, Int)

data WithSrc a = WithSrc { srcPos :: SrcCtx, withoutSrc :: a }
  deriving (Show, Eq, Generic, Generic1, Functor, Foldable, Traversable, Store)

throw :: MonadErr m => ErrType -> String -> m a
throw e s = throwError $ Err e Nothing s

throwIf :: MonadErr m => Bool -> ErrType -> String -> m ()
throwIf True  e s = throw e s
throwIf False _ _ = return ()

addContext :: MonadErr m => String -> m a -> m a
addContext s m = modifyErr m \(Err e p s') -> Err e p (s' ++ "\n" ++ s)

addSrcContext :: MonadErr m => SrcCtx -> m a -> m a
addSrcContext ctx m = modifyErr m updateErr
  where
    updateErr :: Err -> Err
    updateErr (Err e ctx' s) = case ctx' of Nothing -> Err e ctx  s
                                            Just _  -> Err e ctx' s

catchIOExcept :: (MonadIO m , MonadErr m) => IO a -> m a
catchIOExcept m = (liftIO >=> liftEither) $ (liftM Right m) `catches`
  [ Handler \(e::Err)           -> return $ Left e
  , Handler \(e::IOError)       -> return $ Left $ Err DataIOErr   Nothing $ show e
  , Handler \(e::SomeException) -> return $ Left $ Err CompilerErr Nothing $ show e
  ]

instance MonadFail (Either Err) where
  fail s = Left $ Err CompilerErr Nothing s

liftEitherIO :: (Exception e, MonadIO m) => Either e a -> m a
liftEitherIO (Left err) = liftIO $ throwIO err
liftEitherIO (Right x ) = return x

modifyErr :: MonadError e m => m a -> (e -> e) -> m a
modifyErr m f = catchError m \e -> throwError (f e)

assertEq :: (MonadErr m, Pretty a, Eq a) => a -> a -> String -> m ()
assertEq x y s = if x == y then return ()
                           else throw CompilerErr msg
  where msg = "assertion failure (" ++ s ++ "):\n"
              ++ pprint x ++ " != " ++ pprint y ++ "\n"

ignoreExcept :: HasCallStack => Except a -> a
ignoreExcept (Left e) = error $ pprint e
ignoreExcept (Right x) = x


instance Pretty Err
