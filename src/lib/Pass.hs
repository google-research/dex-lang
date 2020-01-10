-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}

module Pass (TopPassM, assertEq, ignoreExcept, liftExceptTop, runFullPass,
             throwTopErr, emitOutput, (>+>), TopPass (..), FullPass,
             runTopPassM, liftIOTop) where

import Control.Monad.State.Strict
import Control.Monad.Except hiding (Except)
import Control.Exception (catch, throwIO)
import Data.Text.Prettyprint.Doc
import Data.Void
import System.IO.Error (IOError)

import Syntax
import PPrint
import Cat

-- === top-level pass ===

type TopPassM env a = ExceptT Result' (CatT env IO) a
type FullPass env = SourceBlock -> TopPassM env [Void]

data TopPass a b where
  TopPass :: Monoid env => (a -> TopPassM env [b]) -> TopPass a b

runFullPass :: Monoid env => env -> FullPass env -> SourceBlock -> IO (Result, env)
runFullPass env pass source = do
  (result, env') <- runTopPassM env (pass source)
  let result' = case result of Left r  -> r
                               Right _ -> Right NoOutput
  return (addErrSrc source (Result result'), env')

runTopPassM :: Monoid env => env -> TopPassM env a -> IO (Either Result' a, env)
runTopPassM env m = runCatT (runExceptT m) env

infixl 1 >+>

(>+>) :: TopPass a b -> TopPass b c -> TopPass a c
(>+>) (TopPass f1) (TopPass f2) = TopPass $ \x -> do
  (env1, env2) <- look
  (ys, env1') <- liftIO $ runTopPassM env1 (f1 x)
  extend (env1', mempty)
  ys' <- liftEither ys
  (zs, env2') <- liftIO $ runTopPassM env2 (mapM f2 ys')
  extend (mempty, env2')
  zs' <- liftEither zs
  return $ concat zs'

throwTopErr :: Err -> TopPassM env a
throwTopErr e = throwError (Left e)

emitOutput :: Output -> TopPassM env a
emitOutput out = throwError (Right out)

liftExceptTop :: Either Err a -> TopPassM env a
liftExceptTop (Left e) = throwError (Left e)
liftExceptTop (Right x) = return x

liftIOTop :: IO a -> TopPassM env a
liftIOTop m = do
  ansExcept <- liftIO $ catchIOExcept $ m `catch` \e ->
                 throwIO $ Err DataIOErr Nothing (show (e::IOError))
  liftExceptTop ansExcept

-- === common monad structure for pure passes ===

assertEq :: (MonadError Err m, Pretty a, Eq a) => a -> a -> String -> m ()
assertEq x y s = if x == y then return ()
                           else throw CompilerErr msg
  where msg = s ++ ": " ++ pprint x ++ " != " ++ pprint y

ignoreExcept :: Except a -> a
ignoreExcept (Left e) = error $ pprint e
ignoreExcept (Right x) = x
