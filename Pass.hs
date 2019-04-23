{-# LANGUAGE FlexibleContexts #-}

module Pass (MonadPass, TopMonadPass, runPass, liftTopPass,
             evalPass, execPass, liftExcept, assertEq, ignoreExcept,
             runTopMonadPass, addErrMsg, liftExceptIO) where

import System.Exit
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.Except hiding (Except)
import Data.Text.Prettyprint.Doc

import Syntax
import Fresh
import PPrint

type Pass a b env = a -> TopMonadPass env b

type MonadPass env state a = ReaderT env (
                               StateT state (
                                 FreshT (
                                   Either Err))) a

-- TODO: change order of except and writer so we can see what was written before error

-- TODO: use IO exceptions rather than (Either Err)
-- TODO: consider 'Except' on b only so we can propagate declared types on error
-- I keep vacillating on whether to use state or reader-writer for env
type TopMonadPass env a = StateT env (ExceptT Err (WriterT [String] IO)) a

runTopMonadPass :: env -> TopMonadPass env a -> IO (Except (a, env), [String])
runTopMonadPass env m = runWriterT $ runExceptT $ runStateT m env

liftTopPass :: state -> MonadPass env state a -> TopMonadPass env a
liftTopPass state m = do env <- get
                         liftExcept $ evalPass env state nameRoot m

runPass :: env -> state -> Var -> MonadPass env state a -> Except (a, state)
runPass env state stem m = runFreshT (runStateT (runReaderT m env) state) stem

evalPass env state stem = liftM fst . runPass env state stem
execPass env state stem = liftM snd . runPass env state stem

liftExcept :: (MonadError e m) => Either e a -> m a
liftExcept = either throwError return

-- TODO: simplify Err so we can easily add extra information
addErrMsg :: MonadError Err m => String -> m a -> m a
addErrMsg s m = catchError m (handler s)
  where handler s (Err e s') = throw e (s' ++ "\n" ++ s)

assertEq :: (Pretty a, Eq a) => a -> a -> String -> Except ()
assertEq x y s = if x == y then return ()
                           else throw CompilerErr msg
  where msg = s ++ ": " ++ pprint x ++ " != " ++ pprint y

ignoreExcept :: Except a -> a
ignoreExcept (Left e) = error $ pprint e
ignoreExcept (Right x) = x

liftExceptIO :: MonadIO m => Except a -> m a
liftExceptIO (Left e) = liftIO $ die (pprint e)
liftExceptIO (Right x) = return x
