module Pass (MonadPass, runPass, execPass, evalPass,
             liftExcept, assertEq, ignoreExcept) where

import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Except hiding (Except)

import Syntax
import Fresh

type MonadPass env state a = ReaderT env (
                               StateT state (
                                 FreshT (
                                   Either Err))) a

runPass :: MonadPass env state a -> env -> state -> Except (a, state)
runPass m env state = runFreshT $ runStateT (runReaderT m env) state

evalPass :: MonadPass env state a -> env -> state -> Except a
evalPass m env state = runFreshT $ evalStateT (runReaderT m env) state

execPass :: MonadPass env state a -> env -> state -> Except state
execPass m env state = runFreshT $ execStateT (runReaderT m env) state

liftExcept :: (MonadError e m) => Either e a -> m a
liftExcept = either throwError return

assertEq :: (Show a, Eq a) => a -> a -> String -> Except ()
assertEq x y s = if x == y then return () else Left (CompilerErr msg)
  where msg = s ++ ": " ++ show x ++ " != " ++ show y

ignoreExcept :: Except a -> a
ignoreExcept (Left e) = error $ show e
ignoreExcept (Right x) = x
