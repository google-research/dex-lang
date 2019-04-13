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

runPass :: env -> state -> Var -> MonadPass env state a -> Except (a, state)
runPass env state stem m = runFreshT (runStateT (runReaderT m env) state) stem

evalPass env state stem = liftM fst . runPass env state stem
execPass env state stem = liftM snd . runPass env state stem

liftExcept :: (MonadError e m) => Either e a -> m a
liftExcept = either throwError return

assertEq :: (Show a, Eq a) => a -> a -> String -> Except ()
assertEq x y s = if x == y then return () else Left (CompilerErr msg)
  where msg = s ++ ": " ++ show x ++ " != " ++ show y

ignoreExcept :: Except a -> a
ignoreExcept (Left e) = error $ show e
ignoreExcept (Right x) = x
