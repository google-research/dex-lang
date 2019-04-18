module Pass (MonadPass, TopMonadPass, runPass, liftTopPass,
             evalPass, execPass, liftExcept, assertEq, ignoreExcept,
             runTopMonadPass) where

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

-- TODO: use IO exceptions rather than (Either Err)
-- TODO: consider 'Except' on b only so we can propagate declared types on error
-- I keep vacillating on whether to use state or reader-writer for env
type TopMonadPass env a = StateT env (WriterT [String] (ExceptT Err IO)) a

runTopMonadPass :: env -> TopMonadPass env a -> IO (Except ((a, env), [String]))
runTopMonadPass env m = runExceptT $ runWriterT (runStateT m env)

liftTopPass :: state -> MonadPass env state a -> TopMonadPass env a
liftTopPass state m = do env <- get
                         liftExcept $ evalPass env state VarRoot m -- TODO: plumb through var stems

runPass :: env -> state -> Var -> MonadPass env state a -> Except (a, state)
runPass env state stem m = runFreshT (runStateT (runReaderT m env) state) stem

evalPass env state stem = liftM fst . runPass env state stem
execPass env state stem = liftM snd . runPass env state stem

liftExcept :: (MonadError e m) => Either e a -> m a
liftExcept = either throwError return

assertEq :: (Pretty a, Eq a) => a -> a -> String -> Except ()
assertEq x y s = if x == y then return () else Left (CompilerErr msg)
  where msg = s ++ ": " ++ pprint x ++ " != " ++ pprint y

ignoreExcept :: Except a -> a
ignoreExcept (Left e) = error $ pprint e
ignoreExcept (Right x) = x
