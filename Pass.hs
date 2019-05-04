{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}

module Pass (MonadPass, TopMonadPass, runPass, liftTopPass,
             evalPass, execPass, liftExcept, assertEq, ignoreExcept,
             runTopMonadPass, liftExceptIO,
             Pass, Result (..), evalDecl, (>+>)) where

import System.Exit
import Control.Monad.State.Strict
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.Except hiding (Except)
import qualified Data.Map.Strict as M
import Data.Text.Prettyprint.Doc
import Data.Maybe (catMaybes)
import Data.Semigroup ((<>))
import Control.Concurrent

import Syntax
import Fresh
import PPrint
import ConcurrentUtil

type MutEnv a = MutMap Name (Maybe a)
type ResultSink = Packet Result -> IO ()

evalDecl :: Monoid env => Pass env a () -> a -> StateT env IO Result
evalDecl pass x = do
  env <- get
  (ans, output) <- liftIO $ runTopMonadPass env (pass x)
  let output' = TextOut (concat output)
  case ans of
    Left e -> return $ output' <> Failed e
    Right (_, env') -> do put $ env' <> env
                          return $ output'

-- === top-level pass (IO because of LLVM JIT API) ===

type TopMonadPass env a = StateT env (ExceptT Err (WriterT [String] IO)) a
type Pass env a b = a -> TopMonadPass env b

infixl 1 >+>
(>+>) :: Pass env1 a b -> Pass env2 b c -> Pass (env1, env2) a c
(>+>) f1 f2 x = do (env1, env2) <- get
                   (y, env1') <- lift $ runStateT (f1 x) env1
                   (z, env2') <- lift $ runStateT (f2 y) env2
                   put (env1', env2')
                   return z

runTopMonadPass :: env -> TopMonadPass env a -> IO (Except (a, env), [String])
runTopMonadPass env m = runWriterT $ runExceptT $ runStateT m env

liftTopPass :: state -> MonadPass env state a -> TopMonadPass env a
liftTopPass state m = do env <- get
                         liftExcept $ evalPass env state nameRoot m

-- === common monad structure for pure passes ===

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
