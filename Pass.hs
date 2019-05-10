{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleContexts #-}

module Pass (Pass, TopPass, runPass, liftTopPass, evalPass, assertEq,
             ignoreExcept, runTopPass, putEnv, getEnv, writeOut,
             (>+>)) where

import System.Exit
import Control.Monad.State.Strict
import Control.Monad.Reader
import Control.Monad.Writer hiding ((<>))
import Control.Monad.Except hiding (Except)
import Data.Text.Prettyprint.Doc

import Syntax
import Fresh
import PPrint

-- === top-level pass ===

type OutChan = Output -> IO ()
newtype TopPass env a = TopPass (ReaderT (env, OutChan)
                                   (ExceptT Err
                                      (WriterT env IO)) a)
  deriving (Functor, Applicative, Monad, MonadIO, MonadError Err)

getEnv :: Monoid env => TopPass env env
getEnv = TopPass $ asks fst

putEnv :: Monoid env => env -> TopPass env ()
putEnv env = TopPass $ tell env

writeOut :: Monoid env => Output -> TopPass env ()
writeOut output = do chanWrite <- getOutChan
                     liftIO $ chanWrite output

getOutChan :: Monoid env => TopPass env OutChan
getOutChan = TopPass $ asks snd

runTopPass :: OutChan -> env -> TopPass env a -> IO (Except a, env)
runTopPass chan env (TopPass m) =
  runWriterT $ runExceptT $ runReaderT m (env, chan)

liftTopPass :: Monoid env => state -> Pass env state a -> TopPass env a
liftTopPass state m = do env <- getEnv
                         liftEither $ evalPass env state nameRoot m

infixl 1 >+>
(>+>) :: (Monoid env1, Monoid env2)
      => (a -> TopPass env1 b)
      -> (b -> TopPass env2 c)
      -> (a -> TopPass (env1, env2) c)
(>+>) f1 f2 x = do (env1, env2) <- getEnv
                   (y, env1') <- liftEnv env1 (f1 x)
                   (z, env2') <- liftEnv env2 (f2 y)
                   putEnv (env1', env2')
                   return z
  where
    liftEnv :: (Monoid env, Monoid env') =>
                  env -> TopPass env a -> TopPass env' (a, env)
    liftEnv env m = do chan <- getOutChan
                       (x, env') <- liftIO $ runTopPass chan env m
                       x' <- liftEither x
                       return (x', env')

-- === common monad structure for pure passes ===

type Pass env state a = ReaderT env (
                               StateT state (
                                 FreshT (
                                   Either Err))) a

runPass :: env -> state -> Var -> Pass env state a -> Except (a, state)
runPass env state stem m = runFreshT (runStateT (runReaderT m env) state) stem

evalPass env state stem = liftM fst . runPass env state stem

assertEq :: (Pretty a, Eq a) => a -> a -> String -> Except ()
assertEq x y s = if x == y then return ()
                           else throw CompilerErr msg
  where msg = s ++ ": " ++ pprint x ++ " != " ++ pprint y

ignoreExcept :: Except a -> a
ignoreExcept (Left e) = error $ pprint e
ignoreExcept (Right x) = x
