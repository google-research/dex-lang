{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleContexts #-}

module Pass (Pass, TopPass, runPass, liftTopPass, evalPass, assertEq,
             ignoreExcept, runTopPass, putEnv, getEnv, writeOut,
             (>+>), throwIf, getSource, writeOutText) where

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
type Source = String
type Cfg = (OutChan, Source)
newtype TopPass env a = TopPass (ReaderT (env, Cfg)
                                   (ExceptT Err
                                      (WriterT env IO)) a)
  deriving (Functor, Applicative, Monad, MonadIO, MonadError Err)

getEnv :: Monoid env => TopPass env env
getEnv = TopPass $ asks $ fst

putEnv :: Monoid env => env -> TopPass env ()
putEnv env = TopPass $ tell env

writeOut :: Monoid env => Output -> TopPass env ()
writeOut output = do chanWrite <- getOutChan
                     liftIO $ chanWrite output

writeOutText :: Monoid env => String -> TopPass env ()
writeOutText s = writeOut [TextOut s]

getOutChan :: Monoid env => TopPass env OutChan
getOutChan = TopPass $ asks $ fst . snd

getSource :: Monoid env => TopPass env Source
getSource = TopPass $ asks $ snd . snd

runTopPass :: Cfg -> env -> TopPass env a -> IO (Except a, env)
runTopPass cfg env (TopPass m) =
  runWriterT $ runExceptT $ runReaderT m (env, cfg)

liftTopPass :: Monoid env =>
                 state -> FreshScope -> Pass env state a -> TopPass env a
liftTopPass state_ scope m = do
  env <- getEnv
  liftEither $ evalPass env state_ scope m

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

liftEnv :: (Monoid env, Monoid env') =>
             env -> TopPass env a -> TopPass env' (a, env)
liftEnv env m = do
  c <- getOutChan
  s <- getSource
  (x, env') <- liftIO $ runTopPass (c,s)env m
  x' <- liftEither x
  return (x', env')

-- === common monad structure for pure passes ===

type Pass env state a = ReaderT env (
                               StateT state (
                                 FreshT (
                                   Either Err))) a

runPass :: env -> state -> FreshScope -> Pass env state a -> Except (a, state)
runPass env state_ scope m = runFreshT (runStateT (runReaderT m env) state_) scope

evalPass :: env -> state -> FreshScope -> Pass env state a -> Except a
evalPass env state_ stem = liftM fst . runPass env state_ stem

assertEq :: (MonadError Err m, Pretty a, Eq a) => a -> a -> String -> m ()
assertEq x y s = if x == y then return ()
                           else throw CompilerErr msg
  where msg = s ++ ": " ++ pprint x ++ " != " ++ pprint y

throwIf :: MonadError Err m => Bool -> String -> m ()
throwIf True  s = throw CompilerErr s
throwIf False _ = return ()

ignoreExcept :: Except a -> a
ignoreExcept (Left e) = error $ pprint e
ignoreExcept (Right x) = x
