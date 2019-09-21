{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}

module Pass (Pass, TopPassM, runPass, liftTopPassM, evalPass, assertEq,
             ignoreExcept, runTopPassM, putEnv, getEnv, writeOut,
             (>+>), throwIf, getSource, writeOutText, TopPass (..)) where

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
newtype TopPassM env a = TopPassM (ReaderT (env, Cfg)
                                   (ExceptT Err
                                      (WriterT env IO)) a)
  deriving (Functor, Applicative, Monad, MonadIO, MonadError Err)

data TopPass a b where
  TopPass :: Monoid env => (a -> TopPassM env b) -> TopPass a b

getEnv :: Monoid env => TopPassM env env
getEnv = TopPassM $ asks $ fst

putEnv :: Monoid env => env -> TopPassM env ()
putEnv env = TopPassM $ tell env

writeOut :: Monoid env => Output -> TopPassM env ()
writeOut output = do chanWrite <- getOutChan
                     liftIO $ chanWrite output

writeOutText :: Monoid env => String -> TopPassM env ()
writeOutText s = writeOut [TextOut s]

getOutChan :: Monoid env => TopPassM env OutChan
getOutChan = TopPassM $ asks $ fst . snd

getSource :: Monoid env => TopPassM env Source
getSource = TopPassM $ asks $ snd . snd

runTopPassM :: Cfg -> env -> TopPassM env a -> IO (Except a, env)
runTopPassM cfg env (TopPassM m) =
  runWriterT $ runExceptT $ runReaderT m (env, cfg)

liftTopPassM :: Monoid env =>
                 state -> FreshScope -> Pass env state a -> TopPassM env a
liftTopPassM state_ scope m = do
  env <- getEnv
  liftEither $ evalPass env state_ scope m

infixl 1 >+>
(>+>) :: TopPass a b -> TopPass b c -> TopPass a c
(>+>) (TopPass f1) (TopPass f2) = TopPass $ \x -> do
  (env1, env2) <- getEnv
  (y, env1') <- liftEnv env1 (f1 x)
  (z, env2') <- liftEnv env2 (f2 y)
  putEnv (env1', env2')
  return z

liftEnv :: (Monoid env, Monoid env') =>
             env -> TopPassM env a -> TopPassM env' (a, env)
liftEnv env m = do
  c <- getOutChan
  s <- getSource
  (x, env') <- liftIO $ runTopPassM (c,s)env m
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
