{-# LANGUAGE FlexibleContexts #-}

module Pass (Pass, TopPass, runPass, liftTopPass,
             evalPass, execPass, liftExcept, assertEq, ignoreExcept,
             runTopPass, liftExceptIO,
             Result (..), evalDecl, (>+>)) where

import System.Exit
import Control.Monad.State.Strict
import Control.Monad.Reader
import Control.Monad.Writer hiding ((<>))
import Control.Monad.Except hiding (Except)
import Data.Text.Prettyprint.Doc

import Syntax
import Fresh
import PPrint

evalDecl :: Monoid env => TopPass env () -> StateT env IO Result
evalDecl pass = do
  env <- get
  (ans, output) <- liftIO $ runTopPass env pass
  let output' = resultText (concat output)
  case ans of
    Left e -> return $ output' <> resultErr e
    Right (_, env') -> do put $ env' <> env
                          return $ output' <> resultComplete

-- === top-level pass (IO because of LLVM JIT API) ===

type TopPass env a = StateT env (ExceptT Err (WriterT [String] IO)) a

infixl 1 >+>
(>+>) :: (a -> TopPass env1 b)
      -> (b -> TopPass env2 c)
      -> (a -> TopPass (env1, env2) c)
(>+>) f1 f2 x = do (env1, env2) <- get
                   (y, env1') <- lift $ runStateT (f1 x) env1
                   (z, env2') <- lift $ runStateT (f2 y) env2
                   put (env1', env2')
                   return z

runTopPass :: env -> TopPass env a -> IO (Except (a, env), [String])
runTopPass env m = runWriterT $ runExceptT $ runStateT m env

liftTopPass :: state -> Pass env state a -> TopPass env a
liftTopPass state m = do env <- get
                         liftExcept $ evalPass env state nameRoot m

-- === common monad structure for pure passes ===

type Pass env state a = ReaderT env (
                               StateT state (
                                 FreshT (
                                   Either Err))) a

runPass :: env -> state -> Var -> Pass env state a -> Except (a, state)
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
