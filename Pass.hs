{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}

module Pass (MonadPass, TopMonadPass, runPass, liftTopPass,
             evalPass, execPass, liftExcept, assertEq, ignoreExcept,
             runTopMonadPass, addErrMsg, liftExceptIO,
             EvalState, MultiPass (..), Pass, Result (..),
             startEval, evalDecl, evalDeclAsync, (>+>)) where

import System.Exit
import Control.Monad.State
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
type Pass env a b = a -> TopMonadPass env b

data EvalState = EvalState (MVar ([Name], M.Map Var Name))
                           (MultiPassState UDecl ())

data MultiPass a b where
  NilPass :: MultiPass a a
  AddPass :: Monoid env => MultiPass a b -> Pass env b c -> MultiPass a c

infixl 1 >+>
(>+>) :: Monoid env => MultiPass a b -> Pass env b c -> MultiPass a c
(>+>) = AddPass

data MultiPassState a b where
  SNilPass :: MultiPassState a a
  SAddPass :: Monoid env =>
    MultiPassState a b -> MutEnv env -> Pass env b c -> MultiPassState a c

startEval :: MultiPass UDecl () -> IO EvalState
startEval x = liftM2 EvalState (newMVar (rawNames "top", mempty))
                               (initializeState x)

evalDecl :: EvalState -> UDecl -> IO Result
evalDecl state decl = do chan <- newChan
                         evalDeclAsync state decl (writeChan chan)
                         liftM mconcat (pipeReadAll chan)

evalDeclAsync :: EvalState -> UDecl -> ResultSink -> IO Name
evalDeclAsync (EvalState statePtr pass) decl write = do
  (name:names, parentMap) <- takeMVar statePtr
  let newMap  = parentMap <> M.fromList (zip (lhsVars decl) (repeat name))
      parents = catMaybes $ map (flip M.lookup parentMap) (freeVars decl)
  putMVar statePtr (names, newMap)
  forkIO $ do evalMultiPass write name parents decl pass
              write EOM
  return name

-- TODO: this is horrible. figure out a good monad
evalMultiPass :: ResultSink -> Name -> [Name] -> a
                   -> MultiPassState a b -> IO (Maybe b)
evalMultiPass write _ _ x SNilPass = return (Just x)
evalMultiPass write name parents x (SAddPass mpass envs pass) = do
  maybeY <- evalMultiPass write name parents x mpass
  case maybeY of
    Nothing -> noEnvUpdate >> return Nothing
    Just y -> do
      env <- liftM (mconcat . catMaybes) $ mapM (readMutMap envs) parents
      (ans, output) <- runTopMonadPass env (pass y)
      write $ Msg $ TextOut (concat output)
      case ans of
        Left e -> do write (Msg (Failed e))
                     noEnvUpdate
                     return Nothing
        Right (ans', env'') -> do writeMutMap name (Just (env'' <> env)) envs
                                  return (Just ans')
  where
    noEnvUpdate = writeMutMap name Nothing envs

initializeState :: MultiPass a b -> IO (MultiPassState a b)
initializeState x = case x of
  NilPass -> return SNilPass
  AddPass xs x -> liftM3 SAddPass (initializeState xs) newMutMap (return x)

-- === top-level pass (IO because of LLVM JIT API) ===

type TopMonadPass env a = StateT env (ExceptT Err (WriterT [String] IO)) a

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
