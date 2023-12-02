-- Copyright 2021 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE UndecidableInstances #-}

module Err (Err (..), ErrType (..), Except (..),
            Fallible (..), Catchable (..), catchErrExcept,
            HardFailM (..), runHardFail, throw,
            catchIOExcept, liftExcept, liftExceptAlt,
            assertEq, ignoreExcept,
            pprint, docAsStr, getCurrentCallStack, printCurrentCallStack,
            ExceptT (..)
            ) where

import Control.Exception hiding (throw)
import Control.Applicative
import Control.Monad
import Control.Monad.Identity
import Control.Monad.Writer.Strict
import Control.Monad.State.Strict
import Control.Monad.Reader
import Data.Coerce
import Data.Foldable (fold)
import Data.Text qualified as T
import Data.Text.Prettyprint.Doc.Render.Text
import Data.Text.Prettyprint.Doc
import GHC.Stack
import System.Environment
import System.IO.Unsafe

-- === core API ===

data Err = Err ErrType String  deriving (Show, Eq)

data ErrType = NoErr
             | ParseErr
             | SyntaxErr
             | TypeErr
             | KindErr
             | LinErr
             | VarDefErr
             | UnboundVarErr
             | AmbiguousVarErr
             | RepeatedVarErr
             | RepeatedPatVarErr
             | InvalidPatternErr
             | CompilerErr
             | IRVariantErr
             | NotImplementedErr
             | DataIOErr
             | MiscErr
             | RuntimeErr
             | ZipErr
             | EscapedNameErr
             | ModuleImportErr
             | SearchFailure -- used as the identity for `Alternative` instances and for MonadFail
               deriving (Show, Eq)

class MonadFail m => Fallible m where
  throwErr :: Err -> m a

class Fallible m => Catchable m where
  catchErr :: m a -> (Err -> m a) -> m a

catchErrExcept :: Catchable m => m a -> m (Except a)
catchErrExcept m = catchErr (Success <$> m) (\e -> return $ Failure e)

catchSearchFailure :: Catchable m => m a -> m (Maybe a)
catchSearchFailure m = (Just <$> m) `catchErr` \case
  Err SearchFailure _ -> return Nothing
  err -> throwErr err

instance Fallible IO where
  throwErr errs = throwIO errs
  {-# INLINE throwErr #-}

instance Catchable IO where
  catchErr cont handler =
    catchIOExcept cont >>= \case
      Success result -> return result
      Failure errs -> handler errs

-- === ExceptT type ===

newtype ExceptT m a = ExceptT { runExceptT :: m (Except a) }

instance Monad m => Functor (ExceptT m) where
  fmap = liftM
  {-# INLINE fmap #-}

instance Monad m => Applicative (ExceptT m) where
  pure = return
  {-# INLINE pure #-}
  liftA2 = liftM2
  {-# INLINE liftA2 #-}

instance Monad m => Monad (ExceptT m) where
  return x = ExceptT $ return (Success x)
  {-# INLINE return #-}
  m >>= f = ExceptT $ runExceptT m >>= \case
    Failure errs -> return $ Failure errs
    Success x    -> runExceptT $ f x
  {-# INLINE (>>=) #-}

instance Monad m => MonadFail (ExceptT m) where
  fail s = ExceptT $ return $ Failure $ Err SearchFailure s
  {-# INLINE fail #-}

instance Monad m => Fallible (ExceptT m) where
  throwErr errs = ExceptT $ return $ Failure errs
  {-# INLINE throwErr #-}

instance Monad m => Alternative (ExceptT m) where
  empty = throw SearchFailure ""
  {-# INLINE empty #-}
  m1 <|> m2 = do
    catchSearchFailure m1 >>= \case
      Nothing -> m2
      Just x -> return x
  {-# INLINE (<|>) #-}

instance Monad m => Catchable (ExceptT m) where
  m `catchErr` f = ExceptT $ runExceptT m >>= \case
    Failure errs -> runExceptT $ f errs
    Success x    -> return $ Success x
  {-# INLINE catchErr #-}

instance MonadState s m => MonadState s (ExceptT m) where
  get = lift get
  {-# INLINE get #-}
  put x = lift $ put x
  {-# INLINE put #-}

instance MonadTrans ExceptT where
  lift m = ExceptT $ Success <$> m
  {-# INLINE lift #-}

-- === Except type ===

-- Except is isomorphic to `Either Err` but having a distinct type makes it
-- easier to debug type errors.

data Except a =
   Failure Err
 | Success a
   deriving (Show, Eq)

instance Functor Except where
  fmap = liftM
  {-# INLINE fmap #-}

instance Applicative Except where
  pure = return
  {-# INLINE pure #-}
  liftA2 = liftM2
  {-# INLINE liftA2 #-}

instance Monad Except where
  return = Success
  {-# INLINE return #-}
  Failure errs >>= _ = Failure errs
  Success x >>= f = f x
  {-# INLINE (>>=) #-}

instance Alternative Except where
  empty = throw SearchFailure ""
  {-# INLINE empty #-}
  m1 <|> m2 = do
    catchSearchFailure m1 >>= \case
      Nothing -> m2
      Just x -> return x
  {-# INLINE (<|>) #-}

instance Catchable Except where
  Success ans `catchErr` _ = Success ans
  Failure errs `catchErr` f = f errs
  {-# INLINE catchErr #-}

-- === HardFail ===

-- Implements Fallible by crashing. Used in type querying when we want to avoid
-- work by trusting decl annotations and skipping the checks.
newtype HardFailM a =
  HardFailM { runHardFail' :: Identity a }
  -- We don't derive Functor, Applicative and Monad, because Identity doesn't
  -- use INLINE pragmas in its own instances, which unnecessarily inhibits optimizations.

instance Functor HardFailM where
  fmap f (HardFailM (Identity x)) = HardFailM $ Identity $ f x
  {-# INLINE fmap #-}

instance Applicative HardFailM where
  pure = HardFailM . Identity
  {-# INLINE pure #-}
  (<*>) = coerce
  {-# INLINE (<*>) #-}
  liftA2 = coerce
  {-# INLINE liftA2 #-}

instance Monad HardFailM where
  (HardFailM (Identity x)) >>= k = k x
  {-# INLINE (>>=) #-}
  return = HardFailM . Identity
  {-# INLINE return #-}

runHardFail :: HardFailM a -> a
runHardFail m = runIdentity $ runHardFail' m
{-# INLINE runHardFail #-}

instance MonadFail HardFailM where
  fail s = error s
  {-# INLINE fail #-}

instance Fallible HardFailM where
  throwErr errs = error $ pprint errs
  {-# INLINE throwErr #-}

-- === convenience layer ===

throw :: Fallible m => ErrType -> String -> m a
throw errTy s = throwErr $ Err errTy s
{-# INLINE throw #-}

getCurrentCallStack :: () -> Maybe [String]
getCurrentCallStack () =
#ifdef DEX_DEBUG
  case reverse (unsafePerformIO currentCallStack) of
    []    -> Nothing
    stack -> Just stack
#else
  Nothing
#endif
{-# NOINLINE getCurrentCallStack #-}

printCurrentCallStack :: Maybe [String] -> String
printCurrentCallStack Nothing = "<no call stack available>"
printCurrentCallStack (Just frames) = fold frames

catchIOExcept :: MonadIO m => IO a -> m (Except a)
catchIOExcept m = liftIO $ (liftM Success m) `catches`
  [ Handler \(e::Err)           -> return $ Failure e
  , Handler \(e::IOError)        -> return $ Failure $ Err DataIOErr   $ show e
  -- Propagate asynchronous exceptions like ThreadKilled; they are
  -- part of normal operation (of the live evaluation modes), not
  -- compiler bugs.
  , Handler \(e::AsyncException) -> liftIO $ throwIO e
  , Handler \(e::SomeException)  -> return $ Failure $ Err CompilerErr $ show e
  ]

liftExcept :: Fallible m => Except a -> m a
liftExcept (Failure errs) = throwErr errs
liftExcept (Success ans) = return ans
{-# INLINE liftExcept #-}

liftExceptAlt :: Alternative m => Except a -> m a
liftExceptAlt = \case
  Success a -> pure a
  Failure _ -> empty
{-# INLINE liftExceptAlt #-}

ignoreExcept :: HasCallStack => Except a -> a
ignoreExcept (Failure e) = error $ pprint e
ignoreExcept (Success x) = x
{-# INLINE ignoreExcept #-}

assertEq :: (HasCallStack, Fallible m, Show a, Pretty a, Eq a) => a -> a -> String -> m ()
assertEq x y s = if x == y then return ()
                           else throw CompilerErr msg
  where msg = "assertion failure (" ++ s ++ "):\n"
              ++ pprint x ++ " != " ++ pprint y ++ "\n\n"
              ++ prettyCallStack callStack ++ "\n"

instance (Monoid w, Fallible m) => Fallible (WriterT w m) where
  throwErr errs = lift $ throwErr errs
  {-# INLINE throwErr #-}

instance Fallible [] where
  throwErr _ = []
  {-# INLINE throwErr #-}

instance Fallible Maybe where
  throwErr _ = Nothing
  {-# INLINE throwErr #-}

-- === small pretty-printing utils ===
-- These are here instead of in PPrint.hs for import cycle reasons

pprint :: Pretty a => a -> String
pprint x = docAsStr $ pretty x
{-# SCC pprint #-}

docAsStr :: Doc ann -> String
docAsStr doc = T.unpack $ renderStrict $ layoutPretty layout $ doc

layout :: LayoutOptions
layout = if unbounded then LayoutOptions Unbounded else defaultLayoutOptions
  where unbounded = unsafePerformIO $ (Just "1"==) <$> lookupEnv "DEX_PPRINT_UNBOUNDED"

-- === instances ===

instance Fallible Except where
  throwErr errs = Failure errs
  {-# INLINE throwErr #-}

instance MonadFail Except where
  fail s = Failure $ Err SearchFailure s
  {-# INLINE fail #-}

instance Exception Err

instance Pretty Err where
  pretty (Err e s) = pretty e <> pretty s

instance Pretty a => Pretty (Except a) where
  pretty (Success x) = "Success:" <+> pretty x
  pretty (Failure e) = "Failure:" <+> pretty e

instance Pretty ErrType where
  pretty e = case e of
    -- NoErr tags a chunk of output that was promoted into the Err ADT
    -- by appending Results.
    NoErr             -> ""
    ParseErr          -> "Parse error:"
    SyntaxErr         -> "Syntax error: "
    TypeErr           -> "Type error:"
    KindErr           -> "Kind error:"
    LinErr            -> "Linearity error: "
    IRVariantErr      -> "Internal IR validation error: "
    VarDefErr         -> "Error in (earlier) definition of variable: "
    UnboundVarErr     -> "Error: variable not in scope: "
    AmbiguousVarErr   -> "Error: ambiguous variable: "
    RepeatedVarErr    -> "Error: variable already defined: "
    RepeatedPatVarErr -> "Error: variable already defined within pattern: "
    InvalidPatternErr -> "Error: not a valid pattern: "
    NotImplementedErr ->
      "Not implemented:" <> line <>
      "Please report this at github.com/google-research/dex-lang/issues\n" <> line
    CompilerErr       ->
      "Compiler bug!" <> line <>
      "Please report this at github.com/google-research/dex-lang/issues\n" <> line
    DataIOErr         -> "IO error: "
    MiscErr           -> "Error:"
    RuntimeErr        -> "Runtime error"
    ZipErr            -> "Zipping error"
    EscapedNameErr    -> "Leaked local variables:"
    ModuleImportErr   -> "Module import error: "
    SearchFailure     -> "Search error (internal error)"

instance Fallible m => Fallible (ReaderT r m) where
  throwErr errs = lift $ throwErr errs
  {-# INLINE throwErr #-}

instance Catchable m => Catchable (ReaderT r m) where
  ReaderT f `catchErr` handler = ReaderT \r ->
    f r `catchErr` \e -> runReaderT (handler e) r

instance Fallible m => Fallible (StateT s m) where
  throwErr errs = lift $ throwErr errs
  {-# INLINE throwErr #-}

instance Catchable m => Catchable (StateT s m) where
  StateT f `catchErr` handler = StateT \s ->
    f s `catchErr` \e -> runStateT (handler e) s
