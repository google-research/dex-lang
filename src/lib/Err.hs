-- Copyright 2021 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}

module Err (Err (..), Errs (..), ErrType (..), Except (..), ErrCtx (..),
            SrcPosCtx, SrcTextCtx, SrcPos,
            Fallible (..), FallibleM (..), HardFailM (..),
            runHardFail, throw, throwErr, throwIf,
            addContext, addSrcContext, addSrcTextContext,
            catchIOExcept, liftExcept,
            assertEq, ignoreExcept, pprint, docAsStr, asCompilerErr,
            FallibleApplicativeWrapper, traverseMergingErrs) where

import Control.Exception hiding (throw)
import Control.Applicative
import Control.Monad
import Control.Monad.Identity
import Control.Monad.State.Strict
import Control.Monad.Reader
import Data.Text (unpack)
import Data.Text.Prettyprint.Doc.Render.Text
import Data.Text.Prettyprint.Doc
import GHC.Stack
import System.Environment
import System.IO.Unsafe

-- === core API ===

data Err = Err ErrType ErrCtx String  deriving (Show, Eq)
newtype Errs = Errs [Err]  deriving (Show, Eq, Semigroup, Monoid)

data ErrType = NoErr
             | ParseErr
             | TypeErr
             | KindErr
             | LinErr
             | UnboundVarErr
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
             | MonadFailErr
               deriving (Show, Eq)

type SrcPosCtx  = Maybe SrcPos
type SrcTextCtx = Maybe (Int, String) -- Int is the offset in the source file
data ErrCtx = ErrCtx
  { srcTextCtx :: SrcTextCtx
  , srcPosCtx  :: SrcPosCtx
  , messageCtx :: [String] }
    deriving (Show, Eq)

type SrcPos = (Int, Int)

class MonadFail m => Fallible m where
  throwErrs :: Errs -> m a
  addErrCtx :: ErrCtx -> m a -> m a

-- We have this in its own class because IO and `Except` can't implement it
-- (but FallibleM can)
class Fallible m => CtxReader m where
  getErrCtx :: m ErrCtx

-- We have this in its own class because StateT can't implement it
-- (but FallibleM, Except and IO all can)
class Fallible m => FallibleApplicative m where
  mergeErrs :: m a -> m b -> m (a, b)

newtype FallibleM a =
  FallibleM { fromFallibleM :: ReaderT ErrCtx Except a }
  deriving (Functor, Applicative, Monad)

instance Fallible FallibleM where
  throwErrs errs = FallibleM $ lift $ throwErrs errs
  addErrCtx ctx (FallibleM m) = FallibleM $ local (<> ctx) m

instance FallibleApplicative FallibleM where
  mergeErrs (FallibleM (ReaderT f1)) (FallibleM (ReaderT f2)) =
    FallibleM $ ReaderT \ctx -> mergeErrs (f1 ctx) (f2 ctx)

instance CtxReader FallibleM where
  getErrCtx = FallibleM ask

instance Fallible IO where
  throwErrs errs = throwIO errs
  addErrCtx ctx m = do
    result <- catchIOExcept m
    liftExcept $ addErrCtx ctx result

instance FallibleApplicative IO where
  mergeErrs m1 m2 = do
    result1 <- catchIOExcept m1
    result2 <- catchIOExcept m2
    liftExcept $ mergeErrs result1 result2

-- === Except type ===

-- Except is isomorphic to `Either Errs` but having a distinct type makes it
-- easier to debug type errors.

data Except a =
   Failure Errs
 | Success a
   deriving (Show, Eq)

instance Functor Except where
  fmap = liftM

instance Applicative Except where
  pure = return
  liftA2 = liftM2

instance Monad Except where
  return = Success
  Failure errs >>= _ = Failure errs
  Success x >>= f = f x

-- === FallibleApplicativeWrapper ===

-- Wraps a Fallible monad, presenting an applicative interface that sequences
-- actions using the error-concatenating `mergeErrs` instead of the default
-- abort-on-failure sequencing.

newtype FallibleApplicativeWrapper m a =
  FallibleApplicativeWrapper { fromFallibleApplicativeWrapper :: m a }
  deriving (Functor)

instance FallibleApplicative m => Applicative (FallibleApplicativeWrapper m) where
  pure x = FallibleApplicativeWrapper $ pure x
  liftA2 f (FallibleApplicativeWrapper m1) (FallibleApplicativeWrapper m2) =
    FallibleApplicativeWrapper $ fmap (uncurry f) (mergeErrs m1 m2)

-- === HardFail ===

-- Implements Fallible by crashing. Used in type querying when we want to avoid
-- work by trusting decl annotations and skipping the checks.
newtype HardFailM a =
  HardFailM { runHardFail' :: Identity a }
  deriving (Functor, Applicative, Monad)

runHardFail :: HardFailM a -> a
runHardFail m = runIdentity $ runHardFail' m

instance MonadFail HardFailM where
  fail s = error s

instance Fallible HardFailM where
  throwErrs errs = error $ pprint errs
  addErrCtx _ cont = cont

instance FallibleApplicative HardFailM where
  mergeErrs cont1 cont2 = (,) <$> cont1 <*> cont2

-- === convenience layer ===

throw :: Fallible m => ErrType -> String -> m a
throw errTy s = throwErrs $ Errs [Err errTy mempty s]

throwErr :: Fallible m => Err -> m a
throwErr err = throwErrs $ Errs [err]

throwIf :: Fallible m => Bool -> ErrType -> String -> m ()
throwIf True  e s = throw e s
throwIf False _ _ = return ()

addContext :: Fallible m => String -> m a -> m a
addContext s m = addErrCtx (mempty {messageCtx = [s]}) m

addSrcContext :: Fallible m => SrcPosCtx -> m a -> m a
addSrcContext ctx m = addErrCtx (mempty {srcPosCtx = ctx}) m

addSrcTextContext :: Fallible m => Int -> String -> m a -> m a
addSrcTextContext offset text m =
  addErrCtx (mempty {srcTextCtx = Just (offset, text)}) m

catchIOExcept :: MonadIO m => IO a -> m (Except a)
catchIOExcept m = liftIO $ (liftM Success m) `catches`
  [ Handler \(e::Errs)          -> return $ Failure e
  , Handler \(e::IOError)       -> return $ Failure $ Errs [Err DataIOErr   mempty $ show e]
  , Handler \(e::SomeException) -> return $ Failure $ Errs [Err CompilerErr mempty $ show e]
  ]

liftExcept :: Fallible m => Except a -> m a
liftExcept (Failure errs) = throwErrs errs
liftExcept (Success ans) = return ans

ignoreExcept :: HasCallStack => Except a -> a
ignoreExcept (Failure e) = error $ pprint e
ignoreExcept (Success x) = x

assertEq :: (HasCallStack, Fallible m, Show a, Pretty a, Eq a) => a -> a -> String -> m ()
assertEq x y s = if x == y then return ()
                           else throw CompilerErr msg
  where msg = "assertion failure (" ++ s ++ "):\n"
              ++ pprint x ++ " != " ++ pprint y ++ "\n\n"
              ++ prettyCallStack callStack ++ "\n"

-- TODO: think about the best way to handle these. This is just a
-- backwards-compatibility shim.
asCompilerErr :: Fallible m => m a -> m a
asCompilerErr cont = addContext "(This is a compiler error!)" cont

-- === small pretty-printing utils ===
-- These are here instead of in PPrint.hs for import cycle reasons

pprint :: Pretty a => a -> String
pprint x = docAsStr $ pretty x

docAsStr :: Doc ann -> String
docAsStr doc = unpack $ renderStrict $ layoutPretty layout $ doc

layout :: LayoutOptions
layout = if unbounded then LayoutOptions Unbounded else defaultLayoutOptions
  where unbounded = unsafePerformIO $ (Just "1"==) <$> lookupEnv "DEX_PPRINT_UNBOUNDED"

traverseMergingErrs :: (Traversable f, FallibleApplicative m)
                    => (a -> m b) -> f a -> m (f b)
traverseMergingErrs f xs =
  fromFallibleApplicativeWrapper $ traverse (\x -> FallibleApplicativeWrapper $ f x) xs

-- === instances ===

instance MonadFail FallibleM where
  fail s = throw MonadFailErr s

instance Fallible Except where
  throwErrs errs = Failure errs

  addErrCtx _ (Success ans) = Success ans
  addErrCtx ctx (Failure (Errs errs)) =
    Failure $ Errs [Err errTy (ctx <> ctx') s | Err errTy ctx' s <- errs]

instance FallibleApplicative Except where
  mergeErrs (Success x) (Success y) = Success (x, y)
  mergeErrs x y = Failure (getErrs x <> getErrs y)
    where getErrs :: Except a -> Errs
          getErrs = \case Failure e  -> e
                          Success _ -> mempty

instance MonadFail Except where
  fail s = Failure $ Errs [Err CompilerErr mempty s]

instance Exception Errs

instance Pretty Err where
  pretty (Err e ctx s) = pretty e <> pretty s <> prettyCtx
    -- TODO: figure out a more uniform way to newlines
    where prettyCtx = case ctx of
            ErrCtx _ Nothing [] -> mempty
            _ -> hardline <> pretty ctx

instance Pretty ErrCtx where
  pretty (ErrCtx maybeTextCtx maybePosCtx messages) =
    -- The order of messages is outer-scope-to-inner-scope, but we want to print
    -- them starting the other way around (Not for a good reason. It's just what
    -- we've always done.)
    prettyLines (reverse messages) <> highlightedSource
    where
      highlightedSource = case (maybeTextCtx, maybePosCtx) of
        (Just (offset, text), Just (start, stop)) ->
           hardline <> pretty (highlightRegion (start - offset, stop - offset) text)
        _ -> mempty

instance Pretty ErrType where
  pretty e = case e of
    -- NoErr tags a chunk of output that was promoted into the Err ADT
    -- by appending Results.
    NoErr             -> ""
    ParseErr          -> "Parse error:"
    TypeErr           -> "Type error:"
    KindErr           -> "Kind error:"
    LinErr            -> "Linearity error: "
    IRVariantErr      -> "Internal IR validation error: "
    UnboundVarErr     -> "Error: variable not in scope: "
    RepeatedVarErr    -> "Error: variable already defined: "
    RepeatedPatVarErr -> "Error: variable already defined within pattern: "
    InvalidPatternErr -> "Error: not a valid pattern: "
    NotImplementedErr -> "Not implemented:"
    CompilerErr       ->
      "Compiler bug!" <> line <>
      "Please report this at github.com/google-research/dex-lang/issues\n" <> line
    DataIOErr         -> "IO error: "
    MiscErr           -> "Error:"
    RuntimeErr        -> "Runtime error"
    ZipErr            -> "Zipping error"
    EscapedNameErr    -> "Escaped name"
    ModuleImportErr   -> "Module import error"
    MonadFailErr      -> "MonadFail error (internal error)"

instance Fallible m => Fallible (ReaderT r m) where
  throwErrs errs = lift $ throwErrs errs
  addErrCtx ctx (ReaderT f) = ReaderT \r -> addErrCtx ctx $ f r

instance FallibleApplicative m => FallibleApplicative (ReaderT r m) where
  mergeErrs (ReaderT f1) (ReaderT f2) =
    ReaderT \r -> mergeErrs (f1 r) (f2 r)

instance CtxReader m => CtxReader (ReaderT r m) where
  getErrCtx = lift getErrCtx

instance Pretty Errs where
  pretty (Errs [err]) = pretty err
  pretty (Errs errs) = prettyLines errs

instance Fallible m => Fallible (StateT s m) where
  throwErrs errs = lift $ throwErrs errs
  addErrCtx ctx (StateT f) = StateT \s -> addErrCtx ctx $ f s

instance CtxReader m => CtxReader (StateT s m) where
  getErrCtx = lift getErrCtx

instance Semigroup ErrCtx where
  ErrCtx text pos ctxStrs <> ErrCtx text' pos' ctxStrs' =
    ErrCtx (leftmostJust  text text')
           (rightmostJust pos  pos' )
           (ctxStrs <> ctxStrs')
instance Monoid ErrCtx where
  mempty = ErrCtx Nothing Nothing []

-- === misc util stuff ===

leftmostJust :: Maybe a -> Maybe a -> Maybe a
leftmostJust (Just x) _ = Just x
leftmostJust Nothing y  = y

rightmostJust :: Maybe a -> Maybe a -> Maybe a
rightmostJust = flip leftmostJust

prettyLines :: (Foldable f, Pretty a) => f a -> Doc ann
prettyLines xs = foldMap (\d -> pretty d <> hardline) xs

highlightRegion :: (Int, Int) -> String -> String
highlightRegion pos@(low, high) s
  | low > high || high > length s = error $ "Bad region: \n"
                                              ++ show pos ++ "\n" ++ s
  | otherwise =
    -- TODO: flag to control line numbers
    -- (disabling for now because it makes quine tests tricky)
    -- "Line " ++ show (1 + lineNum) ++ "\n"

    allLines !! lineNum ++ "\n"
    ++ take start (repeat ' ') ++ take (stop - start) (repeat '^') ++ "\n"
  where
    allLines = lines s
    (lineNum, start, stop) = getPosTriple pos allLines

getPosTriple :: (Int, Int) -> [String] -> (Int, Int, Int)
getPosTriple (start, stop) lines_ = (lineNum, start - offset, stop')
  where
    lineLengths = map ((+1) . length) lines_
    lineOffsets = cumsum lineLengths
    lineNum = maxLT lineOffsets start
    offset = lineOffsets  !! lineNum
    stop' = min (stop - offset) (lineLengths !! lineNum)

cumsum :: [Int] -> [Int]
cumsum xs = scanl (+) 0 xs

maxLT :: Ord a => [a] -> a -> Int
maxLT [] _ = 0
maxLT (x:xs) n = if n < x then -1
                          else 1 + maxLT xs n

