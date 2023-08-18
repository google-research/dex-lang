-- Copyright 2021 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module Err (Err (..), ErrType (..), Except (..),
            ErrCtx (..), SrcTextCtx,
            Fallible (..), Catchable (..), catchErrExcept,
            FallibleM (..), HardFailM (..), CtxReader (..),
            runFallibleM, runHardFail, throw,
            addContext, addSrcContext, addSrcTextContext,
            catchIOExcept, liftExcept, liftExceptAlt,
            assertEq, ignoreExcept,
            pprint, docAsStr, getCurrentCallStack, printCurrentCallStack
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
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.Prettyprint.Doc.Render.Text
import Data.Text.Prettyprint.Doc
import GHC.Generics (Generic (..))
import GHC.Stack
import System.Environment
import System.IO.Unsafe
import SourceInfo

-- === core API ===

data Err = Err ErrType ErrCtx String  deriving (Show, Eq)

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
             | MonadFailErr
             | SearchFailure -- used as the identity for `Alternative` instances
               deriving (Show, Eq)

type SrcTextCtx = Maybe (Int, Text) -- Int is the offset in the source file
data ErrCtx = ErrCtx
  { srcTextCtx :: SrcTextCtx
  , srcPosCtx  :: SrcPosCtx
  , messageCtx :: [String]
  , stackCtx   :: Maybe [String] }
    deriving (Show, Eq, Generic)

class MonadFail m => Fallible m where
  throwErr :: Err -> m a
  addErrCtx :: ErrCtx -> m a -> m a

class Fallible m => Catchable m where
  catchErr :: m a -> (Err -> m a) -> m a

catchErrExcept :: Catchable m => m a -> m (Except a)
catchErrExcept m = catchErr (Success <$> m) (\e -> return $ Failure e)

-- We have this in its own class because IO and `Except` can't implement it
-- (but FallibleM can)
class Fallible m => CtxReader m where
  getErrCtx :: m ErrCtx

newtype FallibleM a =
  FallibleM { fromFallibleM :: ReaderT ErrCtx Except a }
  deriving (Functor, Applicative, Monad)

instance Fallible FallibleM where
  -- TODO: we end up adding the context multiple times when we do throw/catch.
  -- We should fix it.
  throwErr (Err errTy ctx s) = FallibleM $ ReaderT \ambientCtx ->
    throwErr $ Err errTy (ambientCtx <> ctx) s
  {-# INLINE throwErr #-}
  addErrCtx ctx (FallibleM m) = FallibleM $ local (<> ctx) m
  {-# INLINE addErrCtx #-}

instance Catchable FallibleM where
  FallibleM m `catchErr` handler = FallibleM $ ReaderT \ctx ->
    case runReaderT m ctx of
      Failure errs -> runReaderT (fromFallibleM $ handler errs) ctx
      Success ans  -> return ans

instance CtxReader FallibleM where
  getErrCtx = FallibleM ask
  {-# INLINE getErrCtx #-}

instance Alternative FallibleM where
  empty = throw SearchFailure ""
  {-# INLINE empty #-}
  m1 <|> m2 = do
    catchSearchFailure m1 >>= \case
      Nothing -> m2
      Just x -> return x
  {-# INLINE (<|>) #-}

catchSearchFailure :: Catchable m => m a -> m (Maybe a)
catchSearchFailure m = (Just <$> m) `catchErr` \case
  Err SearchFailure _ _ -> return Nothing
  err -> throwErr err

instance Fallible IO where
  throwErr errs = throwIO errs
  {-# INLINE throwErr #-}
  addErrCtx ctx m = do
    result <- catchIOExcept m
    liftExcept $ addErrCtx ctx result
  {-# INLINE addErrCtx #-}

instance Catchable IO where
  catchErr cont handler =
    catchIOExcept cont >>= \case
      Success result -> return result
      Failure errs -> handler errs

runFallibleM :: FallibleM a -> Except a
runFallibleM m = runReaderT (fromFallibleM m) mempty
{-# INLINE runFallibleM #-}

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
  addErrCtx _ cont = cont
  {-# INLINE addErrCtx #-}

-- === convenience layer ===

throw :: Fallible m => ErrType -> String -> m a
throw errTy s = throwErr $ addCompilerStackCtx $ Err errTy mempty s
{-# INLINE throw #-}

addCompilerStackCtx :: Err -> Err
addCompilerStackCtx (Err ty ctx msg) = Err ty ctx{stackCtx = compilerStack} msg
  where
#ifdef DEX_DEBUG
    compilerStack = getCurrentCallStack ()
#else
    compilerStack = stackCtx ctx
#endif

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

addContext :: Fallible m => String -> m a -> m a
addContext s m = addErrCtx (mempty {messageCtx = [s]}) m
{-# INLINE addContext #-}

addSrcContext :: Fallible m => SrcPosCtx -> m a -> m a
addSrcContext ctx m = addErrCtx (mempty {srcPosCtx = ctx}) m
{-# INLINE addSrcContext #-}

addSrcTextContext :: Fallible m => Int -> Text -> m a -> m a
addSrcTextContext offset text m =
  addErrCtx (mempty {srcTextCtx = Just (offset, text)}) m

catchIOExcept :: MonadIO m => IO a -> m (Except a)
catchIOExcept m = liftIO $ (liftM Success m) `catches`
  [ Handler \(e::Err)           -> return $ Failure e
  , Handler \(e::IOError)        -> return $ Failure $ Err DataIOErr   mempty $ show e
  -- Propagate asynchronous exceptions like ThreadKilled; they are
  -- part of normal operation (of the live evaluation modes), not
  -- compiler bugs.
  , Handler \(e::AsyncException) -> liftIO $ throwIO e
  , Handler \(e::SomeException)  -> return $ Failure $ Err CompilerErr mempty $ show e
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
  addErrCtx ctx (WriterT m) = WriterT $ addErrCtx ctx m
  {-# INLINE addErrCtx #-}

instance Fallible [] where
  throwErr _ = []
  {-# INLINE throwErr #-}
  addErrCtx _ m = m
  {-# INLINE addErrCtx #-}

instance Fallible Maybe where
  throwErr _ = Nothing
  {-# INLINE throwErr #-}
  addErrCtx _ m = m
  {-# INLINE addErrCtx #-}

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

instance MonadFail FallibleM where
  fail s = throw MonadFailErr s
  {-# INLINE fail #-}

instance Fallible Except where
  throwErr errs = Failure errs
  {-# INLINE throwErr #-}

  addErrCtx _ (Success ans) = Success ans
  addErrCtx ctx (Failure (Err errTy ctx' s)) =
    Failure $ Err errTy (ctx <> ctx') s
  {-# INLINE addErrCtx #-}

instance MonadFail Except where
  fail s = Failure $ Err CompilerErr mempty s
  {-# INLINE fail #-}

instance Exception Err

instance Pretty Err where
  pretty (Err e ctx s) = pretty e <> pretty s <> prettyCtx
    -- TODO: figure out a more uniform way to newlines
    where prettyCtx = case ctx of
            ErrCtx _ (SrcPosCtx Nothing _) [] Nothing -> mempty
            _ -> hardline <> pretty ctx

instance Pretty ErrCtx where
  pretty (ErrCtx maybeTextCtx maybePosCtx messages stack) =
    -- The order of messages is outer-scope-to-inner-scope, but we want to print
    -- them starting the other way around (Not for a good reason. It's just what
    -- we've always done.)
    prettyLines (reverse messages) <> highlightedSource <> prettyStack
    where
      highlightedSource = case (maybeTextCtx, maybePosCtx) of
        (Just (offset, text), SrcPosCtx (Just (start, stop)) _) ->
           hardline <> pretty (highlightRegion (start - offset, stop - offset) text)
        _ -> mempty
      prettyStack = case stack of
        Nothing -> mempty
        Just s  -> hardline <> "Compiler stack trace:" <> nest 2 (hardline <> prettyLines s)

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
    MonadFailErr      -> "MonadFail error (internal error)"
    SearchFailure     -> "Search error (internal error)"

instance Fallible m => Fallible (ReaderT r m) where
  throwErr errs = lift $ throwErr errs
  {-# INLINE throwErr #-}
  addErrCtx ctx (ReaderT f) = ReaderT \r -> addErrCtx ctx $ f r
  {-# INLINE addErrCtx #-}

instance Catchable m => Catchable (ReaderT r m) where
  ReaderT f `catchErr` handler = ReaderT \r ->
    f r `catchErr` \e -> runReaderT (handler e) r

instance CtxReader m => CtxReader (ReaderT r m) where
  getErrCtx = lift getErrCtx
  {-# INLINE getErrCtx #-}

instance Fallible m => Fallible (StateT s m) where
  throwErr errs = lift $ throwErr errs
  {-# INLINE throwErr #-}
  addErrCtx ctx (StateT f) = StateT \s -> addErrCtx ctx $ f s
  {-# INLINE addErrCtx #-}

instance Catchable m => Catchable (StateT s m) where
  StateT f `catchErr` handler = StateT \s ->
    f s `catchErr` \e -> runStateT (handler e) s

instance CtxReader m => CtxReader (StateT s m) where
  getErrCtx = lift getErrCtx
  {-# INLINE getErrCtx #-}

instance Semigroup ErrCtx where
  ErrCtx text (SrcPosCtx p spanId) ctxStrs stk <> ErrCtx text' (SrcPosCtx p' spanId') ctxStrs' stk' =
    ErrCtx (leftmostJust  text text')
           (SrcPosCtx (rightmostJust p p') (rightmostJust spanId spanId'))
           (ctxStrs <> ctxStrs')
           (leftmostJust stk stk')  -- We usually extend errors form the right

instance Monoid ErrCtx where
  mempty = ErrCtx Nothing emptySrcPosCtx [] Nothing

-- === misc util stuff ===

leftmostJust :: Maybe a -> Maybe a -> Maybe a
leftmostJust (Just x) _ = Just x
leftmostJust Nothing y  = y

rightmostJust :: Maybe a -> Maybe a -> Maybe a
rightmostJust = flip leftmostJust

prettyLines :: (Foldable f, Pretty a) => f a -> Doc ann
prettyLines xs = foldMap (\d -> pretty d <> hardline) xs

highlightRegion :: (Int, Int) -> Text -> Text
highlightRegion pos@(low, high) s
  | low > high || high > T.length s =
      error $ "Bad region: \n" ++ show pos ++ "\n" ++ T.unpack s
  | otherwise =
    -- TODO: flag to control line numbers
    -- (disabling for now because it makes quine tests tricky)
    -- "Line " ++ show (1 + lineNum) ++ "\n"
    allLines !! lineNum <> "\n" <>
    T.replicate start " " <> T.replicate (stop - start) "^" <> "\n"
  where
    allLines = T.lines s
    (lineNum, start, stop) = getPosTriple pos allLines

getPosTriple :: (Int, Int) -> [Text] -> (Int, Int, Int)
getPosTriple (start, stop) lines_ = (lineNum, start - offset, stop')
  where
    lineLengths = map ((+1) . T.length) lines_
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
