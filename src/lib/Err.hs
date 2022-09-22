-- Copyright 2021 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module Err (Err (..), Errs (..), ErrType (..), Except (..), ErrCtx (..),
            SrcPosCtx, SrcTextCtx, SrcPos,
            Fallible (..), Catchable (..), catchErrExcept,
            FallibleM (..), HardFailM (..), CtxReader (..),
            runFallibleM, runHardFail, throw, throwErr,
            addContext, addSrcContext, addSrcTextContext,
            catchIOExcept, liftExcept, liftExceptAlt,
            assertEq, ignoreExcept,
            pprint, docAsStr, getCurrentCallStack, printCurrentCallStack,
            FallibleApplicativeWrapper, traverseMergingErrs,
            SearcherM (..), Searcher (..), runSearcherM) where

import Control.Exception hiding (throw)
import Control.Applicative
import Control.Monad
import Control.Monad.Trans.Maybe
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
import GHC.Stack
import System.Environment
import System.IO.Unsafe

-- === core API ===

data Err = Err ErrType ErrCtx String  deriving (Show, Eq)
newtype Errs = Errs [Err]  deriving (Eq, Semigroup, Monoid)

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
               deriving (Show, Eq)

type SrcPosCtx  = Maybe SrcPos
type SrcTextCtx = Maybe (Int, Text) -- Int is the offset in the source file
data ErrCtx = ErrCtx
  { srcTextCtx :: SrcTextCtx
  , srcPosCtx  :: SrcPosCtx
  , messageCtx :: [String]
  , stackCtx   :: Maybe [String] }
    deriving (Show, Eq)

type SrcPos = (Int, Int)

class MonadFail m => Fallible m where
  throwErrs :: Errs -> m a
  addErrCtx :: ErrCtx -> m a -> m a

class Fallible m => Catchable m where
  catchErr :: m a -> (Errs -> m a) -> m a

catchErrExcept :: Catchable m => m a -> m (Except a)
catchErrExcept m = catchErr (Success <$> m) (\e -> return $ Failure e)

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
  throwErrs (Errs errs) = FallibleM $ ReaderT \ambientCtx ->
    throwErrs $ Errs [Err errTy (ambientCtx <> ctx) s | Err errTy ctx s <- errs]
  {-# INLINE throwErrs #-}
  addErrCtx ctx (FallibleM m) = FallibleM $ local (<> ctx) m
  {-# INLINE addErrCtx #-}

instance Catchable FallibleM where
  FallibleM m `catchErr` handler = FallibleM $ ReaderT \ctx ->
    case runReaderT m ctx of
      Failure errs -> runReaderT (fromFallibleM $ handler errs) ctx
      Success ans  -> return ans

instance FallibleApplicative FallibleM where
  mergeErrs (FallibleM (ReaderT f1)) (FallibleM (ReaderT f2)) =
    FallibleM $ ReaderT \ctx -> mergeErrs (f1 ctx) (f2 ctx)

instance CtxReader FallibleM where
  getErrCtx = FallibleM ask
  {-# INLINE getErrCtx #-}

instance Fallible IO where
  throwErrs errs = throwIO errs
  {-# INLINE throwErrs #-}
  addErrCtx ctx m = do
    result <- catchIOExcept m
    liftExcept $ addErrCtx ctx result
  {-# INLINE addErrCtx #-}

instance Catchable IO where
  catchErr cont handler =
    catchIOExcept cont >>= \case
      Success result -> return result
      Failure errs -> handler errs

instance FallibleApplicative IO where
  mergeErrs m1 m2 = do
    result1 <- catchIOExcept m1
    result2 <- catchIOExcept m2
    liftExcept $ mergeErrs result1 result2

runFallibleM :: FallibleM a -> Except a
runFallibleM m = runReaderT (fromFallibleM m) mempty
{-# INLINE runFallibleM #-}

-- === Except type ===

-- Except is isomorphic to `Either Errs` but having a distinct type makes it
-- easier to debug type errors.

data Except a =
   Failure Errs
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

-- === FallibleApplicativeWrapper ===

-- Wraps a Fallible monad, presenting an applicative interface that sequences
-- actions using the error-concatenating `mergeErrs` instead of the default
-- abort-on-failure sequencing.

newtype FallibleApplicativeWrapper m a =
  FallibleApplicativeWrapper { fromFallibleApplicativeWrapper :: m a }
  deriving (Functor)

instance FallibleApplicative m => Applicative (FallibleApplicativeWrapper m) where
  pure x = FallibleApplicativeWrapper $ pure x
  {-# INLINE pure #-}
  liftA2 f (FallibleApplicativeWrapper m1) (FallibleApplicativeWrapper m2) =
    FallibleApplicativeWrapper $ fmap (uncurry f) (mergeErrs m1 m2)
  {-# INLINE liftA2 #-}

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
  throwErrs errs = error $ pprint errs
  {-# INLINE throwErrs #-}
  addErrCtx _ cont = cont
  {-# INLINE addErrCtx #-}

instance FallibleApplicative HardFailM where
  mergeErrs cont1 cont2 = (,) <$> cont1 <*> cont2

-- === convenience layer ===

throw :: Fallible m => ErrType -> String -> m a
throw errTy s = throwErrs $ Errs [addCompilerStackCtx $ Err errTy mempty s]
{-# INLINE throw #-}

throwErr :: Fallible m => Err -> m a
throwErr err = throwErrs $ Errs [addCompilerStackCtx err]
{-# INLINE throwErr #-}

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
  [ Handler \(e::Errs)           -> return $ Failure e
  , Handler \(e::IOError)        -> return $ Failure $ Errs [Err DataIOErr   mempty $ show e]
  -- Propagate asynchronous exceptions like ThreadKilled; they are
  -- part of normal operation (of the live evaluation modes), not
  -- compiler bugs.
  , Handler \(e::AsyncException) -> liftIO $ throwIO e
  , Handler \(e::SomeException)  -> return $ Failure $ Errs [Err CompilerErr mempty $ show e]
  ]

liftExcept :: Fallible m => Except a -> m a
liftExcept (Failure errs) = throwErrs errs
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

-- === search monad ===

infix 0 <!>
class (Monad m, Alternative m) => Searcher m where
  -- Runs the second computation when the first yields an empty set of results.
  -- This is just `<|>` for greedy searchers like `Maybe`, but in other cases,
  -- like the list monad, it matters that the second computation isn't run if
  -- the first succeeds.
  (<!>) :: m a -> m a -> m a

-- Adds an extra error case to `FallibleM` so we can give it an Alternative
-- instance with an identity element.
newtype SearcherM a = SearcherM { runSearcherM' :: MaybeT FallibleM a }
  deriving (Functor, Applicative, Monad)

runSearcherM :: SearcherM a -> Except (Maybe a)
runSearcherM m = runFallibleM $ runMaybeT (runSearcherM' m)
{-# INLINE runSearcherM #-}

instance MonadFail SearcherM where
  fail _ = SearcherM $ MaybeT $ return Nothing
  {-# INLINE fail #-}

instance Fallible SearcherM where
  throwErrs e = SearcherM $ lift $ throwErrs e
  {-# INLINE throwErrs #-}
  addErrCtx ctx (SearcherM (MaybeT m)) = SearcherM $ MaybeT $
    addErrCtx ctx $ m
  {-# INLINE addErrCtx #-}

instance Alternative SearcherM where
  empty = SearcherM $ MaybeT $ return Nothing
  SearcherM (MaybeT m1) <|> SearcherM (MaybeT m2) = SearcherM $ MaybeT do
    m1 >>= \case
      Just ans -> return $ Just ans
      Nothing -> m2

instance Searcher SearcherM where
  (<!>) = (<|>)
  {-# INLINE (<!>) #-}

instance CtxReader SearcherM where
  getErrCtx = SearcherM $ lift getErrCtx
  {-# INLINE getErrCtx #-}

instance Searcher [] where
  [] <!> m = m
  m  <!> _ = m
  {-# INLINE (<!>) #-}

instance (Monoid w, Searcher m) => Searcher (WriterT w m) where
  WriterT m1 <!> WriterT m2 = WriterT (m1 <!> m2)
  {-# INLINE (<!>) #-}

instance (Monoid w, Fallible m) => Fallible (WriterT w m) where
  throwErrs errs = lift $ throwErrs errs
  {-# INLINE throwErrs #-}
  addErrCtx ctx (WriterT m) = WriterT $ addErrCtx ctx m
  {-# INLINE addErrCtx #-}

instance Searcher m => Searcher (ReaderT r m) where
  ReaderT f1 <!> ReaderT f2 = ReaderT \r -> f1 r <!> f2 r
  {-# INLINE (<!>) #-}

instance Fallible [] where
  throwErrs _ = []
  {-# INLINE throwErrs #-}
  addErrCtx _ m = m
  {-# INLINE addErrCtx #-}

instance Fallible Maybe where
  throwErrs _ = Nothing
  {-# INLINE throwErrs #-}
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

traverseMergingErrs :: (Traversable f, FallibleApplicative m)
                    => (a -> m b) -> f a -> m (f b)
traverseMergingErrs f xs =
  fromFallibleApplicativeWrapper $ traverse (\x -> FallibleApplicativeWrapper $ f x) xs

-- === instances ===

instance MonadFail FallibleM where
  fail s = throw MonadFailErr s
  {-# INLINE fail #-}

instance Fallible Except where
  throwErrs errs = Failure errs
  {-# INLINE throwErrs #-}

  addErrCtx _ (Success ans) = Success ans
  addErrCtx ctx (Failure (Errs errs)) =
    Failure $ Errs [Err errTy (ctx <> ctx') s | Err errTy ctx' s <- errs]
  {-# INLINE addErrCtx #-}

instance FallibleApplicative Except where
  mergeErrs (Success x) (Success y) = Success (x, y)
  mergeErrs x y = Failure (getErrs x <> getErrs y)
    where getErrs :: Except a -> Errs
          getErrs = \case Failure e  -> e
                          Success _ -> mempty

instance MonadFail Except where
  fail s = Failure $ Errs [Err CompilerErr mempty s]
  {-# INLINE fail #-}

instance Exception Errs

instance Show Errs where
  show errs = pprint errs

instance Pretty Err where
  pretty (Err e ctx s) = pretty e <> pretty s <> prettyCtx
    -- TODO: figure out a more uniform way to newlines
    where prettyCtx = case ctx of
            ErrCtx _ Nothing [] Nothing -> mempty
            _ -> hardline <> pretty ctx

instance Pretty ErrCtx where
  pretty (ErrCtx maybeTextCtx maybePosCtx messages stack) =
    -- The order of messages is outer-scope-to-inner-scope, but we want to print
    -- them starting the other way around (Not for a good reason. It's just what
    -- we've always done.)
    prettyLines (reverse messages) <> highlightedSource <> prettyStack
    where
      highlightedSource = case (maybeTextCtx, maybePosCtx) of
        (Just (offset, text), Just (start, stop)) ->
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

instance Fallible m => Fallible (ReaderT r m) where
  throwErrs errs = lift $ throwErrs errs
  {-# INLINE throwErrs #-}
  addErrCtx ctx (ReaderT f) = ReaderT \r -> addErrCtx ctx $ f r
  {-# INLINE addErrCtx #-}

instance Catchable m => Catchable (ReaderT r m) where
  ReaderT f `catchErr` handler = ReaderT \r ->
    f r `catchErr` \e -> runReaderT (handler e) r

instance FallibleApplicative m => FallibleApplicative (ReaderT r m) where
  mergeErrs (ReaderT f1) (ReaderT f2) =
    ReaderT \r -> mergeErrs (f1 r) (f2 r)

instance CtxReader m => CtxReader (ReaderT r m) where
  getErrCtx = lift getErrCtx
  {-# INLINE getErrCtx #-}

instance Pretty Errs where
  pretty (Errs [err]) = pretty err
  pretty (Errs errs) = prettyLines errs

instance Fallible m => Fallible (StateT s m) where
  throwErrs errs = lift $ throwErrs errs
  {-# INLINE throwErrs #-}
  addErrCtx ctx (StateT f) = StateT \s -> addErrCtx ctx $ f s
  {-# INLINE addErrCtx #-}

instance Catchable m => Catchable (StateT s m) where
  StateT f `catchErr` handler = StateT \s ->
    f s `catchErr` \e -> runStateT (handler e) s

instance CtxReader m => CtxReader (StateT s m) where
  getErrCtx = lift getErrCtx
  {-# INLINE getErrCtx #-}

instance Semigroup ErrCtx where
  ErrCtx text pos ctxStrs stk <> ErrCtx text' pos' ctxStrs' stk' =
    ErrCtx (leftmostJust  text text')
           (rightmostJust pos  pos' )
           (ctxStrs <> ctxStrs')
           (leftmostJust stk stk')  -- We usually extend errors form the right
instance Monoid ErrCtx where
  mempty = ErrCtx Nothing Nothing [] Nothing

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
