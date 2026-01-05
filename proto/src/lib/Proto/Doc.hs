-- Copyright 2025 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module Proto.Doc where

import Control.Monad
import Control.Monad.Reader

import Proto.Util

-- === doc tree (think HTML) represented as a sequence of edits ===

-- We normally construct Docs by emitting `DocEdit`s, which are edits against a
-- stateful cursor that tracks which block we're currently pointing to. This way
-- we can render documents incrementally. If we were rendering to html via
-- javascript then we could insert arbitrarily but since we also want to support
-- terminal output we restrict the editing to be append-only.
data DocEdit =
    EnterBlock DocTag
  | LeaveBlock
  | EmitLine String

-- We'll extend this as needed
data DocTag = PlainBlock | ErrorBlock | IndentedBlock

-- === logger class ===

class MonadIO m => Logger m where
  applyEdit :: DocEdit -> m ()

instance Logger DocMonad where
  applyEdit edit = DocMonad do
    edits <- ask
    push edits edit
  {-# INLINE applyEdit #-}

liftDoc :: Logger m => DocMonad a -> m a
liftDoc doc = do
  (ans, edits) <- runDocMonad doc
  mapM_ applyEdit edits
  return ans
{-# INLINE liftDoc #-}

-- === doc builder ===

-- Monadic helper for building docs based on IORef. Concatenation happens by
-- `>>`. Lines are emitted immediately. It's all stateful so it's easy
-- to reason about performance.
newtype DocMonad a = DocMonad (ReaderT (Stack DocEdit) IO a)
               deriving (Functor, Applicative, Monad, MonadIO)
type Doc = DocMonad ()

runDocMonad :: MonadIO m => DocMonad a -> m (a, [DocEdit])
runDocMonad (DocMonad cont) = do
  editsRev <- newStack []
  ans <- liftIO $ runReaderT cont editsRev
  edits <- reverse <$> peekAll editsRev
  return (ans, edits)
{-# INLINE runDocMonad #-}

editsToDoc :: [DocEdit] -> Doc
editsToDoc = mapM_ applyEdit

docToEdits :: MonadIO m => Doc -> m [DocEdit]
docToEdits doc = liftIO $ snd<$> runDocMonad doc

-- Deliberately monomorphic first-order helpers
oneLiner :: String -> Doc
oneLiner s = applyEdit $ EmitLine s

multiLiner :: String -> Doc
multiLiner s = forM_ (lines s) oneLiner

-- We make the higher-order combinators polymorphic
withLogBlock :: Logger m => DocTag -> m a -> m a
withLogBlock tag build = do
  applyEdit $ EnterBlock tag
  ans <- build
  applyEdit $ LeaveBlock
  return ans
{-# INLINE withLogBlock #-}

indented :: Logger m => m a -> m a
indented = withLogBlock IndentedBlock
{-# INLINE indented #-}

 -- === text backend ===

type LogAction = DocEdit -> IO ()

makePlainTextLogAction :: MonadIO m => (String -> IO ()) -> m LogAction
makePlainTextLogAction emitString = do
  tags <- newStack []
  return \case
    EnterBlock tag -> push tags tag
    LeaveBlock -> pop tags >>= \case
      Nothing -> error "Oops. Unbalanced enter/leave"
      Just _ -> return ()
    EmitLine s -> do
      curTags <- peekAll tags
      let indent = sum (curTags <&> \case IndentedBlock -> 1; _ -> 0)
      emitString $ (replicate (2*indent) ' ') <> s

makeStringLogAction :: MonadIO m => m (LogAction, IO String)
makeStringLogAction = do
  stack <- newStack []
  logger <- makePlainTextLogAction \s -> push stack s
  let readResult = do
        sourceLines <- peekAll stack
        return $ unlines $ reverse sourceLines
  return (logger, readResult)

doc2Str :: MonadIO m => Doc -> m String
doc2Str doc = liftIO do
  (logAction, readResult) <- makeStringLogAction
  edits <- docToEdits doc
  mapM_ logAction edits
  readResult
