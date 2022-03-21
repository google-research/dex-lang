-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module Live.Terminal (runTerminal) where

import Control.Concurrent (Chan, readChan, forkIO)
import Control.Monad.State.Strict
import Data.Foldable (fold)
import qualified Data.Map.Strict as M

import System.Console.ANSI (clearScreen, setCursorPosition)
import System.IO (BufferMode (..), hSetBuffering, stdin)

import Actor
import Cat
import Live.Eval
import PPrint (printLitBlock)
import TopLevel

runTerminal :: FilePath -> EvalConfig -> TopStateEx -> IO ()
runTerminal fname opts env = do
  resultsChan <- watchAndEvalFile fname opts env
  displayResultsTerm resultsChan

type DisplayPos = Int
data KeyboardCommand = ScrollUp | ScrollDown | ResetDisplay

type TermDisplayM = StateT DisplayPos (CatT RFragment IO)

displayResultsTerm :: PChan (PChan RFragment) -> IO ()
displayResultsTerm resultsSubscribe =
  runActor \self -> do
     resultsSubscribe `sendPChan` subChan Left (sendOnly self)
     void $ forkIO $ monitorKeyboard $ subChan Right (sendOnly self)
     evalCatT $ flip evalStateT 0 $ forever $ termDisplayLoop self

termDisplayLoop :: (Chan (Either RFragment KeyboardCommand)) -> TermDisplayM ()
termDisplayLoop self = do
  req <- liftIO $ readChan self
  case req of
    Left result -> extend result
    Right command -> case command of
      ScrollUp     -> modify (+ 4)
      ScrollDown   -> modify (\p -> max 0 (p - 4))
      ResetDisplay -> put 0
  results <- look
  pos <- get
  case renderResults results of
    Nothing -> return ()
    Just s  -> liftIO $ do
      let cropped = cropTrailingLines pos s
      setCursorPosition 0 0
      clearScreen -- TODO: clean line-by-line instead
      putStr cropped

cropTrailingLines :: Int -> String -> String
cropTrailingLines n s = unlines $ reverse $ drop n $ reverse $ lines s

-- TODO: show incremental results
renderResults :: RFragment -> Maybe String
renderResults (RFragment NotSet _ _) = Nothing
renderResults (RFragment (Set ids) blocks results) =
  liftM fold $ forM ids $ \i -> do
    b <- M.lookup i blocks
    r <- M.lookup i results
    return $ printLitBlock True b r

-- A non-Actor source.  Sends keyboard command signals as they occur.
monitorKeyboard :: PChan KeyboardCommand -> IO ()
monitorKeyboard chan = do
  hSetBuffering stdin NoBuffering
  forever $ do
    c <- getChar
    case c of
      'k' -> chan `sendPChan` ScrollUp
      'j' -> chan `sendPChan` ScrollDown
      'q' -> chan `sendPChan` ResetDisplay
      _   -> return ()

