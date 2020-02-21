-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

import System.Console.Haskeline
import System.Exit
import Control.Monad
import Control.Monad.State.Strict
import Options.Applicative
import Data.Semigroup ((<>))

import Syntax
import PPrint
import RenderHtml

import TopLevel
import Parser
import LiveOutput

data ErrorHandling = HaltOnErr | ContinueOnErr
data DocFmt = ResultOnly | TextDoc | HtmlDoc
data EvalMode = ReplMode String
              | WebMode    FilePath
              | WatchMode  FilePath
              | ScriptMode FilePath DocFmt ErrorHandling
data CmdOpts = CmdOpts EvalMode EvalOpts

runMode :: EvalMode -> EvalOpts -> IO ()
runMode evalMode opts = do
  env <- execStateT (evalPrelude opts) mempty
  let runEnv m = evalStateT m env
  case evalMode of
    ReplMode prompt ->
      runEnv $ runInputT defaultSettings $ forever (replLoop prompt opts)
    ScriptMode fname fmt _ -> do
      results <- runEnv $ evalFile opts fname
      putStr $ printLitProg fmt results
    WebMode   fname -> runWeb      fname opts env
    WatchMode fname -> runTerminal fname opts env

evalDecl :: EvalOpts -> SourceBlock -> StateT TopEnv IO Result
evalDecl opts block = do
  env <- get
  (env', ans) <- liftIO (evalBlock opts env block)
  modify (<> env')
  return ans

evalFile :: EvalOpts -> FilePath -> StateT TopEnv IO [(SourceBlock, Result)]
evalFile opts fname = do
  source <- liftIO $ readFile fname
  let sourceBlocks = parseProg source
  results <- mapM (evalDecl opts) sourceBlocks
  return $ zip sourceBlocks results

evalPrelude ::EvalOpts-> StateT TopEnv IO ()
evalPrelude opts = do
  result <- evalFile opts (preludeFile opts)
  void $ liftErrIO $ mapM (\(_, Result _ r) -> r) result

replLoop :: String -> EvalOpts -> InputT (StateT TopEnv IO) ()
replLoop prompt opts = do
  sourceBlock <- readMultiline prompt parseTopDeclRepl
  env <- lift get
  result <- lift $ (evalDecl opts) sourceBlock
  case result of Result _ (Left _) -> lift $ put env
                 _ -> return ()
  liftIO $ putStrLn $ pprint result

liftErrIO :: MonadIO m => Except a -> m a
liftErrIO (Left err) = liftIO $ putStrLn (pprint err) >> exitFailure
liftErrIO (Right x) = return x

readMultiline :: (MonadException m, MonadIO m) =>
                   String -> (String -> Maybe a) -> InputT m a
readMultiline prompt parse = loop prompt ""
  where
    dots = replicate 3 '.' ++ " "
    loop prompt' prevRead = do
      source <- getInputLine prompt'
      case source of
        Nothing -> liftIO exitSuccess
        Just s -> case parse s' of
          Just ans -> return ans
          Nothing -> loop dots s'
          where s' = prevRead ++ s ++ "\n"

simpleInfo :: Parser a -> ParserInfo a
simpleInfo p = info (p <**> helper) mempty

printLitProg :: DocFmt -> LitProg -> String
printLitProg TextDoc    prog = foldMap (uncurry printLitBlock) prog
printLitProg ResultOnly prog = foldMap (pprint . snd) prog
printLitProg HtmlDoc    prog = progHtml prog

parseOpts :: ParserInfo CmdOpts
parseOpts = simpleInfo $ CmdOpts <$> parseMode <*> parseEvalOpts

parseMode :: Parser EvalMode
parseMode = subparser $
     (command "repl" $ simpleInfo $
         ReplMode <$> (strOption $ long "prompt" <> value ">=> "
                         <> metavar "STRING" <> help "REPL prompt"))
  <> (command "web"    $ simpleInfo (WebMode    <$> sourceFileInfo ))
  <> (command "watch"  $ simpleInfo (WatchMode  <$> sourceFileInfo ))
  <> (command "script" $ simpleInfo (ScriptMode <$> sourceFileInfo
    <*> (   flag' HtmlDoc (long "html" <> help "HTML literate program output")
        <|> pure TextDoc )
    <*> flag HaltOnErr ContinueOnErr (
                  long "allow-errors"
               <> help "Evaluate programs containing non-fatal type errors")))
  where
    sourceFileInfo = argument str (metavar "FILE" <> help "Source program")

parseEvalOpts :: Parser EvalOpts
parseEvalOpts = EvalOpts
  <$> (flag Jit Interp $ long "interp" <> help "Use interpreter backend")
  <*> (strOption $ long "prelude" <> value "prelude.dx" <> metavar "FILE"
                                  <> help "Prelude file" <> showDefault)
  <*> (flag False True $ long "logall" <> help "Log all debug info")

main :: IO ()
main = do
  CmdOpts evalMode opts <- execParser parseOpts
  runMode evalMode opts
