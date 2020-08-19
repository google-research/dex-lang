-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE DeriveGeneric #-}

import System.Console.Haskeline
import System.Exit
import Control.Monad
import Control.Monad.State.Strict
import Options.Applicative
import System.Posix.Terminal (queryTerminal)
import System.Posix.IO (stdOutput)

import Syntax
import PPrint
import RenderHtml
import Serialize

import TopLevel
import Parser  hiding (Parser)
import LiveOutput

data ErrorHandling = HaltOnErr | ContinueOnErr
data DocFmt = ResultOnly | TextDoc | HtmlDoc
data EvalMode = ReplMode String
              | WebMode    FilePath
              | WatchMode  FilePath
              | ScriptMode FilePath DocFmt ErrorHandling
data CmdOpts = CmdOpts EvalMode EvalConfig

type BlockCounter = Int
type EvalState = (BlockCounter, TopEnv)

runMode :: EvalMode -> EvalConfig -> IO ()
runMode evalMode opts = do
  (n, env) <- memoizeFileEval "prelude.cache" (evalPrelude opts) (preludeFile opts)
  let runEnv m = evalStateT m (n, env)
  case evalMode of
    ReplMode prompt ->
      runEnv $ runInputT defaultSettings $ forever (replLoop prompt opts)
    ScriptMode fname fmt _ -> do
      results <- runEnv $ evalFile opts fname
      printLitProg fmt results
    -- These are broken if the prelude produces any arrays because the blockId
    -- counter restarts at zero. TODO: make prelude an implicit import block
    WebMode   fname -> runWeb      fname opts env
    WatchMode fname -> runTerminal fname opts env

evalDecl :: EvalConfig -> SourceBlock -> StateT EvalState IO Result
evalDecl opts block = do
  (n, env) <- get
  (env', ans) <- liftIO $ evalSourceBlock opts env $ block
  put (n+1, env <> env')
  return ans

evalFile :: EvalConfig -> FilePath -> StateT EvalState IO [(SourceBlock, Result)]
evalFile opts fname = do
  source <- liftIO $ readFile fname
  let sourceBlocks = parseProg source
  results <- mapM (evalDecl opts) sourceBlocks
  return $ zip sourceBlocks results

evalPrelude ::EvalConfig-> FilePath -> IO EvalState
evalPrelude opts fname = flip execStateT (0, mempty) $ do
  result <- evalFile opts fname
  void $ liftErrIO $ mapM (\(_, Result _ r) -> r) result

replLoop :: String -> EvalConfig -> InputT (StateT EvalState IO) ()
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

printLitProg :: DocFmt -> LitProg -> IO ()
printLitProg ResultOnly prog = putStr $ foldMap (nonEmptyNewline . pprint . snd) prog
  where
    nonEmptyNewline [] = []
    nonEmptyNewline l  = l ++ ['\n']
printLitProg HtmlDoc    prog = putStr $ progHtml prog
printLitProg TextDoc    prog = do
  isatty <- queryTerminal stdOutput
  putStr $ foldMap (uncurry (printLitBlock isatty)) prog

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
        <|> flag' ResultOnly (long "result-only" <> help "Only output program results")
        <|> pure TextDoc )
    <*> flag HaltOnErr ContinueOnErr (
                  long "allow-errors"
               <> help "Evaluate programs containing non-fatal type errors")))
  where
    sourceFileInfo = argument str (metavar "FILE" <> help "Source program")

optionList :: [(String, a)] -> ReadM a
optionList opts = eitherReader $ \s -> case lookup s opts of
  Just x  -> Right x
  Nothing -> Left $ "Bad option. Expected one of: " ++ show (map fst opts)

parseEvalOpts :: Parser EvalConfig
parseEvalOpts = EvalConfig
  <$> (option
         (optionList [ ("LLVM", LLVM)
                     , ("LLVM-CUDA", LLVMCUDA)
                     , ("LLVM-MC", LLVMMC)
                     , ("JAX", JAX)
                     , ("interp", Interp)])
         (long "backend" <> value LLVM <> help "Backend (LLVM|LLVM-CUDA|JAX|interp)"))
  <*> (strOption $ long "prelude" <> value "prelude.dx" <> metavar "FILE"
                                  <> help "Prelude file" <> showDefault)
  <*> (optional $ strOption $ long "logto"
                    <> metavar "FILE"
                    <> help "File to log to" <> showDefault)
  <*> pure (error "Backend not initialized")
  <*> pure (error "Logging not initialized")

main :: IO ()
main = do
  CmdOpts evalMode opts <- execParser parseOpts
  engine <- initializeBackend $ backendName opts
  runMode evalMode $ opts { evalEngine = engine }
