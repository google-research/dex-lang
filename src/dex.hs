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
import System.Exit
import System.Directory

import Syntax
import PPrint
import RenderHtml
import Serialize
import Resources

import TopLevel
import Parser  hiding (Parser)
import LiveOutput
import Export

data ErrorHandling = HaltOnErr | ContinueOnErr
data DocFmt = ResultOnly | TextDoc | HTMLDoc | JSONDoc
data EvalMode = ReplMode String
              | WebMode    FilePath
              | WatchMode  FilePath
              | ExportMode FilePath FilePath -- Dex path, .o path
              | ScriptMode FilePath DocFmt ErrorHandling

data CmdOpts = CmdOpts EvalMode (Maybe FilePath) EvalConfig

runMode :: EvalMode -> Maybe FilePath -> EvalConfig -> IO ()
runMode evalMode preludeFile opts = do
  key <- case preludeFile of
           Nothing   -> return $ show curResourceVersion -- memoizeFileEval already checks compiler version
           Just path -> show <$> getModificationTime path
  env <- cached "prelude" key $ evalPrelude opts preludeFile
  let runEnv m = evalStateT m env
  case evalMode of
    ReplMode prompt ->
      runEnv $ runInputT defaultSettings $ forever (replLoop prompt opts)
    ScriptMode fname fmt _ -> do
      results <- runEnv $ evalFile opts fname
      printLitProg fmt results
    -- These are broken if the prelude produces any arrays because the blockId
    -- counter restarts at zero. TODO: make prelude an implicit import block
    WebMode    fname -> runWeb      fname opts env
    WatchMode  fname -> runTerminal fname opts env
    ExportMode dexPath objPath -> do
      results <- fmap snd <$> (runEnv $ evalFile opts dexPath)
      let outputs = foldMap (\(Result outs _) -> outs) results
      let errors = foldMap (\case (Result _ (Left err)) -> [err]; _ -> []) results
      putStr $ foldMap (nonEmptyNewline . pprint) errors
      let exportedFuns = foldMap (\case (ExportedFun name f) -> [(name, f)]; _ -> []) outputs
      unless (backendName opts == LLVM) $ liftEitherIO $
        throw CompilerErr "Export only supported with the LLVM CPU backend"
      exportFunctions objPath exportedFuns env

evalPrelude :: EvalConfig -> Maybe FilePath -> IO TopEnv
evalPrelude opts fname = flip execStateT initTopEnv $ do
  source <- case fname of
              Nothing   -> return $ preludeSource
              Just path -> liftIO $ readFile path
  result <- evalSource opts source
  void $ liftErrIO $ mapM (\(_, Result _ r) -> r) result

replLoop :: String -> EvalConfig -> InputT (StateT TopEnv IO) ()
replLoop prompt opts = do
  sourceBlock <- readMultiline prompt parseTopDeclRepl
  env <- lift get
  result <- lift $ evalDecl opts sourceBlock
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
printLitProg HTMLDoc prog = putStr $ progHtml prog
printLitProg TextDoc prog = do
  isatty <- queryTerminal stdOutput
  putStr $ foldMap (uncurry (printLitBlock isatty)) prog
printLitProg JSONDoc prog =
  forM_ prog $ \(_, result) -> case toJSONStr result of
    "{}" -> return ()
    s -> putStrLn s

nonEmptyNewline [] = []
nonEmptyNewline l  = l ++ ['\n']

parseOpts :: ParserInfo CmdOpts
parseOpts = simpleInfo $ CmdOpts
  <$> parseMode
  <*> (optional $ strOption $ long "prelude" <> metavar "FILE" <> help "Prelude file")
  <*> parseEvalOpts

parseMode :: Parser EvalMode
parseMode = subparser $
     (command "repl" $ simpleInfo $
         ReplMode <$> (strOption $ long "prompt" <> value ">=> "
                         <> metavar "STRING" <> help "REPL prompt"))
  <> (command "web"    $ simpleInfo (WebMode    <$> sourceFileInfo ))
  <> (command "watch"  $ simpleInfo (WatchMode  <$> sourceFileInfo ))
  <> (command "export" $ simpleInfo (ExportMode <$> sourceFileInfo <*> objectFileInfo))
  <> (command "script" $ simpleInfo (ScriptMode <$> sourceFileInfo
    <*> (option
            (optionList [ ("literate"   , TextDoc)
                        , ("result-only", ResultOnly)
                        , ("HTML"       , HTMLDoc)
                        , ("JSON"       , JSONDoc)])
            (long "outfmt" <> value TextDoc
             <> help "Output format (literate(default)|result-only|HTML|JSON"))
    <*> flag HaltOnErr ContinueOnErr (
                  long "allow-errors"
               <> help "Evaluate programs containing non-fatal type errors")))
  where
    sourceFileInfo = argument str (metavar "FILE" <> help "Source program")
    objectFileInfo = argument str (metavar "OBJFILE" <> help "Output path (.o file)")

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
                     , ("interp", Interp)])
         (long "backend" <> value LLVM <> help "Backend (LLVM(default)|LLVM-CUDA|interp)"))
  <*> (optional $ strOption $ long "logto"
                    <> metavar "FILE"
                    <> help "File to log to" <> showDefault)

main :: IO ()
main = do
  CmdOpts evalMode preludeFile opts <- execParser parseOpts
  runMode evalMode preludeFile opts
