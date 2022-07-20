-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE RecordWildCards #-}

import System.Console.Haskeline
import System.Exit
import Control.Monad
import Control.Monad.State.Strict
import Options.Applicative hiding (Success, Failure)
import Text.PrettyPrint.ANSI.Leijen (text, hardline)
import System.Posix.Terminal (queryTerminal)
import System.Posix.IO (stdOutput)
import System.IO (openFile, IOMode (..))

import Data.List
import Data.Functor
import qualified Data.Text as T
import qualified Data.Text.IO as T
import qualified Data.Map.Strict as M

import PPrint (toJSONStr, printResult)
import TopLevel
import Err
import Syntax
import Name
import Parser (parseTopDeclRepl, keyWordStrs, preludeImportBlock)
#ifdef DEX_LIVE
import RenderHtml
import Live.Terminal (runTerminal)
import Live.Web (runWeb)
#endif

data ErrorHandling = HaltOnErr | ContinueOnErr
data DocFmt = ResultOnly
            | TextDoc
            | JSONDoc
#ifdef DEX_LIVE
            | HTMLDoc
#endif
data EvalMode = ReplMode String
              | ScriptMode FilePath DocFmt ErrorHandling
              | ExportMode FilePath FilePath -- Dex path, .o path
              | ClearCache
#ifdef DEX_LIVE
              | WebMode    FilePath
              | WatchMode  FilePath
#endif

data CmdOpts = CmdOpts EvalMode EvalConfig

runMode :: EvalMode -> EvalConfig -> IO ()
runMode evalMode opts = case evalMode of
  ScriptMode fname fmt onErr -> do
    env <- loadCache
    (litProg, finalEnv) <- runTopperM opts env do
      source <- liftIO $ T.readFile fname
      evalSourceText source (printIncrementalSource fmt) \result@(Result _ errs) -> do
        printIncrementalResult fmt result
        return case (onErr, errs) of (HaltOnErr, Failure _) -> False; _ -> True
    printFinal fmt litProg
    storeCache finalEnv
  ReplMode prompt -> do
    env <- loadCache
    void $ runTopperM opts env do
      evalBlockRepl preludeImportBlock
      forever do
         block <- readSourceBlock prompt
         evalBlockRepl block
    where
      evalBlockRepl :: (Topper m, Mut n) => SourceBlock -> m n ()
      evalBlockRepl block = do
        result <- evalSourceBlockRepl block
        case result of
          Result [] (Success ()) -> return ()
          _ -> liftIO $ putStrLn $ pprint result
  ClearCache -> clearCache
#ifdef DEX_LIVE
  -- These are broken if the prelude produces any arrays because the blockId
  -- counter restarts at zero. TODO: make prelude an implicit import block
  WebMode    fname -> do
    env <- loadCache
    runWeb fname opts env
  WatchMode  fname -> do
    env <- loadCache
    runTerminal fname opts env
#endif

printIncrementalSource :: DocFmt -> SourceBlock -> IO ()
printIncrementalSource fmt sb = case fmt of
  ResultOnly -> return ()
  JSONDoc    -> return ()
  TextDoc    -> putStr $ pprint sb
#ifdef DEX_LIVE
  HTMLDoc -> return ()
#endif

printIncrementalResult :: DocFmt -> Result -> IO ()
printIncrementalResult fmt result = case fmt of
  ResultOnly -> case pprint result of [] -> return (); msg -> putStrLn msg
  JSONDoc    -> case toJSONStr result of "{}" -> return (); s -> putStrLn s
  TextDoc    -> do
    isatty <- queryTerminal stdOutput
    putStr $ printResult isatty result
#ifdef DEX_LIVE
  HTMLDoc -> return ()
#endif

printFinal :: DocFmt -> [(SourceBlock, Result)] -> IO ()
printFinal fmt prog = case fmt of
  ResultOnly -> return ()
  TextDoc    -> return ()
  JSONDoc    -> return ()
#ifdef DEX_LIVE
  HTMLDoc    -> putStr $ progHtml prog
#endif

readSourceBlock :: (MonadIO (m n), EnvReader m) => String -> m n SourceBlock
readSourceBlock prompt = do
  sourceMap <- withEnv $ envSourceMap . moduleEnv
  let filenameAndDexCompletions =
        completeQuotedWord (Just '\\') "\"'" listFiles (dexCompletions sourceMap)
  let hasklineSettings = setComplete filenameAndDexCompletions defaultSettings
  liftIO $ runInputT hasklineSettings $ readMultiline prompt (parseTopDeclRepl . T.pack)

dexCompletions :: Monad m => SourceMap n -> CompletionFunc m
dexCompletions sourceMap (line, _) = do
  let varNames = map pprint $ M.keys $ fromSourceMap sourceMap
  -- note: line and thus word and rest have character order reversed
  let (word, rest) = break (== ' ') line
  let startoflineKeywords = ["%bench \"", ":p", ":t", ":html", ":export"]
  let candidates = (if null rest then startoflineKeywords else []) ++
                   keyWordStrs ++ varNames
  let completions = map simpleCompletion $ filter (reverse word `isPrefixOf`) candidates
  return (rest, completions)

readMultiline :: String -> (String -> Maybe a) -> InputT IO a
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

parseOpts :: ParserInfo CmdOpts
parseOpts = simpleInfo $ CmdOpts <$> parseMode <*> parseEvalOpts

helpOption :: String -> String -> Mod f a
helpOption optionName options =
  helpDoc (Just (text optionName <> hardline <> text options))

parseMode :: Parser EvalMode
parseMode = subparser $
     command "repl" (simpleInfo
         (ReplMode <$> strOption (long "prompt" <> value ">=> "
                         <> metavar "STRING" <> help "REPL prompt")))
#ifdef DEX_LIVE
  <> command "web"    (simpleInfo (WebMode    <$> sourceFileInfo))
  <> command "watch"  (simpleInfo (WatchMode  <$> sourceFileInfo))
#endif
  <> command "clean"  (simpleInfo (pure ClearCache))
  <> command "export" (simpleInfo (ExportMode <$> sourceFileInfo <*> objectFileInfo))
  <> command "script" (simpleInfo (ScriptMode <$> sourceFileInfo
  <*> option
        (optionList [ ("literate"   , TextDoc)
                    , ("result-only", ResultOnly)
#ifdef DEX_LIVE
                    , ("html"       , HTMLDoc)
#endif
                    , ("json"       , JSONDoc)])
        (long "outfmt" <> value TextDoc <>
         helpOption "Output format" "literate (default) | result-only | html | json")
  <*> flag ContinueOnErr HaltOnErr (
                long "stop-on-error"
             <> help "Stop program evaluation when an error occurs (type or runtime)")))
  where
    sourceFileInfo = argument str (metavar "FILE" <> help "Source program")
    objectFileInfo = argument str (metavar "OBJFILE" <> help "Output path (.o file)")

optionList :: [(String, a)] -> ReadM a
optionList opts = eitherReader \s -> case lookup s opts of
  Just x  -> Right x
  Nothing -> Left $ "Bad option. Expected one of: " ++ show (map fst opts)

parseEvalOpts :: Parser EvalConfig
parseEvalOpts = EvalConfig
  <$> option
         (optionList backends)
         (long "backend" <> value LLVM <>
          helpOption "Backend" (intercalate " | " $ fst <$> backends))
  <*> (option pathOption $ long "lib-path" <> value [LibBuiltinPath]
    <> metavar "PATH" <> help "Library path")
  <*> optional (strOption $ long "prelude" <> metavar "FILE" <> help "Prelude file")
  <*> optional (strOption $ long "logto"
                    <> metavar "FILE"
                    <> help "File to log to" <> showDefault)
  <*> pure Nothing
  <*> flag NoOptimize Optimize (short 'O' <> help "Optimize generated code")
  where
    backends = [ ("llvm", LLVM)
               , ("llvm-mc", LLVMMC)
#ifdef DEX_CUDA
               , ("llvm-cuda", LLVMCUDA)
#endif
#if DEX_LLVM_VERSION == HEAD
               , ("mlir", MLIR)
#endif
               , ("interpreter", Interpreter)]

pathOption :: ReadM [LibPath]
pathOption = splitPaths [] <$> str
  where
    splitPaths :: [LibPath] -> String -> [LibPath]
    splitPaths revAcc = \case
      []  -> reverse revAcc
      str -> let (p,t) = break (==':') str in
             splitPaths (parseLibPath p:revAcc) (dropWhile (==':') t)

    parseLibPath = \case
      "BUILTIN_LIBRARIES" -> LibBuiltinPath
      path -> LibDirectory path

openLogFile :: EvalConfig -> IO EvalConfig
openLogFile EvalConfig {..} = do
  logFile <- forM logFileName (`openFile` WriteMode)
  return $ EvalConfig {..}

main :: IO ()
main = do
  CmdOpts evalMode opts <- execParser parseOpts
  opts' <- openLogFile opts
  runMode evalMode opts'
