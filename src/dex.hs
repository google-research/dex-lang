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

import qualified Data.ByteString as BS
import Data.List
import qualified Data.Text as T
import qualified Data.Text.Encoding as T
import qualified Data.Map.Strict as M
import qualified System.Console.ANSI as ANSI
import System.Console.ANSI hiding (Color)

import TopLevel
import Err
import Name
import AbstractSyntax (parseTopDeclRepl)
import ConcreteSyntax (keyWordStrs, preludeImportBlock)
import RenderHtml
-- import Live.Terminal (runTerminal)
import Live.Web (runWeb)
import Core
import Types.Core
import Types.Imp
import Types.Source
import Types.Top
import MonadUtil

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
runMode evalMode cfg = case evalMode of
  ScriptMode fname fmt onErr -> do
    env <- loadCache
    ((), finalEnv) <- runTopperM cfg env do
      source <- liftIO $ T.decodeUtf8 <$> BS.readFile fname
      evalSourceText source $ printIncrementalSource fmt
    storeCache finalEnv
  ReplMode prompt -> do
    env <- loadCache
    void $ runTopperM cfg env do
      evalSourceBlockRepl preludeImportBlock
      forever do
         block <- readSourceBlock prompt
         evalSourceBlockRepl block
  ClearCache -> clearCache
#ifdef DEX_LIVE
  WebMode    fname -> do
    env <- loadCache
    runWeb fname cfg env
  WatchMode  _ -> error "not implemented"
#endif

printIncrementalSource :: DocFmt -> SourceBlock -> IO ()
printIncrementalSource fmt sb = case fmt of
  ResultOnly -> return ()
  JSONDoc    -> return ()
  TextDoc    -> putStr $ pprint sb
#ifdef DEX_LIVE
  HTMLDoc -> return ()
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

enumOption :: String -> String -> a -> [(String, a)] -> Parser a
enumOption optName prettyOptName defaultVal options = option
  (optionList options)
  (long optName <> value defaultVal <>
     helpOption prettyOptName (intercalate " | " $ fst <$> options))

parseEvalOpts :: Parser EvalConfig
parseEvalOpts = EvalConfig
  <$> enumOption "backend" "Backend" LLVM backends
  <*> (option pathOption $ long "lib-path" <> value [LibBuiltinPath]
    <> metavar "PATH" <> help "Library path")
  <*> optional (strOption $ long "prelude" <> metavar "FILE" <> help "Prelude file")
  <*> flag NoOptimize Optimize (short 'O' <> help "Optimize generated code")
  <*> enumOption "print" "Print backend" PrintCodegen printBackends
  <*> flag ContinueOnErr HaltOnErr (
                long "stop-on-error"
             <> help "Stop program evaluation when an error occurs (type or runtime)")
  <*> enumOption "loglevel" "Log level" NormalLogLevel logLevels
  <*> pure stdOutLogger
  where
    printBackends = [ ("haskell", PrintHaskell)
                    , ("dex"    , PrintCodegen) ]
    backends = [ ("llvm"   , LLVM  )
               , ("llvm-mc", LLVMMC) ]
    logLevels = [ ("normal", NormalLogLevel)
                , ("debug" , DebugLogLevel ) ]

stdOutLogger :: Outputs -> IO ()
stdOutLogger (Outputs outs) = do
  isatty <- queryTerminal stdOutput
  forM_ outs \out -> putStr $ printOutput isatty out

printOutput :: Bool -> Output -> String
printOutput isatty out = case out of
  Error _ -> addColor isatty Red $ addPrefix ">" $ pprint out
  _       -> addPrefix (addColor isatty Cyan ">") $ pprint $ out

addPrefix :: String -> String -> String
addPrefix prefix str = unlines $ map prefixLine $ lines str
  where prefixLine :: String -> String
        prefixLine s = case s of "" -> prefix
                                 _  -> prefix ++ " " ++ s

addColor :: Bool -> ANSI.Color -> String -> String
addColor False _ s = s
addColor True c s =
  setSGRCode [SetConsoleIntensity BoldIntensity, SetColor Foreground Vivid c]
  ++ s ++ setSGRCode [Reset]


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

main :: IO ()
main = do
  CmdOpts evalMode opts <- execParser parseOpts
  runMode evalMode opts
