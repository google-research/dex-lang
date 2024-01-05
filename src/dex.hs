-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

import System.Console.Haskeline
import System.Exit
import Control.Monad
import Control.Monad.State.Strict
import Options.Applicative hiding (Success, Failure)
import Text.PrettyPrint.ANSI.Leijen (text, hardline)
import System.Posix.Terminal (queryTerminal)
import System.Posix.IO (stdOutput)

import Data.List
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import qualified System.Console.ANSI as ANSI
import System.Console.ANSI hiding (Color)

import TopLevel
import AbstractSyntax (parseTopDeclRepl)
import ConcreteSyntax (keyWordStrs, preludeImportBlock)
import Live.Web
import PPrint  hiding (hardline)
import Core
import Types.Imp
import Types.Source
import Types.Top
import MonadUtil
import Util (readFileText)

data DocFmt = ResultOnly
            | TextDoc

data EvalMode = ReplMode
              | ScriptMode FilePath DocFmt
              | WebMode    FilePath
              | GenerateHTML FilePath FilePath
              | ClearCache

data CmdOpts = CmdOpts EvalMode EvalConfig

runMode :: CmdOpts -> IO ()
runMode (CmdOpts evalMode cfg) = case evalMode of
  ScriptMode fname fmt -> do
    env <- loadCache
    ((), finalEnv) <- runTopperM cfg stdOutLogger env do
      blocks <- parseSourceBlocks <$> readFileText fname
      forM_ blocks \block -> do
        case fmt of
          ResultOnly -> return ()
          TextDoc    -> liftIO $ putStr $ pprint block
        evalSourceBlockRepl block
    storeCache finalEnv
  ReplMode -> do
    env <- loadCache
    void $ runTopperM cfg stdOutLogger env do
      void $ evalSourceBlockRepl preludeImportBlock
      forever do
         block <- readSourceBlock
         void $ evalSourceBlockRepl block
  WebMode    fname -> do
    env <- loadCache
    runWeb fname cfg env
  GenerateHTML fname dest -> do
    env <- loadCache
    generateHTML fname dest cfg env
  ClearCache -> clearCache

stdOutLogger :: Outputs -> IO ()
stdOutLogger (Outputs outs) = do
  isatty <- queryTerminal stdOutput
  forM_ outs \out -> putStr $ printOutput isatty out

readSourceBlock :: (MonadIO (m n), EnvReader m) => m n SourceBlock
readSourceBlock = do
  sourceMap <- withEnv $ envSourceMap . moduleEnv
  let filenameAndDexCompletions =
        completeQuotedWord (Just '\\') "\"'" listFiles (dexCompletions sourceMap)
  let hasklineSettings = setComplete filenameAndDexCompletions defaultSettings
  liftIO $ runInputT hasklineSettings $ readMultiline prompt (parseTopDeclRepl . T.pack)
  where prompt = ">=> "

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
     command "repl" (simpleInfo (pure ReplMode))
  <> command "web"    (simpleInfo (WebMode    <$> sourceFileInfo))
  <> command "generate-html" (simpleInfo (GenerateHTML <$> sourceFileInfo <*> destFileInfo))
  <> command "clean"  (simpleInfo (pure ClearCache))
  <> command "script" (simpleInfo (ScriptMode <$> sourceFileInfo <*> option
        (optionList [ ("literate"   , TextDoc)
                    , ("result-only", ResultOnly)])
        (long "outfmt" <> value TextDoc <>
         helpOption "Output format" "literate (default) | result-only | html | json")))
  where
    sourceFileInfo = argument str (metavar "FILE"    <> help "Source program")
    destFileInfo   = argument str (metavar "OUTFILE" <> help "Output path")

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
  <*> enumOption "loglevel" "Log level" NormalLogLevel logLevels
  where
    printBackends = [ ("haskell", PrintHaskell)
                    , ("dex"    , PrintCodegen) ]
    backends = [ ("llvm"   , LLVM  )
               , ("llvm-mc", LLVMMC) ]
    logLevels = [ ("normal", NormalLogLevel)
                , ("debug" , DebugLogLevel ) ]

printOutput :: Bool -> Output -> String
printOutput isatty out = case out of
  Error _ -> addColor isatty Red $ addPrefix ">" $ pprint out
  _       -> addPrefix (addColor isatty Cyan ">") $ pprint $ out

addPrefix :: String -> String -> String
addPrefix prefix s = unlines $ map prefixLine $ lines s
  where prefixLine :: String -> String
        prefixLine l = case l of "" -> prefix
                                 _  -> prefix ++ " " ++ l

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
      s -> let (p,t) = break (==':') s in
             splitPaths (parseLibPath p:revAcc) (dropWhile (==':') t)

    parseLibPath = \case
      "BUILTIN_LIBRARIES" -> LibBuiltinPath
      path -> LibDirectory path

main :: IO ()
main = execParser parseOpts >>= runMode
