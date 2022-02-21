-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE DeriveGeneric #-}

import System.Console.Haskeline
import System.Exit
import Control.Monad
import Control.Monad.Catch
import Control.Monad.State.Strict
import Options.Applicative hiding (Success, Failure)
import Text.PrettyPrint.ANSI.Leijen (text, hardline)
import System.Posix.Terminal (queryTerminal)
import System.Posix.IO (stdOutput)
import System.IO (stderr, hPutStrLn)

import System.Directory
import Data.List
import qualified Data.Map.Strict as M

import PPrint (toJSONStr, printLitBlock)
import Serialize
import Resources
import TopLevel
import Err
import Syntax
import Name
import Parser (parseTopDeclRepl, keyWordStrs, preludeImportBlock)
#ifdef DEX_LIVE
import RenderHtml
import LiveOutput
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
  ScriptMode fname fmt _ -> do
    env <- loadCache
    ((), finalEnv) <- runTopperM opts env do
      results <- evalFile fname
      liftIO $ printLitProg fmt results
    storeCache finalEnv
  ReplMode prompt -> do
    env <- loadCache
    void $ runTopperM opts env do
      evalBlockRepl preludeImportBlock
      forever do
         block <- readSourceBlock prompt
         evalBlockRepl block
  -- ExportMode dexPath objPath -> do
  --   results <- evalInterblockM opts env $ map snd <$> evalfile dexPath
  --   let outputs = foldMap (\(Result outs _) -> outs) results
  --   let errors = foldMap (\case (Result _ (Failure err)) -> [err]; _ -> []) results
  --   putStr $ foldMap (nonEmptyNewline . pprint) errors
  --   let exportedFuns = foldMap (\case (ExportedFun name f) -> [(name, f)]; _ -> []) outputs
  --   unless (backendName opts == LLVM) $
  --     throw CompilerErr "Export only supported with the LLVM CPU backend"
  --   TopStateEx env' <- return env
  --   -- exportFunctions objPath exportedFuns $ getNameBindings env'
  --   error "not implemented"
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

evalBlockRepl :: (Topper m, Mut n) => SourceBlock -> m n ()
evalBlockRepl block = do
  result <- evalSourceBlockRepl block
  case result of
    Result [] (Success ()) -> return ()
    _ -> liftIO $ putStrLn $ pprint result

liftErrIO :: MonadIO m => Except a -> m a
liftErrIO (Failure err) = liftIO $ putStrLn (pprint err) >> exitFailure
liftErrIO (Success ans) = return ans

readSourceBlock :: (MonadIO (m n), EnvReader m) => String -> m n SourceBlock
readSourceBlock prompt = do
  sourceMap <- withEnv $ envSourceMap . moduleEnv
  let filenameAndDexCompletions =
        completeQuotedWord (Just '\\') "\"'" listFiles (dexCompletions sourceMap)
  let hasklineSettings = setComplete filenameAndDexCompletions defaultSettings
  liftIO $ runInputT hasklineSettings $ readMultiline prompt parseTopDeclRepl

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

printLitProg :: DocFmt -> LitProg -> IO ()
printLitProg ResultOnly prog = putStr $ foldMap (nonEmptyNewline . pprint . snd) prog
#ifdef DEX_LIVE
printLitProg HTMLDoc prog = putStr $ progHtml prog
#endif
printLitProg TextDoc prog = do
  isatty <- queryTerminal stdOutput
  putStr $ foldMap (uncurry (printLitBlock isatty)) prog
printLitProg JSONDoc prog =
  forM_ prog \(_, result) -> case toJSONStr result of
    "{}" -> return ()
    s -> putStrLn s

nonEmptyNewline :: String -> String
nonEmptyNewline [] = []
nonEmptyNewline l  = l ++ ['\n']

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
  <*> flag HaltOnErr ContinueOnErr (
                long "allow-errors"
             <> help "Evaluate programs containing non-fatal type errors")))
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
  <*> optional (strOption $ long "lib-path" <> metavar "PATH" <> help "Library path")
  <*> optional (strOption $ long "prelude" <> metavar "FILE" <> help "Prelude file")
  <*> optional (strOption $ long "logto"
                    <> metavar "FILE"
                    <> help "File to log to" <> showDefault)
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

main :: IO ()
main = do
  CmdOpts evalMode opts <- execParser parseOpts
  runMode evalMode opts
