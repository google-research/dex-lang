-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

import Control.Monad
import Control.Monad.State.Strict
import Options.Applicative hiding (Success, Failure)
import Text.PrettyPrint.ANSI.Leijen (text, hardline)
import System.Posix.Terminal (queryTerminal)
import System.Posix.IO (stdOutput)

import Data.List
import qualified System.Console.ANSI as ANSI
import System.Console.ANSI hiding (Color)

import Types.Source
import TopLevel
import ConcreteSyntax (parseSourceBlocks)
import PPrint
import Util (readFileText)

data EvalMode = ReplMode
              | ScriptMode FilePath
              | WebMode    FilePath
              | GenerateHTML FilePath FilePath
              | ClearCache

data CmdOpts = CmdOpts EvalMode EvalConfig

runMode :: CmdOpts -> IO ()
runMode (CmdOpts evalMode cfg) = case evalMode of
  ScriptMode fname -> do
    env <- initTopState -- loadCache
    void $ runTopperM cfg stdOutLogger env do
      blocks <- parseSourceBlocks <$> readFileText fname
      forM_ blocks \block -> do
        liftIO $ putStr $ pprint block
        evalSourceBlockRepl block
  _ -> error "not implemented"

stdOutLogger :: Outputs -> IO ()
stdOutLogger (Outputs outs) = do
  isatty <- queryTerminal stdOutput
  forM_ outs \out -> do
    when (outputPrintFilter out) do
      putStr $ printOutput isatty out

outputPrintFilter :: Output -> Bool
outputPrintFilter = \case
  TextOut _      -> True
  HtmlOut _      -> False
  SourceInfo _   -> False
  PassResult _ _ -> True
  MiscLog _      -> True
  Error _        -> True

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
  <> command "script" (simpleInfo (ScriptMode <$> sourceFileInfo))
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
  <$> (option pathOption $ long "lib-path" <> value [LibBuiltinPath]
    <> metavar "PATH" <> help "Library path")
  <*> optional (strOption $ long "prelude" <> metavar "FILE" <> help "Prelude file")
  <*> flag NoOptimize Optimize (short 'O' <> help "Optimize generated code")
  <*> enumOption "print" "Print backend" PrintCodegen printBackends
  where
    printBackends = [ ("haskell", PrintHaskell)
                    , ("dex"    , PrintCodegen) ]

printOutput :: Bool -> Output -> String
printOutput isatty out = case out of
  Error _ -> addColor isatty Red $ addPrefix ">" $ pprint out
  _       -> addPrefix (addColor isatty Cyan ">") $ pprint out

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
