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
import WebOutput

data ErrorHandling = HaltOnErr | ContinueOnErr
data DocFmt = ResultOnly | TextDoc | HtmlDoc
data EvalMode = ReplMode String
              | WebMode FName
              | ScriptMode FName DocFmt ErrorHandling
type PreludeFile = String
data EvalOpts = EvalOpts Backend (Maybe PreludeFile)
data CmdOpts = CmdOpts EvalMode EvalOpts

type FName = String

runMode :: EvalMode -> Maybe PreludeFile -> Backend -> IO ()
runMode evalMode prelude backend = do
  env <- execStateT (evalPrelude prelude backend) mempty
  let runEnv m = evalStateT m env
  case evalMode of
    ReplMode prompt ->
      runEnv $ runInputT defaultSettings $ forever (replLoop prompt backend)
    ScriptMode fname fmt _ -> do
      results <- runEnv $ evalFile backend fname
      putStr $ printLitProg fmt results
    WebMode fname -> runWeb fname backend env

evalDecl :: Backend -> SourceBlock -> StateT TopEnv IO Result
evalDecl backend block = do
  env <- get
  (env', ans) <- liftIO (evalBlock backend env block)
  modify (<> env')
  return ans

evalFile :: Backend -> String -> StateT TopEnv IO [(SourceBlock, Result)]
evalFile backend fname = do
  source <- liftIO $ readFile fname
  let sourceBlocks = parseProg source
  results <- mapM (evalDecl backend) sourceBlocks
  return $ zip sourceBlocks results

evalPrelude :: Maybe PreludeFile -> Backend-> StateT TopEnv IO ()
evalPrelude fname backend = do
  result <- evalFile backend fname'
  void $ liftErrIO $ mapM (\(_, Result _ r) -> r) result
  where fname' = case fname of Just f -> f
                               Nothing -> "prelude.dx"

replLoop :: String -> Backend -> InputT (StateT TopEnv IO) ()
replLoop prompt backend = do
  sourceBlock <- readMultiline prompt parseTopDeclRepl
  env <- lift get
  result <- lift $ (evalDecl backend) sourceBlock
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
  <> (command "web"  $ simpleInfo (
         WebMode <$> argument str (metavar "FILE" <> help "Source program")))
  <> (command "script" $ simpleInfo (ScriptMode
    <$> argument str (metavar "FILE" <> help "Source program")
    <*> (   flag' HtmlDoc (long "html" <> help "HTML literate program output")
        <|> pure TextDoc )
    <*> flag HaltOnErr ContinueOnErr (
                  long "allow-errors"
               <> help "Evaluate programs containing non-fatal type errors")))

parseEvalOpts :: Parser EvalOpts
parseEvalOpts = EvalOpts
                   <$> (flag Jit Interp $
                         long "interp" <> help "Use interpreter backend")
                   <*> (optional $ strOption $
                            long "prelude"
                         <> metavar "FILE"
                         <> help "Alternative prelude file")

main :: IO ()
main = do
  CmdOpts evalMode (EvalOpts backend prelude) <- execParser parseOpts
  runMode evalMode prelude backend
