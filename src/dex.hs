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
import Data.Void

import Syntax
import PPrint
import RenderHtml
import Pass
import Type

import Parser
import DeShadow
import Inference
import Imp
import JIT
import Flops
import WebOutput
import Normalize
import Interpreter

data Backend = Jit | Interp
data ErrorHandling = HaltOnErr | ContinueOnErr
data DocFmt = ResultOnly | TextDoc | HtmlDoc
data EvalMode = ReplMode
              | WebMode FName
              | ScriptMode FName DocFmt ErrorHandling
type PreludeFile = String
data EvalOpts = EvalOpts Backend (Maybe PreludeFile)
data CmdOpts = CmdOpts EvalMode EvalOpts

type FName = String

typeCheckPass :: TopPass SourceBlock TopDecl
typeCheckPass = sourcePass >+> deShadowPass >+> typePass >+> checkTyped

fullPassInterp :: TopPass SourceBlock Void
fullPassInterp = typeCheckPass >+> interpPass

fullPassJit :: TopPass SourceBlock Void
fullPassJit = typeCheckPass
          >+> normalizePass >+> checkNExpr
          >+> simpPass      >+> checkNExpr
          >+> impPass       >+> checkImp
          >+> flopsPass
          >+> jitPass

runMode :: Monoid env => EvalMode -> Maybe PreludeFile -> FullPass env -> IO ()
runMode evalMode prelude pass = do
  env <- execStateT (evalPrelude prelude pass) mempty
  let runEnv m = evalStateT m env
  case evalMode of
    ReplMode ->
      runEnv $ runInputT defaultSettings $ forever (replLoop pass)
    ScriptMode fname fmt _ -> do
      results <- runEnv $ evalFile pass fname
      putStr $ printLitProg fmt results
    WebMode fname -> runWeb fname pass env

evalDecl :: Monoid env => FullPass env -> SourceBlock -> StateT env IO Result
evalDecl pass block = do
  env <- get
  (ans, env') <- liftIO (runFullPass env pass block) `catch` (\e ->
                   return (compilerErr (show (e::SomeException)), mempty))
  modify (<> env')
  return ans

compilerErr :: String -> Result
compilerErr s = Result $ Left $ Err CompilerErr Nothing s

evalFile :: Monoid env =>
              FullPass env-> String -> StateT env IO [(SourceBlock, Result)]
evalFile pass fname = do
  source <- liftIO $ readFile fname
  let sourceBlocks = parseProg source
  results <- mapM (evalDecl pass) sourceBlocks
  return $ zip sourceBlocks results

evalPrelude :: Monoid env => Maybe PreludeFile -> FullPass env-> StateT env IO ()
evalPrelude fname pass = do
  result <- evalFile pass fname'
  void $ liftErrIO $ mapM (\(_, (Result r)) -> r) result
  where fname' = case fname of Just f -> f
                               Nothing -> "prelude.dx"

replLoop :: Monoid env => FullPass env-> InputT (StateT env IO) ()
replLoop pass = do
  sourceBlock <- readMultiline ">=> " parseTopDeclRepl
  result <- lift $ evalDecl pass sourceBlock
  liftIO $ putStrLn $ pprint result

liftErrIO :: MonadIO m => Except a -> m a
liftErrIO (Left err) = liftIO $ putStrLn (pprint err) >> exitFailure
liftErrIO (Right x) = return x

readMultiline :: (MonadException m, MonadIO m) =>
                   String -> (String -> Maybe a) -> InputT m a
readMultiline prompt parse = loop prompt ""
  where
    dots = replicate (length prompt - 1) '.' ++ " "
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
     (command "repl" $ simpleInfo (pure ReplMode))
  <> (command "web"  $ simpleInfo (
         WebMode <$> argument str (metavar "FILE" <> help "Source program")))
  <> (command "script" $ simpleInfo (ScriptMode
    <$> argument str (metavar "FILE" <> help "Source program")
    <*> (   flag' TextDoc (long "lit"  <> help "Textual literate program output")
        <|> flag' HtmlDoc (long "html" <> help "HTML literate program output")
        <|> pure ResultOnly)
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
  case backend of
    Jit    -> case fullPassJit    of TopPass f -> runMode evalMode prelude f
    Interp -> case fullPassInterp of TopPass f -> runMode evalMode prelude f
