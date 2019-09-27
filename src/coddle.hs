import System.Console.Haskeline
import System.Exit
import Control.Monad
import Control.Monad.State.Strict
import Options.Applicative
import Data.Semigroup ((<>))
import Data.Void

import Syntax
import PPrint
import Pass
import Type

import Parser
import DeShadow
import Inference
import Imp
import JIT
import Flops
#ifdef CODDLE_WEB
import WebOutput
#endif
import Normalize
import Interpreter

data Backend = Jit | Interp
data ErrorHandling = HaltOnErr | ContinueOnErr
data EvalMode = ReplMode
              | WebMode FName
              | ScriptMode FName DocFmt ErrorHandling
data CmdOpts = CmdOpts EvalMode Backend

type FName = String
type FullPass env = SourceBlock -> TopPassM env Void

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

runMode :: Monoid env => EvalMode -> FullPass env -> IO ()
runMode evalMode pass = do
  env <- execStateT (evalPrelude pass) mempty
  let runEnv m = evalStateT m env
  case evalMode of
    ReplMode ->
      runEnv $ runInputT defaultSettings $ forever (replLoop pass)
    ScriptMode fname fmt _ -> do
      results <- runEnv $ evalFile pass fname
      putStr $ printLitProg fmt results
#if CODDLE_WEB
    WebMode fname -> runWeb fname pass env
#else
    WebMode _ -> error "Compiled without the web interface"
#endif

evalDecl :: Monoid env => FullPass env -> SourceBlock -> StateT env IO Result
evalDecl pass block = do
  env <- get
  ~(Left ans, env') <- liftIO $ runTopPassM env (pass block)
  modify (<> env')
  return ans

evalFile :: Monoid env =>
              FullPass env-> String -> StateT env IO [(SourceBlock, Result)]
evalFile pass fname = do
  source <- liftIO $ readFile fname
  let sourceBlocks = parseProg source
  results <- mapM (evalDecl pass) sourceBlocks
  return $ zip sourceBlocks results

evalPrelude :: Monoid env => FullPass env-> StateT env IO ()
evalPrelude pass = do
  result <- evalFile pass "prelude.cod"
  void $ liftErrIO $ mapM snd result

replLoop :: Monoid env => FullPass env-> InputT (StateT env IO) ()
replLoop pass = do
  sourceBlock <- readMultiline ">=> " parseTopDeclRepl
  result <- lift $ evalDecl pass sourceBlock
  liftIO $ putStrLn $ printResult sourceBlock result

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

parseOpts :: ParserInfo CmdOpts
parseOpts = simpleInfo $ CmdOpts <$> parseMode <*> parseBackend

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

parseBackend :: Parser Backend
parseBackend = flag Jit Interp (long "interp" <> help "Use interpreter backend")

main :: IO ()
main = do
  CmdOpts evalMode backend <- execParser parseOpts
  case backend of
    Jit    -> case fullPassJit    of TopPass f -> runMode evalMode f
    Interp -> case fullPassInterp of TopPass f -> runMode evalMode f
