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
import Util

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

type FullPass env = SourceBlock -> TopPassM env Void
data EvalMode = ReplMode | WebMode String | ScriptMode String
data CmdOpts = CmdOpts { programSource :: Maybe String
                       , webOutput     :: Bool
                       , useInterpreter :: Bool}

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

evalScript :: Monoid env => FullPass env-> String -> StateT env IO ()
evalScript pass fname = do
  evalPrelude pass
  results <- evalFile pass fname
  liftIO $ putStr $ concat $ map (uncurry printLiterate) results

evalRepl :: Monoid env => FullPass env-> StateT env IO ()
evalRepl pass = do
  evalPrelude pass
  runInputT defaultSettings $ forever (replLoop pass)

replLoop :: Monoid env => FullPass env-> InputT (StateT env IO) ()
replLoop pass = do
  sourceBlock <- readMultiline ">=> " parseTopDeclRepl
  result <- lift $ evalDecl pass sourceBlock
  liftIO $ putStrLn $ printResult sourceBlock result

evalWeb :: Monoid env => FullPass env -> String -> IO ()
evalWeb pass fname = do
#if CODDLE_WEB
  env <- execStateT (evalPrelude pass) mempty
  runWeb fname pass env
#else
  _ <- error "Compiled without the web interface"
  undefined pass fname -- Silence the "Defined but not used" warning
#endif

printResult :: SourceBlock -> Result -> String
printResult block result = case result of
  Left err  -> pprint (addErrSource (sbOffset block) (sbText block) err)
  Right out -> pprint out

printLiterate :: SourceBlock -> Result -> String
printLiterate block result =
  sbText block ++ formatResult (printResult block result)
  where
    formatResult :: String -> String
    formatResult = unlines . map addPrefix . lines

    addPrefix :: String -> String
    addPrefix s = case s of "" -> ">"
                            _ -> "> " ++ s

addErrSource :: Int -> String -> Err -> Err
addErrSource n s (Err e p s') = case p of
    Nothing -> Err e p s'
    Just (start, stop) -> Err e p $ s' ++ "\n\n"
                           ++ highlightRegion (start - n, stop - n) s

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

parseOpts :: ParserInfo CmdOpts
parseOpts = info (p <**> helper) mempty
  where p = CmdOpts
            <$> (optional $ argument str (    metavar "FILE"
                                           <> help "Source program"))
            <*> switch (    long "web"
                         <> help "Use web output instead of stdout" )
            <*> switch (    long "interp"
                         <> help "Use interpreter")

runMode :: Monoid env => EvalMode -> FullPass env -> IO ()
runMode evalMode pass = case evalMode of
  ReplMode         -> runEnv $ evalRepl   pass
  ScriptMode fname -> runEnv $ evalScript pass fname
  WebMode    fname -> evalWeb pass fname
  where runEnv m = evalStateT m mempty

main :: IO ()
main = do
  opts <- execParser parseOpts
  let evalMode = case programSource opts of
                   Nothing -> ReplMode
                   Just fname -> if webOutput opts then WebMode    fname
                                                   else ScriptMode fname
  if useInterpreter opts
    then case fullPassInterp of
           TopPass f -> runMode evalMode f
    else  case fullPassJit of
           TopPass f -> runMode evalMode f
