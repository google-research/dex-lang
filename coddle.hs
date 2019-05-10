import System.Console.Haskeline
import System.IO
import System.Exit
import Control.Monad
import Control.Monad.State.Strict
import Control.Monad.Except (liftEither)
import Options.Applicative
import Data.Semigroup ((<>))
import Data.Text.Prettyprint.Doc

import Syntax
import PPrint
import Pass
import Type

import Parser
import Inference
import DeFunc
import Imp
import JIT
import WebOutput

type DeclKey = Int
type ResultChan = Result -> IO ()
type FullPass env = UDecl -> TopPass env ()
data EvalMode = ReplMode | WebMode String | ScriptMode String
data CmdOpts = CmdOpts { programSource :: Maybe String
                       , webOutput     :: Bool}

fullPass = typePass   >+> checkTyped
       >+> deFuncPass >+> checkTyped
       >+> impPass    >+> checkImp
       >+> jitPass

parseFile :: MonadIO m => String -> m [(String, Except UDecl)]
parseFile fname = do
  source <- liftIO $ readFile fname
  return $ parseProg source

evalPrelude :: Monoid env => FullPass env-> StateT env IO ()
evalPrelude pass = do
  prog <- parseFile "prelude.cod"
  mapM_ (evalDecl devnull . pass . ignoreExcept . snd) prog
  where devnull :: ResultChan
        devnull _ = return ()

evalScript :: Monoid env => FullPass env-> String -> StateT env IO ()
evalScript pass fname = do
  evalPrelude pass
  prog <- parseFile fname
  mapM_ evalPrint prog
  where
    evalPrint (text, decl) = do
      printIt "" (resultSource text)
      case decl of
        Left e -> printIt "> " e
        Right decl' -> evalDecl (printIt "> ") (pass decl')

evalRepl :: Monoid env => FullPass env-> StateT env IO ()
evalRepl pass = do
  evalPrelude pass
  runInputT defaultSettings $ forever (replLoop pass)

replLoop :: Monoid env => FullPass env-> InputT (StateT env IO) ()
replLoop pass = do
  source <- getInputLine ">=> "
  case source of
    Nothing -> liftIO exitSuccess
    Just s -> case (parseTopDecl s) of
                Left e -> printIt "" e
                Right decl' -> lift $ evalDecl (printIt "") (pass decl')

evalWeb :: String -> IO ()
evalWeb fname = do
  env <- execStateT (evalPrelude fullPass) mempty
  runWeb fname fullPass env

evalDecl :: Monoid env => ResultChan -> TopPass env () -> StateT env IO ()
evalDecl writeOut pass = do
  env <- get
  (ans, env') <- liftIO $ runTopPass (writeOut . resultText) env pass
  modify $ (<> env')
  liftIO $ writeOut $ case ans of Left e   -> resultErr e
                                  Right () -> resultComplete

printIt :: (Pretty a, MonadIO m) => String -> a -> m ()
printIt prefix x = liftIO $ putStrLn $ unlines
                      [prefix ++ s | s <- lines (pprint x)]

runEnv :: (Monoid s, Monad m) => StateT s m a -> m a
runEnv m = evalStateT m mempty

opts :: ParserInfo CmdOpts
opts = info (p <**> helper) mempty
  where p = CmdOpts
            <$> (optional $ argument str (    metavar "FILE"
                                           <> help "Source program"))
            <*> switch (    long "web"
                         <> help "Whether to use web output instead of stdout" )

parseOpts :: IO EvalMode
parseOpts = do
  CmdOpts file web <- execParser opts
  return $ case file of
    Nothing -> ReplMode
    Just fname -> if web then WebMode    fname
                         else ScriptMode fname

main :: IO ()
main = do
  evalMode <- parseOpts
  case evalMode of
    ReplMode         -> runEnv $ evalRepl   fullPass
    ScriptMode fname -> runEnv $ evalScript fullPass fname
    WebMode    fname -> evalWeb fname
