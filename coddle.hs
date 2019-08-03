import System.Console.Haskeline
import System.Exit
import Control.Monad
import Control.Monad.State.Strict
import Options.Applicative
import Data.Semigroup ((<>))
import Data.Text.Prettyprint.Doc

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
import WebOutput
import Normalize

type ResultChan = Result -> IO ()
type FullPass env = UTopDecl -> TopPass env ()
data EvalMode = ReplMode | WebMode String | ScriptMode String
data CmdOpts = CmdOpts { programSource :: Maybe String
                       , webOutput     :: Bool}

fullPass = deShadowPass
       >+> typePass      >+> checkTyped
       >+> normalizePass >+> checkNExpr
       >+> simpPass      >+> checkNExpr
       -- >+> stripAnnotPass >+> checkNExpr
       >+> impPass       >+> checkImp
       >+> flopsPass
       >+> jitPass

parseFile :: MonadIO m => String -> m (String, [(String, UTopDecl)])
parseFile fname = liftIO $ do
  source <- readFile fname
  liftIO $ case parseProg source of
    Left e -> putStrLn (pprint e) >> exitFailure
    Right decls -> return (source, decls)

evalPrelude :: Monoid env => FullPass env-> StateT env IO ()
evalPrelude pass = do
  (source, prog) <- parseFile "prelude.cod"
  mapM_ (evalDecl source printErr . pass . snd) prog
  where
    printErr (Result _ status _ ) = case status of
      Set (Failed e) -> putStrLn $ pprint e
      _ -> return ()

evalScript :: Monoid env => FullPass env-> String -> StateT env IO ()
evalScript pass fname = do
  evalPrelude pass
  (source, prog) <- parseFile fname
  flip mapM_ prog $ \(declSource, decl) -> do
    printIt "" (resultSource declSource)
    evalDecl source (printIt "> ") (pass decl)

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
                Right decl' -> lift $ evalDecl s (printIt "") (pass decl')

evalWeb :: String -> IO ()
evalWeb fname = do
  env <- execStateT (evalPrelude fullPass) mempty
  runWeb fname fullPass env

evalDecl :: Monoid env =>
              String -> ResultChan -> TopPass env () -> StateT env IO ()
evalDecl source writeOut pass = do
  env <- get
  (ans, env') <- liftIO $ runTopPass (writeOut . resultText, source) env pass
  modify $ (<> env')
  liftIO $ writeOut $ case ans of Left e   -> resultErr e
                                  Right () -> resultComplete

printIt :: (Pretty a, MonadIO m) => String -> a -> m ()
printIt prefix x = liftIO $ putStrLn $ unlines
                      [trim (prefix ++ s) | s <- lines (pprint x)]
  where
    trim :: String -> String
    trim s = reverse $ dropWhile (== ' ') $ reverse s

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
  opts <- execParser opts
  return $ case programSource opts of
    Nothing -> ReplMode
    Just fname -> if webOutput opts then WebMode    fname
                                    else ScriptMode fname

main :: IO ()
main = do
  evalMode <- parseOpts
  case evalMode of
    ReplMode         -> runEnv $ evalRepl   fullPass
    ScriptMode fname -> runEnv $ evalScript fullPass fname
    WebMode    fname -> evalWeb fname
