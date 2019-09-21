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
#ifdef CODDLE_WEB
import WebOutput
#endif
import Normalize
import Interpreter

type ResultChan = Result -> IO ()
type FullPass env = UTopDecl -> TopPassM env ()
data EvalMode = ReplMode | WebMode String | ScriptMode String
data CmdOpts = CmdOpts { programSource :: Maybe String
                       , webOutput     :: Bool
                       , useInterpreter :: Bool}

fullPass :: TopPass UTopDecl ()
fullPass = deShadowPass
       >+> typePass      >+> checkTyped
       >+> normalizePass >+> checkNExpr
       >+> simpPass      >+> checkNExpr
       -- >+> stripAnnotPass >+> checkNExpr
       >+> impPass       >+> checkImp
       >+> flopsPass
       >+> jitPass

fullPassInterp :: TopPass UTopDecl ()
fullPassInterp = deShadowPass >+> typePass >+> checkTyped >+> interpPass

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
  (s, decl) <- readDecl "" ">=> "
  lift $ evalDecl s (printIt "") (pass decl)

readDecl :: String -> String -> InputT (StateT env IO) (String, UTopDecl)
readDecl prevRead prompt = do
  source <- getInputLine prompt
  case source of
    Nothing -> liftIO exitSuccess
    Just s -> case parseTopDeclRepl s' of
                Left e -> do printIt "" e
                             readDecl "" ">=> "
                Right (Just decl') -> return (s', decl')
                Right Nothing -> readDecl s' dots
      where s' = prevRead ++ s ++ "\n"
            dots = replicate (length prompt - 1) '.' ++ " "

evalWeb :: Monoid env => FullPass env -> String -> IO ()
evalWeb pass fname = do
#if CODDLE_WEB
  env <- execStateT (evalPrelude pass) mempty
  runWeb fname pass env
#else
  _ <- error "Compiled without the web interface"
  undefined pass fname -- Silence the "Defined but not used" warning
#endif

evalDecl :: Monoid env =>
              String -> ResultChan -> TopPassM env () -> StateT env IO ()
evalDecl source write pass = do
  env <- get
  (ans, env') <- liftIO $ runTopPassM (write . resultText, source) env pass
  modify $ (<> env')
  liftIO $ write $ case ans of Left e   -> resultErr e
                               Right () -> resultComplete

printIt :: (Pretty a, MonadIO m) => String -> a -> m ()
printIt prefix x = liftIO $ putStrLn $ unlines
                      [trim (prefix ++ s) | s <- lines (pprint x)]
  where
    trim :: String -> String
    trim s = reverse $ dropWhile (== ' ') $ reverse s

runEnv :: (Monoid s, Monad m) => StateT s m a -> m a
runEnv m = evalStateT m mempty

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
    else  case fullPass of
           TopPass f -> runMode evalMode f
