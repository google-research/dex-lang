import System.Console.Haskeline
import System.Exit
import System.IO
import Data.IORef
import Control.Concurrent
import Control.Concurrent.Chan
import Control.Monad
import Control.Monad.Except (throwError)
import Control.Monad.State.Strict
import Options.Applicative
import Data.Semigroup ((<>))
import Data.Maybe (catMaybes)
import Prelude hiding (lookup)

import Syntax
import Parser
import Type
import Util
import Env
import Imp
import JIT
import Inference
import DeFunc
import WebOutput

type TypedVal = ()  -- until we get the interpreter back up

type Driver a = InputT IO a
data CmdOpts = CmdOpts { programSource :: Maybe String
                       , dataSource    :: Maybe String
                       , webOutput     :: Bool}

data TopEnv = TopEnv { typeEnv   :: TypeEnv
                     , deFuncEnv :: DFEnv
                     , impEnv    :: ImpEnv
                     , valEnv    :: PersistEnv}

initEnv = TopEnv mempty mempty mempty mempty

evalSource :: TopEnv -> String -> Driver (TopEnv, [TopDecl ()])
evalSource env source = do
  decls <- lift $ liftErrIO $ parseProg source
  (typed  , typeEnv') <- fullPass (procDecl typePass)   (typeEnv   env) decls
  (defunc , dfEnv'  ) <- fullPass (procDecl deFuncPass) (deFuncEnv env) typed
  (imp    , impEnv' ) <- fullPass (procDecl impPass)    (impEnv    env) defunc
  (jitted , valEnv' ) <- fullPass (procDecl jitPass)    (valEnv    env) imp
  return (TopEnv typeEnv' dfEnv' impEnv' valEnv', jitted)
  where
    fullPass :: (IORef env -> TopDecl a -> Driver (TopDecl b))
                -> env -> [TopDecl a] -> Driver ([TopDecl b], env)
    fullPass p env decls = do envPtr <- lift $ newIORef env
                              decls' <- mapM (p envPtr) decls
                              env' <- lift $ readIORef envPtr
                              return (decls', env')

    procDecl :: Pass a b v t -> IORef (FullEnv v t)
                -> TopDecl a -> Driver (TopDecl b)
    procDecl pass envPtr (TopDecl source instr) = do
      env <- lift $ readIORef envPtr
      case instr of
        TopAssign v expr ->
          do (val, expr') <- lift $ (lowerExpr pass) expr env
             lift $ writeIORef envPtr $ setLEnv (addTop v val) env
             return $ TopDecl source $ TopAssign v expr'
        TopUnpack v expr ->
          do (val, ty, expr') <- lift $ (lowerUnpack pass) v expr env
             lift $ writeIORef envPtr $ setLEnv (addTop v val)
                                      . setTEnv (addTop v ty) $ env
             return $ TopDecl source $ TopUnpack v expr'
        EvalCmd cmd ->
          do cmd' <- lift $ (lowerCmd pass) cmd env
             return $ TopDecl source $ EvalCmd cmd'

evalWeb :: String -> IO ()
evalWeb fname = do
  triggerChan <- onMod fname
  dataReady <- newChan
  initOutput <- evalFile
  ref <- newIORef initOutput
  let evalLoop :: IO ()
      evalLoop = do readChan triggerChan
                    evalFile >>= writeIORef ref
                    writeChan dataReady ()
  forkIO (forever evalLoop)
  serveOutput dataReady ref

  where evalFile :: IO [TopDecl ()]
        evalFile = do
          source <- readFile fname
          (_, decls) <- runMonad $ evalSource initEnv source
          return decls

evalScript :: String -> Driver ()
evalScript fname = do
  source <- lift (readFile fname)
  (_, decls) <- evalSource initEnv source
  lift $ putStr $ concat (map showDeclResult decls)
  return ()

runRepl :: TopEnv -> Driver ()
runRepl initEnv = lift (newIORef initEnv) >>= forever . catchErr . loop
  where
    loop :: IORef TopEnv -> Driver ()
    loop envPtr = do
      source <- getInputLine ">=> "
      env <- lift $ readIORef envPtr
      (newEnv, decls) <- case source of
                  Nothing ->  lift exitSuccess
                  Just s -> evalSource env s
      lift $ putStr $ concat (map showDeclResult decls)
      lift $ writeIORef envPtr newEnv

showDeclResult :: TopDecl a -> String
showDeclResult (TopDecl source instr) = do
  case instr of
    EvalCmd (CmdResult r) -> withSource $ case r of TextOut s -> s
                                                    PlotOut _ _ -> "<plot>"
    EvalCmd (CmdErr e)    -> withSource (show e)
    _ -> ""
  where withSource s = source ++ "\n" ++ s ++ "\n\n"

catchErr :: Driver a -> Driver (Maybe a)
catchErr m = handleInterrupt (return Nothing) (fmap Just m)

opts :: ParserInfo CmdOpts
opts = info (p <**> helper) mempty
  where p = CmdOpts
            <$> (optional $ argument str (    metavar "FILE"
                                           <> help "Source program"))
            <*> (optional $ strOption (    long "data"
                                        <> metavar "DATA"
                                        <> help "Data source (optional)" ))
            <*> switch (    long "web"
                         <> help "Whether to use web output instead of stdout" )

runMonad :: Driver a -> IO a
runMonad d = runInputTBehavior defaultBehavior defaultSettings d

loadData :: String -> IO (TypedVal, Type)
loadData fname = do
  contents <- readFile fname
  undefined
  -- case parseVal contents of
  --   Left e -> do putStrLn "Error loading data"
  --                putStrLn (show e)
  --                exitFailure
  --   Right (t,v) -> return (TypedVal t v, t)

main :: IO ()
main = do
  CmdOpts fname dbname web <- execParser opts
  envWithData <- case dbname of
                   Just dbname -> undefined
                     -- do (inVal, inTy) <- loadData dbname
                     --    return $ ("data", inTy, inVal) `updateEnv` initEnv
                   Nothing -> return initEnv
  case fname of
    Just fname -> if web
      then evalWeb fname
      else runMonad $ evalScript fname

    Nothing    -> runMonad $ runRepl envWithData
