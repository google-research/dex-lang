import Actor
import Control.Monad
import Control.Monad.State
import System.IO
import qualified Data.Map.Strict as M

type Key = String
type Val = String
type StoreID = Int
type ServerMsg = Either Val ClientToServer
type Server a = Actor ServerMsg a

data ClientToServer = Write Key Val | Read Key

inputDriver :: Proc ServerMsg -> Actor () ()
inputDriver server = do
  command <- liftIO $ getLine
  case words command of
    ["write", s1, s2] -> server `send` (Right (Write s1 s2))
    ["read" , s     ] -> server `send` (Right (Read  s))
    _ -> liftIO $ putStrLn "didn't understand command"
  loop
  where loop = inputDriver server

outputDriver :: Actor String ()
outputDriver = do
  receive $ \msg ->
    liftIO $ putStrLn msg
  outputDriver

serverProc :: Server ()
serverProc = do
  self <- getSelf
  input  <- spawn NoTrap (inputDriver self)
  client <- spawn NoTrap outputDriver
  mainServerLoop client mempty

storeProc :: Proc ServerMsg -> Val -> Actor () ()
storeProc server val = receive $ \_ -> do
  if length val > 5 then error "oops!"
                    else server `send` (Left val) >> loop
  where loop = storeProc server val

mainServerLoop :: Proc String -> M.Map Key (Proc ()) -> Server ()
mainServerLoop client stores = receiveAny handleMsg handleErr
  where
    handleMsg msg = case msg of
      Left val -> send client val >> loop
      Right req -> case req of
        Write key val -> do
          self <- getSelf
          store <- spawnLink NoTrap (storeProc self val)
          loopWith $ M.insert key store stores
        Read key -> do
          do case (M.lookup key stores) of
               Nothing -> sorry key
               Just store -> store `send` ()
             loop
    handleErr err = do client `send` ("Store " ++ show err ++ " down")
                       loop
    loop     = mainServerLoop client stores
    loopWith = mainServerLoop client
    sorry key = client `send` ("Store " ++ key ++ " doesn't exist")


main :: IO ()
main = runMainActor Trap serverProc
