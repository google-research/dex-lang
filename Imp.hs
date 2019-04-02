module Imp (impPass, Locs (..), TypedLocs, Size, ImpEnv,
            Statement (..), ImpProgram (..)) where

import Control.Monad.Reader
import Control.Monad.State

import Syntax
import Env
import Record
import Util
import Type

data ImpProgram = ImpProgram [Statement] [Var] deriving (Show)

data Statement = Alloc Var BaseType [Size] -- most-significant last
               | Assignment [Loc] Builtin [Opnd]
               | Move Loc Opnd
               | Loop Index Size [Statement]  deriving (Show)

type Loc = (Var, [Index]) -- most-significant last
data Opnd = ReadOpnd Loc | ImpLit LitVal  deriving (Show)
data Size = FixedSize Opnd | UnknownSize  deriving (Show)
type Index = Var

type ImpM a = ReaderT ImpEnv (StateT ImpState (Either Err)) a
type ImpEnv = FullEnv TypedLocs Size
data ImpState = ImpState { freshState :: Int, blocks :: [[Statement]] }

type Locs = RecTree Loc

type TypedLocs = (Locs, Type)

impPass :: Pass Expr ImpProgram TypedLocs Size
impPass = Pass
  { lowerExpr   = \expr env   -> liftErrIO $ impExprTop env expr
  , lowerUnpack = \v expr env -> liftErrIO $ impUnpack v expr env
  , lowerCmd    = \cmd  env   -> return $ impCmd cmd env }

impCmd :: Command Expr -> ImpEnv -> Command ImpProgram
impCmd (Command cmdName expr) env = case impExprTop env expr of
  Left e -> CmdErr e
  Right (_, prog) -> case cmdName of
                        Imp -> CmdResult $ TextOut $ show prog
                        _ -> Command cmdName prog
impCmd (CmdResult s) _ = CmdResult s
impCmd (CmdErr e)    _ = CmdErr e

impUnpack :: VarName -> Expr -> ImpEnv -> Except (TypedLocs, Size, ImpProgram)
impUnpack _ expr env = do (locs, prog) <- impExprTop env expr
                          return (locs, undefined, prog)

impExprTop :: ImpEnv -> Expr -> Except (TypedLocs, ImpProgram)
impExprTop env expr = do ((val, ty), ImpState _ [statements]) <- evalImp (toImpType expr)
                         return ((val, ty), ImpProgram statements [])  -- TODO: add output vars
  where tempStart = startFresh env
        evalImp m = runStateT (runReaderT m env) (ImpState tempStart [[]])

toImp :: Locs -> Expr -> ImpM ()
toImp dests expr = case expr of
  Lit x -> do let RecLeaf dest = dests
              add $ Move dest (ImpLit x)
  Var v -> do sources <- asks $ fst . (! v) . lEnv
              move sources dests
  BuiltinApp b ts args -> do args' <- toImpNoDest args
                             toImpBuiltin b dests ts args'
  Let p bound body -> do x <- toImpNoDest bound
                         let update = setLEnv $ addLocals (bindPat p x)
                         local update (toImp dests body)
  For b body -> toImpFor dests b body
  Get e ie -> do x <- toImpNoDest e
                 (RecLeaf (i, [])) <- asks $ fst . (! ie) . lEnv
                 move (lookupIdx i x) dests
  RecCon r -> do let RecTree r' = dests
                 void $ sequence $ recZipWith toImp r' r
  -- Unpack ty bound body -> do
  --   ExPackage i x <- compile bound
  --   isets <- asks (bVars . tEnv)
  --   let updateEnv = setLEnv (addBVar (x, JitType isets ty)) . setTEnv (addBVar i)
  --   local updateEnv (compile body)

toImpType :: Expr -> ImpM (Locs, Type)
toImpType (Var v) = asks $ (! v) . lEnv
toImpType expr = do ty <- exprType expr
                    dest <- alloc [] ty
                    toImp dest expr
                    return (dest, ty)

toImpNoDest :: Expr -> ImpM Locs
toImpNoDest expr = liftM fst (toImpType expr)

toImpBuiltin :: Builtin -> Locs -> [Type] -> Locs -> ImpM ()
toImpBuiltin b (RecLeaf dest) ts args = do
  let args' = [ ReadOpnd x | RecLeaf x <- unpackConsTuple (numArgs b) args ]
  add $ Assignment [dest] b args'

toImpFor :: Locs -> Binder -> Expr -> ImpM ()
toImpFor dests (v, TypeVar n) body = do
  idx <- fresh
  let updateEnv = setLEnv $ addLocal (v, (RecLeaf (idx, []), TypeVar n))
      addBody = local updateEnv $  toImp (lookupIdx idx dests) body
  startBlock
  addBody
  block <- endBlock
  idxSet <- asks $ (! n) . tEnv
  add $ Loop idx idxSet block

lookupIdx :: Index -> Locs -> Locs
lookupIdx idx locs = fmap lookup locs
  where lookup (v, idxs) = (v, idx:idxs)

move :: Locs -> Locs -> ImpM ()
move source dest = void $ traverse moveLeaf $ recTreeZip source dest
  where moveLeaf (s, RecLeaf d) = add $ Move d (ReadOpnd s)

startBlock :: ImpM ()
startBlock = modify $ setBlocks ([]:)

endBlock :: ImpM [Statement]
endBlock = do cur:rest <- gets blocks
              modify $ setBlocks (const rest)
              return cur

fresh :: ImpM Var
fresh = do i <- gets freshState
           modify $ \s -> s { freshState = i + 1}
           return (TempVar i)

alloc :: [Size] -> Type -> ImpM Locs
alloc sizes ty = case ty of
  BaseType b -> do v <- fresh
                   add $ Alloc v b sizes
                   return $ RecLeaf (v, [])
  TabType (TypeVar n) valTy -> do size <- asks $ (! n) . tEnv
                                  alloc (size:sizes) valTy
  RecType r -> liftM RecTree $ traverse (alloc sizes) r
  Exists t -> error "Can't do existentials yet"

add :: Statement -> ImpM ()
add s = do curBlock <- gets (head . blocks)
           modify $ setBlocks ((s:curBlock):)


bindPat :: Pat -> Locs -> RecTree (Var, TypedLocs)
bindPat pat locs = fmap bindLeaf $ recTreeZip pat locs
  where bindLeaf ((v, ty), x) = (v, (x, ty))

exprType :: Expr -> ImpM Type
exprType expr = do lenv <- asks lEnv
                   return $ getType (FullEnv (fmap snd lenv) mempty) expr

unpackConsTuple :: Int -> Locs -> [Locs]
unpackConsTuple n v = reverse $ recur n v
  where recur 0 _ = []
        recur n (RecTree (Tup [xs, x])) = x : recur (n-1) xs

setBlocks :: ([[Statement]] -> [[Statement]]) -> ImpState -> ImpState
setBlocks update state = state { blocks = update (blocks state) }

-- figure out the max tempvar in the environment.
-- should probably come up with a better scheme for unique variable names.
startFresh :: ImpEnv -> Int
startFresh = undefined
