module Imp (impPass,ImpEnv) where

import Control.Monad.Reader
import Control.Monad.State
import Data.Foldable (toList)

import Syntax
import Env
import Record
import Util
import Type
import PPrint

type ImpM a = ReaderT ImpEnv (StateT ImpState (Either Err)) a
type ImpEnv = FullEnv Type ()
data ImpState = ImpState { freshState :: Int, blocks :: [[Statement]] }

-- TODO: iExprType :: IExpr -> ImpM IType

impPass :: Pass Expr ImpProgram Type ()
impPass = Pass
  { lowerExpr   = \expr env   -> liftErrIO $ impExprTop env expr
  , lowerUnpack = \v expr env -> liftErrIO $ impUnpack v expr env
  , lowerCmd    = \cmd  env   -> return $ impCmd cmd env }

impCmd :: Command Expr -> ImpEnv -> Command ImpProgram
impCmd (Command cmdName expr) env = case impExprTop env expr of
  Left e -> CmdErr e
  Right (_, prog) -> case cmdName of
                        Imp -> CmdResult $ TextOut $ pprint prog
                        _ -> Command cmdName prog
impCmd (CmdResult s) _ = CmdResult s
impCmd (CmdErr e)    _ = CmdErr e

impUnpack :: VarName -> Expr -> ImpEnv -> Except (Type, (), ImpProgram)
impUnpack _ expr env = do (locs, prog) <- impExprTop env expr
                          return (locs, undefined, prog)

-- TODO: write a consistency checker for ImpPrograms
impExprTop :: ImpEnv -> Expr -> Except (Type, ImpProgram)
impExprTop env expr = do
  (iexpr, ImpState _ [statements]) <- evalImpM (toImp expr)
  return (getType env expr, ImpProgram (reverse statements) (toList iexpr))
  where evalImpM m = runStateT (runReaderT m env) (ImpState 0 [[]])

toImp :: Expr -> ImpM (RecTree IExpr)
toImp expr = case expr of
  Lit x -> return $ RecLeaf (ILit x)
  Var v -> do ty <- exprType expr
              return $ fmap (IVar . ILetVar v . fst) (flatType ty)
  BuiltinApp b ts args -> do
    args' <- toImp args
    case b of
      Iota -> impIota args'
      FoldDeFunc p body -> impFold ts p body args'
      _ -> return $ RecLeaf $ IBuiltinApp b (toList args')
  Let p bound body -> do -- TODO: beware of shadows
    env <- ask
    bound' <- toImp bound
    traverse (uncurry letBind) (recTreeZip p bound')
    ans <- local (setLEnv $ addLocals p) (toImp body)
    return ans
  Get x i -> do xs <- toImp x
                return $ fmap get xs
                where get x = IGet x (ILetVar i [])
  For i body -> toImpFor i body
  RecCon r -> liftM RecTree $ traverse toImp r
  Unpack b i bound body -> do
    RecTree (Tup [RecLeaf iset, x]) <- toImp bound
    -- TODO: bind x
    add $ ImpLet (IIdxSetVar i, IType IntType []) iset
    let updateEnv = setTEnv (addLocal (i, ())) . setLEnv (addLocal b)
    local updateEnv (toImp body)

-- TODO: make a destination-passing version to avoid unnecessary intermediates
toImpFor :: Binder -> Expr -> ImpM (RecTree IExpr)
toImpFor b@(i, TypeVar n) body = do
  bodyTy <- exprType body
  let cellTypes = fmap (addIdx n' . snd) (flatType bodyTy)
  cells <- traverse newCell cellTypes
  startBlock
  results <- local (setLEnv $ addLocal b) (toImp body)
  traverse (\(v,x) -> add $ Update v [i'] x) (recTreeZipEq cells results)
  block <- endBlock
  add $ Loop i' n' block
  return $ fmap IRead cells
  where i' = ILetVar i []
        n' = IIdxSetVar n

impIota :: RecTree IExpr -> ImpM (RecTree IExpr)
impIota args = do
  n' <- newVar n
  out <- newCell (IType IntType [n'])
  i <- freshVar
  add $ Loop i n' [Update out [i] (IVar i)]
  return $ RecTree $ Tup [RecLeaf (IVar n'), RecLeaf (IRead out)]
  where [RecLeaf n] = unpackConsTuple 1 args

impFold :: [Type] -> Pat -> Expr -> RecTree IExpr -> ImpM (RecTree IExpr)
impFold ts p body args = do
  i <- freshVar
  accumCells <- traverse (newCell . snd) (flatType accumTy)
  xs' <- traverse newVar xs
  letBind envBinder env
  block <- do
    startBlock
    letBind accumBinder $ fmap IRead accumCells
    letBind xBinder $ fmap (\x -> IGet (IVar x) i) xs'
    newVals <- local (setLEnv $ addLocals p) (toImp body)
    traverse (uncurry writeCell) $ recTreeZipEq accumCells newVals
    endBlock
  add $ Loop i n' block
  return $ fmap IRead accumCells
  where RecTree (Tup (binders)) = p
        [envBinder, accumBinder@(_, accumTy), xBinder] = map unLeaf binders
        [env, init, xs] = unpackConsTuple 3 args
        [_, _, TypeVar n] = ts
        n' = IIdxSetVar n

impExprType :: IExpr -> ImpM IType
impExprType _ = return $ IType IntType [] -- TODO!

letBind :: Binder -> RecTree IExpr -> ImpM ()
letBind binder@(v,ty) exprs = void $ traverse (add . uncurry ImpLet) $ zipped
  where zipped = recTreeZipEq (flatBinding binder) exprs

newVar :: IExpr -> ImpM IVar
newVar expr = do t <- impExprType expr
                 v <- freshVar
                 add $ ImpLet (v, t) expr
                 return v

writeCell :: CellVar -> IExpr -> ImpM ()
writeCell v val = add $ Update v [] val

newCell :: IType -> ImpM CellVar
newCell ty = do v <- freshCellVar
                add $ Alloc v ty
                return v

flatBinding :: (Var, Type) -> RecTree (IVar, IType)
flatBinding (v, ty) = fmap (\(idx, ty) -> (ILetVar v idx, ty)) (flatType ty)

addIdx :: Size -> IType -> IType
addIdx = undefined

flatType :: Type -> RecTree (RecTreeIdx, IType)
flatType ty = case ty of
  BaseType b -> RecLeaf ([], IType b [])
  RecType r -> RecTree $ fmap flatType r -- TODO: get indices from record
  TabType (TypeVar n) valTy -> fmap f (flatType valTy)
    where f (idx, IType b shape) = (idx, IType b (IIdxSetVar n : shape))


exprType :: Expr -> ImpM Type
exprType expr = do env <- ask
                   return $ getType env expr

startBlock :: ImpM ()
startBlock = modify $ setBlocks ([]:)

endBlock :: ImpM [Statement]
endBlock = do cur:rest <- gets blocks
              modify $ setBlocks (const rest)
              return cur

freshCellVar :: ImpM CellVar
freshCellVar = do i <- gets freshState
                  modify $ setFresh (+ 1)
                  return (CellVar i)

freshVar :: ImpM IVar
freshVar = do i <- gets freshState
              modify $ setFresh (+ 1)
              return (IFresh i)

add :: Statement -> ImpM ()
add s = do curBlock:rest <- gets blocks
           modify $ setBlocks (const $ (s:curBlock):rest)

unpackConsTuple :: Show a => Int -> RecTree a -> [RecTree a]
unpackConsTuple n v = reverse $ recur n v
  where recur 0 (RecTree (Tup [])) = []
        recur n (RecTree (Tup [xs, x])) = x : recur (n-1) xs
        recur _ _ = error $ show v ++ "  " ++ show n

setBlocks update state = state { blocks = update (blocks state) }
setFresh  update state = state { freshState = update (freshState state) }
