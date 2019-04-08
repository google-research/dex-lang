module Imp (impPass, Size, ImpEnv, IVar, CellVar,
            Statement (..), ImpProgram (..), IExpr (..), IType (..)) where

import Control.Monad.Reader
import Control.Monad.State
import Data.Foldable (toList)

import Syntax
import Env
import Record
import Util
import Type

data ImpProgram = ImpProgram [Statement] [IExpr] deriving (Show)
data Statement = Update CellVar [Index] IExpr
               | ImpLet IVar IType IExpr
               | Loop Index Size [Statement]
               | Alloc CellVar IType -- mutable
                   deriving (Show)

data IExpr = ILit LitVal
           | IVar IVar
           | IRead CellVar  -- value semantics - no aliasing
           | IGet IExpr Index
           | IBuiltinApp Builtin [IExpr]
               deriving (Show)

data IType = IType BaseType [Size]  deriving (Show)

data IVar = ILetVar Var RecTreeIdx
          | IIdxSetVar Var  deriving (Show, Ord, Eq)

newtype CellVar = CellVar Int  deriving (Show, Ord, Eq)

type Size = IVar
type Index = IVar

type ImpM a = ReaderT ImpEnv (StateT ImpState (Either Err)) a
type ImpEnv = FullEnv Type Size
data ImpState = ImpState { freshState :: Int, blocks :: [[Statement]] }

impPass :: Pass Expr ImpProgram Type Size
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

impUnpack :: VarName -> Expr -> ImpEnv -> Except (Type, Size, ImpProgram)
impUnpack _ expr env = do (locs, prog) <- impExprTop env expr
                          return (locs, undefined, prog)

-- TODO: write a consistency checker for ImpPrograms
impExprTop :: ImpEnv -> Expr -> Except (Type, ImpProgram)
impExprTop env expr = do
  (iexpr, ImpState _ [statements]) <- evalImpM (toImp expr)
  return (getType env expr, ImpProgram (reverse statements) iexpr)
  where evalImpM m = runStateT (runReaderT m env) (ImpState 0 [[]])

toImp :: Expr -> ImpM [IExpr]
toImp expr = case expr of
  Lit x -> return $ [ILit x]
  Var v -> do ty <- exprType expr
              return $ map (IVar . ILetVar v) (recTreeIdxs ty)
  BuiltinApp b _ args -> do args' <- toImp args
                            return [IBuiltinApp b args']
  Let p bound body -> do -- TODO: beware of shadows
    bound' <- toImp bound
    ty <- exprType expr
    let (names, impTypes) = unzip $ flatPat (fmap fst p) ty
    traverse add $ zipWith3 ImpLet names impTypes bound'
    ans <- local (setLEnv $ addLocals p) (toImp body)
    return ans

  Get x i -> do xs <- toImp x
                return [IGet x (ILetVar i []) | x <- xs]
  For i body -> toImpFor i body
  RecCon r -> liftM concat $ traverse toImp r
  Unpack b i bound body -> do
    [IVar iset,  x] <- toImp bound
    let updateEnv = setTEnv (addLocal (i, iset)) . setLEnv (addLocal b)
    local updateEnv (toImp body)

-- TODO: make a destination-passing version to avoid unnecessary intermediates
toImpFor :: Binder -> Expr -> ImpM [IExpr]
toImpFor b@(i, TypeVar n) body = do
  idxSet <- asks $ (! n) . tEnv
  bodyTy <- exprType body
  let cellTypes = map (addIdx idxSet) (flatType bodyTy)
  cells <- mapM newCell cellTypes
  startBlock
  results <- local (setLEnv $ addLocal b) (toImp body)
  sequence [add $ Update v [i'] x | (v, x) <- zip cells results]
  block <- endBlock
  add $ Loop i' idxSet block
  return $ map IRead cells
  where i' = ILetVar i []

newCell :: IType -> ImpM CellVar
newCell ty = undefined -- do v <- fadd $ Alloc cell ty

recTreeIdxs :: Type -> [RecTreeIdx]
recTreeIdxs = undefined

flatPat :: RecTree Var -> Type -> [(IVar, IType)]
flatPat = undefined

addIdx :: Size -> IType -> IType
addIdx = undefined

flatType :: Type -> [IType]
flatType = undefined

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

add :: Statement -> ImpM ()
add s = do curBlock:rest <- gets blocks
           modify $ setBlocks (const $ (s:curBlock):rest)

setBlocks update state = state { blocks = update (blocks state) }
setFresh  update state = state { freshState = update (freshState state) }
