module Imp (impPass,ImpEnv) where

import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Except (throwError)
import Data.Foldable (toList)
import qualified Data.Map.Strict as M

import Syntax
import Env
import Record
import Util
import Type
import PPrint
import Pass
import Fresh

type ImpM a = MonadPass ImpEnv ImpState a
type ImpEnv = FullEnv Type ()
data ImpState = ImpState { blocks :: [[Statement]]
                         , impEnv :: M.Map Var VarType }
type IsMutable = Bool
type VarType = (IsMutable, IType)

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

initState :: ImpState
initState = ImpState [[]] mempty

checkImpProg :: ImpProgram -> Except ()
checkImpProg prog = case evalPass (void $ impProgType prog) mempty initState of
                      Left (CompilerErr e) -> Left $ CompilerErr $
                                                "\n" ++ pprint prog ++ "\n" ++ e
                      Right ans -> Right ans

impExprTop :: ImpEnv -> Expr -> Except (Type, ImpProgram)
impExprTop env expr = do
  (iexpr, ImpState [statements] _ ) <- runPass (toImp expr) env initState
  let prog = ImpProgram (reverse statements) (toList iexpr)
  checkImpProg prog
  return (getType env expr, prog)

toImp :: Expr -> ImpM (RecTree IExpr)
toImp expr = case expr of
  Lit x -> return $ RecLeaf (ILit x)
  Var v -> do ty <- exprType expr
              return $ fmap (IVar . const v) (flatType ty)  -- TODO: add fields to name
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
                where get x = IGet x i
  For i body -> toImpFor i body
  RecCon r -> liftM RecTree $ traverse toImp r
  Unpack b i bound body -> do
    RecTree (Tup [RecLeaf iset, x]) <- toImp bound
    addLet (i, IType IntType []) iset
    letBind b x
    let updateEnv = setTEnv (addLocal (i, ())) . setLEnv (addLocal b)
    local updateEnv (toImp body)

-- TODO: make a destination-passing version to avoid unnecessary intermediates
toImpFor :: Binder -> Expr -> ImpM (RecTree IExpr)
toImpFor b@(i, TypeVar n) body = do
  bodyTy <- exprType body
  let cellTypes = fmap (addIdx n . snd) (flatType bodyTy)
  cells <- traverse newCell cellTypes
  startBlock
  results <- local (setLEnv $ addLocal b) (toImp body)
  traverse (\(v,x) -> add $ Update v [i] x) (recTreeZipEq cells results)
  block <- endBlock
  add $ Loop i n block
  return $ fmap IVar cells

impIota :: RecTree IExpr -> ImpM (RecTree IExpr)
impIota args = do
  n' <- newVar n
  out <- newCell (IType IntType [n'])
  i <- fresh
  add $ Loop i n' [Update out [i] (IVar i)]
  return $ RecTree $ Tup [RecLeaf (IVar n'), RecLeaf (IVar out)]
  where [RecLeaf n] = unpackConsTuple 1 args

impFold :: [Type] -> Pat -> Expr -> RecTree IExpr -> ImpM (RecTree IExpr)
impFold ts p body args = do
  i <- fresh
  accumCells <- traverse (newCell . snd) (flatType accumTy)
  xs' <- traverse newVar xs
  letBind envBinder env
  block <- do
    startBlock
    letBind accumBinder $ fmap IVar accumCells
    letBind xBinder $ fmap (\x -> IGet (IVar x) i) xs'
    newVals <- local (setLEnv $ addLocals p) (toImp body)
    traverse (uncurry writeCell) $ recTreeZipEq accumCells newVals
    endBlock
  add $ Loop i n block
  return $ fmap IVar accumCells
  where RecTree (Tup (binders)) = p
        [envBinder, accumBinder@(_, accumTy), xBinder] = map unLeaf binders
        [env, init, xs] = unpackConsTuple 3 args
        [_, _, TypeVar n] = ts

letBind :: Binder -> RecTree IExpr -> ImpM ()
letBind binder@(v,ty) exprs = void $ traverse (uncurry addLet) $ zipped
  where zipped = recTreeZipEq (flatBinding binder) exprs

newVar :: IExpr -> ImpM Var
newVar expr = do t <- impExprType expr
                 v <- fresh
                 addLet (v, t) expr
                 return v

addLet :: (Var, IType) -> IExpr -> ImpM ()
addLet (v, ty) expr = do modify $ setEnv $ M.insert v (False, ty)
                         add $ ImpLet (v, ty) expr

writeCell :: Var -> IExpr -> ImpM ()
writeCell v val = add $ Update v [] val

newCell :: IType -> ImpM Var
newCell ty = do v <- fresh
                add $ Alloc v ty
                return v

flatBinding :: (Var, Type) -> RecTree (Var, IType)
flatBinding (v, ty) = undefined -- fmap (\(idx, ty) -> (ILetVar v idx, ty)) (flatType ty)

addIdx :: Size -> IType -> IType
addIdx = undefined

flatType :: Type -> RecTree (RecTreeIdx, IType)
flatType ty = case ty of
  BaseType b -> RecLeaf ([], IType b [])
  RecType r -> RecTree $ fmap flatType r -- TODO: get indices from record
  TabType (TypeVar n) valTy -> fmap f (flatType valTy)
    where f (idx, IType b shape) = (idx, IType b (n : shape))


exprType :: Expr -> ImpM Type
exprType expr = do env <- ask
                   return $ getType env expr

startBlock :: ImpM ()
startBlock = modify $ setBlocks ([]:)

endBlock :: ImpM [Statement]
endBlock = do cur:rest <- gets blocks
              modify $ setBlocks (const rest)
              return (reverse cur)

add :: Statement -> ImpM ()
add s = do curBlock:rest <- gets blocks
           modify $ setBlocks (const $ (s:curBlock):rest)

unpackConsTuple :: Show a => Int -> RecTree a -> [RecTree a]
unpackConsTuple n v = reverse $ recur n v
  where recur 0 (RecTree (Tup [])) = []
        recur n (RecTree (Tup [xs, x])) = x : recur (n-1) xs
        recur _ _ = error $ show v ++ "  " ++ show n

setBlocks update state = state { blocks = update (blocks state) }
setEnv    update state = state { impEnv = update (impEnv state) }

-- === type checking imp programs ===

impExprType :: IExpr -> ImpM IType
impExprType expr = case expr of
  ILit val -> return $ IType (litType val) []
  IVar  v -> liftM snd (lookupVar v)
  IGet e i -> do IType b (_:shape) <- impExprType e
                 checkIsInt i
                 return $ IType b shape
  IBuiltinApp b args -> do -- scalar builtins only
    argTys <- mapM impExprType args
    let (argTyNeeded, outTy) = builtinNaryTy b
    zipWithM checkScalarTy argTyNeeded argTys
    case outTy of
      BaseType b -> return $ IType b []

  where checkScalarTy :: Type -> IType -> ImpM ()
        checkScalarTy (BaseType b) (IType b' []) | b == b'= return ()
        checkScalarTy ty ity = throw $ "Wrong types. Expected:" ++ show ty
                                                     ++ " Got " ++ show ity

impProgType :: ImpProgram -> ImpM [IType]
impProgType (ImpProgram statements exprs) = do
  mapM checkStatementTy statements
  mapM impExprType exprs

lookupVar :: Var -> ImpM VarType
lookupVar v = do x <- gets $ M.lookup v . impEnv
                 case x of Nothing -> throw $ "Unbound variable" ++ pprint v
                           Just x' -> return x'

checkStatementTy :: Statement -> ImpM ()
checkStatementTy statement = case statement of
  Update v idxs expr -> do (mut, IType b  shape ) <- lookupVar v
                           IType b' shape' <- impExprType expr
                           throwIf (not mut) $ err "Updating immutable variable"
                           throwIf (b /= b') $ err "Base type mismatch"
                           throwIf (drop (length idxs) shape /= shape') $
                                    err "Dimension mismatch"
  ImpLet b@(v,ty) expr -> do ty' <- impExprType expr
                             -- doesn't work without alias checking for sizes
                             -- throwIf (ty' /= ty) $ err "Type doesn't match binder"
                             modify $ setEnv $ M.insert v (False, ty)
  Loop i size block -> do modify $ setEnv $ M.insert i (False, IType IntType [])
                          checkIsInt size
                          void $ mapM checkStatementTy block
  Alloc v ty@(IType b shape) -> do void $ mapM checkIsInt shape
                                   modify $ setEnv $ M.insert v (True, ty)
  where err s = s ++ " " ++ pprint statement

-- TODO: add Except to ImpM for more helpful error reporting
checkIsInt :: Var -> ImpM ()
checkIsInt v = do (_, ty) <- lookupVar v
                  throwIf (ty /= IType IntType []) $ "Not a valid size" ++ pprint ty

throw :: String -> ImpM a
throw s = throwError (CompilerErr s)

throwIf :: Bool -> String -> ImpM ()
throwIf True = throw
throwIf False = const (return ())
