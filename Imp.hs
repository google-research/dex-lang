module Imp (impPass) where

import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer (tell)
import Control.Monad.Except (throwError)
import Data.Foldable (toList)

import Syntax
import Env
import Record
import Util
import Type
import PPrint
import Pass
import Fresh

type ImpM a = MonadPass PreEnv ImpState a
type ImpMTop a = TopMonadPass (ImpEnv,PreEnv) a

type ImpEnv = Env VarType
type PreEnv = FullEnv Type ()

data ImpState = ImpState { blocks :: [[Statement]]
                         , impEnv :: ImpEnv }
type IsMutable = Bool
type VarType = (IsMutable, IType)

impPass :: Decl -> ImpMTop ImpDecl
impPass decl = case decl of
  TopLet b expr -> do
    prog <- impExprTop expr
    let b' = toList (flatBinding b)
    put $ ( newEnv (map addImmutFlag b')
          , newFullEnv [b] [])
    return $ ImpTopLet b' prog
  TopUnpack b iv expr -> do
    prog <- impExprTop expr
    let b' = (iv, intTy) : toList (flatBinding b)
    put $ ( newEnv (map addImmutFlag b')
          , newFullEnv [b] [(iv,())])
    return $ ImpTopLet b' prog
  EvalCmd NoOp -> put mempty >> return (ImpEvalCmd unitTy NoOp)
  EvalCmd (Command cmd expr) -> do
    prog <- impExprTop expr
    env <- gets snd
    let ty = getType env expr
    put mempty
    case cmd of Passes -> tell ["\n\nImp\n" ++ pprint prog]
                _ -> return ()
    return $ ImpEvalCmd ty (Command cmd prog)

  where addImmutFlag (v,ty) = (v,(False,ty))

impExprTop :: Expr -> ImpMTop ImpProgram
impExprTop expr = do
  (env, preEnv) <- get
  (iexpr, state) <- liftExcept $ runPass preEnv (ImpState [[]] env) VarRoot (toImp expr)
  let ImpState [statements] _ = state
      prog = ImpProgram (reverse statements) (toList iexpr)
  liftExcept $ checkImpProg env prog
  return prog

checkImpProg :: ImpEnv -> ImpProgram -> Except ()
checkImpProg env prog =
  case evalPass mempty (ImpState [[]] env) (rawVar "!") (void $ impProgType prog) of
    Left (CompilerErr e) -> Left $ CompilerErr $
                              "\n" ++ pprint prog ++ "\n" ++ e
    Right ans -> Right ans

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
    bound' <- toImp bound
    traverse (uncurry letBind) (recTreeZip p bound')
    ans <- local (setLEnv $ addVs p) (toImp body)
    return ans
  Get x i -> do xs <- toImp x
                return $ fmap get xs
                where get x = IGet x i
  For i body -> toImpFor i body
  RecCon r -> liftM RecTree $ traverse toImp r
  Unpack b i bound body -> do
    RecTree (Tup [RecLeaf iset, x]) <- toImp bound
    addLet (i, intTy) iset
    letBind b x
    let updateEnv = setTEnv (addV (i, ())) . setLEnv (addV b)
    local updateEnv (toImp body)

-- TODO: make a destination-passing version to avoid unnecessary intermediates
toImpFor :: Binder -> Expr -> ImpM (RecTree IExpr)
toImpFor b@(i, TypeVar n) body = do
  bodyTy <- exprType body
  let cellTypes = fmap (addIdx n . snd) (flatType bodyTy)
  cells <- traverse newCell cellTypes
  modify $ setEnv $ addV (i, (False, intTy))
  startBlock
  results <- local (setLEnv $ addV b) (toImp body)
  traverse (\(v,x) -> add $ Update v [i] x) (recTreeZipEq cells results)
  block <- endBlock
  add $ Loop i n block
  return $ fmap IVar cells

impIota :: RecTree IExpr -> ImpM (RecTree IExpr)
impIota args = do
  n' <- newVar n
  out <- newCell (IType IntType [n'])
  i <- fresh "iIota"
  add $ Loop i n' [Update out [i] (IVar i)]
  return $ RecTree $ Tup [RecLeaf (IVar n'), RecLeaf (IVar out)]
  where [RecLeaf n] = unpackConsTuple 1 args

impFold :: [Type] -> Pat -> Expr -> RecTree IExpr -> ImpM (RecTree IExpr)
impFold ts p body args = do
  i <- fresh "iFold"
  accumCells <- traverse (newCell . snd) (flatType accumTy)
  xs' <- traverse newVar xs
  letBind envBinder env
  let writeCells val = traverse (uncurry writeCell) $ recTreeZipEq accumCells val
  writeCells init
  block <- do
    startBlock
    letBind accumBinder $ fmap IVar accumCells
    letBind xBinder $ fmap (\x -> IGet (IVar x) i) xs'
    newVals <- local (setLEnv $ addVs p) (toImp body)
    writeCells newVals
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
                 v <- fresh "var"
                 addLet (v, t) expr
                 return v

addLet :: (Var, IType) -> IExpr -> ImpM ()
addLet (v, ty) expr = do modify $ setEnv $ addV (v, (False, ty))
                         add $ ImpLet (v, ty) expr

writeCell :: Var -> IExpr -> ImpM ()
writeCell v val = add $ Update v [] val

newCell :: IType -> ImpM Var
newCell ty = do v <- fresh "cell"
                modify $ setEnv $ addV (v, (True, ty))
                add $ Alloc v ty
                return v

flatBinding :: (Var, Type) -> RecTree (Var, IType)
flatBinding (var, ty) = fmap (\(i,t) -> (qualify var i, t)) (flatType ty)

qualify :: Var -> [RecIdx] -> Var
qualify var idx = foldr (\i v -> Qual v (pprint i) 0) var idx

addIdx :: Size -> IType -> IType
addIdx size (IType ty shape) = (IType ty (size:shape))

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

unpackConsTuple :: Int -> RecTree a -> [RecTree a]
unpackConsTuple n v = reverse $ recur n v
  where recur 0 (RecTree (Tup [])) = []
        recur n (RecTree (Tup [xs, x])) = x : recur (n-1) xs

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
        checkScalarTy ty ity = throw $ "Wrong types. Expected:" ++ pprint ty
                                                     ++ " Got " ++ pprint ity

impProgType :: ImpProgram -> ImpM [IType]
impProgType (ImpProgram statements exprs) = do
  mapM checkStatementTy statements
  mapM impExprType exprs

lookupVar :: Var -> ImpM VarType
lookupVar v = gets $ (! v) . impEnv

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
                             modify $ setEnv $ addV (v, (False, ty))
  Loop i size block -> do modify $ setEnv $ addV (i, (False, intTy))
                          checkIsInt size
                          void $ mapM checkStatementTy block
  Alloc v ty@(IType b shape) -> do void $ mapM checkIsInt shape
                                   modify $ setEnv $ addV (v, (True, ty))
  where err s = s ++ " " ++ pprint statement

-- TODO: add Except to ImpM for more helpful error reporting
checkIsInt :: Var -> ImpM ()
checkIsInt v = do (_, ty) <- lookupVar v
                  throwIf (ty /= intTy) $
                    "Not a valid size " ++ pprint ty

intTy :: IType
intTy = IType IntType []

throw :: String -> ImpM a
throw s = throwError (CompilerErr s)

throwIf :: Bool -> String -> ImpM ()
throwIf True = throw
throwIf False = const (return ())
