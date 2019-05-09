{-# LANGUAGE FlexibleContexts #-}

module Imp (impPass, checkImp) where

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

type ImpM a = Pass ImpEnv ImpState a
type ImpMTop a = TopPass ImpEnv a

type ImpEnv = FullEnv (Type, RecTree Name) Name

data ImpState = ImpState { blocks :: [[Statement]] }

impPass :: Decl -> TopPass ImpEnv ImpDecl
impPass decl = case decl of
  TopLet (v,ty) expr -> do
    prog <- impExprTop expr
    let binders = fmap (\(v', ty') -> (catNames v v', ty'))
                    $ recTreeNamed (flatType' ty)
    put $ newFullEnv [(v, (ty, fmap fst binders))]  []
    return $ ImpTopLet (toList binders) prog
  TopUnpack (v,ty) iv expr -> do
    prog <- impExprTop expr
    let binders = fmap (\(v', ty') -> (catNames v v', ty'))
                    $ recTreeNamed (flatType' ty)
    put $ newFullEnv [(v, (ty, (fmap fst binders)))] [(iv,iv)]
    let b' = (iv, intTy) : toList binders
    return $ ImpTopLet b' prog

  EvalCmd NoOp -> put mempty >> return (ImpEvalCmd unitTy NoOp)
  EvalCmd (Command cmd expr) -> do
    prog <- impExprTop expr
    env <- gets (setLEnv (fmap fst))
    let ty = getType env expr
    put mempty
    case cmd of Passes -> tell ["\n\nImp\n" ++ pprint prog]
                _ -> return ()
    return $ ImpEvalCmd ty (Command cmd prog)

impExprTop :: Expr -> ImpMTop ImpProgram
impExprTop expr = do
  env <- get
  (iexpr, state) <- liftExcept $ runPass env (ImpState [[]]) nameRoot (toImp expr)
  let ImpState [statements] = state
      prog = ImpProgram (reverse statements) (toList iexpr)
  return prog

toImp :: Expr -> ImpM (RecTree IExpr)
toImp expr = case expr of
  Lit x -> return $ RecLeaf (ILit x)
  Var v -> asks $ fmap IVar . snd . (!v) . lEnv
  App (Builtin Iota) n -> toImp n >>= impIota
  App (TApp (Builtin Fold) ts) args -> impFold ts args
  App (Builtin b) args -> do args' <- toImp args
                             return $ RecLeaf $ IBuiltinApp b (toList args')
  Let p bound body -> do
    bound' <- toImp bound
    envUpdates <- traverse (uncurry letBind) (recTreeZip p bound')
    local (setLEnv $ addVs envUpdates) (toImp body)
  Get x i -> do xs <- toImp x
                return $ fmap get xs
                where get x = IGet x i
  For i body -> toImpFor i body
  RecCon r -> liftM RecTree $ traverse toImp r
  Unpack b n bound body -> do
    RecTree (Tup [RecLeaf iset, x]) <- toImp bound
    n' <- freshLike n
    addLet (n', intTy) iset
    envUpdate <- local (setTEnv (addV (n, n'))) (letBind b x)
    let updateEnv = setTEnv (addV (n, n')) . setLEnv (addV envUpdate)
    local updateEnv (toImp body)
  _ -> error $ "Can't lower to imp:\n" ++ pprint expr

letBind :: Binder -> RecTree IExpr -> ImpM (Var, (Type, RecTree Name))
letBind binder@(v,ty) exprs = do
  impBinders <- flatBinding binder
  traverse (uncurry addLet) $ recTreeZipEq impBinders exprs
  return (v, (ty, fmap fst impBinders))

flatBinding :: (Var, Type) -> ImpM (RecTree (Var, IType))
flatBinding (v, ty) = do ty' <- flatType ty
                         traverse freshBinder ty'
  where freshBinder t = do v' <- freshLike v
                           return (v', t)

-- TODO: make a destination-passing version to avoid unnecessary intermediates
toImpFor :: Binder -> Expr -> ImpM (RecTree IExpr)
toImpFor b@(i, TypeVar n) body = do
  i' <- freshLike i
  bodyTy <- exprType body >>= flatType
  let cellTypes = fmap (addIdx n) bodyTy
  cells <- traverse newCell cellTypes
  startBlock
  let updateEnv = setLEnv $ addV $ (i, (TypeVar n, RecLeaf i'))
  results <- local updateEnv (toImp body)
  traverse (\(v,x) -> add $ Update v [i'] x) (recTreeZipEq cells results)
  block <- endBlock
  add $ Loop i' n block
  return $ fmap IVar cells

impIota :: RecTree IExpr -> ImpM (RecTree IExpr)
impIota (RecLeaf n) = do
  n' <- newVar n intTy
  out <- newCell (IType IntType [n'])
  i <- fresh "iIota"
  add $ Loop i n' [Update out [i] (IVar i)]
  return $ RecTree $ Tup [RecLeaf (IVar n'), RecLeaf (IVar out)]

impFold :: [Type] -> Expr -> ImpM (RecTree IExpr)
impFold [_, _, TypeVar n] (RecCon (Tup [Lam p body, x0, xs])) = do
  n' <- asks $ (!n) . tEnv
  x0' <- toImp x0
  xs' <- toImpNewVar xs
  i <- fresh "iFold"
  accumTyFlat <- flatType accumTy
  accumCells <- traverse newCell accumTyFlat
  let writeCells val = traverse (uncurry writeCell) $ recTreeZipEq accumCells val
  writeCells x0'
  block <- do
    startBlock
    updateAccum <- letBind accumBinder $ fmap IVar accumCells
    updateX <- letBind xBinder $ fmap (\x -> IGet (IVar x) i) xs'
    newVals <- local (setLEnv $ addV updateAccum . addV updateX) (toImp body)
    writeCells newVals
    endBlock
  add $ Loop i n' block
  return $ fmap IVar accumCells
  where RecTree (Tup binders) = p
        [accumBinder@(_, accumTy), xBinder] = map unLeaf binders

toImpNewVar :: Expr -> ImpM (RecTree Var)
toImpNewVar expr = do
  ty <- exprType expr
  vals <- toImp expr
  ty' <- flatType ty
  traverse (uncurry newVar) $ recTreeZipEq vals ty'

newVar :: IExpr -> IType -> ImpM Var
newVar expr t = do v <- fresh "var"
                   addLet (v, t) expr
                   return v

addLet :: (Var, IType) -> IExpr -> ImpM ()
addLet (v, ty) expr = add $ ImpLet (v, ty) expr

writeCell :: Var -> IExpr -> ImpM ()
writeCell v val = add $ Update v [] val

newCell :: IType -> ImpM Var
newCell ty = do v <- fresh "cell"
                add $ Alloc v ty
                return v

flatType :: Type -> ImpM (RecTree IType)
flatType ty = case ty of
  BaseType b -> return $ RecLeaf (IType b [])
  RecType r  -> liftM RecTree (traverse flatType r)
  TabType (TypeVar n) valTy -> do n' <- asks $ (!n) . tEnv
                                  valTy' <- flatType valTy
                                  return $ fmap (addIdx n') valTy'

-- version without substituting range vars, not in impM monad
-- TODO: something better
flatType' :: Type -> RecTree IType
flatType' ty = case ty of
  BaseType b -> RecLeaf (IType b [])
  RecType r  -> RecTree (fmap flatType' r)
  TabType (TypeVar n) valTy -> fmap (addIdx n) (flatType' valTy)

addIdx :: Size -> IType -> IType
addIdx n (IType ty shape) = IType ty (n : shape)

intTy :: IType
intTy = IType IntType []

exprType ::Expr -> ImpM Type
exprType expr = do env <- asks (setLEnv (fmap fst))
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

setBlocks update state = state { blocks = update (blocks state) }


-- === type checking imp programs ===

type ImpCheckM a = Pass () (Env VarType) a
type IsMutable = Bool
type VarType = (IsMutable, IType)

checkImp :: ImpDecl -> TopPass (Env IType) ImpDecl
checkImp decl = decl <$ case decl of
  ImpTopLet binders prog -> do
    ty <- check prog
    -- doesn't work without alias checking for sizes
    -- liftExcept $ assertEq ty (map snd binders) ""
    put $ newEnv binders
  ImpEvalCmd _ NoOp -> return ()
  ImpEvalCmd _ (Command cmd prog) -> check prog >> put mempty
  where
    check :: ImpProgram -> TopPass (Env IType) [IType]
    check prog = do env <- gets $ fmap (\t->(False,t))
                    liftExcept $ evalPass () env nameRoot (impProgType prog)

impProgType :: ImpProgram -> ImpCheckM [IType]
impProgType (ImpProgram statements exprs) = do
  mapM checkStatementTy statements
  mapM impExprType exprs

lookupVar :: Var -> ImpCheckM VarType
lookupVar v = gets $ (! v)

checkStatementTy :: Statement -> ImpCheckM ()
checkStatementTy statement = case statement of
  Update v idxs expr -> do (mut, IType b shape ) <- gets $ (! v)
                           IType b' shape' <- impExprType expr
                           throwIf (not mut) $ "Updating immutable variable"
                           throwIf (b /= b') $ "Base type mismatch"
                           throwIf (drop (length idxs) shape /= shape') $
                                    "Dimension mismatch"
  ImpLet b@(v,ty) expr -> do ty' <- impExprType expr
                             -- doesn't work without alias checking for sizes
                             -- throwIf (ty' /= ty) $ "Type doesn't match binder"
                             addVar v (False, ty)
  Loop i size block -> do addVar i (False, intTy)
                          checkIsInt size
                          void $ mapM checkStatementTy block
  Alloc v ty@(IType b shape) -> do void $ mapM checkIsInt shape
                                   addVar v (True, ty)

addVar :: Var -> VarType -> ImpCheckM ()
addVar v ty = do
  env <- get
  -- TODO: re-enable once fixed
  -- throwIf (v `isin` env) $ "Variable " ++ pprint v ++ " already defined"
  modify $ addV (v, ty)

impExprType :: IExpr -> ImpCheckM IType
impExprType expr = case expr of
  ILit val -> return $ IType (litType val) []
  IVar  v -> gets $ snd . (! v)
  IGet e i -> do IType b (_:shape) <- impExprType e
                 checkIsInt i
                 return $ IType b shape
  IBuiltinApp b args -> do -- scalar builtins only
    argTys <- mapM impExprType args
    let ArrType inTy (BaseType out) = builtinType b
    checkArgTys inTy argTys
    return $ IType out []

  where checkArgTys :: Type -> [IType] -> ImpCheckM ()
        checkArgTys (RecType (Tup argTyNeeded)) argTys =
          -- TODO This zipWith silently drops arity errors :(
          zipWithM_ checkScalarTy argTyNeeded argTys
        checkArgTys b@(BaseType _) [argTy] = checkScalarTy b argTy
        checkScalarTy :: Type -> IType -> ImpCheckM ()
        checkScalarTy (BaseType b) (IType b' []) | b == b'= return ()
        checkScalarTy ty ity = throw CompilerErr $
                                       "Wrong types. Expected:" ++ pprint ty
                                                     ++ " Got " ++ pprint ity

checkIsInt :: Var -> ImpCheckM ()
checkIsInt v = do (_, ty) <- lookupVar v
                  throwIf (ty /= intTy) $
                    "Not a valid size " ++ pprint ty

throwIf :: Bool -> String -> ImpCheckM ()
throwIf True = throw CompilerErr
throwIf False = const (return ())
