{-# LANGUAGE FlexibleContexts #-}

module Imp (impPass, checkImp) where

import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Except (liftEither)
import Data.Foldable (toList)
import Data.List (intercalate)

import Syntax
import Env
import Record
import Type
import PPrint
import Pass
import Fresh

type ImpM a = Pass ImpEnv ImpState a
type ImpEnv = FullEnv (Type, RecTree Name) Name
data ImpState = ImpState { blocks :: [[Statement]]
                         , cellsInScope :: [Var] }

impPass :: Decl -> TopPass ImpEnv ImpDecl
impPass decl = case decl of
  TopLet (v,ty) expr -> do
    prog <- impExprTop expr
    let binders = impBinder v (flatType' ty)
    putEnv $ FullEnv (v@>(ty, fmap fst binders)) mempty
    return $ ImpTopLet (toList binders) prog
  TopUnpack (v,ty) iv expr -> do
    prog <- impExprTop expr
    let binders = impBinder v (flatType' ty)
    putEnv $ FullEnv (v@>(ty, fmap fst binders)) (iv@>iv)
    let b' = (iv, intTy) : toList binders
    return $ ImpTopLet b' prog
  EvalCmd NoOp -> return (ImpEvalCmd unitTy NoOp)
  EvalCmd (Command cmd expr) -> do
    prog <- impExprTop expr
    env <- getEnv
    let ty = getType (setLEnv (fmap fst) env) expr
    case cmd of Passes -> writeOut $ "\n\nImp\n" ++ pprint prog
                _ -> return ()
    return $ ImpEvalCmd ty (Command cmd prog)

impBinder :: Name -> RecTree a -> RecTree (Name, a)
impBinder v tree = fmap (onFst newName) (recTreeNamed tree)
   where
     newName fields = rawName $ intercalate "_" (nameTag v : map pprint fields)
     onFst f (x,y) = (f x, y)

impExprTop :: Expr -> TopPass ImpEnv ImpProgram
impExprTop expr = do
  env <- getEnv
  (iexpr, state) <- liftEither $
            runPass env (ImpState [[]] []) (envToScope env) (toImp expr)
  let ImpState [statements] _ = state
  return $ ImpProgram (reverse statements) (toList iexpr)

envToScope :: ImpEnv -> FreshScope
envToScope (FullEnv lenv tenv) = foldMap newScope (lNames <> toList tenv)
  where lNames = concat $ map (toList . snd) (toList lenv)

toImp :: Expr -> ImpM (RecTree IExpr)
toImp expr = case expr of
  Lit x -> return $ RecLeaf (ILit x)
  Var v -> asks $ fmap IVar . snd . (!v) . lEnv
  App (Builtin Iota) n -> toImp n >>= impIota
  App (TApp (Builtin Fold) ts) args -> impFold ts args
  App (Builtin b) args -> do args' <- toImp args
                             return $ RecLeaf $ IBuiltinApp b (toList args')
  Let p bound body -> do
    (bound', cells) <- collectAllocs $ toImp bound
    envUpdates <- traverse (uncurry letBind) (recTreeZip p bound')
    freeCells cells
    local (setLEnv $ addVs envUpdates) (toImp body)
  Get x i -> do xs <- toImp x
                RecLeaf i' <- asks $ snd . (!i) . lEnv
                return $ fmap (\x -> IGet x i') xs
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
toImpFor (i, TypeVar n) body = do
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
addLet (v, ty) expr = do addAlloc v ty
                         add $ Update v [] expr

writeCell :: Var -> IExpr -> ImpM ()
writeCell v val = add $ Update v [] val

newCell :: IType -> ImpM Var
newCell ty = do v <- fresh "cell"
                addAlloc v ty
                return v

freeCells :: [Var] -> ImpM ()
freeCells = mapM_ (add . Free)

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

addAlloc :: Var -> IType -> ImpM ()
addAlloc v ty = do add $ Alloc v ty
                   modify $ setCellsInScope (v:)

collectAllocs :: ImpM a -> ImpM (a, [Var])
collectAllocs m = do prev <- gets cellsInScope
                     ans <- m
                     new <- gets cellsInScope
                     modify $ setCellsInScope (const prev)
                     return (ans, new)

setBlocks update state = state { blocks = update (blocks state) }
setCellsInScope update state = state {cellsInScope = update (cellsInScope state)}

-- === type checking imp programs ===

type ImpCheckM a = Pass () (Env IType) a

checkImp :: ImpDecl -> TopPass (Env IType) ImpDecl
checkImp decl = decl <$ case decl of
  ImpTopLet binders prog -> do
    _ <- check prog
    -- doesn't work without alias checking for sizes
    -- liftEither $ assertEq ty (map snd binders) ""
    putEnv $ newEnv binders
  ImpEvalCmd _ NoOp -> return ()
  ImpEvalCmd _ (Command _ prog) -> void $ check prog
  where
    check :: ImpProgram -> TopPass (Env IType) [IType]
    check prog = do env <- getEnv
                    liftEither $ addContext (pprint prog) $
                      evalPass () env mempty (impProgType prog)

impProgType :: ImpProgram -> ImpCheckM [IType]
impProgType (ImpProgram statements exprs) = do
  mapM checkStatementTy statements
  mapM impExprType exprs

lookupVar :: Var -> ImpCheckM IType
lookupVar v = gets $ (! v)

checkStatementTy :: Statement -> ImpCheckM ()
checkStatementTy statement = case statement of
  Update v _ expr -> do
    IType b  _ <- gets $ (! v)
    IType b' _ <- impExprType expr
    assertEq b b' "Base type mismatch"
    -- can't do this check unless we track assignments a bit
    -- assertEq (drop (length idxs) shape) shape' "Dimension mismatch"
  Loop i size block -> do addVar i intTy
                          checkIsInt size
                          void $ mapM checkStatementTy block
  Alloc v ty@(IType _ shape) -> do void $ mapM checkIsInt shape
                                   addVar v ty
  Free _ -> return () -- TODO (will be easier if we make scopes explicit)

addVar :: Var -> IType -> ImpCheckM ()
addVar v ty = do
  env <- get
  throwIf (v `isin` env) $ "Variable " ++ pprint v ++ " already defined"
  modify $ addV (v, ty)

impExprType :: IExpr -> ImpCheckM IType
impExprType expr = case expr of
  ILit val -> return $ IType (litType val) []
  IVar  v -> gets $ (! v)
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
checkIsInt v = do ty <- lookupVar v
                  assertEq ty intTy "Not a valid size"
