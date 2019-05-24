{-# LANGUAGE FlexibleContexts #-}

module Imp (impPass, checkImp) where

import Control.Monad.Reader
import Control.Monad.Except (liftEither)
import Data.Foldable (fold, toList)
import Data.Maybe (fromJust)
import Data.List (intercalate)

import Syntax
import Env
import Record
import Type
import PPrint
import Pass
import Fresh

type ImpM a = Pass ImpEnv () a
type ImpVal = RecTree IExpr
type ImpEnv = FullEnv (Type, ImpVal) Name

impPass :: Decl -> TopPass ImpEnv ImpDecl
impPass decl = case decl of
  TopLet b expr -> do
    let binders = impBinders b
    prog <- impExprTop binders expr
    putEnv $ asLEnv $ bindWith b (fmap (IVar . fromJust . binderVar) binders)
    return $ ImpTopLet (toList binders) prog
  TopUnpack b iv expr -> do
    let binders = RecTree $ Tup [ RecLeaf (iv %> intTy), impBinders b]
    prog <- impExprTop binders expr
    putEnv $ FullEnv (bindWith b (fmap (IVar . fromJust . binderVar) binders)) (iv@>iv)
    return $ ImpTopLet (toList binders) prog
  EvalCmd NoOp -> return (ImpEvalCmd unitTy [] NoOp)
  EvalCmd (Command cmd expr) -> do
    FullEnv lenv tenv <- getEnv
    let ty = getType (FullEnv (fmap fst lenv) tenv) expr
    let binders = impBinders (rawName "%imptmp" %> ty)
    prog <- impExprTop binders expr
    case cmd of Passes -> writeOut $ "\n\nImp\n" ++ pprint prog
                _ -> return ()
    return $ ImpEvalCmd ty (toList binders) (Command cmd prog)

-- TODO: handle underscore binders
impBinders :: Binder -> RecTree IBinder
impBinders (Ignore ty) = fmap Ignore (flatType' ty)
impBinders (Bind v ty) = fmap (uncurry (%>) . onFst newName) (recTreeNamed itypes)
   where
     itypes = flatType' ty
     newName fields = rawName $ intercalate "_" (nameTag v : map pprint fields)
     onFst f (x,y) = (f x, y)

impExprTop :: RecTree IBinder -> Expr -> TopPass ImpEnv ImpProg
impExprTop dest expr = do
  env <- getEnv
  let dest' = fmap asBuffer dest -- TODO: handle underscores
  liftEither $ evalPass env () (envToScope env) (toImp expr dest')

envToScope :: ImpEnv -> FreshScope
envToScope (FullEnv lenv tenv) = foldMap newScope (lNames <> toList tenv)
  where lNames = map getVar $ concat $ map (toList . snd) (toList lenv)
        getVar (IVar v) = v

toImp :: Expr -> RecTree Dest -> ImpM ImpProg
toImp expr dests = case expr of
  Lit x -> return $ write (RecLeaf (ILit x))
  Var v -> do exprs <- asks $ snd . (!v) . lEnv
              return $ write exprs
  TApp (Builtin Iota) n -> impIota dests n
  App (Builtin Range) n -> let (RecTree (Tup [nDest, _])) = dests
                           in toImp n nDest
  App (TApp (Builtin Fold) ts) args -> impFold dests ts args
  App (Builtin b) args -> do
    let (RecLeaf dest) = dests
    materialize args $ \args' ->
      return $ writeBuiltin b dest (map IVar (toList args'))
  Let p bound body ->
    materialize bound $ \bound' ->
      bindPat p (fmap IVar bound') $
        toImp body dests
  Get x i -> do RecLeaf (IVar i') <- asks $ snd . (!i) . lEnv
                toImp x $ fmap (indexSource i') dests
  For i body -> toImpFor dests i body
  RecCon r -> liftM fold $ sequence $ recZipWith toImp r dests'
                where RecTree dests' = dests
  Unpack b n bound body -> do
    materialize bound $ \(RecTree (Tup [RecLeaf n', x])) -> do
      extendWith (asTEnv (n @> n')) $
        bindPat (RecLeaf b) (fmap IVar x) $
          toImp body dests
  _ -> error $ "Can't lower to imp:\n" ++ pprint expr
  where write = writeExprs dests
        unitCon = RecTree $ Tup []

materialize :: Expr -> (RecTree Name -> ImpM ImpProg) -> ImpM ImpProg
materialize expr body = do
  ty <- exprType expr >>= flatType
  names <- traverse (const (fresh "tmp")) ty
  let binders = fmap (uncurry (%>)) (recTreeZipEq names ty)
      dest = fmap (\v -> Buffer v [] []) names
  writerProg <- toImp expr dest
  readerProg <- body names
  return $ foldr allocProg (writerProg <> readerProg) binders
  where allocProg binder scoped = asProg $ Alloc binder scoped

bindPat :: Pat -> RecTree IExpr -> ImpM ImpProg -> ImpM ImpProg
bindPat pat exprs body = extendWith (asLEnv $ bindRecZip pat exprs) body

loop :: Name -> (Name -> ImpM ImpProg) -> ImpM ImpProg
loop n body = do i <- fresh "i"
                 body' <- body i
                 return $ asProg $ Loop i n body'

-- Destination indices, then source indices
data Dest = Buffer Var [Index] [Index]  deriving Show

asBuffer :: IBinder -> Dest
asBuffer (Bind v _) = Buffer v [] []

indexSource :: Index -> Dest -> Dest
indexSource i (Buffer v destIdxs srcIdxs) = Buffer v destIdxs (i:srcIdxs)

indexDest :: Index -> Dest -> Dest
indexDest i (Buffer v destIdxs srcIdxs) = Buffer v (i:destIdxs) srcIdxs

writeExprs :: RecTree Dest -> RecTree IExpr -> ImpProg
writeExprs dests exprs = fold $ fmap (uncurry writeExpr) (recTreeZipEq dests exprs)

writeExpr :: Dest -> IExpr -> ImpProg
writeExpr (Buffer name destIdxs srcIdxs) expr =
  asProg $ Update name destIdxs Copy [expr']
  where expr' = foldr (flip IGet) expr srcIdxs

writeBuiltin :: Builtin -> Dest -> [IExpr] -> ImpProg
writeBuiltin b (Buffer name destIdxs []) exprs =
  asProg $ Update name destIdxs b exprs

toImpFor :: RecTree Dest -> Binder -> Expr -> ImpM ImpProg
toImpFor dest (Bind i (TypeVar n)) body = do
  n' <- asks $ (!n) . tEnv
  loop n' $ \i' -> do
    extendWith (asLEnv $ i @> (TypeVar n, RecLeaf (IVar i'))) $
      toImp body (fmap (indexDest i') dest)

-- TODO: handle source indices
impIota :: RecTree Dest -> [Type] -> ImpM ImpProg
impIota (RecLeaf (Buffer outVar destIdxs [])) [TypeVar n] = do
  n' <- asks $ (!n) . tEnv
  loop n' $ \i ->
    return $ asProg $ Update outVar (i:destIdxs) Copy [IVar i]

impFold :: RecTree Dest -> [Type] -> Expr -> ImpM ImpProg
impFold dest [_, _, TypeVar n] (RecCon (Tup [Lam p body, x0, xs])) = do
  n' <- asks $ (!n) . tEnv
  materialize x0 $ \accum ->
    materialize xs $ \xs' -> do
      loop' <- loop n' $ \i ->
                 bindPat accumBinder (fmap IVar accum) $
                   bindPat xBinder (fmap (flip IGet i . IVar) xs') $
                     toImp body (fmap asBuffer accum)
      return $ loop' <> writeExprs dest (fmap IVar accum)
  where
    asBuffer :: Name -> Dest
    asBuffer v = Buffer v [] []
    RecTree (Tup [accumBinder, xBinder]) = p

asProg :: Statement -> ImpProg
asProg statement = ImpProg [statement]

flatType :: Type -> ImpM (RecTree IType)
flatType ty = case ty of
  BaseType b -> return $ RecLeaf (IType b [])
  RecType r  -> liftM RecTree (traverse flatType r)
  TabType (TypeVar n) valTy -> do n' <- asks $ (!n) . tEnv
                                  valTy' <- flatType valTy
                                  return $ fmap (addIdx n') valTy'
  -- TODO: fix this (only works for range)
  Exists _ -> return (RecTree (Tup [RecLeaf intTy, RecTree (Tup [])]))
  _ -> error $ "Can't flatten type: " ++ show ty

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
exprType expr = do FullEnv lenv tenv <- ask
                   return $ getType (FullEnv (fmap fst lenv) tenv) expr

-- === type checking imp programs ===

type ImpCheckM a = Pass (Env IType) () a

checkImp :: ImpDecl -> TopPass (Env IType) ImpDecl
checkImp decl = decl <$ case decl of
  ImpTopLet binders prog -> do
    check binders prog
    putEnv $ bindFold binders
  ImpEvalCmd _ _ NoOp -> return ()
  ImpEvalCmd _ bs (Command _ prog) -> check bs prog
  where
    check :: [IBinder] -> ImpProg -> TopPass (Env IType) ()
    check bs prog = do
      env <- getEnv
      liftEither $ addContext (pprint prog) $
          evalPass (bindFold bs <> env) () mempty (checkProg prog)

checkProg :: ImpProg -> ImpCheckM ()
checkProg (ImpProg statements) = mapM_ checkStatement statements

lookupVar :: Var -> ImpCheckM IType
lookupVar v = asks $ (! v)

checkStatement :: Statement -> ImpCheckM ()
checkStatement statement = case statement of
  Alloc b body -> do
    env <- ask
    if fromJust (binderVar b) `isin` env then throw CompilerErr "Shadows!"
                                         else return ()
    extendWith (bind b) (checkProg body)
  Update v idxs Copy [expr] -> do
    mapM_ checkIsInt idxs
    IType b  shape  <- asks $ (! v)
    IType b' shape' <- impExprType expr
    assertEq b b' "Base type mismatch in copy"
    assertEq (drop (length idxs) shape) shape' "Dimension mismatch"
  Update v idxs builtin args -> do -- scalar builtins only
    argTys <- mapM impExprType args
    let ArrType inTy (BaseType b) = builtinType builtin
    checkArgTys inTy argTys
    IType b' shape  <- asks $ (! v)
    case drop (length idxs) shape of
      [] -> assertEq b b' "Base type mismatch in builtin application"
      _  -> throw CompilerErr "Writing to non-scalar buffer"
  Loop i size block -> extendWith (i @> intTy) $ do
                          checkIsInt size
                          checkProg block

impExprType :: IExpr -> ImpCheckM IType
impExprType expr = case expr of
  ILit val -> return $ IType (litType val) []
  IVar v   -> asks $ (! v)
  IGet e i -> do IType b (_:shape) <- impExprType e
                 checkIsInt i
                 return $ IType b shape

checkArgTys :: Type -> [IType] -> ImpCheckM ()
checkArgTys (RecType (Tup argTyNeeded)) argTys =
  -- TODO This zipWith silently drops arity errors :(
    zipWithM_ checkScalarTy argTyNeeded argTys
checkArgTys b@(BaseType _) [argTy] = checkScalarTy b argTy

checkScalarTy :: Type -> IType -> ImpCheckM ()
checkScalarTy (BaseType b) (IType b' []) | b == b'= return ()
checkScalarTy ty ity = throw CompilerErr $ "Wrong types. Expected:" ++ pprint ty
                                                         ++ " Got " ++ pprint ity

checkIsInt :: Var -> ImpCheckM ()
checkIsInt v = do ty <- lookupVar v
                  assertEq ty intTy "Not a valid size"
