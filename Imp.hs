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
type ImpVal = RecTree Name
type ImpEnv = FullEnv (Type, ImpVal) Name
type Dest = (Var, [Index])

impPass :: Decl -> TopPass ImpEnv ImpDecl
impPass decl = case decl of
  TopLet b expr -> do
    let binders = impBinders b
    prog <- impExprTop binders expr
    putEnv $ asLEnv $ bindWith b (fmap (fromJust . binderVar) binders)
    return $ ImpTopLet (toList binders) prog
  TopUnpack b iv expr -> do
    let binders = RecTree $ Tup [ RecLeaf (iv %> intTy), impBinders b]
    prog <- impExprTop binders expr
    putEnv $ FullEnv (bindWith b (fmap (fromJust . binderVar) binders)) (iv@>iv)
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
  let dest' = fmap (\(Bind v _) -> (v, [])) dest -- TODO: handle underscores
  liftEither $ evalPass env () (envToScope env) (toImpDest dest' expr)

envToScope :: ImpEnv -> FreshScope
envToScope (FullEnv lenv tenv) = foldMap newScope (lNames <> toList tenv)
  where lNames = concat $ map (toList . snd) (toList lenv)

toImpDest :: RecTree Dest -> Expr -> ImpM ImpProg
toImpDest dest expr = case expr of
  Lit x -> return $ write (RecLeaf (ILit x))
  Var v -> liftM write $ asks $ fmap IVar . snd . (!v) . lEnv
  TApp (Builtin Iota) n -> impIota dest n
  App (Builtin Range) n -> toImpExpr n $ \n' ->
                             return $ write $ RecTree $ Tup [n', unitCon]
  App (TApp (Builtin Fold) ts) args -> impFold dest ts args
  App (Builtin b) args ->
    toImpExpr args $ \args' ->
      return $ write $ RecLeaf $ IBuiltinApp b (toList args')
  Let p bound body ->
    toImpExpr bound $ \bound' ->
      letBind p bound' $
        toImpDest dest body
  Get x i -> do
    RecLeaf i' <- asks $ snd . (!i) . lEnv
    toImpExpr x $ \xs ->
      return $ write $ fmap (flip IGet i') xs
  For i body -> toImpFor dest i body
  RecCon r -> liftM fold $ sequence $ recZipWith toImpDest dests r
                where RecTree dests = dest
  Unpack b n bound body -> do
    toImpExpr bound $ \(RecTree (Tup [RecLeaf iset, x])) -> do
      n' <- freshLike n
      body' <- extendWith (asTEnv (n @> n')) $
                 letBind (RecLeaf b) x $
                   toImpDest dest body
      return $ makeLet (n' %> intTy) iset body'
  _ -> error $ "Can't lower to imp:\n" ++ pprint expr
  where write = writeExprs dest
        unitCon = RecTree $ Tup []

toImpExpr :: Expr -> (RecTree IExpr -> ImpM ImpProg) -> ImpM ImpProg
toImpExpr expr cont = do
  ty <- exprType expr >>= flatType
  bs <- traverse (freshBinder "tmp") ty
  let dests = fmap asDest bs
  prog <- toImpDest dests expr
  prog' <- cont $ fmap (IVar . fst) dests
  return $ makeAllocs bs $ prog <> prog'
  -- TODO: think about fresh variable and env contexts!

asDest :: IBinder -> Dest
asDest (Bind v _) = (v, [])

freshBinder :: String -> IType -> ImpM IBinder
freshBinder s ty = do v <- fresh s
                      return (v %> ty)

writeExprs :: RecTree Dest -> RecTree IExpr -> ImpProg
writeExprs dests exprs = ImpProg $ toList $
                           fmap (uncurry writeExpr) (recTreeZipEq dests exprs)

writeExpr :: Dest -> IExpr -> Statement
writeExpr (name, idxs) expr = Update name idxs expr

letBind :: Pat -> RecTree IExpr -> ImpM ImpProg -> ImpM ImpProg
letBind pat exprs cont = do
  impBinders <- liftM recTreeJoin $ traverse flatBinding pat
  let vs = fmap (fromJust . binderVar) impBinders
  extendWith (asLEnv $ bindRecZip pat vs) $ do
    prog <- cont
    return $ foldr (uncurry makeLet) prog (recTreeZipEq impBinders exprs)

flatBinding :: Binder -> ImpM (RecTree IBinder)
flatBinding (Ignore ty) = liftM (fmap Ignore) (flatType ty)
flatBinding (Bind v ty) = do ty' <- flatType ty
                             traverse freshBinder ty'
  where freshBinder t = do v' <- freshLike v
                           return (v' %> t)

makeLet :: IBinder -> IExpr -> ImpProg -> ImpProg
makeLet b@(Bind v _) expr body = ImpProg [Alloc b
                                           (ImpProg [Update v [] expr] <> body)]

makeAllocs :: Foldable f => f IBinder -> ImpProg -> ImpProg
makeAllocs bs prog = foldr (\b p -> asProg (Alloc b p)) prog bs

toImpFor :: RecTree Dest -> Binder -> Expr -> ImpM ImpProg
toImpFor dest (Bind i (TypeVar n)) body = do
  i' <- freshLike i
  let dest' = fmap (\(v, idxs) -> (v, i':idxs)) dest
  body' <- extendWith (asLEnv $ i @> (TypeVar n, RecLeaf i')) $
             toImpDest dest' body
  return $ asProg $ Loop i' n body'

impIota :: RecTree Dest -> [Type] -> ImpM ImpProg
impIota (RecLeaf (outVar, outIdxs)) [TypeVar n] = do
  n' <- asks $ (!n) . tEnv
  i <- fresh "iIota"
  return $ asProg $ Loop i n' $ asProg $ Update outVar (i:outIdxs) (IVar i)

impFold :: (RecTree Dest) -> [Type] -> Expr -> ImpM ImpProg
impFold dest [_, _, TypeVar n] (RecCon (Tup [Lam p body, x0, xs])) = do
  n' <- asks $ (!n) . tEnv
  toImpExpr x0 $ \x0' ->
    toImpExpr xs $ \xs' -> do
      let destExprs = fmap destAsExpr dest
      i <- fresh "iFold"
      body' <- letBind accumBinder destExprs $
                 letBind xBinder (fmap (flip IGet i) xs') $
                   toImpDest dest body
      return $ writeExprs dest x0' <> asProg (Loop i n' body')
  where RecTree (Tup [accumBinder, xBinder]) = p
        accumTy = binderAnn (unLeaf accumBinder)

-- TODO: likely bug. haven't thought about whether we need foldr or foldl
destAsExpr :: Dest -> IExpr
destAsExpr (v, idxs) = foldr (flip IGet) (IVar v) idxs

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
    checkTypeValid (binderAnn b)
    env <- ask
    if fromJust (binderVar b) `isin` env then throw CompilerErr "Shadows!"
                                         else return ()
    extendWith (bind b) (checkProg body)
  Update v idxs expr -> do
    mapM_ checkIsInt idxs
    IType b  shape  <- asks $ (! v)
    IType b' shape' <- impExprType expr
    assertEq b b' "Base type mismatch"
    assertEq (drop (length idxs) shape) shape' "Dimension mismatch"
  Loop i size block -> extendWith (i @> intTy) $ do
                          checkIsInt size
                          checkProg block

checkTypeValid :: IType -> ImpCheckM ()
checkTypeValid _ = return () -- TODO


impExprType :: IExpr -> ImpCheckM IType
impExprType expr = case expr of
  ILit val -> return $ IType (litType val) []
  IVar v   -> asks $ (! v)
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
