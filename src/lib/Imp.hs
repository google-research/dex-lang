-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

module Imp (impPass, checkImp, impExprType, substIExpr, substIType) where

import Control.Monad.Reader
import Control.Monad.Except hiding (Except)
import Data.Foldable

import Syntax
import Env
import Type
import PPrint
import Pass
import Cat
import Serialize
import Fresh hiding (freshName)
import Subst
import Record

type ImpEnv = Env [IExpr]
type EmbedEnv = (Scope, ImpProg)
type ImpM a = ReaderT ImpEnv (CatT EmbedEnv (Either Err)) a

impPass :: TopPass NTopDecl ImpDecl
impPass = TopPass $ \decl -> case decl of
  NTopDecl _ (Let (v:>ty) bound) -> do
    tys' <- toImpTypeTop ty
    (env, scope) <- look
    let (vs, scope') = renames (replicate (length tys') v) scope
    let bs' = zipWith (:>) vs tys'
    extend $ asSnd scope'
    ((), prog) <- liftTop $ toImpCExpr (map asDest bs') bound
    let xs = [IVar v' (derefTypeIfScalar ty') | (v':>ty') <- bs']
    extend $ asFst $ v@>xs
    return [ImpTopLet bs' prog]
  NTopDecl _ (Unpack _ tv bound) -> do
    let b = tv:>(IRefType (IntType,[]))
    ((), prog) <- liftTop $ do x <- toImpScalarAtom bound
                               store (asDest b) x
    extend (tv @> [IVar tv intTy], tv @> ())
    return [ImpTopLet [b] prog]
  NRuleDef _ _ _ -> error "Shouldn't have this left"
  NEvalCmd (Command cmd (ty, expr)) -> do
    ts <- toImpTypeTop (getType expr)
    let bs = [Name "%imptmp" i :> t | (i, t) <- zip [0..] ts]
    ((), prog) <- liftTop $ toImpExpr (map asDest bs) expr
    case cmd of
      ShowImp -> emitOutput $ TextOut $ pprint prog
      _ -> return [ImpEvalCmd (Command cmd (ty, bs, prog))]

liftTop :: ImpM a -> TopPassM (ImpEnv, Scope) (a, ImpProg)
liftTop m = do
  (env, scope) <- look
  (ans, (_, prog)) <- liftExceptTop $ runCatT (runReaderT m env) (scope, mempty)
  return (ans, prog)

toImpTypeTop :: Type -> TopPassM (ImpEnv, Scope) [IType]
toImpTypeTop ty = liftM (map IRefType . fst) $ liftTop $ toImpArrayType ty

toImpExpr :: [IExpr] -> Expr -> ImpM ()
toImpExpr dests expr = case expr of
  Decl (Let b@(_:>ty) bound) body -> do
    tys <- toImpArrayType ty
    withAllocs tys $ \bDests -> do
      toImpCExpr bDests bound
      xs <- mapM loadIfScalar bDests
      extendR (bindEnv b xs) $ toImpExpr dests body
  Decl (Unpack _ tv bound) body -> do
    x <- toImpAtom bound
    extendR (tv @> x) $ toImpExpr dests body
  CExpr expr -> toImpCExpr dests expr
  Atom atom -> do
    xs <- toImpAtom atom
    zipWithM_ copyOrStore dests xs

toImpAtom :: Atom -> ImpM [IExpr]
toImpAtom atom = case atom of
  Var v _ -> lookupVar v
  PrimCon con -> case con of
    Lit x -> return [ILit x]
    MemRef _ refs -> return $ map IRef refs
    RecCon _ r -> liftM fold $ mapM toImpAtom r
    TabGet x i -> do
      i' <- toImpScalarAtom i
      xs <- toImpAtom x
      mapM (loadIfScalar . flip IGet i') xs
    IdxLit _ i   -> return [ILit (IntLit i)]
    RecGet x i -> do
      xs <- toImpAtom x
      let (RecType _ rTy) = getType x
      return $ snd $ recGet (listIntoRecord rTy xs) i
    MemRef _ refs -> return $ map IRef refs
    _ -> error $ "Not implemented: " ++ pprint atom
  _ -> error $ "Not a scalar atom: " ++ pprint atom

toImpScalarAtom :: Atom -> ImpM IExpr
toImpScalarAtom atom = do
  atom' <- toImpAtom atom
  case atom' of [x] -> return x
                _   -> error "Expected scalar"

toImpCExpr :: [IExpr] -> CExpr -> ImpM ()
toImpCExpr dests op = case op of
  Scan x ~(LamExpr b@(v:> (RecType _ (Tup [n, cTy]))) body) -> do
    carryTys <- toImpArrayType cTy
    let (carryOutDests, mapDests) = splitAt (length carryTys) dests
    n' <- typeToSize n
    xs' <- toImpAtom x
    zipWithM_ copyOrStore carryOutDests xs'
    withAllocs carryTys $ \carryTmpDests -> do
       (i', (_, loopBody)) <- scoped $ do
           zipWithM_ copy carryTmpDests carryOutDests
           carryTmpVals <- mapM loadIfScalar carryTmpDests
           i' <- freshName "i"
           let iVar = IVar i' intTy
           extendR (v @> (iVar:carryTmpVals)) $ do
              let indexedDests = [IGet d iVar | d <- mapDests]
              toImpExpr (carryOutDests ++ indexedDests) $ body
           return i'
       emitStatement (Nothing, Loop i' n' loopBody)
  TabCon _ rows -> do
    rows' <- mapM toImpAtom rows
    void $ sequence [zipWithM_ copyOrStore (indexedDests i) row
                    | (i, row) <- zip [0..] rows']
    where indexedDests i = [IGet d (ILit (IntLit i)) | d <- dests]
  MonadRun rArgs sArgs m -> do
    rArgs' <- toImpAtom rArgs
    sArgs' <- toImpAtom sArgs
    zipWithM_ copyOrStore sDests sArgs'
    mapM_ initializeZero wDests
    toImpAction (rArgs', wDests, sDests) aDests m
    where (aDests, wDests, sDests) = splitRunDests eff a dests
          ~(Monad eff a) = getType m
  LensGet x l -> do
    x' <- toImpAtom x
    ansRefs <- mapM (lensGet l) x'
    zipWithM_ copyOrStore dests ansRefs
  IntAsIndex n i -> do
    i' <- toImpScalarAtom i
    n' <- typeToSize n
    ans <- emitInstr $ IPrimOp $
             FFICall "int_to_index_set" [IntType, IntType] IntType [i', n']
    store dest ans
    where [dest] = dests
  Cmp cmpOp ty x y -> do
    x' <- toImpScalarAtom x
    y' <- toImpScalarAtom y
    ans <- emitInstr $ IPrimOp $ ScalarBinOp (op' cmpOp) x' y'
    store dest ans
    where [dest] = dests
          op' = case ty of BaseType RealType -> FCmp
                           _                 -> ICmp
  IdxSetSize n -> typeToSize n      >>= copyOrStore dest where [dest] = dests
  Range      n -> toImpScalarAtom n >>= store       dest where [dest] = dests
  ScalarUnOp IndexAsInt i -> toImpScalarAtom i >>= store dest where [dest] = dests
  _ -> do
    op' <- traverseExpr op
              (return . toImpBaseType)
              toImpScalarAtom
              (const (return ()))
    ans <- emitInstr $ IPrimOp op'
    store dest ans
    where [dest] = dests

bindEnv :: BinderP a -> b -> Env b
bindEnv (v:>_) x = v @> x

withAllocs :: [ArrayType] -> ([IExpr] -> ImpM a) -> ImpM a
withAllocs [] body = body []
withAllocs (ty:tys) body = withAlloc ty $ \x -> withAllocs tys (\xs -> body (x:xs))

withAlloc :: ArrayType -> (IExpr -> ImpM a) -> ImpM a
withAlloc ty body = do
  v <- freshName "x"
  let ty' = IRefType ty
  emitStatement (Just (v :> ty'), Alloc ty)
  ans <- body (IVar v ty')
  emitStatement (Nothing, Free v ty)
  return ans

splitRunDests :: EffectType -> Type -> [IExpr] -> ([IExpr], [IExpr], [IExpr])
splitRunDests (Effect _ w _) a dests = (aDest, wDest, sDest)
  where
    nw = length (flattenType w)
    na = length (flattenType a)
    (aDest, dests') = splitAt na dests
    (wDest, sDest)  = splitAt nw dests'

type MContext = ([IExpr], [IExpr], [IExpr])

toImpActionExpr :: MContext -> [IExpr] -> Expr -> ImpM ()
toImpActionExpr mdests dests expr = case expr of
  Decl (Let b@(_:>ty) bound) body -> do
    tys <- toImpArrayType ty
    withAllocs tys $ \bsDests -> do
      toImpCExpr bsDests bound
      xs <- mapM loadIfScalar bsDests
      extendR (bindEnv b xs) $ toImpActionExpr mdests dests body
  Atom m -> toImpAction mdests dests m
  _ -> error $ "Unexpected expression " ++ pprint expr

toImpAction :: MContext -> [IExpr] -> Atom -> ImpM ()
toImpAction mdests@(rVals, wDests, sDests) outDests (PrimCon con) = case con of
  Bind rhs (LamExpr b@(_:>ty) body) -> do
    tys <- toImpArrayType ty
    withAllocs tys $ \bsDests -> do
      toImpAction mdests bsDests rhs
      xs <- mapM loadIfScalar bsDests
      extendR (bindEnv b xs) $ toImpActionExpr mdests outDests body
  Return _ x -> do
    x' <- toImpAtom x
    zipWithM_ copyOrStore outDests x'
  MonadCon _ _ l m -> case m of
    MAsk -> do
      ans <- mapM (lensGet l) rVals
      zipWithM_ copyOrStore outDests ans
    MTell x -> do
      x' <- toImpAtom x
      wDests' <- mapM (lensIndexRef l) wDests
      zipWithM_ addToDest wDests' x'
    MPut x -> do
      x' <- toImpAtom x
      sDests' <- mapM (lensIndexRef l) sDests
      zipWithM_ copyOrStore sDests' x'
    MGet -> do
      ans <- mapM (loadIfScalar >=> lensGet l) sDests
      zipWithM_ copyOrStore outDests ans
  _ -> error $ "Unexpected expression" ++ pprint con

lensGet :: Atom -> IExpr -> ImpM IExpr
lensGet (PrimCon (LensCon lens)) x = case lens of
  LensId _ -> return x
  LensCompose a b -> lensGet a x >>= lensGet b
  IdxAsLens _ i -> do
    ~[i'] <- toImpAtom i
    loadIfScalar $ IGet x i'
lensGet expr _ = error $ "Not a lens expression: " ++ pprint expr

lensIndexRef :: Atom -> IExpr -> ImpM IExpr
lensIndexRef (PrimCon (LensCon lens)) x = case lens of
  LensId _ -> return x
  LensCompose a b -> lensIndexRef a x >>= lensIndexRef b
  IdxAsLens _ i -> do
    ~[i'] <- toImpAtom i
    return $ IGet x i'
lensIndexRef expr _ = error $ "Not a lens expression: " ++ pprint expr

toImpArrayType :: Type -> ImpM [ArrayType]
toImpArrayType ty = case ty of
  BaseType b  -> return [(b, [])]
  TabType a b -> do
    n  <- typeToSize a
    arrTys <- toImpArrayType b
    return [(t, n:shape) | (t, shape) <- arrTys]
  -- TODO: fix this (only works for range)
  RecType _ r -> liftM fold $ traverse toImpArrayType r
  Exists _    -> return [(IntType, [])]
  TypeVar _   -> return [(IntType, [])]
  IdxSetLit _ -> return [(IntType, [])]
  _ -> error $ "Can't lower type to imp: " ++ pprint ty

toImpBaseType :: Type -> BaseType
toImpBaseType ty = case ty of
  BaseType b  -> b
  TabType _ a -> toImpBaseType a
  Exists _    -> IntType
  TypeVar _   -> IntType
  IdxSetLit _ -> IntType
  _ -> error $ "Unexpected type: " ++ pprint ty

loadIfScalar :: IExpr -> ImpM IExpr
loadIfScalar x = case impExprType x of
  IRefType (_, []) -> load x
  IRefType (_, _ ) -> return x
  _ -> error "Expected a reference"

asDest :: IBinder -> IExpr
asDest (v:>ty) = IVar v ty

derefTypeIfScalar :: IType -> IType
derefTypeIfScalar ty = case ty of
  IRefType (b, []) -> IValType b
  IRefType (_, _ ) ->  ty
  _ -> error "Expected a reference"

lookupVar :: Name -> ImpM [IExpr]
lookupVar v = do
  x <- asks $ flip envLookup v
  return $ case x of
    Nothing -> error $ "Lookup failed: " ++ pprint v
    Just v' -> v'

typeToSize :: Type -> ImpM IExpr
typeToSize (TypeVar v) = do
  ~[n] <- lookupVar v
  return n
typeToSize (IdxSetLit n) = return $ ILit (IntLit n)
typeToSize ty = error $ "Not implemented: " ++ pprint ty

copyOrStore :: IExpr -> IExpr -> ImpM ()
copyOrStore dest src = case impExprType src of
  IValType _ -> store dest src
  IRefType _ -> copy  dest src

addToDest :: IExpr -> IExpr -> ImpM ()
addToDest dest src = case impExprType src of
  IValType RealType -> do
    cur <- load dest
    updated <- emitInstr $ IPrimOp $ ScalarBinOp FAdd cur src
    store dest updated
  ty -> error $ "Writing only implemented for scalars" ++ pprint ty

initializeZero :: IExpr -> ImpM()
initializeZero ref = case impExprType ref of
  IRefType (RealType, []) -> store ref (ILit (RealLit 0.0))
  ty -> error $ "Zeros not implemented for type: " ++ pprint ty

copy :: IExpr -> IExpr -> ImpM ()
copy dest src = emitStatement (Nothing, Copy dest src)

load :: IExpr -> ImpM IExpr
load x = emitInstr $ Load x

store :: IExpr -> IExpr -> ImpM ()
store dest src = emitStatement (Nothing, Store dest src)

freshName :: Name -> ImpM Name
freshName v = do
  scope <- looks fst
  let v' = rename v scope
  extend $ asFst (v' @> ())
  return v'

emitStatement :: ImpStatement -> ImpM ()
emitStatement statement = extend $ asSnd $ ImpProg [statement]

emitInstr :: ImpInstr -> ImpM IExpr
emitInstr instr = do
  v <- freshName "v"
  case ignoreExcept (instrType instr) of
    Just ty -> do
      emitStatement (Just (v:>ty), instr)
      return $ IVar v ty
    Nothing -> error "Expected non-void result"

-- -- === Substitutions ===

substIExpr :: Env IExpr -> IExpr -> IExpr
substIExpr env expr = case expr of
  IVar v _ -> case envLookup env v of
                Just x  -> x
                Nothing -> error $ "Lookup failed " ++ pprint expr
  IGet v i -> IGet (substIExpr env v) (substIExpr env i)
  ILit _   -> expr
  IRef _   -> expr

substIType :: Env IExpr -> IType -> IType
substIType env ty = case ty of
  IValType _          -> ty
  IRefType (b, shape) -> IRefType (b, map (substIExpr env) shape)

-- === type checking imp programs ===

type ImpCheckM a = CatT (Env IType) (Either Err) a

checkImp :: TopPass ImpDecl ImpDecl
checkImp = TopPass checkImp'

checkImp' :: ImpDecl -> TopPassM (Env IType) [ImpDecl]
checkImp' decl = [decl] <$ case decl of
  ImpTopLet bs prog -> do
    check bs prog
    -- Scalars are dereferenced after each top-level decl
    extend $ bindFold $ fmap (fmap derefTypeIfScalar) bs
  ImpEvalCmd (Command _ (_, bs, prog)) -> check bs prog
  where
    check :: [IBinder] -> ImpProg -> TopPassM (Env IType) ()
    check bs prog = do
      env <- look
      void $ liftExceptTop $ addContext (pprint prog) $
         runCatT (checkProg prog) (env <> bindFold bs)

checkProg :: ImpProg -> ImpCheckM ()
checkProg (ImpProg statements) =
  mapM_ (\x -> addContext (pprint x) (checkStatement x)) statements

checkStatement :: ImpStatement -> ImpCheckM ()
checkStatement (maybeBinder, instr) = do
  maybeTy <- instrTypeChecked instr
  case (maybeBinder, maybeTy) of
    (Nothing, Nothing) -> return ()
    (Nothing, Just _ ) -> throw CompilerErr $ "Result of non-void instruction must be assigned"
    (Just _ , Nothing) -> throw CompilerErr $ "Can't assign result of void instruction"
    (Just (v:>ty), Just ty') -> do
      env <- look
      when (v `isin` env) $ throw CompilerErr $ "shadows:" ++ pprint v
      checkValidType ty
      assertEq ty ty' "Type mismatch in instruction"
      extend $ v@>ty

instrTypeChecked :: ImpInstr -> ImpCheckM (Maybe IType)
instrTypeChecked instr = case instr of
  IPrimOp op -> return $ Just $ impOpType op -- TODO: check args
  Load ref -> do
    b <- (checkIExpr >=>  fromScalarRefType) ref
    return $ Just $ IValType b
  Store dest val -> do
    b <- (checkIExpr >=> fromScalarRefType) dest
    valTy <- checkIExpr val
    assertEq (IValType b) valTy "Type mismatch in store"
    return Nothing
  Copy dest source -> do
    destTy   <- (checkIExpr >=> fromRefType) dest
    sourceTy <- (checkIExpr >=> fromRefType) source
    assertEq sourceTy destTy "Type mismatch in store"
    return Nothing
  Alloc ty -> return $ Just $ IRefType ty
  Free _ _ -> return Nothing  -- TODO: check matched alloc/free
  Loop i size block -> do
    checkInt size
    void $ scoped $ extend (i @> intTy) >> checkProg block
    return Nothing

checkValidType :: IType -> ImpCheckM ()
checkValidType (IValType _         ) = return ()
checkValidType (IRefType (_, shape)) = mapM_ checkInt shape

checkIExpr :: IExpr -> ImpCheckM IType
checkIExpr expr = case expr of
  ILit val -> return $ IValType (litType val)
  -- TODO: check shape matches vector length
  IRef (Array shape vec) -> return $ IRefType (b, shape')
    where (_, b, _) = vecRefInfo vec
          shape' = map (ILit . IntLit) shape
  IVar v _ -> looks $ (! v)
  IGet e i -> do
    ~(IRefType (b, (_:shape))) <- checkIExpr e
    checkInt i
    return $ IRefType (b, shape)

checkInt :: IExpr -> ImpCheckM ()
checkInt expr = do
  ty <- checkIExpr expr
  assertEq (IValType IntType) ty $ "Not an int: " ++ pprint expr

fromRefType :: MonadError Err m => IType -> m ArrayType
fromRefType (IRefType ty) = return ty
fromRefType ty = throw CompilerErr $ "Not a reference type: " ++ pprint ty

fromScalarRefType :: MonadError Err m => IType -> m BaseType
fromScalarRefType (IRefType (b, [])) = return b
fromScalarRefType ty = throw CompilerErr $ "Not a scalar reference type: " ++ pprint ty

impExprType :: IExpr -> IType
impExprType expr = case expr of
  ILit v    -> IValType (litType v)
  IRef (Array shape vec) -> IRefType (b, shape')
    where (_, b, _) = vecRefInfo vec
          shape' = map (ILit . IntLit) shape
  IVar _ ty -> ty
  IGet e _  -> case impExprType e of
    IRefType (b, (_:shape)) -> IRefType (b, shape)
    ty -> error $ "Can't index into: " ++ pprint ty

instrType :: MonadError Err m => ImpInstr -> m (Maybe IType)
instrType instr = case instr of
  IPrimOp op      -> return $ Just $ impOpType op
  Load ref        -> liftM (Just . IValType) $ fromScalarRefType (impExprType ref)
  Store _ _       -> return Nothing
  Copy  _ _       -> return Nothing
  Alloc ty        -> return $ Just $ IRefType ty
  Free _ _        -> return Nothing
  Loop _ _ _      -> return Nothing

impOpType :: IPrimOp -> IType
impOpType (ScalarBinOp op _ _) = IValType ty  where (_, _, ty) = binOpType op
impOpType (ScalarUnOp  op _  ) = IValType ty  where (_,    ty) = unOpType  op
impOpType (Select ty _ _ _   ) = IValType ty
impOpType (FFICall _ _ ty _  ) = IValType ty
impOpType op = error $ "Not allowed in Imp IR: " ++ pprint op

intTy :: IType
intTy = IValType IntType

realTy :: IType
realTy = IValType RealType

boolTy :: IType
boolTy = IValType BoolType
