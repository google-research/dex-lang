-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

module Imp (toImpModule, checkImpModule, impExprType, impExprToAtom) where

import Control.Monad.Reader
import Control.Monad.Except hiding (Except)
import Data.Foldable

import Syntax
import Env
import Type
import PPrint
import Cat
import Serialize
import Fresh
import Subst
import Record

type ImpEnv = Env (Type, [IExpr])
type EmbedEnv = (Scope, ImpProg)
type ImpM a = ReaderT ImpEnv (Cat EmbedEnv) a

-- TODO: free refs that aren't exported
toImpModule :: Module -> ImpModule
toImpModule (Module decls result) = ImpModule vs prog env
  where
    ((vs, env), prog) = runImpM $ do
                          (bs, substEnv) <- toImpTopDecls decls
                          return (bs, subst (substEnv, mempty) result)

runImpM :: ImpM a -> (a, ImpProg)
runImpM m = (ans, prog)
  where (ans, (_, prog)) = runCat (runReaderT m mempty) mempty

toImpTopDecls :: [Decl] -> ImpM ([IVar], FullEnv Atom Type)
toImpTopDecls [] = return ([], mempty)
toImpTopDecls (decl:decls) = do
  (env, vs, substEnv) <- toImpTopDecl decl
  (vs', substEnv') <- extendR env $ toImpTopDecls decls
  return (vs ++ vs', substEnv' <> substEnv)

toImpTopDecl :: Decl -> ImpM (ImpEnv, [IVar], FullEnv Atom Type)
toImpTopDecl decl = case decl of
  Let b@(_:>ty) bound -> do
    tys <- toImpArrayType ty
    vs <- sequence [freshVar ("x" :> IRefType t) | t <- tys]
    let dests = map IVar vs
    toImpCExpr dests bound
    xs <- mapM loadIfScalar dests
    return (b @> (ty, xs), vs, b @> L (impExprsToAtom (ty, dests)))

toImpExpr :: [IExpr] -> Expr -> ImpM ()
toImpExpr dests expr = case expr of
  Decl (Let b@(_:>ty) bound) body -> do
    tys <- toImpArrayType ty
    withAllocs tys $ \bDests -> do
      toImpCExpr bDests bound
      xs <- mapM loadIfScalar bDests
      extendR (b @> (ty, xs)) $ toImpExpr dests body
  Decl (Unpack (_:>ty) tv bound) body -> do
    x <- toImpAtom bound
    extendR (tv @> (ty, x)) $ toImpExpr dests body
  CExpr e   -> toImpCExpr dests e
  Atom atom -> do
    xs <- toImpAtom atom
    zipWithM_ copyOrStore dests xs

toImpAtom :: Atom -> ImpM [IExpr]
toImpAtom atom = case atom of
  Var v -> lookupVar v
  PrimCon con -> case con of
    Lit x -> return [ILit x]
    MemRef _ ref -> return [IRef ref]
    RecCon r -> liftM fold $ mapM toImpAtom r
    TabGet x i -> do
      i' <- toImpScalarAtom i
      xs <- toImpAtom x
      mapM (loadIfScalar . flip IGet i') xs
    IdxLit _ i   -> return [ILit (IntLit i)]
    RecGet x i -> do
      xs <- toImpAtom x
      let (RecType rTy) = getType x
      return $ snd $ recGet (listIntoRecord rTy xs) i
    _ -> error $ "Not implemented: " ++ pprint atom
  _ -> error $ "Not a scalar atom: " ++ pprint atom

impExprsToAtom :: (Type, [IExpr]) -> Atom
impExprsToAtom (ty, xs) = restructureAtom ty $ map impExprToAtom xs

impExprToAtom :: IExpr -> Atom
impExprToAtom e = case e of
  IVar (v:>ty) -> Var (v:> impTypeToType ty)
  ILit x       -> PrimCon $ Lit x
  IRef ref     -> PrimCon $ MemRef ty ref
    where (Array shape vec) = ref
          (_, b, _) = vecRefInfo vec
          ty = foldr TabType (BaseType b) (map IdxSetLit shape)
  IGet _ _ -> error "Not implemented"

-- TODO: possibly avoid this by maintaining atoms in the env instead of [IExpr]
restructureAtom :: Type -> [Atom] -> Atom
restructureAtom (BaseType _) [x] = x
restructureAtom (IdxSetLit n) [x] = PrimCon (AsIdxAtomic n x)
restructureAtom (RecType r ) xs = PrimCon $ RecCon $
  fmap (uncurry restructureAtom) $ listIntoRecord r xs
restructureAtom (TabType n a) xs = PrimCon $ AtomicFor (LamExpr i (Atom body))
  where
    i = rename ("i":>n) (foldMap freeVars xs)
    body = restructureAtom a [PrimCon $ TabGet x (Var i) | x <- xs]
restructureAtom ty x = error $ "Can't restructure: " ++ pprint (ty, x)

impTypeToType :: IType -> Type
impTypeToType (IValType b) = BaseType b
impTypeToType (IRefType (b, shape)) =
  foldr (\(ILit (IntLit n)) a -> TabType (IdxSetLit n) a) (BaseType b) shape

toImpScalarAtom :: Atom -> ImpM IExpr
toImpScalarAtom atom = do
  atom' <- toImpAtom atom
  case atom' of [x] -> return x
                _   -> error "Expected scalar"

toImpCExpr :: [IExpr] -> CExpr -> ImpM ()
toImpCExpr dests op = case op of
  Scan x (LamExpr b body) -> do
    let (RecType (Tup [n, cTy])) = varAnn b
    carryTys <- toImpArrayType cTy
    let (carryOutDests, mapDests) = splitAt (length carryTys) dests
    n' <- typeToSize n
    xs' <- toImpAtom x
    zipWithM_ copyOrStore carryOutDests xs'
    withAllocs carryTys $ \carryTmpDests -> do
       (i', (_, loopBody)) <- scoped $ do
           zipWithM_ copy carryTmpDests carryOutDests
           carryTmpVals <- mapM loadIfScalar carryTmpDests
           i' <- freshVar ("i":>intTy)
           let iVar = IVar i'
           extendR (b @> (varAnn b, (iVar:carryTmpVals))) $ do
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

withAllocs :: [ArrayType] -> ([IExpr] -> ImpM a) -> ImpM a
withAllocs [] body = body []
withAllocs (ty:tys) body = withAlloc ty $ \x -> withAllocs tys (\xs -> body (x:xs))

withAlloc :: ArrayType -> (IExpr -> ImpM a) -> ImpM a
withAlloc ty body = do
  ~ref@(IVar v) <- newAlloc ty
  ans <- body ref
  emitStatement (Nothing, Free v)
  return ans

newAlloc :: ArrayType -> ImpM IExpr
newAlloc ty = do
  v <- freshVar ("x" :> IRefType ty)
  emitStatement (Just v, Alloc ty)
  return $ IVar v

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
      extendR (b @> (ty, xs)) $ toImpActionExpr mdests dests body
  Atom m -> toImpAction mdests dests m
  _ -> error $ "Unexpected expression " ++ pprint expr

toImpAction :: MContext -> [IExpr] -> Atom -> ImpM ()
toImpAction mdests@(rVals, wDests, sDests) outDests (PrimCon con) = case con of
  Bind rhs (LamExpr b@(_:>ty) body) -> do
    tys <- toImpArrayType ty
    withAllocs tys $ \bsDests -> do
      toImpAction mdests bsDests rhs
      xs <- mapM loadIfScalar bsDests
      extendR (b @> (ty, xs)) $ toImpActionExpr mdests outDests body
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
  RecType r   -> liftM fold $ traverse toImpArrayType r
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

derefTypeIfScalar :: IType -> IType
derefTypeIfScalar ty = case ty of
  IRefType (b, []) -> IValType b
  IRefType (_, _ ) ->  ty
  _ -> error "Expected a reference"

lookupVar :: VarP a -> ImpM [IExpr]
lookupVar v = do
  x <- asks $ flip envLookup v
  return $ case x of
    Nothing -> error $ "Lookup failed: " ++ pprint (varName v)
    Just (_, v') -> v'

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

freshVar :: IVar -> ImpM IVar
freshVar v = do
  scope <- looks fst
  let v' = rename v scope
  extend $ asFst (v' @> ())
  return v'

emitStatement :: ImpStatement -> ImpM ()
emitStatement statement = extend $ asSnd $ ImpProg [statement]

emitInstr :: ImpInstr -> ImpM IExpr
emitInstr instr = do
  case ignoreExcept (instrType instr) of
    Just ty -> do
      v <- freshVar ("v":>ty)
      emitStatement (Just v, instr)
      return $ IVar v
    Nothing -> error "Expected non-void result"

-- === type checking imp programs ===

type ImpCheckM a = CatT (Env IType) (Either Err) a

checkImpModule :: ImpModule -> Except ()
checkImpModule m = return ()

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
    (Just v@(_:>ty), Just ty') -> do
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
  Free _   -> return Nothing  -- TODO: check matched alloc/free
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
  IVar v -> looks $ (! v)
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
  IVar (_:>ty) -> ty
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
  Free _          -> return Nothing
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
