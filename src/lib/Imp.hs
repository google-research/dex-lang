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
  NTopDecl _ (NLet (v:>ty) bound) -> do
    tys' <- toImpTypeTop ty
    (env, scope) <- look
    let (vs, scope') = renames (replicate (length tys') v) scope
    let bs' = zipWith (:>) vs tys'
    extend $ asSnd scope'
    ((), prog) <- liftTop $ toImp (map asDest bs') bound
    let xs = [IVar v' (derefTypeIfScalar ty') | (v':>ty') <- bs']
    extend $ asFst $ v@>xs
    return [ImpTopLet bs' prog]
  NTopDecl _ (NUnpack _ tv bound) -> do
    let b = tv:>(IRefType (IntType,[]))
    ((), prog) <- liftTop $ toImp [asDest b] bound
    extend (tv @> [IVar tv intTy], tv @> ())
    return [ImpTopLet [b] prog]
  NRuleDef _ _ _ -> error "Shouldn't have this left"
  NEvalCmd (Command cmd (ty, expr)) -> do
    ts <- toImpTypeTop (getNExprType expr)
    let bs = [Name "%imptmp" i :> t | (i, t) <- zip [0..] ts]
    ((), prog) <- liftTop $ toImp (map asDest bs) expr
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

toImp :: [IExpr] -> NExpr -> ImpM ()
toImp dests expr = case expr of
  NDecl (NLet b@(_:>ty) bound) body -> do
    tys <- toImpArrayType ty
    withAllocs tys $ \bDests -> do
      toImp bDests bound
      xs <- mapM loadIfScalar bDests
      extendR (bindEnv b xs) $ toImp dests body
  NDecl (NUnpack _ tv bound) body -> do
    withAllocs [(IntType, [])] $ \[tvDest] -> do
       toImp [tvDest] bound
       x <- load tvDest
       extendR (tv @> [x]) $ toImp dests body
  NScan x (NLamExpr ~[i:>n, b@(_:>ty)] body) -> do
    x' <- toImpAtom x
    n' <- typeToSize n
    carryTys <- toImpArrayType ty
    let (carryOutDests, mapDests) = splitAt (length carryTys) dests
    zipWithM_ copyOrStore carryOutDests x'
    withAllocs carryTys $ \carryTmpDests -> do
       (i', (_, loopBody)) <- scoped $ do
           zipWithM_ copy carryTmpDests carryOutDests
           carryTmpVals <- mapM loadIfScalar carryTmpDests
           i' <- freshName i
           let iVar = IVar i' intTy
           extendR (i @> [iVar] <> bindEnv b carryTmpVals) $ do
              let indexedDests = [IGet d iVar | d <- mapDests]
              toImp (carryOutDests ++ indexedDests) $ body
           return i'
       emitStatement (Nothing, Loop i' n' loopBody)
  NPrimOp MRun ts ~[rArgs, sArgs, m] -> do
    let (aDests, wDests, sDests) = splitRunDests ts dests
    rArgs' <- toImpAtom rArgs
    sArgs' <- toImpAtom sArgs
    zipWithM_ copyOrStore sDests sArgs'
    mapM_ initializeZero wDests
    toImpAction (rArgs', wDests, sDests) aDests m
  NPrimOp LensGet _ ~[x, l] -> do
    x' <- toImpAtom x
    ansRefs <- mapM (lensGet l) x'
    zipWithM_ copyOrStore dests ansRefs
  NPrimOp IdxSetSize ~[n] _ -> do
    n' <- typeToSize n
    let [dest] = dests
    copyOrStore dest n'
  NPrimOp IntAsIndex ~[n] ~[i] -> do
    ~[i'] <- toImpAtom i
    n' <- typeToSize n
    let op = FFICall 2 "int_to_index_set"
    ans <- emitInstr $ IPrimOp op [IntType, IntType, IntType] [i', n']
    let [dest] = dests
    store dest ans
  NPrimOp b ts xs -> do
    let ts' = map toImpBaseType ts
    xs' <- mapM toImpAtom xs
    toImpPrimOp b dests ts' (concat xs')
  NRecGet xs i -> do
    let (RecType _ r) = atomType xs
    xs' <- toImpAtom xs
    let x = snd $ recGet (listIntoRecord r xs') i
    zipWithM_ copyOrStore dests x
  NAtom x -> do
    xs' <- toImpAtom x
    zipWithM_ copyOrStore dests xs'
  NTabCon _ _ xs -> do
    xs' <- mapM toImpAtom xs
    void $ sequence [copyOrStore (indexedDest d i) x | (i, row) <- zip [0..] xs'
                                                     , (x, d) <- zip row dests]
    where indexedDest dest i = IGet dest (ILit (IntLit i))
  NApp _ _ -> error "NApp should be gone by now"

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

splitRunDests :: [Type] -> [IExpr] -> ([IExpr], [IExpr], [IExpr])
splitRunDests ts dests = (aDest, wDest, sDest)
  where
    [_, nw, _, na] = map (length . flattenType) ts
    (aDest, dests') = splitAt na dests
    (wDest, sDest)  = splitAt nw dests'

toImpAtom :: NAtom -> ImpM [IExpr]
toImpAtom atom = case atom of
  NLit x   -> return [ILit x]
  NVar v _ -> lookupVar v
  NGet x i -> do
    ~[i'] <- toImpAtom i
    x' <- toImpAtom x
    mapM (loadIfScalar . flip IGet i') x'
  NRecCon _ r -> liftM fold $ traverse toImpAtom r
  _ -> error $ "Not implemented: " ++ pprint atom

type MContext = ([IExpr], [IExpr], [IExpr])

toImpActionExpr :: MContext -> [IExpr] -> NExpr -> ImpM ()
toImpActionExpr mdests dests expr = case expr of
  NDecl (NLet b@(_:>ty) bound) body -> do
    tys <- toImpArrayType ty
    withAllocs tys $ \bsDests -> do
      toImp bsDests bound
      xs <- mapM loadIfScalar bsDests
      extendR (bindEnv b xs) $ toImpActionExpr mdests dests body
  NAtom m -> toImpAction mdests dests m
  _ -> error $ "Unexpected expression " ++ pprint expr

toImpAction :: MContext -> [IExpr] -> NAtom -> ImpM ()
toImpAction mdests@(rVals, wDests, sDests) outDests m = case m of
  NDoBind rhs (NLamExpr ~[b@(_:>ty)] body) -> do
    tys <- toImpArrayType ty
    withAllocs tys $ \bsDests -> do
      toImpAction mdests bsDests rhs
      xs <- mapM loadIfScalar bsDests
      extendR (bindEnv b xs) $ toImpActionExpr mdests outDests body
  NAtomicPrimOp (MPrim MReturn) _ ~[x] -> toImp outDests (NAtom x)
  NAtomicPrimOp (MPrim p) _ ~(l:args) -> case p of
    MAsk -> do
      ans <- mapM (lensGet l) rVals
      zipWithM_ copyOrStore outDests ans
    MTell-> do
      x' <- toImpAtom x
      wDests' <- mapM (lensIndexRef l) wDests
      zipWithM_ addToDest wDests' x'
      where [x] = args
    MPut -> do
      x' <- toImpAtom x
      sDests' <- mapM (lensIndexRef l) sDests
      zipWithM_ copyOrStore sDests' x'
      where [x] = args
    MGet -> do
      ans <- mapM (loadIfScalar >=> lensGet l) sDests
      zipWithM_ copyOrStore outDests ans
    MReturn -> error "shouldn't be able to get here"
  _ -> error $ "Unexpected expression" ++ pprint m

lensGet :: NAtom -> IExpr -> ImpM IExpr
lensGet (NAtomicPrimOp (LensPrim lens) _ args) x = case (lens, args) of
  (LensId     , ~[])     -> return x
  (LensCompose, ~[a, b]) -> lensGet a x >>= lensGet b
  (IdxAsLens  , ~[i])    -> do
    ~[i'] <- toImpAtom i
    loadIfScalar $ IGet x i'
lensGet expr _ = error $ "Not a lens expression: " ++ pprint expr

lensIndexRef :: NAtom -> IExpr -> ImpM IExpr
lensIndexRef (NAtomicPrimOp (LensPrim lens) _ args) x = case (lens, args) of
  (LensId     , ~[])     -> return x
  (LensCompose, ~[a, b]) -> lensIndexRef a x >>= lensIndexRef b
  (IdxAsLens  , ~[i])    -> do
    ~[i'] <- toImpAtom i
    return $ IGet x i'

lensIndexRef expr _ = error $ "Not a lens expression: " ++ pprint expr

toImpPrimOp :: Builtin -> [IExpr] -> [BaseType] -> [IExpr] -> ImpM ()
toImpPrimOp Range      (dest:_) _ [x] = store dest x
toImpPrimOp IndexAsInt [dest]   _ [x] = store dest x
toImpPrimOp (MemRef refs) dests _ [] =
  sequence_ [copy d (IRef r) | (d, r) <- zip dests refs]
toImpPrimOp b [dest] ts xs = do
  ans <- emitInstr $ IPrimOp b ts xs
  store dest ans
toImpPrimOp b dests _ _ = error $ "Can't compile primop: " ++ show (b, dests)

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
    updated <- emitInstr $ IPrimOp FAdd [] [cur, src]
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

-- === Substitutions ===

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
  IPrimOp b tys xs -> do
    (argTys, outTy) <- impBuiltinType b tys
    argTys' <- mapM checkIExpr xs
    assertEq argTys argTys' "Type mismatch in primop args"
    return outTy
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

impBuiltinType :: MonadError Err m => Builtin -> [BaseType] -> m ([IType], Maybe IType)
impBuiltinType IAdd [] = return ([intTy, intTy], Just intTy)
impBuiltinType ISub [] = return ([intTy, intTy], Just intTy)
impBuiltinType IMul [] = return ([intTy, intTy], Just intTy)
impBuiltinType Rem  [] = return ([intTy, intTy], Just intTy)
impBuiltinType FAdd [] = return ([realTy, realTy], Just realTy)
impBuiltinType FSub [] = return ([realTy, realTy], Just realTy)
impBuiltinType FMul [] = return ([realTy, realTy], Just realTy)
impBuiltinType FDiv [] = return ([realTy, realTy], Just realTy)
impBuiltinType FNeg [] = return ([realTy], Just realTy)
impBuiltinType (Cmp _) [IntType ] = return ([intTy , intTy ], Just boolTy)
impBuiltinType (Cmp _) [RealType] = return ([realTy, realTy], Just boolTy)
impBuiltinType And [] = return ([boolTy, boolTy], Just boolTy)
impBuiltinType Or  [] = return ([boolTy, boolTy], Just boolTy)
impBuiltinType Not [] = return ([boolTy]        , Just boolTy)
impBuiltinType Select [ty] = return ([boolTy, ty', ty'], Just ty')  where ty' = IValType ty
impBuiltinType BoolToInt [] = return ([boolTy], Just intTy)
impBuiltinType IntToReal [] = return ([intTy] , Just realTy)
impBuiltinType (FFICall _ _) (retTy:argTys) = return (map IValType argTys, Just (IValType retTy))
impBuiltinType b ts = throw CompilerErr $ "Bad Imp builtin: " ++ pprint b ++ " @ " ++ pprint ts

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
  IPrimOp b tys _ -> liftM snd $ impBuiltinType b tys
  Load ref        -> liftM (Just . IValType) $ fromScalarRefType (impExprType ref)
  Store _ _       -> return Nothing
  Copy  _ _       -> return Nothing
  Alloc ty        -> return $ Just $ IRefType ty
  Free _ _        -> return Nothing
  Loop _ _ _      -> return Nothing

intTy :: IType
intTy = IValType IntType

realTy :: IType
realTy = IValType RealType

boolTy :: IType
boolTy = IValType BoolType
