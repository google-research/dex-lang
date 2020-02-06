-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

module Imp (toImpModule, checkImpModule, impExprToAtom, impExprType) where

import Control.Applicative
import Control.Monad.Reader
import Control.Monad.Except hiding (Except)
import Data.Foldable
import Data.Traversable

import Syntax
import Env
import Type
import PPrint
import Cat
import Serialize
import Fresh
import Subst
import Record
import Embed (wrapDecls)

type ImpEnv = Env IAtom
type EmbedEnv = (Scope, ImpProg)
type ImpM a = ReaderT ImpEnv (Cat EmbedEnv) a

data IAtomP a = ILeaf a | ICon (PrimCon Type (IAtomP a) ())  deriving (Show)
type IAtom = IAtomP IExpr

toImpModule :: Module -> ImpModule
toImpModule m = ImpModule vs prog result
  where ((vs, result), (_, prog)) =
          runCat (runReaderT (toImpModule' m) mempty) mempty

toImpModule' :: Module -> ImpM ([IVar], TopEnv)
toImpModule' (Module _ decls result) = do
  let vs = resultVars result
  outAllocs <- mapM topAlloc vs
  let outTuple = PrimCon $ RecCon $ Tup $ map Var vs
  let outDests = ICon    $ RecCon $ Tup $ outAllocs
  toImpExpr (fmap IVar outDests) (wrapDecls decls outTuple)
  let substEnv = fold [v @> L (impAtomToAtom (fmap IVar out))
                      | (v, out) <- zip vs outAllocs]
  let flatAllocVars = concat $ map toList outAllocs
  return (flatAllocVars, subst (substEnv, mempty) result)

resultVars :: TopEnv -> [Var]
resultVars env = [v:>ty | (v, L ty) <- envPairs $ freeVars env]

topAlloc :: Var -> ImpM (IAtomP IVar)
topAlloc (v:>ty) = do
  tys <- toImpArrayType [] ty
  flip traverse tys $ \impTy -> freshVar (v :> IRefType impTy)

toImpExpr :: IAtom -> Expr -> ImpM ()
toImpExpr dests expr = case expr of
  Decl (Let b bound) body -> do
    withAllocs b $ \bDests -> do
      toImpCExpr bDests bound
      xs <- mapM loadIfScalar bDests
      extendR (b @> xs) $ toImpExpr dests body
  CExpr e   -> toImpCExpr dests e
  Atom atom -> do
    xs <- toImpAtom atom
    copyOrStoreIAtom dests xs

toImpAtom :: Atom -> ImpM IAtom
toImpAtom atom = case atom of
  Var v -> lookupVar v
  PrimCon con -> case con of
    Lit x        -> return $ ILeaf $ ILit x
    MemRef _ ref -> return $ ILeaf $ IRef ref
    RecCon r     -> liftM (ICon . RecCon) $ mapM toImpAtom r
    TabGet x i -> do
      i' <- toImpScalarAtom i
      xs <- toImpAtom x
      traverse loadIfScalar $ indexIAtom xs i'
    IdxLit _ i   -> return $ ILeaf (ILit (IntLit i))
    RecGet x i -> do
      x' <- toImpAtom x
      case x' of
        ICon (RecCon r)-> return $ recGet r i
        val -> error $ "Expected a record, got: " ++ show val
    _ -> error $ "Not implemented: " ++ pprint atom
  _ -> error $ "Not a scalar atom: " ++ pprint atom

toImpScalarAtom :: Atom -> ImpM IExpr
toImpScalarAtom atom = do
  atom' <- toImpAtom atom
  case atom' of ILeaf x -> return x
                _       -> error "Expected scalar"

toImpCExpr :: IAtom -> CExpr -> ImpM ()
toImpCExpr dests op = case op of
  TabCon _ rows -> do
    rows' <- mapM toImpAtom rows
    void $ sequence [copyOrStoreIAtom (indexIAtom dests $ ILit (IntLit i)) row
                    | (i, row) <- zip [0..] rows']
  For (LamExpr b body) -> do
    n' <- typeToSize (varAnn b)
    emitLoop n' $ \i -> do
      let ithDest = indexIAtom dests i
      extendR (b @> ILeaf i) $ toImpExpr ithDest body
  MonadRun rArgs sArgs m -> do
    rArgs' <- toImpAtom rArgs
    sArgs' <- toImpAtom sArgs
    copyOrStoreIAtom sDests sArgs'
    mapM_ initializeZero wDests
    toImpAction (rArgs', wDests, sDests) aDests m
    where (ICon (RecCon (Tup [aDests, wDests, sDests]))) = dests
  LensGet x l -> do
    x' <- toImpAtom x
    ansRefs <- mapM (lensGet l) x'
    copyOrStoreIAtom dests ansRefs
  IntAsIndex n i -> do
    i' <- toImpScalarAtom i
    n' <- typeToSize n
    ans <- emitInstr $ IPrimOp $
             FFICall "int_to_index_set" [IntType, IntType] IntType [i', n']
    store dest ans
    where (ILeaf dest) = dests
  Cmp cmpOp ty x y -> do
    x' <- toImpScalarAtom x
    y' <- toImpScalarAtom y
    ans <- emitInstr $ IPrimOp $ ScalarBinOp (op' cmpOp) x' y'
    store dest ans
    where (ILeaf dest) = dests
          op' = case ty of BaseType RealType -> FCmp
                           _                 -> ICmp
  IdxSetSize n -> do
    n' <- typeToSize n
    copyOrStore dest n'
    where (ILeaf dest) = dests
  ScalarUnOp IndexAsInt i -> toImpScalarAtom i >>= store dest
    where (ILeaf dest) = dests
  _ -> do
    op' <- traverseExpr op
              (return . toImpBaseType)
              toImpScalarAtom
              (const (return ()))
    ans <- emitInstr $ IPrimOp op'
    store dest ans
    where ~(ILeaf dest) = dests

withAllocs :: Var -> (IAtom -> ImpM a) -> ImpM a
withAllocs (_:>ty) body = do
  dest <- toImpArrayType [] ty >>= mapM newAlloc
  ans <- body dest
  flip mapM_ dest $ \(IVar v) -> emitStatement (Nothing, Free v)
  return ans

newAlloc :: ArrayType -> ImpM IExpr
newAlloc ty = do
  v <- freshVar ("x" :> IRefType ty)
  emitStatement (Just v, Alloc ty)
  return $ IVar v

type MContext = (IAtom, IAtom, IAtom)

toImpActionExpr :: MContext -> IAtom -> Expr -> ImpM ()
toImpActionExpr mdests dests expr = case expr of
  Decl (Let b bound) body -> do
    withAllocs b $ \bsDests -> do
      toImpCExpr bsDests bound
      xs <- mapM loadIfScalar bsDests
      extendR (b @> xs) $ toImpActionExpr mdests dests body
  Atom m -> toImpAction mdests dests m
  _ -> error $ "Unexpected expression " ++ pprint expr

toImpAction :: MContext -> IAtom -> Atom -> ImpM ()
toImpAction mdests@(rVals, wDests, sDests) outDests (PrimCon con) = case con of
  Bind rhs (LamExpr b body) -> do
    withAllocs b $ \bsDests -> do
      toImpAction mdests bsDests rhs
      xs <- mapM loadIfScalar bsDests
      extendR (b @> xs) $ toImpActionExpr mdests outDests body
  Return _ x -> do
    x' <- toImpAtom x
    copyOrStoreIAtom outDests x'
  Seq (LamExpr b body) -> do
    n' <- typeToSize (varAnn b)
    emitLoop n' $ \i -> do
      let ithDest = indexIAtom outDests i
      extendR (b @> ILeaf i) $ toImpActionExpr mdests ithDest body
  MonadCon _ _ l m -> case m of
    MAsk -> do
      ans <- mapM (lensGet l) rVals
      copyOrStoreIAtom outDests ans
    MTell x -> do
      x' <- toImpAtom x
      wDests' <- mapM (lensIndexRef l) wDests
      zipWithM_ addToDest (toList wDests') (toList x')
    MPut x -> do
      x' <- toImpAtom x
      sDests' <- mapM (lensIndexRef l) sDests
      copyOrStoreIAtom sDests' x'
    MGet -> do
      ans <- mapM loadIfScalar sDests >>= mapM (lensGet l)
      copyOrStoreIAtom outDests ans
  _ -> error $ "Unexpected expression" ++ pprint con

lensGet :: Atom -> IExpr -> ImpM IExpr
lensGet (PrimCon (LensCon lens)) x = case lens of
  LensId _ -> return x
  LensCompose a b -> lensGet a x >>= lensGet b
  IdxAsLens _ i -> do
    i' <- toImpScalarAtom i
    loadIfScalar $ IGet x i'
lensGet expr _ = error $ "Not a lens expression: " ++ pprint expr

lensIndexRef :: Atom -> IExpr -> ImpM IExpr
lensIndexRef (PrimCon (LensCon lens)) x = case lens of
  LensId _ -> return x
  LensCompose a b -> lensIndexRef a x >>= lensIndexRef b
  IdxAsLens _ i -> do
    ~(ILeaf i') <- toImpAtom i
    return $ IGet x i'
lensIndexRef expr _ = error $ "Not a lens expression: " ++ pprint expr

indexIAtom :: IAtom -> IExpr -> IAtom
indexIAtom x i = case x of
  ICon (RecZip _ r) -> ICon $ RecCon $ fmap (flip indexIAtom i) r
  ILeaf x' -> ILeaf $ IGet x' i
  _ -> error $ "Unexpected atom: " ++ show x

toImpArrayType :: [IExpr] -> Type -> ImpM (IAtomP ArrayType)
toImpArrayType ns ty = case ty of
  BaseType b  -> return $ ILeaf (b, ns)
  -- TODO: zip if element type is a record
  TabType a b -> do
    n  <- typeToSize a
    toImpArrayType (ns ++ [n]) b
  RecType r -> case ns of
    [] -> liftM (ICon . RecCon    ) $ traverse (toImpArrayType ns) r
    _  -> liftM (ICon . RecZip ns') $ traverse (toImpArrayType ns) r
    where
      ns' = map fromIntLit ns
      fromIntLit (ILit (IntLit n)) = n
  TypeVar _   -> return $ ILeaf (IntType, ns)
  IdxSetLit _ -> return $ ILeaf (IntType, ns)
  _ -> error $ "Can't lower type to imp: " ++ pprint ty

impExprToAtom :: IExpr -> Atom
impExprToAtom e = case e of
  IVar (v:>ty) -> Var (v:> impTypeToType ty)
  ILit x       -> PrimCon $ Lit x
  IRef ref     -> PrimCon $ MemRef ty ref
    where (Array shape vec) = ref
          (_, b, _) = vecRefInfo vec
          ty = foldr TabType (BaseType b) (map IdxSetLit shape)
  _ -> error "Not implemented"

impTypeToType :: IType -> Type
impTypeToType (IValType b) = BaseType b
impTypeToType (IRefType (b, shape)) =
  foldr (\(ILit (IntLit n)) a -> TabType (IdxSetLit n) a) (BaseType b) shape

impAtomToAtom :: IAtom -> Atom
impAtomToAtom (ILeaf e) = impExprToAtom e
impAtomToAtom (ICon con) = PrimCon $ fmapExpr con id impAtomToAtom (const undefined)

toImpBaseType :: Type -> BaseType
toImpBaseType ty = case ty of
  BaseType b  -> b
  TabType _ a -> toImpBaseType a
  TypeVar _   -> IntType
  IdxSetLit _ -> IntType
  _ -> error $ "Unexpected type: " ++ pprint ty

loadIfScalar :: IExpr -> ImpM IExpr
loadIfScalar x = case impExprType x of
  IRefType (_, []) -> load x
  IRefType (_, _ ) -> return x
  _ -> error "Expected a reference"

lookupVar :: VarP a -> ImpM IAtom
lookupVar v = do
  x <- asks $ flip envLookup v
  return $ case x of
    Nothing -> error $ "Lookup failed: " ++ pprint (varName v)
    Just v' -> v'

typeToSize :: Type -> ImpM IExpr
typeToSize (TypeVar v) = do
  ~(ILeaf n) <- lookupVar v
  return n
typeToSize (IdxSetLit n) = return $ ILit (IntLit n)
typeToSize ty = error $ "Not implemented: " ++ pprint ty

copyOrStoreIAtom :: IAtom -> IAtom -> ImpM ()
copyOrStoreIAtom dest src = zipWithM_ copyOrStore (toList dest) (toList src)

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

initializeZero :: IExpr -> ImpM ()
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

emitLoop :: IExpr -> (IExpr -> ImpM ()) -> ImpM ()
emitLoop n body = do
  (i, (_, loopBody)) <- scoped $ do
    i <- freshVar ("i":>intTy)
    body $ IVar i
    return i
  emitStatement (Nothing, Loop i n loopBody)

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
checkImpModule (ImpModule vs prog _) = void $ runCatT (checkProg prog) env
  where env = foldMap (\v -> v@> varAnn v) vs

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

instance Functor IAtomP where
  fmap = fmapDefault

instance Foldable IAtomP where
  foldMap = foldMapDefault

instance Traversable IAtomP where
  traverse f (ILeaf x) = liftA ILeaf (f x)
  traverse f (ICon con) = liftA ICon $ traverseExpr con pure (traverse f) pure
