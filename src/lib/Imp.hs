-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Imp (toImpModule, impExprToAtom, impExprType) where

import Control.Applicative
import Control.Monad.Reader
import Control.Monad.Except hiding (Except)
import Control.Monad.Writer
import Data.Foldable
import Data.Traversable
import Data.Text.Prettyprint.Doc

import Syntax
import Env
import Type
import PPrint
import Cat
import Subst
import Record
import Embed (wrapDecls)

type ImpEnv = Env IAtom
type EmbedEnv = (Scope, ImpProg)
type ImpM = ReaderT ImpEnv (Cat EmbedEnv)

data IAtomP a = ILeaf a | ICon (PrimCon Type (IAtomP a) ())  deriving (Show)
type IAtom = IAtomP IExpr

toImpModule :: TopEnv -> Module -> ImpModule
toImpModule env (Module ty@(imports, _) m) = Module ty (ImpModBody vs prog result)
  where ((vs, result), (_, prog)) =
          flip runCat mempty $ flip runReaderT mempty $
              toImpModBody env imports m

toImpModBody :: TopEnv -> TypeEnv -> ModBody -> ImpM ([IVar], TopEnv)
toImpModBody topEnv imports (ModBody decls result) = do
  let decls' = map (subst (topSubstEnv topEnv, mempty)) decls
  let vs = [v:>ty | (v, L ty) <- envPairs $ freeVars result `envDiff` imports]
  let outTuple = Con $ RecCon $ Tup $ map Var vs
  (outDest, vs') <- makeDest $ getType outTuple
  let (ICon (RecCon (Tup outDests))) = outDest
  toImpExpr outDest (wrapDecls decls' outTuple)
  let substEnv = fold [v @> L (impAtomToAtom x) | (v, x) <- zip vs outDests]
  return (vs', subst (substEnv, mempty) result)

toImpExpr :: IAtom -> Expr -> ImpM ()
toImpExpr dests expr = case expr of
  Decl (Let b bound) body -> do
    withAllocs b $ \xs-> do
      toImpCExpr xs bound
      extendR (b @> xs) $ toImpExpr dests body
  CExpr e   -> toImpCExpr dests e
  Atom atom -> do
    xs <- toImpAtom atom
    copyIAtom dests xs

toImpAtom :: Atom -> ImpM IAtom
toImpAtom atom = case atom of
  Var v -> lookupVar v
  Con con -> case con of
    Lit x        -> return $ ILeaf $ ILit x
    ArrayRef ref -> return $ ILeaf $ IRef ref
    _ -> liftM ICon $ traverseExpr con return toImpAtom $
                        const (error "unexpected lambda")
  _ -> error $ "Not a scalar atom: " ++ pprint atom

fromScalarIAtom :: IAtom -> ImpM IExpr
fromScalarIAtom atom = case atom of
  ILeaf x               -> return x
  ICon (AGet (ILeaf x)) -> load x
  ICon (AsIdx _ x)      -> fromScalarIAtom x
  _ -> error $ "Expected scalar, got: " ++ pprint atom

fromScalarDest :: IAtom -> IExpr
fromScalarDest (ICon (AGet (ILeaf x))) = x
fromScalarDest atom = error $ "Not a scalar dest " ++ pprint atom

toImpCExpr :: IAtom -> CExpr -> ImpM ()
toImpCExpr dests op = case op of
  TabCon _ _ rows -> do
    rows' <- mapM toImpAtom rows
    void $ sequence [copyIAtom (tabGetIAtom dests $ ILit (IntLit i)) row
                    | (i, row) <- zip [0..] rows']
  For (LamExpr b body) -> do
    n' <- typeToSize (varAnn b)
    emitLoop n' $ \i -> do
      let ithDest = tabGetIAtom dests i
      extendR (b @> asIdx (varAnn b) i) $ toImpExpr ithDest body
  TabGet x i -> do
    i' <- toImpAtom i >>= fromScalarIAtom
    xs <- toImpAtom x
    copyIAtom dests $ tabGetIAtom xs i'
  RecGet x i -> do
    x' <- toImpAtom x
    case x' of
      ICon (RecCon r)-> copyIAtom dests $ recGet r i
      val -> error $ "Expected a record, got: " ++ show val
  RunReader r (LamExpr ref body) -> do
    r' <- toImpAtom r
    extendR (ref @> r') $ toImpExpr dests body
  RunWriter (LamExpr ref body) -> do
    mapM_ initializeZero wDest
    extendR (ref @> wDest) $ toImpExpr aDest body
    where (ICon (RecCon (Tup [aDest, wDest]))) = dests
  RunState s (LamExpr ref body) -> do
    s' <- toImpAtom s
    copyIAtom sDest s'
    extendR (ref @> sDest) $ toImpExpr aDest body
    where (ICon (RecCon (Tup [aDest, sDest]))) = dests
  IndexEff _ ~(Dep ref) _ i (LamExpr ref' body) -> do
    i' <- toImpAtom i >>= fromScalarIAtom
    curRef <- lookupVar ref
    extendR (ref' @> tabGetIAtom curRef i') (toImpExpr dests body)
  PrimEffect ~(Dep ref) _ m -> do
    case m of
      MAsk -> do
        rVals <- lookupVar ref
        copyIAtom dests rVals
      MTell x -> do
        wDests <- lookupVar ref
        x' <- toImpAtom x
        zipWithM_ addToDest (toList wDests) (toList x')
      MPut x -> do
        sDests <- lookupVar ref
        x' <- toImpAtom x
        copyIAtom sDests x'
      MGet -> do
        sDests <- lookupVar ref
        copyIAtom dests sDests
  IntAsIndex n i -> do
    i' <- toImpAtom i >>= fromScalarIAtom
    n' <- typeToSize n
    ans <- emitInstr $ IPrimOp $
             FFICall "int_to_index_set" [IntType, IntType] IntType [i', n']
    store dest ans
    where (ICon (AsIdx _ (ICon (AGet (ILeaf dest))))) = dests
  Cmp cmpOp ty x y -> do
    x' <- toImpAtom x >>= fromScalarIAtom
    y' <- toImpAtom y >>= fromScalarIAtom
    ans <- emitInstr $ IPrimOp $ ScalarBinOp (op' cmpOp) x' y'
    store (fromScalarDest dests) ans
    where op' = case ty of BaseType RealType -> FCmp
                           _                 -> ICmp
  IdxSetSize n -> do
    n' <- typeToSize n
    copyOrStore (fromScalarDest dests) n'
  ScalarUnOp IndexAsInt i ->
    toImpAtom i >>= fromScalarIAtom >>= store (fromScalarDest dests)
  _ -> do
    op' <- traverseExpr op
              (return . toImpBaseType)
              (toImpAtom >=> fromScalarIAtom)
              (const (return ()))
    ans <- emitInstr $ IPrimOp op'
    store (fromScalarDest dests) ans

withAllocs :: Var -> (IAtom -> ImpM a) -> ImpM a
withAllocs (_:>ty) body = do
  (dest, vs) <- makeDest ty
  flip mapM_ vs $ \v@(_:>IRefType refTy) -> emitStatement (Just v, Alloc refTy)
  ans <- body dest
  flip mapM_ vs $ \v -> emitStatement (Nothing, Free v)
  return ans

makeDest :: Type -> ImpM (IAtom, [IVar])
makeDest ty = runWriterT $ makeDest' [] ty

makeDest' :: [IExpr] -> Type -> WriterT [IVar] ImpM IAtom
makeDest' shape ty = case ty of
  BaseType b  -> do
    v <- lift $ freshVar ("v":> IRefType (b, shape))
    tell [v]
    return $ ICon $ AGet $ ILeaf $ IVar v
  TabType n b -> do
    n'  <- lift $ typeToSize n
    liftM (ICon . AFor n) $ makeDest' (shape ++ [n']) b
  RecType r   -> liftM (ICon . RecCon ) $ traverse (makeDest' shape) r
  IdxSetLit n -> liftM (ICon . AsIdx (IdxSetLit n)) $ makeDest' shape (BaseType IntType)
  _ -> error $ "Can't lower type to imp: " ++ pprint ty

tabGetIAtom :: IAtom -> IExpr -> IAtom
tabGetIAtom x i = case x of
  ICon (AFor _ body) -> impIndexSubst i body
  _ -> error $ "Unexpected atom: " ++ show x

impIndexSubst :: IExpr -> IAtom -> IAtom
impIndexSubst i atom = case atom of
  ILeaf x  -> ILeaf $ IGet x i
  ICon con -> ICon $ fmapExpr con id (impIndexSubst i) (error "unexpected lambda")

impExprToAtom :: IExpr -> Atom
impExprToAtom e = case e of
  IVar (v:>ty) -> Var (v:> impTypeToType ty)
  ILit x       -> Con $ Lit x
  IRef ref     -> Con $ ArrayRef ref
  _ -> error "Not implemented"

impTypeToType :: IType -> Type
impTypeToType (IValType b) = BaseType b
impTypeToType (IRefType (b, shape)) = ArrayType shape' b
  where shape' = map (\(ILit (IntLit n)) -> n) shape

impAtomToAtom :: IAtom -> Atom
impAtomToAtom (ILeaf e) = impExprToAtom e
impAtomToAtom (ICon con) = Con $ fmapExpr con id impAtomToAtom (const undefined)

toImpBaseType :: Type -> BaseType
toImpBaseType ty = case ty of
  BaseType b  -> b
  TabType _ a -> toImpBaseType a
  TypeVar _   -> IntType
  IdxSetLit _ -> IntType
  _ -> error $ "Unexpected type: " ++ pprint ty

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
typeToSize (Range low high) = do
  low'  <- toImpDepVal low
  high' <- toImpDepVal high
  emitInstr $ IPrimOp $ ScalarBinOp ISub high' low'

toImpDepVal :: Dep -> ImpM IExpr
toImpDepVal (DepLit i) = return $ ILit $ IntLit i

-- TODO: this is pretty iffy
copyIAtom :: IAtom -> IAtom -> ImpM ()
copyIAtom dest src = zipWithM_ copyOrStore (toList dest) (toList src)

asIdx :: Type -> IExpr -> IAtom
asIdx n i = ICon $ AsIdx n (ILeaf i)

-- === Imp embedding ===

-- TODO: be stricter about where we expect values vs refs
-- and remove loadIfRef and copyOrStore
loadIfRef :: IExpr -> ImpM IExpr
loadIfRef x = case impExprType x of
  IValType _ -> return x
  IRefType _ -> load x

copyOrStore :: IExpr -> IExpr -> ImpM ()
copyOrStore dest src = case impExprType src of
  IValType _ -> store dest src
  IRefType _ -> copy  dest src

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

fromIInt :: IExpr -> Int
fromIInt ~(ILit (IntLit x)) = x

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

addToDest :: IExpr -> IExpr -> ImpM ()
addToDest dest src = do
  cur <- load dest
  src' <- loadIfRef src
  updated <- emitInstr $ IPrimOp $ ScalarBinOp FAdd cur src'
  store dest updated

initializeZero :: IExpr -> ImpM ()
initializeZero ref = case impExprType ref of
  IRefType (RealType, []) -> store ref (ILit (RealLit 0.0))
  IRefType (RealType, (n:_)) -> emitLoop n $ \i -> initializeZero $ IGet ref i
  ty -> error $ "Zeros not implemented for type: " ++ pprint ty

-- === type checking imp programs ===

type ImpCheckM a = CatT (Env IType) (Either Err) a

instance IsModuleBody ImpModBody where
  checkModuleBody imports (ImpModBody vs prog result) = do
    let env = foldMap (\v -> v@> varAnn v) vs
    ((), env') <- runCatT (checkProg prog) env
    let tyEnv = fmap (L . impTypeToType) (env <> env')
    checkModuleBody (imports <> tyEnv) (ModBody [] result)

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
  IRef (Array shape b _) -> return $ IRefType (b, shape')
    where shape' = map (ILit . IntLit) shape
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
  IRef (Array shape b _) -> IRefType (b, shape')
    where shape' = map (ILit . IntLit) shape
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

instance Pretty IAtom where
  pretty atom = case atom of
    ILeaf x  -> pretty x
    ICon con -> pretty (ConExpr con)
