-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances #-}

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
import Fresh
import Subst
import Record
import Embed (wrapDecls)

type ImpEnv = Env IAtom
type EmbedEnv = (Scope, ImpProg)
type ImpM = ReaderT ImpEnv (Cat EmbedEnv)

data IAtomP a = ILeaf a | ICon (PrimCon Type (IAtomP a) ())  deriving (Show)
type IAtom = IAtomP IExpr

toImpModule :: Module -> ImpModule
toImpModule (Module ty m) = Module ty (ImpModBody vs prog result)
  where ((vs, result), (_, prog)) =
          runCat (runReaderT (toImpModBody m) mempty) mempty

toImpModBody :: ModBody -> ImpM ([IVar], SubstEnv)
toImpModBody (ModBody decls result) = do
  let vs = resultVars result
  let outTuple = PrimCon $ RecCon $ Tup $ map Var vs
  (outDest, vs') <- makeDest $ getType outTuple
  let (ICon (RecCon (Tup outDests))) = outDest
  toImpExpr outDest (wrapDecls decls outTuple)
  let substEnv = fold [v @> L (impAtomToAtom x) | (v, x) <- zip vs outDests]
  return (vs', subst (substEnv, mempty) result)

resultVars :: SubstEnv -> [Var]
resultVars env = [v:>ty | (v, L ty) <- envPairs $ freeVars env]

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
  PrimCon con -> case con of
    Lit x        -> return $ ILeaf $ ILit x
    ArrayRef ref -> return $ ILeaf $ IRef ref
    TabGet x i -> do
      i' <- toImpAtom i >>= fromScalarIAtom
      xs <- toImpAtom x
      return $ tabGetIAtom xs i'
    RecGet x i -> do
      x' <- toImpAtom x
      case x' of
        ICon (RecCon r)-> return $ recGet r i
        val -> error $ "Expected a record, got: " ++ show val
    _ -> liftM ICon $ traverseExpr con return toImpAtom $
                        const (error "unexpected lambda")
    _ -> error $ "Not implemented: " ++ pprint atom
  _ -> error $ "Not a scalar atom: " ++ pprint atom

fromScalarIAtom :: IAtom -> ImpM IExpr
fromScalarIAtom atom = case atom of
  ILeaf x                     -> return x
  ICon (LoadScalar (ILeaf x)) -> load x
  ICon (AsIdx _ x)            -> fromScalarIAtom x
  _ -> error $ "Expected scalar, got: " ++ pprint atom

fromScalarDest :: IAtom -> IExpr
fromScalarDest (ICon (LoadScalar (ILeaf x))) = x
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
      extendR (b @> asIdx n' i) $ toImpExpr ithDest body
  MonadRun rArgs sArgs m -> do
    rArgs' <- toImpAtom rArgs
    sArgs' <- toImpAtom sArgs
    copyIAtom sDests sArgs'
    mapM_ initializeZero wDests
    toImpAction (rArgs', wDests, sDests) aDests m
    where (ICon (RecCon (Tup [aDests, wDests, sDests]))) = dests
  LensGet x l -> do
    x' <- toImpAtom x
    ansRefs <- lensGet l x'
    copyIAtom dests ansRefs
  IntAsIndex n i -> do
    i' <- toImpAtom i >>= fromScalarIAtom
    n' <- typeToSize n
    ans <- emitInstr $ IPrimOp $
             FFICall "int_to_index_set" [IntType, IntType] IntType [i', n']
    store dest ans
    where (ICon (AsIdx _ (ICon (LoadScalar (ILeaf dest))))) = dests
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
  flip mapM_ vs $ \v@(_:>IRefType ty) -> emitStatement (Just v, Alloc ty)
  ans <- body dest
  flip mapM_ vs $ \v -> emitStatement (Nothing, Free v)
  return ans

makeDest :: Type -> ImpM (IAtom, [IVar])
makeDest ty = runWriterT $ makeDest' [] ty

makeDest' :: [IExpr] -> Type -> WriterT [IVar] ImpM IAtom
makeDest' shape ty = case ty of
  BaseType b  -> do
    v <- lift $ freshVar ("v":> IRefType (b, shape))
    let scalarRef = foldr (const (ICon . aget)) (ILeaf (IVar v)) shape
    tell [v]
    return $ ICon $ LoadScalar $ scalarRef
    where aget x = ArrayGep x (ICon IdxFromStack)
  TabType n b -> do
    n'  <- lift $ typeToSize n
    liftM (ICon . AFor n) $ makeDest' (shape ++ [n']) b
  RecType r   -> liftM (ICon . RecCon ) $ traverse (makeDest' shape) r
  IdxSetLit n -> liftM (ICon . AsIdx n) $ makeDest' shape (BaseType IntType)
  _ -> error $ "Can't lower type to imp: " ++ pprint ty

type MContext = (IAtom, IAtom, IAtom)

toImpActionExpr :: MContext -> IAtom -> Expr -> ImpM ()
toImpActionExpr mdests dests expr = case expr of
  Decl (Let b bound) body -> do
    withAllocs b $ \xs-> do
      toImpCExpr xs bound
      extendR (b @> xs) $ toImpActionExpr mdests dests body
  Atom m -> toImpAction mdests dests m
  _ -> error $ "Unexpected expression " ++ pprint expr

toImpAction :: MContext -> IAtom -> Atom -> ImpM ()
toImpAction mdests@(rVals, wDests, sDests) outDests (PrimCon con) = case con of
  Bind rhs (LamExpr b body) -> do
    withAllocs b $ \xs -> do
      toImpAction mdests xs rhs
      extendR (b @> xs) $ toImpActionExpr mdests outDests body
  Return _ x -> do
    x' <- toImpAtom x
    copyIAtom outDests x'
  Seq (LamExpr b body) -> do
    n' <- typeToSize (varAnn b)
    emitLoop n' $ \i -> do
      let ithDest = tabGetIAtom outDests i
      extendR (b @> asIdx n' i) $ toImpActionExpr mdests ithDest body
  MonadCon _ _ l m -> case m of
    MAsk -> do
      ans <- lensGet l rVals
      copyIAtom outDests ans
    MTell x -> do
      x' <- toImpAtom x
      wDests' <- lensIndexRef l wDests
      zipWithM_ addToDest (toList wDests') (toList x')
    MPut x -> do
      x' <- toImpAtom x
      sDests' <- lensIndexRef l sDests
      copyIAtom sDests' x'
    MGet -> do
      ans <- lensGet l sDests
      copyIAtom outDests ans
  _ -> error $ "Unexpected expression" ++ pprint con

lensGet :: Atom -> IAtom -> ImpM IAtom
lensGet (PrimCon (LensCon lens)) x = case lens of
  LensId _ -> return x
  LensCompose a b -> lensGet a x >>= lensGet b
  IdxAsLens _ i -> do
    i' <- toImpAtom i >>= fromScalarIAtom
    return $ tabGetIAtom x i'
lensGet expr _ = error $ "Not a lens expression: " ++ pprint expr

lensIndexRef :: Atom -> IAtom -> ImpM IAtom
lensIndexRef (PrimCon (LensCon lens)) x = case lens of
  LensId _ -> return x
  LensCompose a b -> lensIndexRef a x >>= lensIndexRef b
  IdxAsLens _ i -> do
    i' <- toImpAtom i >>= fromScalarIAtom
    return $ tabGetIAtom x i'
lensIndexRef expr _ = error $ "Not a lens expression: " ++ pprint expr

tabGetIAtom :: IAtom -> IExpr -> IAtom
tabGetIAtom x i = case x of
  ICon (AFor _ body) -> impIndexSubst [] i body
  _ -> error $ "Unexpected atom: " ++ show x

impIndexSubst :: [()] -> IExpr -> IAtom -> IAtom
impIndexSubst stack i atom = case atom of
  ICon con -> case con of
    AFor n body -> ICon $ AFor n $ impIndexSubst (():stack) i body
    ArrayGep x (ICon IdxFromStack)-> case stack of
      []        -> ILeaf $ IGet x' i  where (ILeaf x') = x
      ():stack' -> ICon $ ArrayGep (impIndexSubst stack' i x) (ICon IdxFromStack)
    _ -> ICon $ fmapExpr con id (impIndexSubst stack i) (error "unexpected lambda")
  _ -> error "Unused index"

impExprToAtom :: IExpr -> Atom
impExprToAtom e = case e of
  IVar (v:>ty) -> Var (v:> impTypeToType ty)
  ILit x       -> PrimCon $ Lit x
  IRef ref     -> PrimCon $ ArrayRef ref
  _ -> error "Not implemented"

impTypeToType :: IType -> Type
impTypeToType (IValType b) = BaseType b
impTypeToType (IRefType (b, shape)) = ArrayType shape' b
  where shape' = map (\(ILit (IntLit n)) -> n) shape

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

-- TODO: this is pretty iffy
copyIAtom :: IAtom -> IAtom -> ImpM ()
copyIAtom dest src = zipWithM_ copyOrStore (toList dest) (toList src)

asIdx :: IExpr -> IExpr -> IAtom
asIdx n i = ICon $ AsIdx (fromIInt n) (ILeaf i)

-- === Imp embedding ===

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
fromIInt (ILit (IntLit x)) = x

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

-- === type checking imp programs ===

type ImpCheckM a = CatT (Env IType) (Either Err) a

instance IsModuleBody ImpModBody where
  checkModuleBody _ (ImpModBody vs prog result) = do
    let env = foldMap (\v -> v@> varAnn v) vs
    ((), env') <- runCatT (checkProg prog) env
    let tyEnv = fmap (L . impTypeToType) (env <> env')
    checkModuleBody tyEnv (ModBody [] result)

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
    ICon con -> pretty (PrimConExpr con)
