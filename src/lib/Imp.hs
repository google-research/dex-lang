-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE PatternSynonyms #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Imp (toImpFunction, impExprType) where

import Control.Monad.Trans.Identity
import Control.Monad.Reader
import Control.Monad.Except hiding (Except)
import Control.Monad.State
import Control.Monad.Writer
import Data.Foldable
import Data.Functor.Reverse
import Data.Text.Prettyprint.Doc

import Array
import Syntax
import Env
import Type
import PPrint
import Cat
import Subst
import Record
import Util (bindM2)

type EmbedEnv = ([IVar], (Scope, ImpProg))
type ImpM = Cat EmbedEnv

toImpFunction :: ([Var], Expr) -> ImpFunction
toImpFunction (vsIn, expr) = runImpM $ do
  (vsOut, prog) <- scopedBlock $ materializeResult
  let arrIn  = flip fmap vsIn  (\(v :> ArrayTy b)        -> v :> b)
  let arrOut = flip fmap vsOut (\(v :> IRefType (_, b))  -> v :> b)
  return $ ImpFunction arrOut arrIn prog
  where
    materializeResult = do
      ans <- toImpExpr mempty expr
      (outDest, vsOut) <- allocDest Unmanaged $ getType expr
      copyAtom outDest ans
      return vsOut

runImpM :: ImpM a -> a
runImpM m = fst $ runCat m mempty

toImpExpr :: SubstEnv -> Expr -> ImpM Atom
toImpExpr env expr = case expr of
  Decl (Let b bound) body -> do
    b' <- traverse (impSubst env) b
    ans <- toImpCExpr env bound
    toImpExpr (env <> b'@> L ans) body
  CExpr op -> toImpCExpr env op
  Atom atom -> impSubst env atom

toImpCExpr :: SubstEnv -> CExpr -> ImpM Atom
toImpCExpr env op = do
  op' <- traverseExpr op (impSubst env) (impSubst env) (substLamPartial env)
  toImpCExpr' op'

substLamPartial :: SubstEnv -> LamExpr -> ImpM (LamExpr, SubstEnv)
substLamPartial env (LamExpr b body) = do
  b' <- traverse (impSubst env) b
  return (LamExpr b' body, env)

impSubst :: Subst a => SubstEnv -> a -> ImpM a
impSubst env x = do
  scope <- looks (fst . snd)
  return $ subst (env, scope) x

toImpCExpr' :: PrimOp Type Atom (LamExpr, SubstEnv) -> ImpM Atom
toImpCExpr' op = case op of
  TabCon n _ rows -> do
    dest <- alloc resultTy
    forM_ (zip [0..] rows) $ \(i, row) -> do
      i' <- intToIndex n $ IIntVal i
      ithDest <- impTabGet dest i'
      copyAtom ithDest row
    return dest
  For d (LamExpr b@(_:>idxTy) body, env) -> do
    n' <-  indexSetSize idxTy
    dest <- alloc resultTy
    emitLoop d n' $ \i -> do
      i' <- intToIndex idxTy i
      ithDest <- impTabGet dest i'
      ans <- toImpExpr (env <> b @> L i') body
      copyAtom ithDest ans
    return dest
  TabGet x i -> impTabGet x i
  SumGet x getLeft ->
    case x of
      SumVal _ l r -> return $ if getLeft then l else r
      val -> error $ "Expected a sum type, got: " ++ pprint val
  SumTag x ->
    case x of
      SumVal t _ _ -> return t
      val -> error $ "Expected a sum type, got: " ++ pprint val
  RecGet x i -> do
    case x of
      RecVal r -> return $ recGet r i
      val -> error $ "Expected a record, got: " ++ pprint val
  RunReader r (LamExpr ref body, env) -> do
    toImpExpr (env <> ref @> L r) body
  RunWriter (LamExpr ref body, env) -> do
    wDest <- alloc wTy
    initializeAtomZero wDest
    aResult <- toImpExpr (env <> ref @> L wDest) body
    return $ PairVal aResult wDest
    where (PairTy _ wTy) = resultTy
  RunState s (LamExpr ref body, env) -> do
    sDest <- alloc sTy
    copyAtom sDest s
    aResult <- toImpExpr (env <> ref @> L sDest) body
    return $ PairVal aResult sDest
    where (PairTy _ sTy) = resultTy
  IndexEff _ ref i (LamExpr b body, env) -> do
    ref' <- impTabGet ref i
    toImpExpr (env <> b @> L ref') body
  PrimEffect ref m -> do
    case m of
      MAsk    -> return ref
      MTell x -> addToAtom ref x >> return UnitVal
      MPut x  -> copyAtom  ref x >> return UnitVal
      MGet -> do
        dest <- alloc resultTy
        copyAtom dest ref
        return dest
  IntAsIndex n i -> do
    i' <- fromScalarAtom i
    n' <- indexSetSize n
    ans <- emitInstr $ IPrimOp $
             FFICall "int_to_index_set" [IntType, IntType] IntType [i', n']
    return $ toScalarAtom resultTy ans
  Cmp _ _ _ _ -> error $ "All instances of Cmp should get resolved in simplification"
  IdxSetSize n -> liftM (toScalarAtom resultTy) $ indexSetSize n
  IndexAsInt i -> toScalarAtom IntTy <$> indexToInt (getType i) i
  Inject e -> do
    let rt@(TC (IndexRange t low _)) = getType e
    offset <- case low of
      InclusiveLim a -> indexToInt t a
      ExclusiveLim a -> indexToInt t a >>= impAdd IOne
      Unlimited      -> return IZero
    restrictIdx <- indexToInt rt e
    idx <- impAdd restrictIdx offset
    intToIndex t idx
  _ -> do
    op' <- traverseExpr op (return . toImpBaseType) fromScalarAtom (const (return ()))
    liftM (toScalarAtom resultTy) $ emitInstr (IPrimOp op')
  where
    resultTy :: Type
    resultTy = getType $ CExpr $ fmapExpr op id id fst

toScalarAtom :: Type -> IExpr -> Atom
toScalarAtom _  (ILit v) = Con $ Lit v
toScalarAtom ty x@(IVar (v:>_)) = case ty of
  BaseTy _                -> Var (v:>ty)
  TC (IntRange       _ _) -> Con $ AsIdx ty $ toScalarAtom IntTy x
  TC (IndexRange ty' _ _) -> Con $ AsIdx ty $ toScalarAtom ty' x
  _ -> error $ "Not a scalar type: " ++ pprint ty


anyValue :: Type -> IExpr
anyValue (TC (BaseType RealType))   = ILit $ RealLit 1.0
anyValue (TC (BaseType IntType))    = ILit $ IntLit 1
anyValue (TC (BaseType BoolType))   = ILit $ BoolLit False
anyValue (TC (BaseType StrType))    = ILit $ StrLit ""
-- XXX: This is not strictly correct, because those types might not have any
--      inhabitants. We might want to consider emitting some run-time code that
--      aborts the program if this really ends up being the case.
anyValue (TC (IntRange _ _))        = ILit $ IntLit 0
anyValue (TC (IndexRange _ _ _))    = ILit $ IntLit 0
anyValue t = error $ "Expected a scalar type in anyValue, got: " ++ pprint t

fromScalarAtom :: Atom -> ImpM IExpr
fromScalarAtom atom = case atom of
  Var (v:>BaseTy b) -> return $ IVar (v :> IValType b)
  Con (Lit x)       -> return $ ILit x
  Con (AGet x)      -> load =<< fromArrayAtom x []
  Con (AsIdx _ x)   -> fromScalarAtom x
  Con (AnyValue ty) -> return $ anyValue ty
  _ -> error $ "Expected scalar, got: " ++ pprint atom

fromArrayAtom :: Atom -> [IDimType] -> ImpM IExpr
fromArrayAtom atom dims = case atom of
  -- TODO: Assert dims match?
  Var   (v:>IArrayTy dims' b) -> return $ IVar $ v :> IRefType (dims', b)
  Var v@(_:>ArrayTy _)        -> castArray v dims
  _ -> error $ "Expected array, got: " ++ pprint atom

data AllocType = Managed | Unmanaged

alloc :: Type -> ImpM Atom
alloc ty = fst <$> allocDest Managed ty

allocDest :: AllocType -> Type -> ImpM (Atom, [IVar])
allocDest allocTy ty = do
  (dest, vs) <- makeDest "v" ty
  flip mapM_ vs $ \v@(_:>IRefType refTy) -> emitStatement (Just v, Alloc refTy)
  case allocTy of
    Managed   -> extend $ asFst vs
    Unmanaged -> return ()
  return (dest, vs)

makeDest :: Name -> Type -> ImpM (Atom, [IVar])
makeDest name ty = runWriterT $ makeDest' name [] ty

-- TODO: Handle more complicated index sets (possibly emit IPrecomputed instead of IUniform)
extendDims :: Type -> [IDimType] -> ImpM [IDimType]
extendDims t dims = case t of
  (TC (IntRange _ _))     -> uniform
  (TC (IndexRange _ _ _)) -> case dims of
    [] -> uniform
    _  -> error $ "IndexRanges only supported in the outermost array dimension"
  (RecTy rec) -> do
    newDims <- traverse (flip extendDims dims) $ toList rec
    appendUniform <$> (impProd $ fmap (\(IUniform sz:_) -> sz) newDims)
  (SumTy l r) -> do
    ~(IUniform l':_) <- extendDims l dims
    ~(IUniform r':_) <- extendDims r dims
    appendUniform <$> impAdd l' r'
  _           -> error "Missing a case for an index set type"
  where
    appendUniform sz = dims ++ [IUniform sz]
    uniform = appendUniform <$> indexSetSize t

makeDest' :: Name -> [IDimType] -> Type -> WriterT [IVar] ImpM Atom
makeDest' name dims (TabTy n b) = do
  newDims <- lift $ n `extendDims` dims
  liftM (Con . AFor n) $ makeDest' name newDims b
makeDest' name dims ty@(TC con) = case con of
  BaseType b  -> do
    v <- lift $ freshVar (name :> IRefType (dims, b))
    tell [v]
    return $ Con $ AGet $ Var (fmap impTypeToType v)
  RecType r   -> liftM RecVal $ traverse (makeDest' name dims) r
  IntRange   _ _   -> scalarIndexSet ty
  IndexRange _ _ _ -> scalarIndexSet ty
  _ -> error $ "Can't lower type to imp: " ++ pprint con
  where
    scalarIndexSet t = liftM (Con . AsIdx t) $ makeDest' name dims (BaseTy IntType)
makeDest' _ _ ty = error $ "Can't lower type to imp: " ++ pprint ty

impTabGet :: Atom -> Atom -> ImpM Atom
impTabGet a@(Con (AFor it _)) i = do
  i' <- indexToInt it i
  -- XXX: We traverse the full atom to include the it in dims
  ~(Con (AFor _ b)) <- flip traverseLeaves a $ \(~(Con (AGet arr))) dims -> do
    arr' <- fromArrayAtom arr dims
    ans  <- emitInstr $ IGet arr' i'
    return $ Con $ AGet $ impExprToAtom ans
  return b
impTabGet _ _ = error "Expected an array atom in impTabGet"

intToIndex :: Type -> IExpr -> ImpM Atom
intToIndex ty@(TC con) i = case con of
  IntRange _ _      -> iAsIdx
  IndexRange _ _ _  -> iAsIdx
  BaseType BoolType -> impExprToAtom <$> emitUnOp UnsafeIntToBool i
  RecType r -> do
    strides <- getStrides $ fmap (\t->(t,t)) r
    liftM RecVal $
      flip evalStateT i $ forM strides $ \(ty', _, stride) -> do
        i' <- get
        iCur  <- lift $ impDiv i' stride
        iRest <- lift $ impRem i' stride
        put iRest
        lift $ intToIndex ty' iCur
  SumType (l, r) -> do
    ls <- indexSetSize l
    isLeft <- impCmp Less i ls
    li <- intToIndex l i
    ri <- intToIndex r =<< impSub i ls
    return $ Con $ SumCon (toScalarAtom BoolTy isLeft) li ri
  _ -> error $ "Unexpected type " ++ pprint con
  where
    iAsIdx = return $ Con $ AsIdx ty $ impExprToAtom i
intToIndex ty _ = error $ "Unexpected type " ++ pprint ty

indexToInt :: Type -> Atom -> ImpM IExpr
indexToInt ty idx = case ty of
  BoolTy  -> emitUnOp BoolToInt =<< fromScalarAtom idx
  RecTy rt -> do
    case idx of
      (RecVal rv) -> do
        rWithStrides <- getStrides $ recZipWith (,) rv rt
        foldrM f (IIntVal 0) rWithStrides
        where
        f :: (Atom, Type, IExpr) -> IExpr -> ImpM IExpr
        f (i, it, stride) cumIdx = do
          i' <- indexToInt it i
          iDelta  <- impMul i' stride
          impAdd cumIdx iDelta
      _ -> error $ "Expected a record, got: " ++ pprint idx
  SumTy lType rType     -> do
    case idx of
      (SumVal con lVal rVal) -> do
        lTypeSize <- indexSetSize lType
        lInt <- indexToInt lType lVal
        rInt <- impAdd lTypeSize =<< indexToInt rType rVal
        conExpr <- fromScalarAtom con
        impSelect conExpr lInt rInt
      _ -> error $ "Expected a sum constructor, got: " ++ pprint idx
  TC (IntRange _ _)     -> fromScalarAtom idx
  TC (IndexRange _ _ _) -> fromScalarAtom idx
  _ -> error $ "Unexpected type " ++ pprint ty

getStrides :: Traversable f => f (a, Type) -> ImpM (f (a, Type, IExpr))
getStrides xs =
  liftM getReverse $ flip evalStateT (IIntVal 1) $
    forM (Reverse xs) $ \(x, ty) -> do
      stride  <- get
      size    <- lift $ indexSetSize ty
      stride' <- lift $ impMul stride size
      put stride'
      return (x, ty, stride)

impExprToAtom :: IExpr -> Atom
impExprToAtom e = case e of
  IVar (v:>ty) -> Var (v:> impTypeToType ty)
  ILit x       -> Con $ Lit x

impTypeToType :: IType -> Type
impTypeToType (IValType b)     = BaseTy b
impTypeToType (IRefType arrTy) = TC $ IArrayType arrTy

toImpBaseType :: Type -> BaseType
toImpBaseType (TabTy _ a) = toImpBaseType a
toImpBaseType (TC con) = case con of
  BaseType b       -> b
  IntRange _ _     -> IntType
  IndexRange _ _ _ -> IntType
  _ -> error $ "Unexpected type: " ++ pprint con
toImpBaseType ty = error $ "Unexpected type: " ++ pprint ty

indexSetSize :: Type -> ImpM IExpr
indexSetSize (TC con) = case con of
  IntRange low high -> do
    low'  <- fromScalarAtom low
    high' <- fromScalarAtom high
    impSub high' low'
  IndexRange n low high -> do
    low' <- case low of
      InclusiveLim x -> indexToInt n x
      ExclusiveLim x -> indexToInt n x >>= impAdd IOne
      Unlimited      -> return IZero
    high' <- case high of
      InclusiveLim x -> indexToInt n x >>= impAdd IOne
      ExclusiveLim x -> indexToInt n x
      Unlimited      -> indexSetSize n
    impSub high' low'
  RecType r -> do
    sizes <- traverse indexSetSize r
    impProd $ toList sizes
  BaseType BoolType -> return $ IIntVal 2
  SumType (l, r) -> bindM2 impAdd (indexSetSize l) (indexSetSize r)
  _ -> error $ "Not implemented " ++ pprint con
indexSetSize ty = error $ "Not implemented " ++ pprint ty

traverseLeaves :: (Atom -> [IDimType] -> ImpM Atom) -> Atom -> ImpM Atom
traverseLeaves f x = runIdentityT $ traverseLeavesM (\a d -> lift $ f a d) x

traverseLeavesM :: (Monad (m ImpM), MonadTrans m) => (Atom -> [IDimType] -> m ImpM Atom) -> Atom -> m ImpM Atom
traverseLeavesM = traverseLeaves' []

traverseLeaves' :: (Monad (m ImpM), MonadTrans m) => [IDimType] -> (Atom -> [IDimType] -> m ImpM Atom) -> Atom -> m ImpM Atom
traverseLeaves' dims f atom = case atom of
  Var _        -> f atom dims
  Con (Lit  _) -> f atom dims
  Con (AGet _) -> f atom dims
  Con destCon -> Con <$> case destCon of
    AFor n body -> do
      newDims <- lift $ (n `extendDims` dims)
      AFor n <$> traverseLeaves' newDims f body
    AsIdx n idx -> (AsIdx n) <$> recur idx
    RecCon r    -> RecCon    <$> traverse recur r
    _ -> error $ "Not a valid Imp atom: " ++ pprint atom
  _ ->   error $ "Not a valid Imp atom: " ++ pprint atom
  where recur = traverseLeaves' dims f

leavesList :: Atom -> ImpM [(Atom, [IDimType])]
leavesList atom = execWriterT $ flip traverseLeavesM atom $ \leaf dims ->
  tell [(leaf, dims)] >> return leaf

copyAtom :: Atom -> Atom -> ImpM ()
copyAtom dest src = bindM2 (zipWithM_ copyLeaf) (leavesList dest) (leavesList src)

-- TODO: Assert dims are equal?
copyLeaf :: (Atom, [IDimType]) -> (Atom, [IDimType]) -> ImpM ()
copyLeaf (~(Con (AGet dest)), destDims) (src, srcDims) = case src of
  Con (AGet src') -> bindM2 copy  dest' (fromArrayAtom src' srcDims)
  _               -> bindM2 store dest' (fromScalarAtom src)
  where dest' = fromArrayAtom dest destDims

initializeAtomZero :: Atom -> ImpM ()
initializeAtomZero x = void $ flip traverseLeaves x $ \(~leaf@((Con (AGet dest)))) dims ->
  fromArrayAtom dest dims >>= initializeZero >> return leaf

addToAtom :: Atom -> Atom -> ImpM ()
addToAtom dest src = bindM2 (zipWithM_ addToAtomLeaf) (leavesList dest) (leavesList src)

addToAtomLeaf :: (Atom, [IDimType]) -> (Atom, [IDimType]) -> ImpM ()
addToAtomLeaf (~(Con (AGet dest)), destDims) (src, srcDims) = case src of
  Con (AGet src') -> bindM2 addToDestFromRef dest' (fromArrayAtom src' srcDims)
  _               -> bindM2 addToDestScalar  dest' (fromScalarAtom src)
  where dest' = fromArrayAtom dest destDims

-- === Imp embedding ===

impProd :: [IExpr] -> ImpM IExpr
impProd []     = return $ IOne
impProd (x:xs) = foldrM impMul x xs

emitUnOp :: ScalarUnOp -> IExpr -> ImpM IExpr
emitUnOp op x = emitInstr $ IPrimOp $ ScalarUnOp op x

emitBinOp :: ScalarBinOp -> IExpr -> IExpr -> ImpM IExpr
emitBinOp op x y = emitInstr $ IPrimOp $ ScalarBinOp op x y

impAdd :: IExpr -> IExpr -> ImpM IExpr
impAdd IZero y = return y
impAdd x IZero = return x
impAdd (IIntVal x) (IIntVal y) = return $ IIntVal $ x + y
impAdd x y = emitBinOp IAdd x y

impMul :: IExpr -> IExpr -> ImpM IExpr
impMul IOne y = return y
impMul x IOne = return x
impMul (IIntVal x) (IIntVal y) = return $ IIntVal $ x * y
impMul x y = emitBinOp IMul x y

impDiv :: IExpr -> IExpr -> ImpM IExpr
impDiv x IOne = return x
impDiv x y = emitBinOp IDiv x y

impRem :: IExpr -> IExpr -> ImpM IExpr
impRem _ IOne = return IZero
impRem x y = emitBinOp Rem x y

impSub :: IExpr -> IExpr -> ImpM IExpr
impSub (IIntVal a) (IIntVal b)  = return $ IIntVal $ a - b
impSub a IZero = return a
impSub x y = emitBinOp ISub x y

impCmp :: CmpOp -> IExpr -> IExpr -> ImpM IExpr
impCmp GreaterEqual (IIntVal a) (IIntVal b) = return $ ILit $ BoolLit $ a >= b
impCmp op x y = emitBinOp (ICmp op) x y

-- Precondition: x and y don't have array types
impSelect :: IExpr -> IExpr -> IExpr -> ImpM IExpr
impSelect p x y = emitInstr $ IPrimOp $ Select t p x y
  where (IValType t) = impExprType x

copy :: IExpr -> IExpr -> ImpM ()
copy dest src = emitStatement (Nothing, Copy dest src)

load :: IExpr -> ImpM IExpr
load x = emitInstr $ Load x

castArray :: Var -> [IDimType] -> ImpM IExpr
castArray v@(_:>(ArrayTy b)) dims = emitInstr $ CastArray v (dims, b)
castArray _ _ = error "Expected an array in castArray"

store :: IExpr -> IExpr -> ImpM ()
store dest src = emitStatement (Nothing, Store dest src)

freshVar :: IVar -> ImpM IVar
freshVar v = do
  scope <- looks (fst . snd)
  let v' = rename v scope
  extend $ asSnd $ asFst (v' @> ())
  return v'

emitLoop :: Direction -> IExpr -> (IExpr -> ImpM ()) -> ImpM ()
emitLoop d n body = do
  (i, loopBody) <- scopedBlock $ do
    i <- freshVar ("i":>IIntTy)
    body $ IVar i
    return i
  emitStatement (Nothing, Loop d i n loopBody)

scopedBlock :: ImpM a -> ImpM (a, ImpProg)
scopedBlock body = do
  (ans, (allocs, (scope', prog))) <- scoped body
  extend (mempty, (scope', mempty))  -- Keep the scope extension to avoid reusing variable names
  let frees = ImpProg [(Nothing, Free v) | v <- allocs]
  return (ans, prog <> frees)

emitStatement :: ImpStatement -> ImpM ()
emitStatement statement = extend $ asSnd $ asSnd $ ImpProg [statement]

emitInstr :: ImpInstr -> ImpM IExpr
emitInstr instr = do
  case ignoreExcept (instrType instr) of
    Just ty -> do
      v <- freshVar ("v":>ty)
      emitStatement (Just v, instr)
      return $ IVar v
    Nothing -> error "Expected non-void result"

addToDestFromRef :: IExpr -> IExpr -> ImpM ()
addToDestFromRef dest src = case impExprType dest of
  IRefType ([], RealType) -> do
    cur  <- load dest
    src' <- load src
    updated <- emitInstr $ IPrimOp $ ScalarBinOp FAdd cur src'
    store dest updated
  IRefType ((dim:_), RealType) ->
    emitLoop Fwd (dimSize dim) $ \i -> do
      dest' <- emitInstr $ IGet dest i
      src'  <- emitInstr $ IGet src  i
      addToDestFromRef dest' src'
  ty -> error $ "Addition not implemented for type: " ++ pprint ty

addToDestScalar :: IExpr -> IExpr -> ImpM ()
addToDestScalar dest src = do
  cur  <- load dest
  updated <- emitInstr $ IPrimOp $ ScalarBinOp FAdd cur src
  store dest updated

initializeZero :: IExpr -> ImpM ()
initializeZero ref = case impExprType ref of
  IRefType ([],    RealType)   -> store ref (ILit (RealLit 0.0))
  IRefType ((dim:_), RealType) ->
    emitLoop Fwd (dimSize dim) $ \i -> emitInstr (IGet ref i) >>= initializeZero
  ty -> error $ "Zeros not implemented for type: " ++ pprint ty

dimSize :: IDimType -> IExpr
dimSize dimTy = case dimTy of
  IUniform s -> s
  IPrecomputed (_ :> IRefType ([IUniform s], _)) -> s
  _ -> error $ "Unexpected dim type in dimSize: " ++ pprint dimTy

-- === type checking imp programs ===

-- State keeps track of _all_ names used in the program, Reader keeps the type env.
type ImpCheckM a = StateT Scope (ReaderT (Env IType) (Either Err)) a

instance Checkable ImpFunction where
  checkValid (ImpFunction _ vsIn (ImpProg prog)) = do
    let scope = foldMap (varAsEnv . fmap (const ())) vsIn
    void $ runReaderT (runStateT (checkProg prog) scope) mempty

checkProg :: [ImpStatement] -> ImpCheckM ()
checkProg [] = return ()
checkProg ((maybeBinder, instr):prog) = do
  maybeTy <- instrTypeChecked instr
  case (maybeBinder, maybeTy) of
    (Nothing, Nothing) -> checkProg prog
    (Nothing, Just _ ) -> throw CompilerErr $ "Result of non-void instruction must be assigned"
    (Just _ , Nothing) -> throw CompilerErr $ "Can't assign result of void instruction"
    (Just v@(_:>ty), Just ty') -> do
      checkBinder v
      checkValidType ty
      assertEq ty ty' "Type mismatch in instruction"
      extendR (v@>ty) $ checkProg prog

instrTypeChecked :: ImpInstr -> ImpCheckM (Maybe IType)
instrTypeChecked instr = case instr of
  IPrimOp op -> liftM Just $ checkImpOp op
  Load ref -> do
    b <- (checkIExpr >=> fromScalarRefType) ref
    return $ Just $ IValType b
  Store dest val -> do
    b <- (checkIExpr >=> fromScalarRefType) dest
    valTy <- checkIExpr val
    assertEq (IValType b) valTy "Type mismatch in store"
    return Nothing
  Copy dest source -> do
    _ <- (checkIExpr >=> fromRefType) dest
    _ <- (checkIExpr >=> fromRefType) source
    -- FIXME: Reenable this check!
    --assertEq sourceTy destTy "Type mismatch in copy"
    return Nothing
  CastArray v (dims, b) -> case v of
    _ :> ArrayTy b' -> do
      env <- get
      when (not $ v `isin` env) $ throw CompilerErr $ "Unbound array variable: " ++ pprint v
      assertEq b b' "Type mismatch in cast array"
      return $ Just $ IRefType (dims, b)
    _ -> throw CompilerErr $ "Casting a non-array variable to array"
  Alloc ty -> return $ Just $ IRefType ty
  Free _   -> return Nothing  -- TODO: check matched alloc/free
  Loop _ i size (ImpProg block) -> do
    checkInt size
    checkBinder i
    extendR (i @> IIntTy) $ checkProg block
    return Nothing
  IGet e i -> do
    ~(IRefType ((_:dims), b)) <- checkIExpr e
    checkInt i
    return $ Just $ IRefType (dims, b)

checkBinder :: IVar -> ImpCheckM ()
checkBinder v = do
  env <- get
  when (v `isin` env) $ throw CompilerErr $ "shadows: " ++ pprint v
  modify (<>(v@>()))

checkValidType :: IType -> ImpCheckM ()
checkValidType (IValType _        ) = return ()
checkValidType (IRefType (dims, _)) = mapM_ checkDimType dims

checkDimType :: IDimType -> ImpCheckM ()
checkDimType dimTy = case dimTy of
  IUniform sz -> checkInt sz
  IPrecomputed (_ :> IRefType ([IUniform sz], IntType)) -> checkInt sz
  IPrecomputed _ -> throw CompilerErr $ "Unexpected precomputed stride array type: " ++ pprint dimTy

checkIExpr :: IExpr -> ImpCheckM IType
checkIExpr expr = case expr of
  ILit val -> return $ IValType (litType val)
  -- TODO: check shape matches vector length
  IVar v -> asks $ (! v)

checkInt :: IExpr -> ImpCheckM ()
checkInt expr = do
  ty <- checkIExpr expr
  assertEq (IValType IntType) ty $ "Not an int: " ++ pprint expr

checkImpOp :: IPrimOp -> ImpCheckM IType
checkImpOp op = do
  op' <- traverseExpr op
           return
           (\x  -> checkIExpr x)
           (error "shouldn't have lambda")
  case op' of
    ScalarBinOp scalarOp x y -> do
      checkEq x (IValType x')
      checkEq y (IValType y')
      return $ IValType ty
      where (x', y', ty) = binOpType scalarOp
    ScalarUnOp scalarOp x -> do
      checkEq x (IValType x')
      return $ IValType ty
      where (x', ty) = unOpType scalarOp
    Select ty _ x y -> do
      checkEq (IValType ty) x
      checkEq (IValType ty) y
      return $ IValType ty
    FFICall _ _ ty _   -> return $ IValType ty -- TODO: check
    _ -> error $ "Not allowed in Imp IR: " ++ pprint op
  where
    checkEq :: (Pretty a, Eq a) => a -> a -> ImpCheckM ()
    checkEq t t' = assertEq t t' (pprint op)

fromRefType :: MonadError Err m => IType -> m IArrayType
fromRefType (IRefType ty) = return ty
fromRefType ty = throw CompilerErr $ "Not a reference type: " ++ pprint ty

fromScalarRefType :: MonadError Err m => IType -> m BaseType
fromScalarRefType (IRefType ([], b)) = return b
fromScalarRefType ty = throw CompilerErr $ "Not a scalar reference type: " ++ pprint ty

impExprType :: IExpr -> IType
impExprType expr = case expr of
  ILit v    -> IValType (litType v)
  IVar (_:>ty) -> ty

instrType :: MonadError Err m => ImpInstr -> m (Maybe IType)
instrType instr = case instr of
  IPrimOp op      -> return $ Just $ impOpType op
  Load ref        -> liftM (Just . IValType) $ fromScalarRefType (impExprType ref)
  Store _ _       -> return Nothing
  Copy  _ _       -> return Nothing
  CastArray _ ty  -> return $ Just $ IRefType ty
  Alloc ty        -> return $ Just $ IRefType ty
  Free _          -> return Nothing
  Loop _ _ _ _    -> return Nothing
  IGet e _        -> case impExprType e of
    IRefType ((_:dims), b) -> return $ Just $ IRefType (dims, b)
    ty -> error $ "Can't index into: " ++ pprint ty


impOpType :: IPrimOp -> IType
impOpType (ScalarBinOp op _ _) = IValType ty  where (_, _, ty) = binOpType op
impOpType (ScalarUnOp  op _  ) = IValType ty  where (_,    ty) = unOpType  op
impOpType (Select ty _ _ _   ) = IValType ty
impOpType (FFICall _ _ ty _  ) = IValType ty
impOpType op = error $ "Not allowed in Imp IR: " ++ pprint op

pattern IIntTy :: IType
pattern IIntTy = IValType IntType

pattern IIntVal :: Int -> IExpr
pattern IIntVal x = ILit (IntLit x)

pattern IZero :: IExpr
pattern IZero = IIntVal 0

pattern IOne :: IExpr
pattern IOne = IIntVal 1
