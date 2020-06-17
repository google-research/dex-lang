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

import Prelude hiding (pi)
import Control.Monad.Reader
import Control.Monad.Except hiding (Except)
import Control.Monad.State
import Control.Monad.Writer
import Data.Foldable
import Data.Text.Prettyprint.Doc

import Array
import Syntax
import Env
import Type
import PPrint
import Cat
import Util (bindM2)

type EmbedEnv = ([IVar], (Scope, ImpProg))
type ImpM = Cat EmbedEnv

toImpFunction :: ([ScalarTableVar], Block) -> ImpFunction
toImpFunction (vsIn, block) = runImpM vsIn $ do
  (vsOut, prog) <- scopedBlock $ materializeResult
  let vsOut' = flip fmap vsOut (\(v :> IRefType t) -> v :> t)
  return $ ImpFunction vsOut' vsIn prog
  where
    materializeResult = do
      ans <- toImpBlock mempty block
      (outDest, vsOut) <- allocDest Unmanaged $ getType block
      copyAtom outDest ans
      return vsOut

runImpM :: [ScalarTableVar] -> ImpM a -> a
runImpM inVars m = fst $ runCat m (mempty, (inVarScope, mempty))
  where
    inVarScope :: Scope
    inVarScope = fmap (const Nothing) $
      foldMap varAsEnv $ fmap (fmap $ const ()) inVars

toImpBlock :: SubstEnv -> Block -> ImpM Atom
toImpBlock env (Block decls result) = do
  env' <- catFoldM toImpDecl env decls
  toImpExpr (env <> env') result

toImpDecl ::  SubstEnv -> Decl -> ImpM SubstEnv
toImpDecl env (Let b bound) = do
  b' <- traverse (impSubst env) b
  ans <- toImpExpr env bound
  return $ b' @> ans

toImpExpr :: SubstEnv -> Expr -> ImpM Atom
toImpExpr env expr = case expr of
  App x i -> case getType x of
    TabTy _ _ -> do
      x' <- impSubst env x
      i' <- impSubst env i
      impTabGet x' i'
    _ -> error $ "shouldn't have non-table app left"
  Atom x   -> impSubst env x
  Op   op  -> toImpOp =<< traverse (impSubst env) op
  Hof  hof -> toImpHof env hof

impSubst :: HasVars a => SubstEnv -> a -> ImpM a
impSubst env x = do
  -- We already assume that the expression is de-shadowed, so there's no need
  -- to pass in the scope. We don't even maintain one for the Expr we're traversing.
  -- The one in ImpM only keeps the scope for the Imp program!
  return $ subst (env, mempty) x

toImpOp :: PrimOp Atom -> ImpM Atom
toImpOp op = case op of
  TabCon (TabTy n _) rows -> do
    dest <- alloc resultTy
    forM_ (zip [0..] rows) $ \(i, row) -> do
      i' <- intToIndex n $ IIntVal i
      ithDest <- impTabGet dest i'
      copyAtom ithDest row
    return dest
  SumGet x getLeft ->
    case x of
      SumVal _ l r -> return $ if getLeft then l else r
      val -> error $ "Expected a sum type, got: " ++ pprint val
  SumTag x ->
    case x of
      SumVal t _ _ -> return t
      val -> error $ "Expected a sum type, got: " ++ pprint val
  Fst ~(PairVal x _) -> return x
  Snd ~(PairVal _ y) -> return y
  PrimEffect ~(Con (RefCon _ ref)) m -> do
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
             FFICall "int_to_index_set" IntType [i', n']
    return $ toScalarAtom resultTy ans
  Cmp _ _ _ -> error $ "All instances of Cmp should get resolved in simplification"
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
  IndexRef ~(Con (RefCon h ref)) i ->
    liftM (Con . RefCon h) $ impTabGet ref i
  _ -> do
    op' <- traverse fromScalarAtom op
    toScalarAtom resultTy <$> emitInstr (IPrimOp op')
  where
    resultTy :: Type
    resultTy = getType $ Op op

toImpHof :: SubstEnv -> Hof -> ImpM Atom
toImpHof env hof = do
  resultTy <- impSubst env $ getType $ Hof hof
  case hof of
    For d (Lam (Abs b@(_:>idxTy) (_, body))) -> do
      idxTy' <- impSubst env idxTy
      n' <- indexSetSize idxTy'
      dest <- alloc resultTy
      emitLoop d n' $ \i -> do
        i' <- intToIndex idxTy i
        ithDest <- impTabGet dest i'
        ans <- toImpBlock (env <> b @> i') body
        copyAtom ithDest ans
      return dest
    RunReader r (BinaryFunVal region ref _ body) -> do
      r' <- impSubst env r
      toImpBlock (env <> ref @> refVal region r') body
    RunWriter (BinaryFunVal region ref _ body) -> do
      wDest <- alloc wTy
      initializeAtomZero wDest
      aResult <- toImpBlock (env <> ref @> refVal region wDest) body
      return $ PairVal aResult wDest
      where (PairTy _ wTy) = resultTy
    RunState s (BinaryFunVal region ref _ body) -> do
      s' <- impSubst env s
      sDest <- alloc sTy
      copyAtom sDest s'
      aResult <- toImpBlock (env <> ref @> refVal region sDest) body
      return $ PairVal aResult sDest
      where (PairTy _ sTy) = resultTy

refVal :: Var -> Atom -> Atom
refVal region ref = Con (RefCon (Var region) ref)

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
  Con (AGet x)      -> load =<< fromArrayAtom x
  Con (AsIdx _ x)   -> fromScalarAtom x
  Con (AnyValue ty) -> return $ anyValue ty
  _ -> error $ "Expected scalar, got: " ++ pprint atom

fromArrayAtom :: Atom -> ImpM IExpr
fromArrayAtom atom = case atom of
  Var (n:>t) -> return $ IVar (n :> IRefType t)
  _ -> error $ "Expected array, got: " ++ pprint atom

toScalarAtom :: Type -> IExpr -> Atom
toScalarAtom ty ie = case ie of
  ILit l -> Con $ Lit l
  IVar (v :> IValType b) -> case ty of
    BaseTy b' | b == b'     -> Var (v :> ty)
    TC (IntRange _ _)       -> Con $ AsIdx ty $ toScalarAtom IntTy ie
    TC (IndexRange ty' _ _) -> Con $ AsIdx ty $ toScalarAtom ty' ie
    _ -> unreachable
  _ -> unreachable
  where
    unreachable = error $ "Cannot convert " ++ show ie ++ " to " ++ show ty

toArrayAtom :: IExpr -> Atom
toArrayAtom ie = case ie of
  IVar (v :> IRefType t) -> Var $ v :> t
  _                      -> error $ "Not an array atom: " ++ show ie

data AllocType = Managed | Unmanaged

alloc :: Type -> ImpM Atom
alloc ty = fst <$> allocDest Managed ty

allocDest :: AllocType -> Type -> ImpM (Atom, [IVar])
allocDest allocTy ty = do
  (dest, vs) <- makeDest "v" ty
  flip mapM_ vs $ \v@(_:>IRefType refTy) -> do
    numel <- elemCount refTy
    emitStatement (Just v, Alloc refTy numel)
  case allocTy of
    Managed   -> extend $ asFst vs
    Unmanaged -> return ()
  return (dest, vs)

makeDest :: Name -> Type -> ImpM (Atom, [IVar])
makeDest name ty = runWriterT $ makeDest' name id ty

makeDest' :: Name -> (ScalarTableType -> ScalarTableType) -> Type -> WriterT [IVar] ImpM Atom
makeDest' name mkTy (TabTy n b) = do
  Con . AFor n <$> makeDest' name (\t -> mkTy $ TabTy n t) b
makeDest' name mkTy ty@(TC con) = case con of
  BaseType b  -> do
    v <- lift $ freshVar (name :> (IRefType $ mkTy $ BaseTy b))
    tell [v] -- TODO: Revise!
    return $ Con $ AGet $ toArrayAtom (IVar v)
  PairType a b -> PairVal <$> makeDest' name mkTy a <*> makeDest' name mkTy b
  UnitType -> return UnitVal
  IntRange   _ _   -> scalarIndexSet ty
  IndexRange _ _ _ -> scalarIndexSet ty
  _ -> error $ "Can't lower type to imp: " ++ pprint con
  where
    scalarIndexSet t = Con . AsIdx t <$> makeDest' name mkTy IntTy
makeDest' _ _ ty = error $ "Can't lower type to imp: " ++ pprint ty

impTabGet :: Atom -> Atom -> ImpM Atom
impTabGet (Con (AFor it b)) i = do
  i' <- indexToInt it i
  flip traverseLeaves b $ \(~(Con (AGet arr))) -> do
    arr' <- fromArrayAtom arr >>= (`impGet` i')
    return $ Con $ AGet $ toArrayAtom arr'
impTabGet _ _ = error "Expected an array atom in impTabGet"

intToIndex :: Type -> IExpr -> ImpM Atom
intToIndex ty@(TC con) i = case con of
  IntRange _ _      -> iAsIdx
  IndexRange _ _ _  -> iAsIdx
  BaseType BoolType -> toScalarAtom BoolTy <$> emitUnOp UnsafeIntToBool i
  PairType a b -> do
    bSize <- indexSetSize b
    iA <- intToIndex a =<< impDiv i bSize
    iB <- intToIndex b =<< impRem i bSize
    return $ PairVal iA iB
  SumType l r -> do
    ls <- indexSetSize l
    isLeft <- impCmp Less i ls
    li <- intToIndex l i
    ri <- intToIndex r =<< impSub i ls
    return $ Con $ SumCon (toScalarAtom BoolTy isLeft) li ri
  PairType a b -> do
    bSize <- indexSetSize b
    iA <- intToIndex a =<< impDiv i bSize
    iB <- intToIndex b =<< impRem i bSize
    return $ PairVal iA iB
  _ -> error $ "Unexpected type " ++ pprint con
  where
    iAsIdx = return $ Con $ AsIdx ty $ toScalarAtom IntTy i
intToIndex ty _ = error $ "Unexpected type " ++ pprint ty

indexToInt :: Type -> Atom -> ImpM IExpr
indexToInt ty idx = case ty of
  BoolTy  -> emitUnOp BoolToInt =<< fromScalarAtom idx
  SumTy lType rType -> case idx of
    SumVal con lVal rVal -> do
      lTypeSize <- indexSetSize lType
      lInt <- indexToInt lType lVal
      rInt <- impAdd lTypeSize =<< indexToInt rType rVal
      conExpr <- fromScalarAtom con
      impSelect conExpr lInt rInt
    _ -> error $ "Expected a sum constructor, got: " ++ pprint idx
  PairTy a b -> case idx of
    PairVal aIdx bIdx -> do
      aIdx' <- indexToInt a aIdx
      bIdx' <- indexToInt b bIdx
      bSize <- indexSetSize b
      impMul bSize aIdx' >>= impAdd bIdx'
    _ -> error $ "Expected a pair constructor, got: " ++ pprint idx
  TC (IntRange _ _)     -> fromScalarAtom idx
  TC (IndexRange _ _ _) -> fromScalarAtom idx
  _ -> error $ "Unexpected type " ++ pprint ty

fromILitInt :: IExpr -> Int
fromILitInt (ILit (IntLit x)) = x
fromILitInt expr = error $ "Not an int: " ++ pprint expr

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
  PairType a b -> do
    a' <- indexSetSize a
    b' <- indexSetSize b
    impMul a' b'
  BaseType BoolType -> return $ IIntVal 2
  SumType l r -> bindM2 impAdd (indexSetSize l) (indexSetSize r)
  _ -> error $ "Not implemented " ++ pprint con
indexSetSize ty = error $ "Not implemented " ++ pprint ty

elemCount :: ScalarTableType -> ImpM IExpr
elemCount t = case t of
  TabTy n b -> bindM2 impMul (indexSetSize n) (elemCount b)
  BaseTy _  -> return IOne
  _ -> error $ "Not a scalar table type: " ++ pprint t

offsetTo :: ScalarTableType -> IExpr -> ImpM IExpr
offsetTo t i = case t of
  TabTy _ b -> impMul i =<< elemCount b
  BaseTy _  -> error "Indexing into a scalar!"
  _ -> error $ "Not a scalar table type: " ++ pprint t

traverseLeaves :: Applicative m => (Atom -> m Atom) -> Atom -> m Atom
traverseLeaves f atom = case atom of
  Var _        -> f atom
  Con (Lit  _) -> f atom
  Con (AGet _) -> f atom
  Con destCon -> Con <$> case destCon of
    AFor n body -> AFor n  <$> recur body
    AsIdx n idx -> AsIdx n <$> recur idx
    PairCon x y -> PairCon <$> recur x <*> recur y
    UnitCon     -> pure UnitCon
    _ -> error $ "Not a valid Imp atom: " ++ pprint atom
  _ ->   error $ "Not a valid Imp atom: " ++ pprint atom
  where recur = traverseLeaves f

leavesList :: Atom -> [Atom]
leavesList atom = execWriter $ flip traverseLeaves atom $ \l -> tell [l] >> return l

copyAtom :: Atom -> Atom -> ImpM ()
copyAtom dest src = zipWithM_ copyLeaf (leavesList dest) (leavesList src)

-- TODO: Assert dims are equal?
copyLeaf :: Atom -> Atom -> ImpM ()
copyLeaf ~(Con (AGet dest)) src = case src of
  Con (AGet src') -> bindM2 copy  dest' (fromArrayAtom src' )
  _               -> bindM2 store dest' (fromScalarAtom src)
  where dest' = fromArrayAtom dest

initializeAtomZero :: Atom -> ImpM ()
initializeAtomZero x = void $ flip traverseLeaves x $ \(~leaf@((Con (AGet dest)))) ->
  fromArrayAtom dest >>= initializeZero >> return leaf

addToAtom :: Atom -> Atom -> ImpM ()
addToAtom dest src = zipWithM_ addToAtomLeaf (leavesList dest) (leavesList src)

addToAtomLeaf :: Atom -> Atom -> ImpM ()
addToAtomLeaf ~(Con (AGet dest)) src = case src of
  Con (AGet src') -> bindM2 addToDestFromRef dest' (fromArrayAtom src')
  _               -> bindM2 addToDestScalar  dest' (fromScalarAtom src)
  where dest' = fromArrayAtom dest

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
impSelect p x y = emitInstr $ IPrimOp $ Select p x y

impGet :: IExpr -> IExpr -> ImpM IExpr
impGet ref i = case ref of
  (IVar (_ :> IRefType t)) -> emitInstr . IOffset ref =<< (t `offsetTo` i)
  _ -> error $ "impGet called with non-ref: " ++ show ref

copy :: IExpr -> IExpr -> ImpM ()
copy dest src = case dest of
  (IVar (_ :> IRefType t)) -> do
    numElements <- elemCount t
    emitStatement (Nothing, Copy dest src numElements)
  _ -> error $ "copy called with non-ref destination: " ++ show dest

load :: IExpr -> ImpM IExpr
load x = emitInstr $ Load x

store :: IExpr -> IExpr -> ImpM ()
store dest src = emitStatement (Nothing, Store dest src)

freshVar :: IVar -> ImpM IVar
freshVar v = do
  scope <- looks (fst . snd)
  let v' = rename v scope
  extend $ asSnd $ asFst (v' @> Nothing)
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
  IRefType RealTy -> do
    cur  <- load dest
    src' <- load src
    updated <- emitInstr $ IPrimOp $ ScalarBinOp FAdd cur src'
    store dest updated
  IRefType (TabTy n _) -> do
    n' <- indexSetSize n
    emitLoop Fwd n' $ \i -> bindM2 addToDestFromRef (impGet dest i) (impGet src i)
  ty -> error $ "Addition not implemented for type: " ++ pprint ty

addToDestScalar :: IExpr -> IExpr -> ImpM ()
addToDestScalar dest src = do
  cur  <- load dest
  updated <- emitInstr $ IPrimOp $ ScalarBinOp FAdd cur src
  store dest updated

initializeZero :: IExpr -> ImpM ()
initializeZero ref = case impExprType ref of
  IRefType RealTy      -> store ref (ILit (RealLit 0.0))
  IRefType (TabTy n _) -> do
    n' <- indexSetSize n
    emitLoop Fwd n' $ \i -> impGet ref i >>= initializeZero
  ty -> error $ "Zeros not implemented for type: " ++ pprint ty

-- === type checking imp programs ===

-- State keeps track of _all_ names used in the program, Reader keeps the type env.
type ImpCheckM a = StateT (Env ()) (ReaderT (Env IType) (Either Err)) a

instance Checkable ImpFunction where
  checkValid (ImpFunction _ vsIn (ImpProg prog)) = do
    let scope = foldMap (varAsEnv . fmap (const ())) vsIn
    let env   = foldMap (varAsEnv . fmap IRefType) vsIn
    void $ runReaderT (runStateT (checkProg prog) scope) env

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
  Copy dest source _ -> do
    destTy   <- (checkIExpr >=> fromRefType) dest
    sourceTy <- (checkIExpr >=> fromRefType) source
    assertEq sourceTy destTy "Type mismatch in copy"
    return Nothing
  Alloc ty _ -> return $ Just $ IRefType ty
  Free _   -> return Nothing  -- TODO: check matched alloc/free
  Loop _ i size (ImpProg block) -> do
    checkInt size
    checkBinder i
    extendR (i @> IIntTy) $ checkProg block
    return Nothing
  IOffset e i -> do
    ~(IRefType (TabTy _ b)) <- checkIExpr e
    checkInt i
    return $ Just $ IRefType b

checkBinder :: IVar -> ImpCheckM ()
checkBinder v = do
  scope <- get
  when (v `isin` scope) $ throw CompilerErr $ "shadows: " ++ pprint v
  modify (<>(v@>()))

checkValidType :: IType -> ImpCheckM ()
checkValidType (IValType _)           = return ()
checkValidType (IRefType (TabTy _ b)) = checkValidType $ IRefType b
checkValidType (IRefType (BaseTy _))  = return ()
checkValidType t = throw CompilerErr $ "Invalid Imp type: " ++ show t

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
  op' <- traverse checkIExpr op
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
    Select _ x y -> checkEq x y >> return x
    FFICall _ ty _ -> return $ IValType ty -- TODO: check
    _ -> error $ "Not allowed in Imp IR: " ++ pprint op
  where
    checkEq :: (Pretty a, Show a, Eq a) => a -> a -> ImpCheckM ()
    checkEq t t' = assertEq t t' (pprint op)

fromRefType :: MonadError Err m => IType -> m ScalarTableType
fromRefType (IRefType ty) = return ty
fromRefType ty = throw CompilerErr $ "Not a reference type: " ++ pprint ty

fromScalarRefType :: MonadError Err m => IType -> m BaseType
fromScalarRefType (IRefType (BaseTy b)) = return b
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
  Copy  _ _ _     -> return Nothing
  Alloc ty _      -> return $ Just $ IRefType ty
  Free _          -> return Nothing
  Loop _ _ _ _    -> return Nothing
  IOffset e _     -> case impExprType e of
    IRefType (TabTy _ b) -> return $ Just $ IRefType b
    ty -> error $ "Can't index into: " ++ pprint ty

impOpType :: IPrimOp -> IType
impOpType (ScalarBinOp op _ _) = IValType ty  where (_, _, ty) = binOpType op
impOpType (ScalarUnOp  op _  ) = IValType ty  where (_,    ty) = unOpType  op
impOpType (Select _ x _    )   = impExprType x
impOpType (FFICall _ ty _ ) = IValType ty
impOpType op = error $ "Not allowed in Imp IR: " ++ pprint op

pattern IIntTy :: IType
pattern IIntTy = IValType IntType

pattern IIntVal :: Int -> IExpr
pattern IIntVal x = ILit (IntLit x)

pattern IZero :: IExpr
pattern IZero = IIntVal 0

pattern IOne :: IExpr
pattern IOne = IIntVal 1
