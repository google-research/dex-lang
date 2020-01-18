-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}

module Type (TypeEnv, checkTyped, getType, atomType, litType, unpackExists,
             builtinType, BuiltinType (..), instantiateTVs, abstractTVs,
             checkNExpr, patType, tangentBunType, listIntoRecord, flattenType,
             getNExprType, splitLinArgs, nBuiltinType, isAtomicBuiltin) where
import Control.Monad
import Control.Monad.Except hiding (Except)
import Control.Monad.Reader
import Data.List (elemIndex)
import Data.Foldable
import Data.Either (isLeft)
import Data.Text.Prettyprint.Doc

import Syntax
import Env
import Record
import Pass
import PPrint
import Cat
import Util (traverseFun)

-- TODO: consider making linearity checking a separate pass?
type TypeEnv = FullEnv SigmaType Kind
data Spent = Spent (Env ()) Bool
type TypeCheckEnv = FullEnv (SigmaType, Spent) Kind
data TypeMCtx = TypeMCtx { srcCtx   :: SrcCtx
                         , tyEnv    :: TypeCheckEnv }
type TypeM a = ReaderT TypeMCtx (CatT Spent (Either Err)) a

checkTyped :: TopPass TopDecl TopDecl
checkTyped = TopPass $ \decl -> [stripSrcAnnotTopDecl decl] <$ case decl of
  TopDecl _ decl' -> do
    env <- liftTop (getTypeDecl decl')
    extend env
  RuleDef ann ty tlam -> do
    _ <- liftTop $ getTypeDecl $ LetPoly ("_":>ty) tlam
    liftTop $ checkRuleDefType ann ty
  EvalCmd (Command GetType expr) -> do
    ty <- liftTop (getTypeChecked expr)
    emitOutput $ TextOut $ pprint ty
  EvalCmd (Command _ expr) -> do
    ty <- liftTop (getTypeChecked expr)
    env <- look
    when (isLeft (checkData env ty)) $
      throwTopErr $ Err TypeErr Nothing (" Can't print values of type: " ++ pprint ty)

liftTop :: TypeM a -> TopPassM TypeCheckEnv a
liftTop m = do
  env <- look
  liftExceptTop $ evalTypeM (TypeMCtx Nothing env) m

evalTypeM :: TypeMCtx -> TypeM a -> Except a
evalTypeM env m = liftM fst $ runCatT (runReaderT m env) mempty

getTypeChecked :: Expr -> TypeM Type
getTypeChecked expr = case expr of
    Lit c -> do
      when (c == realZero) spendFreely
      return $ BaseType (litType c)
    Var v ty ts -> do
      mapM_ checkTy ts
      x <- asks $ flip envLookup v . tyEnv
      case x of
        Just (L (Forall kinds body, s)) -> do
          checkWithCtx $ do spend s
                            zipWithM_ checkClassConstraints kinds ts
          let ty' = instantiateTVs ts body
          assertEq ty ty' "Var annotation"
          return ty
        _ -> throw CompilerErr $ "Lookup failed:" ++ pprint v
    PrimOp Scan ~ts@[cTy, yTy, n] ~[x, fs] -> do
      let (For ip (Lam _ p body)) = stripSrcAnnot fs
      checkWithCtx $ do
          mapM_ checkTy ts
          zipWithM_ checkClassConstraints [isData, noCon, idxSet] ts
          (xTy, xSpent) <- scoped $ recur x
          let env = foldMap (asEnv mempty) ip <> foldMap (asEnv xSpent) p
          (bodyTy, bodySpent) <- scoped $ extendTyEnv env $ recur body
          assertEq cTy xTy "Scan carry"
          assertEq (pair cTy yTy) bodyTy "Scan body"
          case spendCart xSpent bodySpent of
            Nothing -> throwCartErr [xSpent, bodySpent]
            Just s  -> extend s
      return $ pair cTy (n==>yTy)
    PrimOp b ts args -> do
      checkWithCtx $ do
          mapM_ checkTy ts
          zipWithM_ checkClassConstraints kinds ts
          argTys'' <- liftM2 (++) (traverseProd k recur linArgs)
                                  (checkNothingSpent $ traverse recur nlArgs)
          assertEq argTys' argTys'' "Builtin"
      return ansTy'
      where
        BuiltinType kinds (numLin, k) argTys ansTy = builtinType b
        (ansTy':argTys') = map (instantiateTVs ts) (ansTy:argTys)
        (linArgs, nlArgs) = splitAt numLin args
    Decl (DoBind p bound) body -> do
      checkShadowPat p
      (eff, spent) <- scoped $ do
                        ~(Monad eff a) <- recur bound
                        assertEq (patType p) a "DoBind"
                        return eff
      ~(Monad eff' retTy) <- extendTyEnv (foldMap (asEnv spent) p) $ recur body
      assertEq eff eff' "Effect type mismatch"
      return $ Monad eff retTy
    Decl decl body -> do
      env <- getTypeDecl decl
      extendTyEnv env (recur body)
    Lam m p body -> do
      checkWithCtx $ checkTy (patType p) >> checkShadowPat p
      bodyTy <- case m of
        Mult Lin -> do v <- getPatName p
                       checkSpent v (pprint p) $ recurWithP (asSpent v) p body
        _ -> recurWithP mempty p body
      return $ ArrType m (patType p) bodyTy
    For p body -> do
      checkWithCtx $ do
          checkClassConstraint IdxSet (patType p)
          checkTy (patType p)
          checkShadowPat p
      liftM (TabType (patType p)) (recurWithP mempty p body)
    App e arg  -> do
      ~(ArrType (Mult l) a b) <- recur e
      checkWithCtx $ do
          a' <- case l of Lin    ->                     recur arg
                          NonLin -> checkNothingSpent $ recur arg
          assertEq a a' "App"
      return b
    Get e ie   -> do
      ~(TabType a b) <- recur e
      checkWithCtx $ do a' <- recur ie
                        assertEq a a' "Get"
      return b
    RecCon k r -> liftM (RecType k) (traverseProd k recur r)
    TabCon ty xs -> do
      checkWithCtx $ checkClassConstraint Data ty
      case ty of
        TabType _ bodyTy -> do
          xTys <- mapM recur xs
          mapM_ (\t -> assertEq bodyTy t "table")  xTys  -- TODO: check length too
          return ty
        _ -> throw CompilerErr $ "Expected a table type: " ++ pprint ty
    Pack e ty exTy -> do
      let (Exists exBody) = exTy
      rhsTy <- recur e
      assertEq (instantiateTVs [ty] exBody) rhsTy "Pack"
      return exTy
    IdxLit n i | 0 <= i && i < n -> return $ IdxSetLit n
               | otherwise -> throw TypeErr $ "Index out of bounds: "
                                ++ pprint i ++ " of " ++ pprint n
    SrcAnnot e pos -> local (\r -> r {srcCtx = Just pos}) (recur e)
    Annot _ _    -> error $ "Shouldn't have annot left"
  where
    recur = getTypeChecked
    recurWithP s p  = extendTyEnv (foldMap (asEnv s) p) . recur

getTypeDecl :: Decl -> TypeM TypeCheckEnv
getTypeDecl decl = case decl of
  LetMono p rhs -> do
    checkShadowPat p
    ((), spent) <- scoped $ checkWithCtx $ do
                       ty <- recur rhs
                       assertEq (patType p) ty "LetMono"
    return (foldMap (asEnv spent) p)
  DoBind _ _ -> error "Shouldn't have DoBind here"
  LetPoly b@(v:>ty) tlam -> do
    checkShadow b
    ((), spent) <- scoped $ checkWithCtx $ do
                       ty' <- getTypeTLam tlam
                       assertEq ty ty' "TLam"
    return $ v @> L (ty, spent)
  Unpack b tv _ -> do  -- TODO: check bound expression!
    -- TODO: check leaks
    let tb = tv :> idxSet
    checkShadow b
    checkShadow tb
    extendTyEnv (tbind tb) $ checkTy (binderAnn b)
    return (tbind tb <> asEnv mempty b)
  TyDef NewType v [] ty -> do
    checkTy ty
    classes <- getClasses ty
    return (v @> T classes)
  TyDef NewType _ _ _ -> error "Type parameters in newtype not implemented"
  TyDef TyAlias _ _ _ -> error "Shouldn't have TAlias left"
  where
    recur = getTypeChecked

extendTyEnv :: TypeCheckEnv -> TypeM a -> TypeM a
extendTyEnv env m = local (\ctx -> ctx { tyEnv = tyEnv ctx <> env }) m

checkWithCtx :: TypeM () -> TypeM ()
checkWithCtx m = do
  pos <- asks srcCtx
  addSrcContext pos m

getTypeTLam :: TLam -> TypeM SigmaType
getTypeTLam (TLam tbs body) = do
  mapM_ checkShadow tbs
  ty <- extendTyEnv (foldMap tbind tbs) (getTypeChecked body)
  let (vs, kinds) = unzip [(v, k) | v :> k <- tbs]
  return $ Forall kinds (abstractTVs vs ty)

checkTy :: Type -> TypeM ()
checkTy _ = return () -- TODO: check kind and unbound type vars

checkShadow :: BinderP b -> TypeM ()
checkShadow (v :> _) = checkWithCtx $ do
  env <- asks tyEnv
  if v `isin` env
    then throw CompilerErr $ pprint v ++ " shadowed"
    else return ()

checkShadowPat :: Traversable f => f (BinderP b) -> TypeM ()
checkShadowPat pat = mapM_ checkShadow pat -- TODO: check mutual shadows!

asEnv :: Spent -> Binder -> TypeCheckEnv
asEnv s (v:>ty) = v @> L (asSigma ty, s)

unpackExists :: Type -> Name -> Except Type
unpackExists (Exists body) v = return $ instantiateTVs [TypeVar v] body
unpackExists ty _ = throw CompilerErr $ "Can't unpack " ++ pprint ty

checkRuleDefType :: RuleAnn -> SigmaType -> TypeM ()
checkRuleDefType (LinearizationDef v) linTy = do
  ty@(Forall kinds body, _) <- asks $ fromL . (!v) . tyEnv
  (a, b) <- case body of
              ArrType _ a b -> return (a, b)
              _ -> throw TypeErr $
                     "Bad type for linearization-annotated function: " ++ pprint ty
  let linTyExpected = Forall kinds $ a --> RecType Cart (Tup [b, a --@ b])
  unless (linTy == linTyExpected) $ throw TypeErr $
     "Annotation should have type: " ++ pprint linTyExpected

patType :: RecTree Binder -> Type
patType (RecLeaf (_:>ty)) = ty
patType (RecTree r) = RecType Cart $ fmap patType r

litType :: LitVal -> BaseType
litType v = case v of
  IntLit  _ -> IntType
  RealLit _ -> RealType
  StrLit  _ -> StrType
  BoolLit _ -> BoolType

-- BuiltinType represents types of the form
--     forall [_, _]. (_, _, _) --o (_,_,_) -> _
--  or forall [_, _]. (_: _: _) --o (_,_,_) -> _
type LinSpec = (Int, ProdKind)  -- Int is number of linear args
data BuiltinType = BuiltinType [Kind] LinSpec [Type] Type

noCon :: Kind
noCon = Kind []

idxSet :: Kind
idxSet = Kind [IdxSet]

vspace :: Kind
vspace = Kind [VSpace]

isData :: Kind
isData = Kind [Data]

getType :: Expr -> Type
getType expr = case expr of
    Lit c      -> BaseType (litType c)
    Var _ ty _ -> ty
    PrimOp b ts _ -> instantiateTVs ts ansTy
      where BuiltinType _ _ _ ansTy = builtinType b
    Decl _ body  -> getType body
    Lam m p body -> ArrType m (patType p) (getType body)
    For   p body -> TabType   (patType p) (getType body)
    App e _ -> b where (ArrType _ _ b) = getType e
    Get e _ -> b where (TabType   _ b) = getType e
    RecCon k r   -> RecType k $ fmap getType r
    TabCon ty _  -> ty
    Pack _ _ ty  -> ty
    IdxLit n _   -> IdxSetLit n
    SrcAnnot e _ -> getType e
    Annot _ _    -> error $ "Shouldn't have annot left"

builtinType :: Builtin -> BuiltinType
builtinType builtin = case builtin of
  IAdd     -> ibinOpType
  ISub     -> ibinOpType
  IMul     -> ibinOpType
  Rem      -> ibinOpType
  Cmp _    -> nonLinBuiltin [isData] [a, a] bool
  Pow      -> ibinOpType
  FAdd     -> BuiltinType [] (2, Cart) [real, real] real
  FSub     -> BuiltinType [] (2, Cart) [real, real] real
  FMul     -> BuiltinType [] (2, Tens) [real, real] real
  FDiv     -> BuiltinType [] (1, Cart) [real, real] real
  FNeg     -> BuiltinType [] (1, Cart) [real] real
  And      -> BuiltinType [] (0, Cart) [bool, bool] bool
  Or       -> BuiltinType [] (0, Cart) [bool, bool] bool
  Not      -> BuiltinType [] (0, Cart) [bool] bool
  Todo     -> nonLinBuiltin [noCon] [] a
  NewtypeCast -> nonLinBuiltin [noCon, noCon] [a] b
  -- This is only used for inference. Scan is handled specially wrt linearity.
  Scan     -> nonLinBuiltin [isData, noCon, idxSet]
                [a, k ==> (a --> pair a b)] (pair a (k==>b))
  IndexAsInt -> nonLinBuiltin [idxSet] [i] int
  IntAsIndex -> nonLinBuiltin [idxSet] [int] i
  IdxSetSize -> nonLinBuiltin [idxSet] [] int
  Range    -> nonLinBuiltin [] [int] (Exists unitTy)
  BoolToInt -> nonLinBuiltin [] [bool] int
  IntToReal -> nonLinBuiltin [] [int] real
  Select    -> nonLinBuiltin [isData] [bool, a, a] a
  -- TODO: this breaks for tuple or non-reals
  Linearize   -> nonLinBuiltin [vspace, vspace] [a --> b, a] (pair b (a --@ b))
  Transpose   -> BuiltinType [vspace, vspace] (1, Tens) [a --@ b] (b --@ a)
  VZero   -> nonLinBuiltin [vspace] [] a
  VAdd    -> nonLinBuiltin [vspace] [a, a] a
  VSingle -> nonLinBuiltin [vspace, idxSet] [j, a] (j ==> a)
  VSum    -> nonLinBuiltin [vspace, idxSet] [j ==> a] a
  Filter -> nonLinBuiltin [noCon, idxSet]
              [a --> bool, j ==> a] (Exists (i==>a'))
    where a' = BoundTVar 1  -- under an extra binder
  FFICall n _ -> nonLinBuiltin kinds argTys retTy
    where kinds = take (n + 1) (repeat noCon)
          retTy:argTys = take (n + 1) (map BoundTVar [0..])
  MemRef _ -> nonLinBuiltin [isData] [] a
  MRun    -> nonLinBuiltin (monadCon ++ [noCon]) [r, s, monad d] (tup [d, w, s])
  MPrim mprim -> case mprim of
    MAsk    -> nonLinBuiltin (monadCon ++ [noCon]) [Lens r d] (monad d)
    MTell   -> nonLinBuiltin (monadCon ++ [vspace]) [Lens w d, d] (monad unitTy)
    MGet    -> nonLinBuiltin (monadCon ++ [noCon]) [Lens s d] (monad d)
    MPut    -> nonLinBuiltin (monadCon ++ [noCon]) [Lens s d, d] (monad unitTy)
    MReturn -> nonLinBuiltin (monadCon ++ [noCon]) [d] (monad d)
  LensGet -> nonLinBuiltin [noCon, noCon] [a, Lens a b] b
  LensPrim p -> case p of
    IdxAsLens   -> nonLinBuiltin [idxSet, noCon] [i] (Lens (i==>b) b)
    LensCompose -> nonLinBuiltin [noCon, noCon, noCon] [Lens a b, Lens b c] (Lens a c)
    LensId      -> nonLinBuiltin [noCon] [] (Lens a a)
  where
    ibinOpType    = nonLinBuiltin [] [int , int ] int
    [r, w, s] = map BoundTVar [0,1,2]
    i = BoundTVar 0
    a = BoundTVar 0
    b = BoundTVar 1
    c = BoundTVar 2
    d = BoundTVar 3
    j = BoundTVar 1
    k = BoundTVar 2
    int  = BaseType IntType
    real = BaseType RealType
    bool = BaseType BoolType
    tup xs = RecType Cart (Tup xs)
    nonLinBuiltin kinds argTys ansTy = BuiltinType kinds (0, Cart) argTys ansTy
    monad a' = Monad (Effect r w s) a'
    -- Specializing writer monad to vector space addition for now
    monadCon = [noCon, vspace, noCon]

pair :: Type -> Type -> Type
pair x y = RecType Cart (Tup [x, y])

instantiateTVs :: [Type] -> Type -> Type
instantiateTVs vs x = subAtDepth 0 sub x
  where sub depth tvar =
          case tvar of
            Left v -> TypeVar v
            Right i | i >= depth -> if i' < length vs && i >= 0
                                      then vs !! i'
                                      else error $ "Bad index: "
                                             ++ show i' ++ " / " ++ pprint vs
                                             ++ " in " ++ pprint x
                    | otherwise  -> BoundTVar i
              where i' = i - depth

abstractTVs :: [Name] -> Type -> Type
abstractTVs vs x = subAtDepth 0 sub x
  where sub depth tvar = case tvar of
                           Left v -> case elemIndex v vs of
                                       Nothing -> TypeVar v
                                       Just i  -> BoundTVar (depth + i)
                           Right i -> BoundTVar i

subAtDepth :: Int -> (Int -> Either Name Int -> Type) -> Type -> Type
subAtDepth d f ty = case ty of
    BaseType _    -> ty
    TypeVar v     -> f d (Left v)
    ArrType m a b -> ArrType (recur m) (recur a) (recur b)
    TabType a b   -> TabType (recur a) (recur b)
    RecType k r   -> RecType k (fmap recur r)
    TypeApp a b   -> TypeApp (recur a) (map recur b)
    Monad eff a   -> Monad (fmap recur eff) (recur a)
    Lens a b      -> Lens (recur a) (recur b)
    Exists body   -> Exists (recurWith 1 body)
    IdxSetLit _   -> ty
    BoundTVar n   -> f d (Right n)
    Mult _        -> ty
    NoAnn         -> NoAnn
  where recur        = subAtDepth d f
        recurWith d' = subAtDepth (d + d') f


-- === Built-in type classes ===

checkClassConstraints :: Kind -> Type -> TypeM ()
checkClassConstraints (Kind cs) ty =
  checkWithCtx $ mapM_ (flip checkClassConstraint ty) cs

checkClassConstraint :: ClassName -> Type -> TypeM ()
checkClassConstraint c ty = do
  env <- asks tyEnv
  liftEither $ checkClassConstraint' env c ty

getClasses :: Type -> TypeM Kind
getClasses ty = do
  env <- asks tyEnv
  return $ Kind $ filter (isInClass env) [VSpace, IdxSet, Data]
  where
    isInClass env c = case checkClassConstraint' env c ty of Left  _ -> False
                                                             Right _ -> True

checkClassConstraint' :: TypeCheckEnv -> ClassName -> Type -> Except ()
checkClassConstraint' env c ty = case c of
  VSpace -> checkVSpace env ty
  IdxSet -> checkIdxSet env ty
  Data   -> checkData   env ty

checkVSpace :: TypeCheckEnv -> Type -> Except ()
checkVSpace env ty = case ty of
  TypeVar v         -> checkVarClass env VSpace v
  BaseType RealType -> return ()
  TabType _ a       -> recur a
  RecType _ r       -> mapM_ recur r
  _                 -> throw TypeErr $ " Not a vector space: " ++ pprint ty
  where recur = checkVSpace env

checkIdxSet :: TypeCheckEnv -> Type -> Except ()
checkIdxSet env ty = case ty of
  TypeVar v   -> checkVarClass env IdxSet v
  IdxSetLit _ -> return ()
  RecType _ r -> mapM_ recur r
  _           -> throw TypeErr $ " Not a valid index set: " ++ pprint ty
  where recur = checkIdxSet env

checkData :: TypeCheckEnv -> Type -> Except ()
checkData env ty = case ty of
  TypeVar v   -> checkVarClass env IdxSet v `catchError`
                    const (checkVarClass env Data v)
  BaseType _  -> return ()
  TabType _ a -> recur a
  RecType _ r -> mapM_ recur r
  IdxSetLit _ -> return ()
  Exists a    -> recur a
  _           -> throw TypeErr $ " Not serializable data: " ++ pprint ty
  where recur = checkData env

checkVarClass :: TypeCheckEnv -> ClassName -> Name -> Except ()
checkVarClass env c v = do
  case envLookup env v of
    Just (T (Kind cs)) ->
      unless (c `elem` cs) $ throw TypeErr $ " Type variable \""  ++ pprint v ++
                                             "\" not in class: " ++ pprint c
    _ -> throw CompilerErr $ "Lookup of kind failed:" ++ pprint v

-- === Normalized IR ===

type NTypeEnv = FullEnv (Type, Spent) ()
type NTypeM a = ReaderT NTypeEnv (CatT Spent (Either Err)) a

checkNExpr ::TopPass NTopDecl NTopDecl
checkNExpr = TopPass $ \topDecl -> [topDecl] <$ case topDecl of
  NTopDecl _ decl -> do
    env <- liftPass (pprint decl) $ checkNDecl decl
    extend env
  NRuleDef _ _ _ -> return () -- TODO!
  NEvalCmd (Command _ (_, expr)) ->
    liftPass (pprint expr) $ void $ getNTypeChecked expr
  where
    liftPass :: String -> NTypeM a -> TopPassM NTypeEnv a
    liftPass ctx m = do
      env <- look
      liftM fst $ liftExceptTop $ addContext ctx $
        runCatT (runReaderT m env) mempty

getNTypeChecked :: NExpr -> NTypeM Type
getNTypeChecked expr = case expr of
  NDecl decl body -> do
    env <- checkNDecl decl
    extendR env $ getNTypeChecked body
  NScan x (NLamExpr ~[ib@(_:>i), xb] body) -> do
    checkNBinder ib
    let carryTy = binderAnn xb
    checkNBinder xb
    (x', xSpent) <- scoped $ atomTypeChecked x
    assertEq carryTy x' "Scan arg"
    let env = nBinderEnv xSpent xb <> nBinderEnv mempty ib
    (bodyTy, bodySpent) <- scoped $ extendR env (getNTypeChecked body)
    let (carryTy', outTy) = fromPairTy bodyTy
    assertEq carryTy carryTy' "Scan output"
    case spendCart xSpent bodySpent of
      Nothing -> throwCartErr [xSpent, bodySpent]
      Just s  -> extend s
    return $ pairTy carryTy (TabType i outTy)
  NPrimOp Todo ~[ty] _ -> checkNTy ty >> return ty
  NPrimOp b ts x -> do
    assertEq False (isAtomicBuiltin b) $ "Atomic builtin in NExpr: " ++ pprint b
    checkPrimOpType b ts x
  NApp e x -> do
    ~(ArrType (Mult l) a b) <- atomTypeChecked e
    -- TODO: use cartesian/tensor information from function type
    a' <- case l of Lin    ->                     atomTypeChecked x
                    NonLin -> checkNothingSpent $ atomTypeChecked x
    assertEq a a' "App"
    return b
  NRecGet e i -> do
    ty <- atomTypeChecked e
    case ty of
      RecType _ r -> return $ recGet r i
      _ -> throw CompilerErr $ "Expected record, got: " ++ pprint ty
  NAtom x -> atomTypeChecked x
  NTabCon n ty xs -> do
    xTys <- mapM atomTypeChecked xs
    mapM_ (\t -> assertEq ty t "Tab constructor") xTys
    return $ TabType n ty

checkNDecl :: NDecl -> NTypeM NTypeEnv
checkNDecl decl = case decl of
  NLet b expr -> do
    checkNBinder b
    (t, s) <- scoped $ getNTypeChecked expr
    assertEq (binderAnn b) t "Decl"
    return $ nBinderEnv s b
  NUnpack b tv _ -> do  -- TODO: check bound expression!
    checkNShadow (tv :> idxSet)
    extendR (tv @> T ()) $ checkNBinder b
    return $ nBinderEnv mempty b <> tv @> T ()

nBinderEnv :: Spent -> NBinder -> NTypeEnv
nBinderEnv s (v:>ty) = v @> L (ty, s)

atomType :: NAtom -> Type
atomType atom = case atom of
  NLit x    -> BaseType (litType x)
  NVar _ ty -> ty
  NGet e _  -> b where (TabType _ b) = atomType e
  NAtomicFor (_:>n) body -> TabType n (getNExprType body)
  NLam m lam -> ArrType m a b  where ([a], b) = nLamType lam
  NRecCon k r -> RecType k $ fmap atomType r
  NAtomicPrimOp b ts _ -> ansTy
    where (_, ansTy, _) = ignoreExcept $ nBuiltinType b ts
  NDoBind _ f -> snd $ nLamType f

nLamType :: NLamExpr -> ([Type], Type)
nLamType (NLamExpr bs body) = (map binderAnn bs, getNExprType body)

getNExprType :: NExpr -> Type
getNExprType expr = case expr of
  NDecl _ body -> getNExprType body
  NScan _ (NLamExpr ~[_:>n, _] body) -> pairTy carryTy (TabType n outTy)
    where (RecType _ (Tup [carryTy, outTy])) = getNExprType body
  NPrimOp b ts _ -> ansTys
    where (_, ansTys, _) = ignoreExcept $ nBuiltinType b ts
  NApp e _ -> b  where (ArrType _ _ b) = atomType e
  NRecGet e i -> case atomType e of
      RecType _ r -> recGet r i
      ty          -> error $ "Expected record, got: " ++ pprint ty
  NAtom x -> atomType x
  NTabCon n ty _ -> TabType n ty

atomTypeChecked :: NAtom -> NTypeM Type
atomTypeChecked atom = case atom of
  NLit x -> do
    when (x == realZero) spendFreely
    return $ BaseType (litType x)
  NVar v ty -> do
    x <- asks $ flip envLookup v
    case x of
      Just (L (ty', s)) -> do
        spend s
        assertEq ty' ty "NVar annot"
        return ty
      _ -> throw CompilerErr $ "Lookup failed:" ++ pprint v
  NGet e i -> do
    ~(TabType a b) <- atomTypeChecked e
    a' <- atomTypeChecked i
    assertEq a a' "Get"
    return b
  NAtomicFor b body -> do
    checkNBinder b
    bodyTy <- extendR (nBinderEnv mempty b) (getNTypeChecked body)
    return $ TabType (binderAnn b) bodyTy
  NLam (Mult NonLin) lam -> do
    (~[a], b) <- lamTypeChecked lam
    return $ ArrType (Mult NonLin) a b
  NLam (Mult Lin) (NLamExpr ~[b@(v:>_)] body) -> do
    checkNBinder b
    let env = nBinderEnv (asSpent v) b
    bodyTys <- checkSpent v (pprint b) $ extendR env (getNTypeChecked body)
    return $ ArrType (Mult Lin) (binderAnn b) bodyTys
  NLam ty _ -> error $ "Expected multiplicity, got: " ++ pprint ty
  NRecCon k r -> liftM (RecType k) (traverseProd k atomTypeChecked r)
  NDoBind m f -> do
    mTy <- atomTypeChecked m
    (~[a], mb) <- lamTypeChecked f
    case mb of
      Monad eff b -> do
        assertEq mTy (Monad eff a) "Mismatch in bind"
        return $ Monad eff b
      _ -> throw CompilerErr $ "expected monad, got " ++ pprint mb
  NAtomicPrimOp b ts xs -> do
    assertEq True (isAtomicBuiltin b) $ "Non-atomic builtin in NExpr: " ++ pprint b
    checkPrimOpType b ts xs

checkPrimOpType :: Builtin -> [Type] -> [NAtom] -> NTypeM Type
checkPrimOpType b tys xs = do
  mapM_ checkNTy tys
  (argTys, ansTys, lin) <- nBuiltinType b tys
  argTys' <- sequenceLinArgs lin (map atomTypeChecked xs)
  assertEq argTys argTys' (pprint b)
  return ansTys

lamTypeChecked :: NLamExpr -> NTypeM ([Type], Type)
lamTypeChecked (NLamExpr bs body) = do
  mapM_ checkNBinder bs
  bodyTy <- extendR (foldMap (nBinderEnv mempty) bs) (getNTypeChecked body)
  return (map binderAnn bs, bodyTy)

checkNTy :: Type -> NTypeM ()
checkNTy _ = return () -- TODO!

checkNBinder :: NBinder -> NTypeM ()
checkNBinder b = do
  checkNTy (binderAnn b)
  checkNShadow b

checkNShadow :: BinderP b -> NTypeM ()
checkNShadow (v :> _) = do
  env <- ask
  if v `isin` env
    then throw CompilerErr $ pprint v ++ " shadowed"
    else return ()

-- TODO: check number of type args first
nBuiltinType :: MonadError Err m
             => Builtin -> [Type] -> m ([Type], Type, ArgLinearity)
nBuiltinType builtin ts =
  case builtin of
    IAdd  -> return $ ibinOpType
    ISub  -> return $ ibinOpType
    IMul  -> return $ ibinOpType
    Rem   -> return $ ibinOpType
    Pow   -> return $ ibinOpType
    FAdd  -> return $ cartBuiltin [real, real] real
    FSub  -> return $ cartBuiltin [real, real] real
    FNeg  -> return $ cartBuiltin [real]       real
    FMul  -> return $ tensBuiltin [real, real] real
    FDiv  -> return $ ([real, real], real, [(Lin, 1), (NonLin, 1)])
    And   -> return $ nonLinBuiltin [bool, bool] bool
    Or    -> return $ nonLinBuiltin [bool, bool] bool
    Not   -> return $ nonLinBuiltin [bool]       bool
    Todo  -> return $ nonLinBuiltin [] t  where [t] = ts
    Range -> return $ nonLinBuiltin [int] (Exists (unitTy))
    IdxSetSize -> return $ nonLinBuiltin [] int
    IndexAsInt -> return $ nonLinBuiltin [i] int  where [i] = ts
    IntAsIndex -> return $ nonLinBuiltin [int] i  where [i] = ts
    BoolToInt  -> return $ nonLinBuiltin [bool] int
    IntToReal  -> return $ nonLinBuiltin [int] real
    Cmp _ -> return $ nonLinBuiltin [t, t] bool      where [t] = ts
    Select -> return $ nonLinBuiltin [bool, t, t] t  where [t] = ts
    Linearize -> return ( [ArrType (Mult NonLin) a b, a]
                        , pairTy b (ArrType (Mult Lin) a b)
                        , [(NonLin, 2)])
      where [a, b] = ts
    Transpose -> return ( [ArrType (Mult Lin) as bs]
                        , (ArrType (Mult Lin) bs as)
                        , [(Lin, 1)] )
      where [as, bs] = ts
    MemRef _ -> return $ nonLinBuiltin [] t  where [t] = ts
    FFICall _ _ -> return (argTys, retTy, [(NonLin, length argTys)])
      where retTy:argTys = ts
    -- TODO: make this easier (just derive from Expr type?)
    MRun -> do
      let [a] = tyArgs
      return $ nonLinBuiltin [r, s, monad a] (RecType Cart $ Tup [a, w, s])
      where
        r:w:s:tyArgs = ts
        monad a = Monad (Effect r w s) a
    MPrim mprim -> case mprim of
      MAsk  -> return $ nonLinBuiltin [Lens r a]    (monad a)
      MTell -> return $ nonLinBuiltin [Lens w a, a] (monad unitTy)
      MGet  -> return $ nonLinBuiltin [Lens s a]    (monad a)
      MPut  -> return $ nonLinBuiltin [Lens s a, a] (monad unitTy)
      MReturn -> return $ nonLinBuiltin [a] (monad a)
      where
        [r, w, s, a] = ts
        monad b = Monad (Effect r w s) b
    LensGet -> return $ nonLinBuiltin [a, Lens a b] b  where [a, b] = ts
    LensPrim p -> case p of
      IdxAsLens   -> return $ nonLinBuiltin [n] (Lens (TabType n a) a)
         where [n, a] = ts
      LensCompose -> return $ nonLinBuiltin [Lens a b, Lens b c ] (Lens a c)
         where [a, b, c] = ts
      LensId      -> return $ nonLinBuiltin [] (Lens a a)  where [a] = ts
    _ -> throw TypeErr $ "Can't have this builtin in NExpr: " ++ pprint builtin
  where
    nonLinBuiltin xs y = (xs, y, [(NonLin, length xs)])
    cartBuiltin   xs y = (xs, y, [(Lin, length xs)])
    tensBuiltin   xs y = (xs, y, [(Lin, 1) | _ <- xs])
    ibinOpType = nonLinBuiltin [int, int] int
    int  = BaseType IntType
    real = BaseType RealType
    bool = BaseType BoolType

pairTy :: Type -> Type -> Type
pairTy x y = RecType Cart $ Tup [x, y]

fromPairTy :: Type -> (Type, Type)
fromPairTy (RecType _ (Tup [x, y])) = (x, y)
fromPairTy ty = error $ "Not a pair type: " ++ pprint ty

isAtomicBuiltin :: Builtin -> Bool
isAtomicBuiltin (MPrim    _) = True
isAtomicBuiltin (LensPrim _) = True
isAtomicBuiltin _            = False

tangentBunType :: Type -> Type
tangentBunType ty = case ty of
  BaseType b -> case b of RealType -> pairTy ty ty
                          _ -> ty
  TypeVar _ -> ty  -- can only be an index set
  ArrType l a b -> ArrType l (recur a) (recur b)
  TabType n a   -> TabType n (recur a)
  Exists t    -> Exists $ recur t
  IdxSetLit _ -> ty
  BoundTVar _ -> ty
  _ -> error "Not implemented"
  where recur = tangentBunType

-- === utils for working with linearity ===

spend :: (MonadError Err m, MonadCat Spent m) => Spent -> m ()
spend s = do
  spent <- look
  case spendTens spent s of
    Just _  -> extend s
    Nothing -> throw LinErr $ "pattern already spent: " ++ pprint s

asSpent :: Name -> Spent
asSpent v = Spent (v@>()) False

spendFreely :: MonadCat Spent m => m ()
spendFreely = extend $ Spent mempty True

checkSpent :: (MonadError Err m, MonadCat Spent m) => Name -> String -> m a -> m a
checkSpent v vStr m = do
  (ans, Spent vs consumes) <- scoped m
  unless  (consumes || v `isin` vs) $ throw LinErr $ "pattern never spent: " ++ vStr
  extend (Spent (vs `envDiff` (v@>())) consumes)
  return ans

checkNothingSpent :: (MonadError Err m, MonadCat Spent m) => m a -> m a
checkNothingSpent m = do
  (ans, spent@(Spent vs _)) <- scoped m
  unless (null vs) $ throw LinErr $
    "nonlinear function consumed linear data: " ++ pprint spent
  return ans

getPatName :: (MonadError Err m, Traversable f) => f (BinderP b) -> m Name
getPatName p = case toList p of
  []  -> throw LinErr $
           "empty patterns not allowed for linear lambda (for silly reasons)"
  (v:>_):_ -> return v


-- args are a tensor product of Cartesian products
type ArgLinearity = [(Multiplicity, Int)]

splitLinArgs :: ArgLinearity -> [a] -> [(Multiplicity, [a])]
splitLinArgs [] [] = []
splitLinArgs [] _  = error "Leftover args"
splitLinArgs ((l, n):linSpecs) xs = (l, xs') : splitLinArgs linSpecs rest
  where (xs', rest) = splitAt n xs

sequenceLinArgs :: (MonadError Err m, MonadCat Spent m)
                      => ArgLinearity -> [m a] -> m [a]
sequenceLinArgs argLin ms = do
  chunks' <- sequence $ flip map (splitLinArgs argLin ms) $ \(l, chunk) ->
    case l of Lin    -> shareLinear chunk
              NonLin -> sequence $ map checkNothingSpent chunk
  return $ concat chunks'

traverseProd :: (MonadError Err m, MonadCat Spent m, Traversable f) =>
                  ProdKind -> (a -> m b) -> f a -> m (f b)
traverseProd k f xs = case k of
  Cart -> shareLinear $ fmap f xs
  Tens -> traverse f xs

shareLinear :: (MonadError Err m, MonadCat Spent m, Traversable f) =>
                 f (m a) -> m (f a)
shareLinear actions = do
  (ys, spents) <- liftM unzip' $ traverse scoped actions
  case foldMaybe spendCart cartSpentId spents of
    Just spent' -> extend spent'
    Nothing     -> throwCartErr (toList spents)
  return ys
  where unzip' x = (fmap fst x, fmap snd x)

throwCartErr :: MonadError Err m => [Spent] -> m ()
throwCartErr spents = throw LinErr $
                        "different consumption by Cartesian product elements: "
                          ++ pprint (toList spents)

spendTens :: Spent -> Spent -> Maybe Spent
spendTens (Spent vs consumes) (Spent vs' consumes') = do
  unless (null (envIntersect vs vs')) Nothing
  return $ Spent (vs <> vs') (consumes || consumes')

tensSpentId :: Spent
tensSpentId = Spent mempty False

spendCart :: Spent -> Spent -> Maybe Spent
spendCart (Spent vs consumes) (Spent vs' consumes') = do
  unless (consumes  || vs' `containedWithin` vs ) Nothing
  unless (consumes' || vs  `containedWithin` vs') Nothing
  return $ Spent (vs <> vs') (consumes && consumes')
  where containedWithin x y = null $ x `envDiff` y

cartSpentId :: Spent
cartSpentId = Spent mempty True

realZero :: LitVal
realZero = RealLit 0.0

flattenType :: Type -> [(BaseType, [Int])]
flattenType ty = case ty of
  BaseType b  -> [(b, [])]
  RecType _ r -> concat $ map flattenType $ toList r
  TabType (IdxSetLit n) a -> [(b, n:shape) | (b, shape) <- flattenType a]
  IdxSetLit _ -> [(IntType, [])]
  -- temporary hack. TODO: fix
  TabType _             a -> [(b, 0:shape) | (b, shape) <- flattenType a]
  TypeVar _               -> [(IntType, [])]
  _ -> error $ "Unexpected type: " ++ show ty

listIntoRecord :: Record Type -> [a] -> Record (Type, [a])
listIntoRecord r xs = fst $ traverseFun f r xs
  where f :: Type -> [a] -> ((Type, [a]), [a])
        f ty xsRest = ((ty, curXs), rest)
          where (curXs, rest) = splitAt (length (flattenType ty)) xsRest

-- TODO: consider putting the errors in the monoid itself.
instance Semigroup Spent where
  s <> s' = case spendTens s s' of
              Just s'' -> s''
              Nothing -> error "Spent twice (this shouldn't happen)"

instance Monoid Spent where
  mempty = tensSpentId
  mappend = (<>)

instance Pretty Spent where
  pretty (Spent vs True ) = pretty (envNames vs ++ ["*"])
  pretty (Spent vs False) = pretty (envNames vs)

foldMaybe :: Traversable f => (a -> a -> Maybe a) -> a -> f a -> Maybe a
foldMaybe f x0 xs = foldl f' (Just x0) xs
  where f' prev x = do prev' <- prev
                       f prev' x
