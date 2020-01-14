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
             checkNExpr, patType, tangentBunType, tangentBunNType,
             getNExprType, splitLinArgs, nBuiltinType) where
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
    MAsk    -> nonLinBuiltin monadCon []  (monad r)
    MTell   -> nonLinBuiltin monadCon [w] (monad unitTy)
    MGet    -> nonLinBuiltin monadCon []  (monad s)
    MPut    -> nonLinBuiltin monadCon [s] (monad unitTy)
    MReturn -> nonLinBuiltin (monadCon ++ [noCon]) [d] (monad d)
  where
    ibinOpType    = nonLinBuiltin [] [int , int ] int
    [r, w, s] = map BoundTVar [0,1,2]
    i = BoundTVar 0
    a = BoundTVar 0
    b = BoundTVar 1
    -- c = BoundTVar 2
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
    Exists body   -> Exists (recurWith 1 body)
    IdxSetLit _   -> ty
    BoundTVar n   -> f d (Right n)
    Mult _        -> ty
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

type NTypeEnv = FullEnv (NType, Spent) ()
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

getNTypeChecked :: NExpr -> NTypeM [NType]
getNTypeChecked expr = case expr of
  NDecl (NDoBind bs rhs) body -> do
    mapM_ checkNBinder bs
    (ty, spent) <- scoped $ atomTypeChecked rhs
    case ty of
      NMonad eff a -> do
        assertEq (map binderAnn bs) a "Do bind"
        bodyTy <- extendR (nBinderEnv spent bs) $ getNTypeChecked body
        case bodyTy of
          [NMonad eff' _] -> assertEq eff eff' "Effect type mismatch"
          ty' -> throw CompilerErr $ "expected monad, got " ++ pprint ty'
        return bodyTy
      _ -> error "expected monad"
  NDecl decl body -> do
    env <- checkNDecl decl
    extendR env $ getNTypeChecked body
  NScan b@(_:>i) bs xs body -> do
    checkNBinder b
    let carryTys = map binderAnn bs
    mapM_ checkNBinder bs
    (xs', xsSpent) <- scoped $ atomTypesChecked xs
    assertEq carryTys xs' "Scan arg"
    let env = nBinderEnv xsSpent bs <> nBinderEnv mempty [b]
    (bodyTys, bodySpent) <- scoped $ extendR env (getNTypeChecked body)
    let (carryTys', outTys) = splitAt (length bs) bodyTys
    assertEq carryTys carryTys' "Scan output"
    case spendCart xsSpent bodySpent of
      Nothing -> throwCartErr [xsSpent, bodySpent]
      Just s  -> extend s
    return $ carryTys ++ map (NTabType i) outTys
  NPrimOp Todo ~[ts] _ -> do
    mapM_ checkNTy ts
    return ts
  NPrimOp b ts xs -> do
    mapM_ (mapM_ checkNTy) ts
    (argTys, ansTys, lin) <- nBuiltinType b ts
    argTys' <- sequenceLinArgs lin (map atomTypeChecked xs)
    assertEq argTys argTys' (pprint b)
    return ansTys
  NApp e xs -> do
    ~(NArrType l as bs) <- atomTypeChecked e
    -- TODO: use cartesian/tensor information from function type
    as' <- case l of Lin    ->                     atomTypesChecked xs
                     NonLin -> checkNothingSpent $ atomTypesChecked xs
    assertEq as as' "App"
    return bs
  NAtoms xs -> shareLinear (fmap atomTypeChecked xs)
  NTabCon n ty xs -> do
    xTys <- mapM atomTypeChecked xs
    mapM_ (\t -> assertEq ty t "Tab constructor") xTys
    return [NTabType n ty]

checkNDecl :: NDecl -> NTypeM NTypeEnv
checkNDecl decl = case decl of
  NLet bs expr -> do
    mapM_ checkNBinder bs
    (ts, s) <- scoped $ getNTypeChecked expr
    assertEq (map binderAnn bs) ts "Decl"
    return $ nBinderEnv s bs
  NUnpack bs tv _ -> do  -- TODO: check bound expression!
    checkNShadow (tv :> idxSet)
    extendR (tv @> T ()) $ mapM_ checkNBinder bs
    return $ nBinderEnv mempty bs <> tv @> T ()

nBinderEnv :: Spent -> [NBinder] -> NTypeEnv
nBinderEnv s bs = foldMap (\(v:>ty) -> v @> L (ty, s)) bs

atomType :: NAtom -> NType
atomType atom = case atom of
  NLit x    -> NBaseType (litType x)
  NVar _ ty -> ty
  NGet e _  -> b where (NTabType _ b) = atomType e
  NAtomicFor (_:>n) body -> NTabType n (atomType body)
  NLam m bs body -> NArrType m (map binderAnn bs) (getNExprType body)

getNExprType :: NExpr -> [NType]
getNExprType expr = case expr of
  NDecl _ body -> getNExprType body
  NScan (_:>n) bs _ body -> carryTys ++ map (NTabType n) outTys
    where bodyTys = getNExprType body
          (carryTys, outTys) = splitAt (length bs) bodyTys
  NPrimOp b ts _ -> ansTys
    where (_, ansTys, _) = ignoreExcept $ nBuiltinType b ts
  NApp e _ -> bs
    where (NArrType _ _ bs) = atomType e
  NAtoms xs -> map atomType xs
  NTabCon n ty _ -> [NTabType n ty]

atomTypeChecked :: NAtom -> NTypeM NType
atomTypeChecked atom = case atom of
  NLit x -> do
    when (x == realZero) spendFreely
    return $ NBaseType (litType x)
  NVar v ty -> do
    x <- asks $ flip envLookup v
    case x of
      Just (L (ty', s)) -> do
        spend s
        assertEq ty' ty "NVar annot"
        return ty
      _ -> throw CompilerErr $ "Lookup failed:" ++ pprint v
  NGet e i -> do
    ~(NTabType a b) <- atomTypeChecked e
    a' <- atomTypeChecked i
    assertEq a a' "Get"
    return b
  NAtomicFor b body -> do
    checkNBinder b
    bodyTy <- extendR (nBinderEnv mempty [b]) (atomTypeChecked body)
    return $ NTabType (binderAnn b) bodyTy
  NLam NonLin bs body -> do
    mapM_ checkNBinder bs
    bodyTys <- extendR (nBinderEnv mempty bs) (getNTypeChecked body)
    return $ NArrType NonLin (map binderAnn bs) bodyTys
  NLam Lin bs body -> do
    mapM_ checkNBinder bs
    v <- getPatName bs
    let env = nBinderEnv (asSpent v) bs
    bodyTys <- checkSpent v (pprint bs) $ extendR env (getNTypeChecked body)
    return $ NArrType Lin (map binderAnn bs) bodyTys
  NMonadVal expr -> do
    ~[ty] <- getNTypeChecked expr
    return ty

atomTypesChecked :: [NAtom] -> NTypeM [NType]
atomTypesChecked xs = traverseProd Cart atomTypeChecked xs

checkNTy :: NType -> NTypeM ()
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
                  => Builtin -> [[NType]] -> m ([NType], [NType], ArgLinearity)
nBuiltinType builtin ts =
  case builtin of
    IAdd  -> return $ ibinOpType
    ISub  -> return $ ibinOpType
    IMul  -> return $ ibinOpType
    Rem   -> return $ ibinOpType
    Pow   -> return $ ibinOpType
    FAdd  -> return $ cartBuiltin [real, real] [real]
    FSub  -> return $ cartBuiltin [real, real] [real]
    FNeg  -> return $ cartBuiltin [real]       [real]
    FMul  -> return $ tensBuiltin [real, real] [real]
    FDiv  -> return $ ([real, real], [real], [(Lin, 1), (NonLin, 1)])
    And   -> return $ nonLinBuiltin [bool, bool] [bool]
    Or    -> return $ nonLinBuiltin [bool, bool] [bool]
    Not   -> return $ nonLinBuiltin [bool]       [bool]
    Todo  -> return $ nonLinBuiltin [] [t]  where [[t]] = ts
    Range -> return $ nonLinBuiltin [int] [NExists []]
    IdxSetSize -> return $ nonLinBuiltin [] [int]
    IndexAsInt -> return $ nonLinBuiltin [i] [int]  where [[i]] = ts
    IntAsIndex -> return $ nonLinBuiltin [int] [i]  where [[i]] = ts
    BoolToInt  -> return $ nonLinBuiltin [bool] [int]
    IntToReal  -> return $ nonLinBuiltin [int] [real]
    Cmp _ -> do
      t <- fromScalar ts
      return $ nonLinBuiltin [t, t] [bool]
    Select -> do
      t <- fromScalar ts
      return $ nonLinBuiltin [bool, t, t] [t]
    Linearize -> return ( [NArrType NonLin as bs] ++ as
                        , (bs ++ [NArrType Lin as bs])
                        , [(NonLin, 1 + length as)])
      where [as, bs] = ts
    Transpose -> return ( [NArrType Lin as bs]
                        , [NArrType Lin bs as]
                        , [(Lin, 1)] )
      where [as, bs] = ts
    MemRef _ -> return $ nonLinBuiltin [] t  where [t] = ts
    FFICall _ _ -> return (argTys', retTy, [(NonLin, length argTys')])
      where
        retTy:argTys = ts
        argTys' = concat argTys
    -- TODO: make this easier (just derive from Expr type?)
    MRun -> do
      let [a] = tyArgs
      return $ nonLinBuiltin (r ++ s ++ [nmonad a]) (a ++ w ++ s)
      where
        r:w:s:tyArgs = ts
        nmonad a = NMonad (Effect r w s) a
    MPrim mprim -> case mprim of
      MAsk  -> return $ nonLinBuiltin [] [nmonad r]
      MTell -> return $ nonLinBuiltin w  [nmonad []]
      MGet  -> return $ nonLinBuiltin [] [nmonad s]
      MPut  -> return $ nonLinBuiltin s  [nmonad []]
      MReturn -> do
        let [a] = tyArgs
        return $ nonLinBuiltin a [nmonad a]
      where
        r:w:s:tyArgs = ts
        nmonad a = NMonad (Effect r w s) a
    _ -> throw TypeErr $ "Can't have this builtin in NExpr: " ++ pprint builtin
  where
    nonLinBuiltin xs ys = (xs, ys, [(NonLin, length xs)])
    cartBuiltin   xs ys = (xs, ys, [(Lin, length xs)])
    tensBuiltin   xs ys = (xs, ys, [(Lin, 1) | _ <- xs])
    ibinOpType = nonLinBuiltin [int, int] [int]
    int  = NBaseType IntType
    real = NBaseType RealType
    bool = NBaseType BoolType

    fromOne :: MonadError Err m => [[NType]] -> m NType
    fromOne ts' = case ts' of
      [[t]]  -> return t
      _ -> throw TypeErr $ "Expected single NType, got: " ++ pprint ts'

    fromScalar :: MonadError Err m => [[NType]] -> m NType
    fromScalar ts' = do
      t <- fromOne ts'
      if isNScalar t
        then return t
        else throw TypeErr $ "Expected scalar type, got: " ++ pprint t

isNScalar :: NType -> Bool
isNScalar ty = case ty of
  NBaseType  _ -> True
  NIdxSetLit _ -> True
  NTypeVar   _ -> True
  _            -> False

tangentBunNType :: NType -> [NType]
tangentBunNType ty = case ty of
  NBaseType b -> case b of RealType -> [ty, ty]
                           _ -> [ty]
  NTypeVar _ -> [ty]  -- can only be an index set
  NArrType l as bs -> [NArrType l (foldMap recur as) (foldMap recur bs)]
  NTabType n a -> map (NTabType n) (recur a)
  NExists ts -> [NExists $ foldMap recur ts]
  NIdxSetLit _ -> [ty]
  NBoundTVar _ -> [ty]
  where recur = tangentBunNType

tangentBunType :: Type -> Type
tangentBunType ty = case ty of
  BaseType b -> case b of RealType -> pair ty ty
                          _ -> ty
  ArrType l a b -> ArrType l (recur a) (recur b)
  _ -> error $ "Don't know bundle type for: " ++ pprint ty
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
