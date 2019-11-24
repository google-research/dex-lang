-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module GenExpr (sampleExpr, defaultGenOptions, GenOptions (..)
        , testSampleExpr, GenEnv (..), genSourceBlock, genUTopDecl) where

import Control.Monad
import Control.Monad.Reader
import Hedgehog hiding (Var, Command)
import Hedgehog.Internal.Shrink (towards)
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Lens.Micro.Platform
import Data.Text.Prettyprint.Doc
import Data.String


import Record
import Env
import Syntax
import PPrint


testSample :: (Pretty a) => GenM a -> Range.Size -> IO ()
testSample m s =
    Gen.sample (runReaderT (Gen.resize s (pprint <$> m))
        (GenEnv mempty mempty defaultGenOptions))
    >>= putStrLn

testSampleExpr :: Int -> IO ()
testSampleExpr n = testSample sampleExpr (fromIntegral n)


-- Variable names associated with a type
type TypeEnv = M.Map SigmaType [Name]

-- Variable names in scope
type ScopeEnv = S.Set Name

data GenOptions = GenOptions {
      tableSize :: Int
    , numberSize :: Int
    , tupleSize :: Int
    , returnTypePref :: Int
    }
    deriving (Show, Eq, Ord)

defaultGenOptions :: GenOptions
defaultGenOptions = GenOptions {
      tableSize = 10
    , numberSize = 10
    , tupleSize = 5
    , returnTypePref = 2
    }

data GenEnv = GenEnv {
      typeEnv :: TypeEnv
    , scopeEnv :: ScopeEnv
    , optsEnv :: GenOptions}
    deriving (Show, Eq, Ord)

-- lens
typeEnvL :: Lens' GenEnv TypeEnv
typeEnvL = lens typeEnv (\e t -> e{typeEnv = t})
scopeEnvL :: Lens' GenEnv ScopeEnv
scopeEnvL = lens scopeEnv (\e s -> e{scopeEnv = s})
optsEnvL :: Lens' GenEnv GenOptions
optsEnvL = lens optsEnv (\e s -> e{optsEnv = s})
tableSizeL :: Lens' GenEnv Int
tableSizeL = optsEnvL . lens tableSize (\e t -> e{tableSize=t})
numberSizeL :: Lens' GenEnv Int
numberSizeL = optsEnvL . lens numberSize (\e t -> e{numberSize = t})
tupleSizeL :: Lens' GenEnv Int
tupleSizeL = optsEnvL . lens tupleSize (\e t -> e{tupleSize = t})
returnTypePrefL :: Lens' GenEnv Int
returnTypePrefL = optsEnvL . lens returnTypePref (\e t -> e{returnTypePref = t})

-- utils
setBinding :: (Name, SigmaType) -> GenEnv -> GenEnv
setBinding (v, ty) =
    over (typeEnvL . at ty) ((Just [v]) `mappend`) . over scopeEnvL (S.insert v)
setBinding' :: (Name, Type) -> GenEnv -> GenEnv
setBinding' (v, ty) = setBinding (v, Forall [] ty)
setBindings' :: [(Name, Type)] -> GenEnv -> GenEnv
setBindings' vs = foldl (.) id (setBinding' <$> vs)
withBindings :: [(Name, Type)] -> GenM a -> GenM a
withBindings vs g = local (setBindings' vs) g
notShadowed :: Name -> GenM Bool
notShadowed n = view (scopeEnvL . to (S.notMember n))

genUntil :: MonadGen m => (a -> m Bool) -> m a -> m a
genUntil f gen = do
    x <- gen
    isValid <- f x
    if isValid then return x else genUntil f gen

small :: MonadGen m => m a -> m a
small = Gen.scale (`div` 2)

genSized :: MonadGen m => m a -> m a -> m a
genSized leaf tree = Gen.sized (\n -> if n == 0 then leaf else tree)

element :: MonadGen m => [a] -> m a
element = Gen.prune . Gen.element

prefer :: MonadGen m => Int -> m a -> m a -> m a
prefer w p r = Gen.prune (Gen.frequency [(w, p), (1, r)])

type GenM a = ReaderT GenEnv Gen a

allTypes :: Type -> [Type]
allTypes ty = ty : case ty of
    ArrType _ t1 t2 -> allTypes t1 ++ allTypes t2
    TabType _ t -> allTypes t
    RecType _ ~(Tup ts) -> concatMap allTypes ts
    _ -> []

preferReturnType :: Type -> GenM Type -> GenM Type
preferReturnType ty b = view returnTypePrefL >>= (\n -> prefer n (element (allTypes ty)) b)


-- | TODO: StrType
genBaseType :: GenM BaseType
genBaseType = element [IntType, BoolType, RealType]


genRecTypeWith :: GenM a -> GenM (Record a)
genRecTypeWith g = Tup <$> record
    where
        record = view tupleSizeL >>= \n -> Gen.list (Range.linear 2 n) (small g)

genRecType :: GenM (Record Type)
genRecType = genRecTypeWith genType

genTabTypeWith :: GenM Type -> GenM Type
genTabTypeWith g = liftM2 TabType genIdxSet (small g)

genTabType :: GenM Type
genTabType = genTabTypeWith genType

-- types that can be lowered to IType
genValType :: GenM Type
genValType = genSized leaf tree
    where
        leaf = BaseType <$> genBaseType
        tree = Gen.frequency [
              (1, leaf)
            , (2, (RecType Cart) <$> genRecTypeWith genValType)
            , (2, genTabTypeWith genValType)
            ]


genIdxSet :: GenM IdxSet
genIdxSet = genSized leaf tree
    where
        lit = view tableSizeL >>= \n -> Gen.integral_ (Range.constant 1 n)
        leaf = IdxSetLit <$> lit
        tree = Gen.frequency [
                  (1, leaf)
                --   Tuple index has not been implemented in JIT
                -- , (2, RecType <$> genRecTypeWith genIdxSet)
            ]

-- TODO: TypeVar, Exists, BoundTVar.
genLeafType :: GenM Type
genLeafType = BaseType <$> genBaseType

-- TODO: Linear type, Tens
genTreeType :: GenM Type
genTreeType = Gen.choice [
      genLeafType
    , arr
    , genTabType
    , (RecType Cart) <$> genRecType
    ]
  where
      sub = small genType
      arr = liftM2 (ArrType NonLin) sub sub


genType :: GenM Type
genType = Gen.shrink shrinkType $ Gen.prune (genSized genLeafType genTreeType)

shrinkType :: Type -> [Type]
shrinkType = tail . shrinkLis
    where
        shrinkLis :: Type -> [Type]
        shrinkLis ty = case ty of
            ArrType lin t1 t2 ->
                -- TODO: generate smaller list
                liftM2 (ArrType lin) (shrinkLis t1) (shrinkLis t2) ++ shrinkType t1
            TabType idx t ->
                liftM2 TabType (shrinkLis idx) (shrinkLis t) ++ shrinkType t
            (IdxSetLit n) -> IdxSetLit <$> towards n 1
            _ -> [ty]


genPatP :: (Type -> Ann) -> Type -> GenM (UPat, [(Name, Type)])
genPatP ann ty = case ty of
    (RecType _ (Tup as)) -> Gen.frequency [(1, genLeafPat), (2, genTupPat as)]
    _ -> genLeafPat
    where
        genLeafPat = do
            n <- genName
            return (RecLeaf (n :> (ann ty)), [(n, ty)])
        genTreePat :: [Type] -> GenM ([UPat], [(Name, Type)])
        genTreePat [] = return ([], [])
        genTreePat (t:ts) = do
            (p1, vs1) <- genPatP ann t
            (restp, restv) <- withBindings vs1 (genTreePat ts) -- make sure names are unique
            return (p1:restp, vs1 ++ restv)
        genTupPat :: [Type] -> GenM (UPat, [(Name, Type)])
        genTupPat ts = do
            (ps, vs) <- genTreePat ts
            return (RecTree (Tup ps), vs)


-- | variable or literal value
--
genLit :: BaseType -> GenM (ExprP b)
genLit ty = Lit <$> case ty of
    IntType ->
        view numberSizeL >>= \n -> IntLit <$> Gen.integral_ (Range.constant (negate n) n)
    BoolType -> BoolLit <$> Gen.bool_
    RealType ->
        view (numberSizeL . to fromIntegral) >>= \n -> RealLit <$> Gen.realFrac_ (Range.constant (negate n) n)
    StrType -> error "Str type not implemented"

genName :: GenM Name
genName = Gen.prune (genUntil notShadowed (flip Name 0 <$> str))
    where
        strLen = Range.constant 0 5
        strTail = Gen.frequency [(10, Gen.alphaNum), (1, return '\'')]
        str = fromString <$> liftM2 (:) Gen.lower (Gen.list strLen strTail)

genVars :: Type -> GenM [ExprP b]
genVars t = view (typeEnvL . at (Forall [] t) . to (maybe [] id) . to (map (flip Var [])))

withVars :: Type -> GenM (ExprP b) -> GenM (ExprP b)
withVars t g = do
    vs <- genVars t
    e <- g
    if null vs
        then return e
        else prefer 3 (Gen.element vs) (return e) -- preference to variable

-- TODO: Linear type
genLam :: Type -> Type -> GenM UExpr
genLam a b = do
    (pat, env) <- genPatP Ann a
    body <- withBindings env (genExpr b)
    return (Lam NonLin pat body)


-- table
genTabCon :: Int -> Type -> GenM UExpr
genTabCon n ty = TabCon NoAnn <$> replicateM n (small (genExpr ty))

genFor :: Type -> Type -> GenM UExpr
genFor a b = do
    (pat, env) <- small (genPatP Ann a)
    body <- withBindings env (small (genExpr b))
    return (For pat body)

genTable :: IdxSet -> Type -> GenM UExpr
genTable ty@(IdxSetLit n) b = Gen.choice [genTabCon n b, genFor ty b]
genTable ty b = genFor ty b

-- TODO: LetPoly, TAlias, Unpack
genDecl :: Type -> GenM UExpr
genDecl ty = do
    -- preference over return type to increase variable usage
    declTy <- small (preferReturnType ty genType)
    declExpr <- small (genExpr declTy)
    (declPat, env) <- small (genPatP (const NoAnn) declTy)
    body <- small (withBindings env (genExpr ty))
    return (Decl (LetMono declPat declExpr) body)

genGet :: Type -> GenM UExpr
genGet ty = do
    idxty <- small genIdxSet
    idx <- small (genExpr idxty)
    body <- small (genExpr (TabType idxty ty))
    return (Get body idx)


genApp :: Type -> GenM UExpr
genApp ty = do
    argty <- small (preferReturnType ty genType)
    fun <- small (genExpr (ArrType NonLin argty ty))
    arg <- small (genExpr argty)
    return (App fun arg)

-- TODO: Tens
genRecCon :: Record Type -> GenM UExpr
genRecCon ~(Tup ts) = RecCon Cart <$> Tup <$> traverse (small . genExpr) ts


genLeafExpr :: Type -> GenM UExpr
genLeafExpr ty = withVars ty $ case ty of
    BaseType t -> genLit t
    ArrType _ t1 t2 -> genLam t1 t2
    TabType i t -> genTable i t
    RecType _ rt -> genRecCon rt
    IdxSetLit n -> do
        val <- Gen.integral_ (Range.constant 0 (n - 1))
        return $ Annot (PrimOp IntAsIndex [] [Lit (IntLit val)]) ty
    _ -> undefined

genTreeExpr :: Type -> GenM UExpr
genTreeExpr ty = Gen.choice $ case ty of
    BaseType{} -> commons
    ArrType _ t1 t2 -> genLam t1 t2 : commons
    TabType i t -> genTable i t : commons
    RecType _ rt -> genRecCon rt : commons
    _ -> commons
    where
        commons = [
                  genDecl ty
                , genApp ty
                , genGet ty
            ]

genExpr :: Type -> GenM UExpr
genExpr ty = genSized (genLeafExpr ty) (genTreeExpr ty)

sampleExpr :: GenM UExpr
sampleExpr = do
    ty <- genValType
    genExpr ty


genUTopDecl :: GenM UTopDecl
genUTopDecl = (EvalCmd . Command (EvalExpr Printed)) <$> sampleExpr

genSourceBlock :: GenM SourceBlock
genSourceBlock = do
    topdecl <- UTopDecl <$> genUTopDecl
    case topdecl of
        ~(UTopDecl (EvalCmd (Command _ e))) -> return (SourceBlock 0 0 (pprint e) topdecl)