-- Copyright 2021 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE UndecidableInstances #-}

module SourceRename ( renameSourceNamesTopUDecl, uDeclErrSourceMap
                    , renameSourceNamesUExpr ) where

import Prelude hiding (id, (.))
import Data.List (sort)
import Control.Category
import Control.Monad.Except hiding (Except)
import qualified Data.Set        as S
import qualified Data.Map.Strict as M

import Err
import Name
import Core (EnvReader (..), withEnv, lookupSourceMapPure)
import PPrint ()
import IRVariants
import Types.Source
import Types.Primitives
import Types.Core (Env (..), ModuleEnv (..))

renameSourceNamesTopUDecl
  :: (Fallible1 m, EnvReader m)
  => ModuleSourceName -> UTopDecl VoidS VoidS -> m n (Abs UTopDecl SourceMap n)
renameSourceNamesTopUDecl mname decl = do
  Distinct <- getDistinct
  Abs renamedDecl sourceMapLocalNames <- liftRenamer $ sourceRenameTopUDecl decl
  let sourceMap = SourceMap $ fmap (fmap (\(LocalVar v) -> ModuleVar mname (Just v))) $
                    fromSourceMap sourceMapLocalNames
  return $ Abs renamedDecl sourceMap
{-# SCC renameSourceNamesTopUDecl #-}

uDeclErrSourceMap:: ModuleSourceName -> UTopDecl VoidS VoidS -> SourceMap n
uDeclErrSourceMap mname decl =
  SourceMap $ M.fromSet (const [ModuleVar mname Nothing]) (sourceNames decl)
{-# SCC uDeclErrSourceMap #-}

renameSourceNamesUExpr :: (Fallible1 m, EnvReader m) => UExpr VoidS -> m n (UExpr n)
renameSourceNamesUExpr expr = do
  Distinct <- getDistinct
  liftRenamer $ sourceRenameE expr
{-# SCC renameSourceNamesUExpr #-}

sourceRenameTopUDecl
  :: (Renamer m, Distinct o)
  => UTopDecl i i' -> m o (Abs UTopDecl SourceMap o)
sourceRenameTopUDecl udecl =
  sourceRenameB udecl \udecl' -> do
    SourceMap fullSourceMap <- askSourceMap
    let partialSourceMap = fullSourceMap `M.restrictKeys` sourceNames udecl
    return $ Abs udecl' $ SourceMap partialSourceMap

data RenamerSubst n = RenamerSubst { renamerSourceMap :: SourceMap n
                                   , renamerMayShadow :: Bool }

newtype RenamerM (n::S) (a:: *) =
  RenamerM { runRenamerM :: OutReaderT RenamerSubst (ScopeReaderT FallibleM) n a }
  deriving ( Functor, Applicative, Monad, MonadFail, Fallible
           , ScopeReader, ScopeExtender)

liftRenamer :: (EnvReader m, Fallible1 m, SinkableE e) => RenamerM n (e n) -> m n (e n)
liftRenamer cont = do
  sm <- withEnv $ envSourceMap . moduleEnv
  Distinct <- getDistinct
  (liftExcept =<<) $ liftM runFallibleM $ liftScopeReaderT $
    runOutReaderT (RenamerSubst sm False) $ runRenamerM $ cont

class ( Monad1 m, ScopeReader m
      , ScopeExtender m, Fallible1 m) => Renamer m where
  askMayShadow :: m n Bool
  setMayShadow :: Bool -> m n a -> m n a
  askSourceMap    :: m n (SourceMap n)
  extendSourceMap :: SourceName -> UVar n -> m n a -> m n a

instance Renamer RenamerM where
  askMayShadow = RenamerM $ renamerMayShadow <$> askOutReader
  askSourceMap = RenamerM $ renamerSourceMap <$> askOutReader
  setMayShadow mayShadow (RenamerM cont) = RenamerM do
    RenamerSubst sm _ <- askOutReader
    localOutReader (RenamerSubst sm mayShadow) cont
  extendSourceMap name var (RenamerM cont) = RenamerM do
    RenamerSubst sm mayShadow <- askOutReader
    let ext = SourceMap $ M.singleton name [LocalVar var]
    localOutReader (RenamerSubst (sm <> ext) mayShadow) cont

class SourceRenamableE e where
  sourceRenameE :: (Distinct o, Renamer m) => e i -> m o (e o)

class SourceRenamableB (b :: B) where
  sourceRenameB :: (Renamer m, Distinct o)
                => b i i'
                -> (forall o'. DExt o o' => b o o' -> m o' a)
                -> m o a

instance SourceRenamableE (SourceNameOr UVar) where
  sourceRenameE (SourceName sourceName) =
    InternalName sourceName <$> lookupSourceName sourceName
  sourceRenameE _ = error "Shouldn't be source-renaming internal names"

lookupSourceName :: Renamer m => SourceName -> m n (UVar n)
lookupSourceName v = do
  sm <- askSourceMap
  case lookupSourceMapPure sm v of
    [] -> throw UnboundVarErr $ pprint v
    LocalVar v' : _ -> return v'
    [ModuleVar _ maybeV] -> case maybeV of
      Just v' -> return v'
      Nothing -> throw VarDefErr v
    vs -> throw AmbiguousVarErr $ ambiguousVarErrMsg v vs

ambiguousVarErrMsg :: SourceName -> [SourceNameDef n] -> String
ambiguousVarErrMsg v defs =
  -- we sort the lines to make the result a bit more deterministic for quine tests
  pprint v ++ " is defined:\n" ++ unlines (sort $ map defsPretty defs)
  where
    defsPretty :: SourceNameDef n -> String
    defsPretty (ModuleVar mname _) = case mname of
      Main -> "in this file"
      Prelude -> "in the prelude"
      OrdinaryModule mname' -> "in " ++ pprint mname'
    defsPretty (LocalVar _) =
      error "shouldn't be possible because module vars can't shadow local ones"

instance SourceRenamableE (SourceNameOr (Name (AtomNameC CoreIR))) where
  sourceRenameE (SourceName sourceName) = do
    lookupSourceName sourceName >>= \case
      UAtomVar v -> return $ InternalName sourceName v
      _ -> throw TypeErr $ "Not an ordinary variable: " ++ pprint sourceName
  sourceRenameE _ = error "Shouldn't be source-renaming internal names"

instance SourceRenamableE (SourceNameOr (Name DataConNameC)) where
  sourceRenameE (SourceName sourceName) = do
    lookupSourceName sourceName >>= \case
      UDataConVar v -> return $ InternalName sourceName v
      _ -> throw TypeErr $ "Not a data constructor: " ++ pprint sourceName
  sourceRenameE _ = error "Shouldn't be source-renaming internal names"

instance SourceRenamableE (SourceNameOr (Name ClassNameC)) where
  sourceRenameE (SourceName sourceName) = do
    lookupSourceName sourceName >>= \case
      UClassVar v -> return $ InternalName sourceName v
      _ -> throw TypeErr $ "Not a class name: " ++ pprint sourceName
  sourceRenameE _ = error "Shouldn't be source-renaming internal names"

instance SourceRenamableE (SourceNameOr (Name EffectNameC)) where
  sourceRenameE (SourceName sourceName) = do
    lookupSourceName sourceName >>= \case
      UEffectVar v -> return $ InternalName sourceName v
      _ -> throw TypeErr $ "Not an effect name: " ++ pprint sourceName
  sourceRenameE _ = error "Shouldn't be source-renaming internal names"

instance SourceRenamableE (SourceNameOr (Name c)) => SourceRenamableE (SourceOrInternalName c) where
  sourceRenameE (SourceOrInternalName x) = SourceOrInternalName <$> sourceRenameE x

instance (SourceRenamableE e, SourceRenamableB b) => SourceRenamableE (Abs b e) where
  sourceRenameE (Abs b e) = sourceRenameB b \b' -> Abs b' <$> sourceRenameE e

instance SourceRenamableB (UBinder (AtomNameC CoreIR)) where
  sourceRenameB b cont = sourceRenameUBinder UAtomVar b cont

instance SourceRenamableE (UAnn req) where
  sourceRenameE UNoAnn = return UNoAnn
  sourceRenameE (UAnn ann) = UAnn <$> sourceRenameE ann

instance SourceRenamableB (UAnnBinder req) where
  sourceRenameB (UAnnBinder b ann cs) cont = do
    ann' <- sourceRenameE ann
    cs'  <- mapM sourceRenameE cs
    sourceRenameB b \b' ->
      cont $ UAnnBinder b' ann' cs'

instance SourceRenamableE UExpr' where
  sourceRenameE expr = setMayShadow True case expr of
    UVar v -> UVar <$> sourceRenameE v
    ULit l -> return $ ULit l
    ULam lam -> ULam <$> sourceRenameE lam
    UPi (UPiExpr pats appExpl eff body) ->
      sourceRenameB pats \pats' ->
        UPi <$> (UPiExpr pats' <$> pure appExpl <*> sourceRenameE eff <*> sourceRenameE body)
    UApp f xs ys -> UApp <$> sourceRenameE f
       <*> forM xs sourceRenameE
       <*> forM ys (\(name, y) -> (name,) <$> sourceRenameE y)
    UTabPi (UTabPiExpr pat body) ->
      sourceRenameB pat \pat' ->
        UTabPi <$> (UTabPiExpr pat' <$> sourceRenameE body)
    UDepPairTy (UDepPairType expl pat body) ->
      sourceRenameB pat \pat' ->
        UDepPairTy <$> (UDepPairType expl pat' <$> sourceRenameE body)
    UDepPair lhs rhs ->
      UDepPair <$> sourceRenameE lhs <*> sourceRenameE rhs
    UTabApp f x -> UTabApp <$> sourceRenameE f <*> mapM sourceRenameE x
    UFor d (UForExpr pat body) ->
      sourceRenameB pat \pat' ->
        UFor d <$> UForExpr pat' <$> sourceRenameE body
    UCase scrut alts ->
      UCase <$> sourceRenameE scrut <*> mapM sourceRenameE alts
    UDo block -> UDo <$> sourceRenameE block
    UHole -> return UHole
    UTypeAnn e ty -> UTypeAnn <$> sourceRenameE e <*> sourceRenameE ty
    UTabCon xs -> UTabCon <$> mapM sourceRenameE xs
    UPrim p xs -> UPrim p <$> mapM sourceRenameE xs
    UFieldAccess x f -> UFieldAccess <$> sourceRenameE x <*> pure f
    UNatLit   x -> return $ UNatLit x
    UIntLit   x -> return $ UIntLit x
    UFloatLit x -> return $ UFloatLit x

instance SourceRenamableE UAlt where
  sourceRenameE (UAlt pat body) =
    sourceRenameB pat \pat' ->
      UAlt pat' <$> sourceRenameE body

instance SourceRenamableE UEffectRow where
  sourceRenameE (UEffectRow row tailVar) =
    UEffectRow <$> row' <*> mapM sourceRenameE tailVar
    where row' = S.fromList <$> traverse sourceRenameE (S.toList row)

instance SourceRenamableE UEffect where
  sourceRenameE (URWSEffect rws name) = URWSEffect rws <$> sourceRenameE name
  sourceRenameE UExceptionEffect = return UExceptionEffect
  sourceRenameE UIOEffect = return UIOEffect
  sourceRenameE (UUserEffect name) = UUserEffect <$> sourceRenameE name

instance SourceRenamableE a => SourceRenamableE (WithSrcE a) where
  sourceRenameE (WithSrcE pos e) = addSrcContext pos $
    WithSrcE pos <$> sourceRenameE e

instance SourceRenamableB a => SourceRenamableB (WithSrcB a) where
  sourceRenameB (WithSrcB pos b) cont = addSrcContext pos $
    sourceRenameB b \b' -> cont $ WithSrcB pos b'

instance SourceRenamableB UTopDecl where
  sourceRenameB decl cont = case decl of
    ULocalDecl d -> sourceRenameB d \d' -> cont $ ULocalDecl d'
    UDataDefDecl dataDef tyConName dataConNames -> do
      dataDef' <- sourceRenameE dataDef
      sourceRenameUBinder UTyConVar tyConName \tyConName' ->
        sourceRenameUBinderNest UDataConVar dataConNames \dataConNames' ->
           cont $ UDataDefDecl dataDef' tyConName' dataConNames'
    UStructDecl tyConName structDef -> do
      sourceRenameUBinder UPunVar tyConName \tyConName' -> do
        structDef' <- sourceRenameE structDef
        cont $ UStructDecl tyConName' structDef'
    UInterface paramBs methodTys className methodNames -> do
      Abs paramBs' (ListE methodTys') <-
        sourceRenameB paramBs \paramBs' -> do
          methodTys' <- mapM sourceRenameE methodTys
          return $ Abs paramBs' $ ListE methodTys'
      sourceRenameUBinder UClassVar className \className' ->
        sourceRenameUBinderNest UMethodVar methodNames \methodNames' ->
          cont $ UInterface paramBs' methodTys' className' methodNames'
    UInstance className conditions params methodDefs instanceName expl -> do
      className' <- sourceRenameE className
      Abs conditions' (PairE (ListE params') (ListE methodDefs')) <-
        sourceRenameE $ Abs conditions (PairE (ListE params) $ ListE methodDefs)
      sourceRenameB instanceName \instanceName' ->
        cont $ UInstance className' conditions' params' methodDefs' instanceName' expl
    UEffectDecl opTypes effName opNames -> do
      opTypes' <- mapM (\(UEffectOpType p ty) -> (UEffectOpType p) <$> sourceRenameE ty) opTypes
      sourceRenameUBinder UEffectVar effName \effName' ->
        sourceRenameUBinderNest UEffectOpVar opNames \opNames' ->
          cont $ UEffectDecl opTypes' effName' opNames'
    UHandlerDecl _ _ _ _ _ _ _ -> error "not implemented"

instance SourceRenamableB UDecl' where
  sourceRenameB decl cont = case decl of
    ULet ann pat ty expr -> do
      expr' <- sourceRenameE expr
      ty' <- mapM sourceRenameE ty
      sourceRenameB pat \pat' ->
        cont $ ULet ann pat' ty' expr'
    UExprDecl e -> cont =<< (UExprDecl <$> sourceRenameE e)
    UPass -> cont UPass

instance SourceRenamableE ULamExpr where
  sourceRenameE (ULamExpr args expl effs resultTy body) =
    sourceRenameB args \args' -> ULamExpr args'
      <$> pure expl
      <*> mapM sourceRenameE effs
      <*> mapM sourceRenameE resultTy
      <*> sourceRenameE body

instance SourceRenamableE UBlock' where
  sourceRenameE (UBlock decls result) =
    sourceRenameB decls \decls' -> do
      result' <- sourceRenameE result
      return $ UBlock decls' result'

instance SourceRenamableB UnitB where
  sourceRenameB UnitB cont = cont UnitB

instance (SourceRenamableB b1, SourceRenamableB b2)
         => SourceRenamableB (EitherB b1 b2) where
  sourceRenameB (LeftB  b) cont = sourceRenameB b \b' -> cont $ LeftB  b'
  sourceRenameB (RightB b) cont = sourceRenameB b \b' -> cont $ RightB b'

instance (SourceRenamableB b1, SourceRenamableB b2) => SourceRenamableB (PairB b1 b2) where
  sourceRenameB (PairB b1 b2) cont = do
    sourceRenameB b1 \b1' ->
      sourceRenameB b2 \b2' ->
        cont $ PairB b1' b2'

instance SourceRenamableB b => SourceRenamableB (WithExpl b) where
  sourceRenameB (WithExpl x b) cont = sourceRenameB b \b' -> cont $ WithExpl x b'

sourceRenameUBinderNest
  :: (Color c, Renamer m, Distinct o)
  => (forall l. Name c l -> UVar l)
  -> Nest (UBinder c) i i'
  -> (forall o'. DExt o o' => Nest (UBinder c) o o' ->  m o' a)
  -> m o a
sourceRenameUBinderNest _ Empty cont = cont Empty
sourceRenameUBinderNest asUVar (Nest b bs) cont =
  sourceRenameUBinder asUVar b \b' ->
    sourceRenameUBinderNest asUVar bs \bs' ->
      cont $ Nest b' bs'

sourceRenameUBinder :: (Color c, Distinct o, Renamer m)
                    => (forall l. Name c l -> UVar l)
                    -> UBinder c i i'
                    -> (forall o'. DExt o o' => UBinder c o o' -> m o' a)
                    -> m o a
sourceRenameUBinder asUVar ubinder cont = case ubinder of
  UBindSource b -> do
    SourceMap sm <- askSourceMap
    mayShadow <- askMayShadow
    let shadows = M.member b sm
    when (not mayShadow && shadows) $
      throw RepeatedVarErr $ pprint b
    withFreshM (getNameHint b) \freshName -> do
      Distinct <- getDistinct
      extendSourceMap b (asUVar $ binderName freshName) $
        cont $ UBind b freshName
  UBind _ _ -> error "Shouldn't be source-renaming internal names"
  UIgnore -> cont UIgnore

instance SourceRenamableE UDataDef where
  sourceRenameE (UDataDef tyConName paramBs dataCons) = do
    sourceRenameB paramBs \paramBs' -> do
      dataCons' <- forM dataCons \(dataConName, argBs) -> do
        argBs' <- sourceRenameE argBs
        return (dataConName, argBs')
      return $ UDataDef tyConName paramBs' dataCons'

instance SourceRenamableE UStructDef where
  sourceRenameE (UStructDef tyConName paramBs fields methods) = do
    sourceRenameB paramBs \paramBs' -> do
      fields' <- forM fields \(fieldName, ty) -> do
        ty' <- sourceRenameE ty
        return (fieldName, ty')
      methods' <- forM methods \(ann, methodName, lam) -> do
        lam' <- sourceRenameE lam
        return (ann, methodName, lam')
      return $ UStructDef tyConName paramBs' fields' methods'

instance SourceRenamableE UDataDefTrail where
  sourceRenameE (UDataDefTrail args) = sourceRenameB args \args' ->
    return $ UDataDefTrail args'

instance (SourceRenamableE e1, SourceRenamableE e2) => SourceRenamableE (PairE e1 e2) where
  sourceRenameE (PairE x y) = PairE <$> sourceRenameE x <*> sourceRenameE y

instance (SourceRenamableE e1, SourceRenamableE e2) => SourceRenamableE (EitherE e1 e2) where
  sourceRenameE (LeftE  x) = LeftE  <$> sourceRenameE x
  sourceRenameE (RightE x) = RightE <$> sourceRenameE x

instance SourceRenamableE e => SourceRenamableE (ListE e) where
  sourceRenameE (ListE xs) = ListE <$> mapM sourceRenameE xs

instance SourceRenamableE UnitE where
  sourceRenameE UnitE = return UnitE

instance SourceRenamableE UMethodDef' where
  sourceRenameE (UMethodDef ~(SourceName v) expr) = do
    lookupSourceName v >>= \case
      UMethodVar v' -> UMethodDef (InternalName v v') <$> sourceRenameE expr
      _ -> throw TypeErr $ "not a method name: " ++ pprint v

instance SourceRenamableE UEffectOpDef where
  sourceRenameE (UReturnOpDef expr) = do
    UReturnOpDef <$> sourceRenameE expr
  sourceRenameE (UEffectOpDef rp ~(SourceName v) expr) = do
    lookupSourceName v >>= \case
      UEffectOpVar v' -> UEffectOpDef rp (InternalName v v') <$> sourceRenameE expr
      _ -> throw TypeErr $ "not an effect operation name: " ++ pprint v

instance SourceRenamableB b => SourceRenamableB (Nest b) where
  sourceRenameB (Nest b bs) cont =
    sourceRenameB b \b' ->
      sourceRenameB bs \bs' ->
        cont $ Nest b' bs'
  sourceRenameB Empty cont = cont Empty

-- === renaming patterns ===

-- We want to ensure that pattern siblings don't shadow each other, so we carry
-- the set of in-scope siblings' names along with the normal renaming env.

type SiblingSet = S.Set SourceName

class SourceRenamablePat (pat::B) where
  sourceRenamePat :: (Distinct o, Renamer m)
                  => SiblingSet
                  -> pat i i'
                  -> (forall o'. DExt o o' => SiblingSet -> pat o o' -> m o' a)
                  -> m o a

instance SourceRenamablePat (UBinder (AtomNameC CoreIR)) where
  sourceRenamePat sibs ubinder cont = do
    newSibs <- case ubinder of
      UBindSource b -> do
        when (S.member b sibs) $ throw RepeatedPatVarErr $ pprint b
        return $ S.singleton b
      UIgnore -> return mempty
      UBind _ _ -> error "Shouldn't be source-renaming internal names"
    sourceRenameB ubinder \ubinder' ->
      cont (sibs <> newSibs) ubinder'

instance SourceRenamablePat UPat' where
  sourceRenamePat sibs pat cont = case pat of
    UPatBinder b -> sourceRenamePat sibs b \sibs' b' -> cont sibs' $ UPatBinder b'
    UPatCon con bs -> do
      -- TODO Deduplicate this against the code for sourceRenameE of
      -- the SourceName case of SourceNameOr
      con' <- sourceRenameE con
      sourceRenamePat sibs bs \sibs' bs' ->
        cont sibs' $ UPatCon con' bs'
    UPatDepPair (PairB p1 p2) ->
      sourceRenamePat sibs  p1 \sibs' p1' ->
        sourceRenamePat sibs' p2 \sibs'' p2' ->
          cont sibs'' $ UPatDepPair $ PairB p1' p2'
    UPatProd bs -> sourceRenamePat sibs bs \sibs' bs' -> cont sibs' $ UPatProd bs'
    UPatTable ps -> sourceRenamePat sibs ps \sibs' ps' -> cont sibs' $ UPatTable ps'

instance SourceRenamablePat UnitB where
  sourceRenamePat sibs UnitB cont = cont sibs UnitB

instance (SourceRenamablePat p1, SourceRenamablePat p2)
         => SourceRenamablePat (PairB p1 p2) where
  sourceRenamePat sibs (PairB p1 p2) cont =
    sourceRenamePat sibs p1 \sibs' p1' ->
      sourceRenamePat sibs' p2 \sibs'' p2' ->
        cont sibs'' $ PairB p1' p2'

instance (SourceRenamablePat p1, SourceRenamablePat p2)
         => SourceRenamablePat (EitherB p1 p2) where
  sourceRenamePat sibs (LeftB p) cont =
    sourceRenamePat sibs p \sibs' p' ->
      cont sibs' $ LeftB p'
  sourceRenamePat sibs (RightB p) cont =
    sourceRenamePat sibs p \sibs' p' ->
    cont sibs' $ RightB p'

instance SourceRenamablePat p => SourceRenamablePat (WithSrcB p) where
   sourceRenamePat sibs (WithSrcB pos pat) cont = addSrcContext pos do
     sourceRenamePat sibs pat \sibs' pat' ->
       cont sibs' $ WithSrcB pos pat'

instance SourceRenamablePat p => SourceRenamablePat (Nest p) where
  sourceRenamePat sibs (Nest b bs) cont =
    sourceRenamePat sibs b \sibs' b' ->
      sourceRenamePat sibs' bs \sibs'' bs' ->
        cont sibs'' $ Nest b' bs'
  sourceRenamePat sibs Empty cont = cont sibs Empty

instance SourceRenamableB UPat' where
  sourceRenameB pat cont =
    sourceRenamePat mempty pat \_ pat' -> cont pat'

-- === source name sets ===

-- It's a shame we require these. They're redundant with the intended
-- information in SourceRenamableB but the continuation style doesn't let us
-- access the additional source names, only the full set. But it's not a huge
-- amount of code and there's nothing tricky about it.

-- Note that this is only expected to return the _bound source names_!
class HasSourceNames (b::B) where
  sourceNames :: b n l -> S.Set SourceName

instance HasSourceNames UTopDecl where
  sourceNames decl = case decl of
    ULocalDecl d -> sourceNames d
    UDataDefDecl _ ~(UBindSource tyConName) dataConNames -> do
      S.singleton tyConName <> sourceNames dataConNames
    UStructDecl ~(UBindSource tyConName) _ -> do
      S.singleton tyConName
    UInterface _ _ ~(UBindSource className) methodNames -> do
      S.singleton className <> sourceNames methodNames
    UInstance _ _ _ _ instanceName _ -> sourceNames instanceName
    UEffectDecl _ ~(UBindSource effName) opNames -> do
      S.singleton effName <> sourceNames opNames
    UHandlerDecl _ _ _ _ _ _ handlerName -> sourceNames handlerName

instance HasSourceNames UDecl' where
  sourceNames = \case
    ULet _ pat _ _ -> sourceNames pat
    UExprDecl _ -> S.empty
    UPass -> S.empty

instance HasSourceNames UPat' where
  sourceNames = \case
    UPatBinder b -> sourceNames b
    UPatCon _ bs -> sourceNames bs
    UPatDepPair (PairB p1 p2) -> sourceNames p1 <> sourceNames p2
    UPatProd bs -> sourceNames bs
    UPatTable ps -> sourceNames ps

instance HasSourceNames b => HasSourceNames (WithSrcB b) where
  sourceNames (WithSrcB _ pat) = sourceNames pat

instance (HasSourceNames b1, HasSourceNames b2)
         => HasSourceNames (PairB b1 b2) where
  sourceNames (PairB b1 b2) = sourceNames b1 <> sourceNames b2

instance HasSourceNames b => HasSourceNames (MaybeB b)where
  sourceNames b = case b of
    JustB b' -> sourceNames b'
    _ -> mempty

instance HasSourceNames b => HasSourceNames (Nest b)where
  sourceNames Empty = mempty
  sourceNames (Nest b rest) =
    sourceNames b <> sourceNames rest

instance HasSourceNames (UBinder c) where
  sourceNames b = case b of
    UBindSource name -> S.singleton name
    UIgnore -> mempty
    UBind _ _ -> error "Shouldn't be source-renaming internal names"

-- === misc instance ===

instance SinkableE RenamerSubst where
  sinkingProofE = undefined
