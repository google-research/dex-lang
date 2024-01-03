-- Copyright 2021 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE UndecidableInstances #-}

module SourceRename ( renameSourceNamesTopUDecl, uDeclErrSourceMap
                    , renameSourceNamesUExpr ) where

import Prelude hiding (id, (.))
import Control.Category
import Control.Monad.Reader
import Control.Monad.State.Strict
import qualified Data.Set        as S
import qualified Data.Map.Strict as M

import Err
import Name
import Core (EnvReader (..), withEnv, lookupSourceMapPure)
import MonadUtil
import MTL1
import PPrint
import IRVariants
import Types.Source
import Types.Primitives
import Types.Top (Env (..), ModuleEnv (..))

renameSourceNamesTopUDecl
  :: (Fallible1 m, EnvReader m, TopLogger1 m)
  => TopNameDescription -> UTopDecl VoidS VoidS -> m n (Abs UTopDecl SourceMap n)
renameSourceNamesTopUDecl desc decl = do
  Distinct <- getDistinct
  Abs renamedDecl sourceMapLocalNames <- liftRenamer $ sourceRenameTopUDecl decl
  let sourceMap = SourceMap $ fmap (fmap (\(LocalVar _ v) -> ModuleVar desc (Just v))) $
                    fromSourceMap sourceMapLocalNames
  return $ Abs renamedDecl sourceMap
{-# SCC renameSourceNamesTopUDecl #-}

uDeclErrSourceMap:: TopNameDescription -> UTopDecl VoidS VoidS -> SourceMap n
uDeclErrSourceMap desc decl =
  SourceMap $ M.fromSet (const [ModuleVar desc Nothing]) (sourceNames decl)
{-# SCC uDeclErrSourceMap #-}

renameSourceNamesUExpr :: (Fallible1 m, EnvReader m, TopLogger1 m) => UExpr VoidS -> m n (UExpr n)
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
  RenamerM { runRenamerM :: ReaderT1 RenamerSubst (ScopeReaderT (ExceptT (State NamingInfo))) n a }
  deriving ( Functor, Applicative, Monad, MonadFail, Fallible
           , ScopeReader, ScopeExtender)

liftRenamer :: (EnvReader m, Fallible1 m, SinkableE e, TopLogger1 m) => RenamerM n (e n) -> m n (e n)
liftRenamer cont = do
  sm <- withEnv $ envSourceMap . moduleEnv
  Distinct <- getDistinct
  m <- liftScopeReaderT $ runReaderT1 (RenamerSubst sm False) $ runRenamerM $ cont
  let (ans, namingInfo) = runState (runExceptT m) mempty
  emitLog $ Outputs [SourceInfo $ SINamingInfo namingInfo]
  liftExcept ans

class ( Monad1 m, ScopeReader m
      , ScopeExtender m, Fallible1 m) => Renamer m where
  askMayShadow :: m n Bool
  setMayShadow :: Bool -> m n a -> m n a
  askSourceMap    :: m n (SourceMap n)
  extendSourceMap :: SrcId -> SourceName -> UVar n -> m n a -> m n a
  emitNameInfo :: SrcId -> NameInfo -> m n ()

instance Renamer RenamerM where
  askMayShadow = RenamerM $ renamerMayShadow <$> ask
  askSourceMap = RenamerM $ renamerSourceMap <$> ask
  setMayShadow mayShadow (RenamerM cont) = RenamerM do
    local (\(RenamerSubst sm _) -> RenamerSubst sm mayShadow) cont
  extendSourceMap sid name var (RenamerM cont) = RenamerM do
    let ext = SourceMap $ M.singleton name [LocalVar sid var]
    local (\(RenamerSubst sm mayShadow) -> RenamerSubst (sm <> ext) mayShadow) cont
  emitNameInfo sid info = do
    NamingInfo curNameInfo <- RenamerM $ lift11 $ lift1 $ lift get
    let newNameInfo = M.insert sid info curNameInfo
    RenamerM $ lift11 $ lift1 $ lift $ put $ NamingInfo newNameInfo

class SourceRenamableE e where
  sourceRenameE :: (Distinct o, Renamer m) => e i -> m o (e o)

class SourceRenamableB (b :: B) where
  sourceRenameB :: (Renamer m, Distinct o)
                => b i i'
                -> (forall o'. DExt o o' => b o o' -> m o' a)
                -> m o a

instance SourceRenamableE (SourceNameOr UVar) where
  sourceRenameE (SourceName sid sourceName) =
    InternalName sid sourceName <$> lookupSourceName sid sourceName
  sourceRenameE _ = error "Shouldn't be source-renaming internal names"

lookupSourceName :: Renamer m => SrcId -> SourceName -> m n (UVar n)
lookupSourceName sid v = do
  sm <- askSourceMap
  case lookupSourceMapPure sm v of
    [] -> throw sid $ UnboundVarErr $ pprint v
    LocalVar binderSid v' : _ -> do
      emitNameInfo sid $ LocalOcc binderSid
      return v'
    [ModuleVar desc maybeV] -> case maybeV of
      Just v' -> do
        emitNameInfo sid $ TopOcc (pprint desc)
        return v'
      Nothing -> throw sid $ VarDefErr $ pprint v
    vs -> throw sid $ AmbiguousVarErr (pprint v) (map pprint vs)

instance SourceRenamableE (SourceNameOr (Name (AtomNameC CoreIR))) where
  sourceRenameE (SourceName sid sourceName) = do
    lookupSourceName sid sourceName >>= \case
      UAtomVar v -> return $ InternalName sid sourceName v
      _ -> throw sid $ NotAnOrdinaryVar $ pprint sourceName
  sourceRenameE _ = error "Shouldn't be source-renaming internal names"

instance SourceRenamableE (SourceNameOr (Name DataConNameC)) where
  sourceRenameE (SourceName sid sourceName) = do
    lookupSourceName sid sourceName >>= \case
      UDataConVar v -> return $ InternalName sid sourceName v
      _ -> throw sid $ NotADataCon $ pprint sourceName
  sourceRenameE _ = error "Shouldn't be source-renaming internal names"

instance SourceRenamableE (SourceNameOr (Name ClassNameC)) where
  sourceRenameE (SourceName sid sourceName) = do
    lookupSourceName sid sourceName >>= \case
      UClassVar v -> return $ InternalName sid sourceName v
      _ -> throw sid $ NotAClassName $ pprint sourceName
  sourceRenameE _ = error "Shouldn't be source-renaming internal names"

instance SourceRenamableE (SourceNameOr (Name c)) => SourceRenamableE (SourceOrInternalName c) where
  sourceRenameE (SourceOrInternalName x) = SourceOrInternalName <$> sourceRenameE x

instance (SourceRenamableE e, SourceRenamableB b) => SourceRenamableE (Abs b e) where
  sourceRenameE (Abs b e) = sourceRenameB b \b' -> Abs b' <$> sourceRenameE e

instance SourceRenamableB (UBinder (AtomNameC CoreIR)) where
  sourceRenameB b cont = sourceRenameUBinder UAtomVar b cont

instance SourceRenamableE UAnn where
  sourceRenameE UNoAnn = return UNoAnn
  sourceRenameE (UAnn ann) = UAnn <$> sourceRenameE ann

instance SourceRenamableB UAnnBinder where
  sourceRenameB (UAnnBinder expl b ann cs) cont = do
    ann' <- sourceRenameE ann
    cs' <- mapM sourceRenameE cs
    sourceRenameB b \b' -> cont $ UAnnBinder expl b' ann' cs'

instance SourceRenamableE UExpr where
  sourceRenameE (WithSrcE sid expr) = liftM (WithSrcE sid) $ setMayShadow True case expr of
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

instance SourceRenamableB UDecl where
  sourceRenameB (WithSrcB sid decl) cont = case decl of
    ULet ann pat ty expr -> do
      expr' <- sourceRenameE expr
      ty' <- mapM sourceRenameE ty
      sourceRenameB pat \pat' ->
        cont $ WithSrcB sid $ ULet ann pat' ty' expr'
    UExprDecl e -> do
      e' <- UExprDecl <$> sourceRenameE e
      cont $ WithSrcB sid e'
    UPass -> cont $ WithSrcB sid UPass

instance SourceRenamableE ULamExpr where
  sourceRenameE (ULamExpr args expl effs resultTy body) =
    sourceRenameB args \args' -> ULamExpr args'
      <$> pure expl
      <*> mapM sourceRenameE effs
      <*> mapM sourceRenameE resultTy
      <*> sourceRenameE body

instance SourceRenamableE UBlock where
  sourceRenameE (WithSrcE sid (UBlock decls result)) =
    sourceRenameB decls \decls' -> do
      result' <- sourceRenameE result
      return $ WithSrcE sid $ UBlock decls' result'

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

sourceRenameUBinder
  :: (Color c, Distinct o, Renamer m)
  => (forall l. Name c l -> UVar l)
  -> UBinder c i i'
  -> (forall o'. DExt o o' => UBinder c o o' -> m o' a)
  -> m o a
sourceRenameUBinder asUVar (WithSrcB sid ubinder) cont = case ubinder of
  UBindSource b -> do
    SourceMap sm <- askSourceMap
    mayShadow <- askMayShadow
    let shadows = M.member b sm
    when (not mayShadow && shadows) $ throw sid $ RepeatedVarErr $ pprint b
    withFreshM (getNameHint b) \name -> do
      Distinct <- getDistinct
      emitNameInfo sid $ LocalBinder []
      extendSourceMap sid b (asUVar $ binderName name) $
        cont $ WithSrcB sid $ UBind b name
  UBind _ _ -> error "Shouldn't be source-renaming internal names"
  UIgnore -> cont $ WithSrcB sid $ UIgnore

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

instance SourceRenamableE UMethodDef where
  sourceRenameE (WithSrcE sid ((UMethodDef ~(SourceName vSid v) expr))) = WithSrcE sid <$> do
    lookupSourceName vSid v >>= \case
      UMethodVar v' -> UMethodDef (InternalName vSid v v') <$> sourceRenameE expr
      _ -> throw vSid $ NotAMethodName $ pprint v

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
  sourceRenamePat sibs (WithSrcB sid ubinder) cont = do
    newSibs <- case ubinder of
      UBindSource b -> do
        when (S.member b sibs) $ throw sid $ RepeatedPatVarErr $ pprint b
        return $ S.singleton b
      UIgnore -> return mempty
      UBind _ _ -> error "Shouldn't be source-renaming internal names"
    sourceRenameB (WithSrcB sid ubinder) \ubinder' ->
      cont (sibs <> newSibs) ubinder'

instance SourceRenamablePat UPat where
  sourceRenamePat sibs (WithSrcB sid pat) cont = case pat of
    UPatBinder b -> sourceRenamePat sibs b \sibs' b' ->
      cont sibs' $ WithSrcB sid $ UPatBinder b'
    UPatCon con bs -> do
      -- TODO Deduplicate this against the code for sourceRenameE of
      -- the SourceName case of SourceNameOr
      con' <- sourceRenameE con
      sourceRenamePat sibs bs \sibs' bs' ->
        cont sibs' $ WithSrcB sid $ UPatCon con' bs'
    UPatDepPair (PairB p1 p2) ->
      sourceRenamePat sibs  p1 \sibs' p1' ->
        sourceRenamePat sibs' p2 \sibs'' p2' ->
          cont sibs'' $ WithSrcB sid $ UPatDepPair $ PairB p1' p2'
    UPatProd  bs -> sourceRenamePat sibs bs \sibs' bs' -> cont sibs' $ WithSrcB sid $ UPatProd bs'
    UPatTable ps -> sourceRenamePat sibs ps \sibs' ps' -> cont sibs' $ WithSrcB sid $ UPatTable ps'

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

instance SourceRenamablePat p => SourceRenamablePat (Nest p) where
  sourceRenamePat sibs (Nest b bs) cont =
    sourceRenamePat sibs b \sibs' b' ->
      sourceRenamePat sibs' bs \sibs'' bs' ->
        cont sibs'' $ Nest b' bs'
  sourceRenamePat sibs Empty cont = cont sibs Empty

instance SourceRenamableB UPat where
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
    UDataDefDecl _ ~(WithSrcB _ (UBindSource tyConName)) dataConNames -> do
      S.singleton tyConName <> sourceNames dataConNames
    UStructDecl ~(WithSrcB _ (UBindSource tyConName)) _ -> do
      S.singleton tyConName
    UInterface _ _ ~(WithSrcB _ (UBindSource className)) methodNames -> do
      S.singleton className <> sourceNames methodNames
    UInstance _ _ _ _ instanceName _ -> sourceNames instanceName

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

instance HasSourceNames (UBinder' c) where
  sourceNames b = case b of
    UBindSource name -> S.singleton name
    UIgnore -> mempty
    UBind _ _ -> error "Shouldn't be source-renaming internal names"

-- === misc instance ===

instance SinkableE RenamerSubst where
  sinkingProofE = undefined
