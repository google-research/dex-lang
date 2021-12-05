-- Copyright 2021 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module SourceRename (renameSourceNames) where

import Prelude hiding (id, (.))
import Control.Category
import Control.Monad.Except hiding (Except)
import qualified Data.Set        as S
import qualified Data.Map.Strict as M

-- import Subst
import Err
import LabeledItems
import Name
import Syntax

renameSourceNames :: (Distinct n, Fallible m)
                  => Scope (n::S) -> SourceMap n -> SourceUModule -> m (UModule n)
renameSourceNames scope sourceMap sourceModule =
  liftExcept $ runFallibleM $ runScopeReaderT scope $
    runOutReaderT (RenamerSubst sourceMap False) $ runRenamerM $
      renameSourceNames' sourceModule

data RenamerSubst n = RenamerSubst { renamerSourceMap :: SourceMap n
                                   , renamerMayShadow :: Bool }

newtype RenamerM (n::S) (a:: *) =
  RenamerM { runRenamerM :: OutReaderT RenamerSubst (ScopeReaderT FallibleM) n a }
  deriving ( Functor, Applicative, Monad, MonadFail, Fallible
           , AlwaysImmut, ScopeReader, ScopeExtender)

class ( Monad1 m, AlwaysImmut m, ScopeReader m
      , ScopeExtender m, Fallible1 m) => Renamer m where
  askMayShadow :: m n Bool
  setMayShadow :: Bool -> m n a -> m n a
  askSourceMap :: m n (SourceMap n)
  extendSourceMap :: (SourceMap n) -> m n a -> m n a

instance Renamer RenamerM where
  askMayShadow = RenamerM $ renamerMayShadow <$> askOutReader
  askSourceMap = RenamerM $ renamerSourceMap <$> askOutReader
  setMayShadow mayShadow (RenamerM cont) = RenamerM do
    RenamerSubst sm _ <- askOutReader
    localOutReader (RenamerSubst sm mayShadow) cont
  extendSourceMap sourceMap (RenamerM cont) = RenamerM do
    RenamerSubst sm mayShadow <- askOutReader
    localOutReader (RenamerSubst (sm <> sourceMap) mayShadow) cont

renameSourceNames' :: Renamer m => SourceUModule -> m o (UModule o)
renameSourceNames' (SourceUModule decl) = do
  (RenamerContent _ sourceMap decl') <- runRenamerNameGenT $ sourceRenameB decl
  return $ UModule decl' sourceMap

class SourceRenamableE e where
  sourceRenameE :: Renamer m => e i -> m o (e o)

class SourceRenamableB (b :: B) where
  sourceRenameB :: Renamer m
                => b i i'
                -> RenamerNameGenT m (b o) o

data RenamerNameGenT (m::MonadKind1) (e::E) (n::S) =
  RenamerNameGenT { runRenamerNameGenT :: (m n (RenamerContent e n)) }

data RenamerContent e n where
  RenamerContent
    :: Distinct l
    => ScopeFrag n l
    -> SourceMap l
    -> e l
    -> RenamerContent e n

instance (Renamer m) => NameGen (RenamerNameGenT m) where
  returnG expr = RenamerNameGenT do
    Distinct <- getDistinct
    return $ RenamerContent id mempty expr
  bindG (RenamerNameGenT action) cont = RenamerNameGenT do
    (RenamerContent frag sourceMap expr) <- action
    extendScope frag $ extendSourceMap sourceMap $ do
      (RenamerContent frag2 sourceMap2 expr2) <- runRenamerNameGenT $ cont expr
      withExtEvidence frag2 do
        let sourceMap' = sink sourceMap <> sourceMap2
        return $ RenamerContent (frag >>> frag2) sourceMap' expr2
  getDistinctEvidenceG = RenamerNameGenT do
    Distinct <- getDistinct
    return $ RenamerContent id mempty Distinct

withSourceRenameB :: SourceRenamableB b
                  => Renamer m
                  => b i i'
                  -> (forall o'. b o o' -> m o' r) -> m o r
withSourceRenameB b cont = do
  (RenamerContent frag sourceMap b') <- runRenamerNameGenT $ sourceRenameB b
  extendScope frag $ extendSourceMap sourceMap $ cont b'

instance SourceRenamableE (SourceNameOr UVar) where
  sourceRenameE (SourceName sourceName) = do
    SourceMap sourceMap <- askSourceMap
    case M.lookup sourceName sourceMap of
      Nothing -> throw UnboundVarErr $ pprint sourceName
      Just (WithColor AtomNameRep    name) -> return $ InternalName $ UAtomVar name
      Just (WithColor TyConNameRep   name) -> return $ InternalName $ UTyConVar name
      Just (WithColor DataConNameRep name) -> return $ InternalName $ UDataConVar name
      Just (WithColor ClassNameRep   name) -> return $ InternalName $ UClassVar name
      Just (WithColor MethodNameRep  name) -> return $ InternalName $ UMethodVar name
      Just (WithColor DataDefNameRep _   ) -> error "Shouldn't find these in source map"
      Just (WithColor SuperclassNameRep _) -> error "Shouldn't find these in source map"
  sourceRenameE _ = error "Shouldn't be source-renaming internal names"

lookupSourceName :: Renamer m => SourceName -> m n (WithColor Name n)
lookupSourceName v = do
  SourceMap sourceMap <- askSourceMap
  case M.lookup v sourceMap of
    Nothing     -> throw UnboundVarErr $ pprint v
    Just envVal -> return envVal

instance NameColor c => SourceRenamableE (SourceNameOr (Name c)) where
  sourceRenameE (SourceName sourceName) = do
    lookupSourceName sourceName >>= \case
      WithColor rep val -> case eqNameColorRep rep (nameColorRep :: NameColorRep c) of
        Just ColorsEqual -> return $ InternalName val
        Nothing -> throw TypeErr $ "Incorrect name color: " ++ pprint sourceName
  sourceRenameE _ = error "Shouldn't be source-renaming internal names"

instance (SourceRenamableE e, SourceRenamableB b) => SourceRenamableE (Abs b e) where
  sourceRenameE (Abs b e) = withSourceRenameB b \b' -> Abs b' <$> sourceRenameE e

instance SourceRenamableB (UBinder AtomNameC) where
  sourceRenameB b = sourceRenameUBinder b

instance SourceRenamableB UPatAnn where
  sourceRenameB (UPatAnn b ann) = RenamerNameGenT do
    ann' <- mapM sourceRenameE ann
    runRenamerNameGenT $ (flip UPatAnn ann') `fmapG` sourceRenameB b

instance SourceRenamableB (UAnnBinder AtomNameC) where
  sourceRenameB (UAnnBinder b ann) = RenamerNameGenT do
    ann' <- sourceRenameE ann
    runRenamerNameGenT $ (flip UAnnBinder ann') `fmapG` sourceRenameB b

instance SourceRenamableB UPatAnnArrow where
  sourceRenameB (UPatAnnArrow b arrow) =
    (flip UPatAnnArrow arrow) `fmapG` sourceRenameB b

instance SourceRenamableE UExpr' where
  sourceRenameE expr = setMayShadow True case expr of
    UVar v -> UVar <$> sourceRenameE v
    ULam (ULamExpr arr pat body) ->
      withSourceRenameB pat \pat' ->
        ULam <$> ULamExpr arr pat' <$> sourceRenameE body
    UPi (UPiExpr arr pat eff body) ->
      withSourceRenameB pat \pat' ->
        UPi <$> (UPiExpr arr pat' <$> sourceRenameE eff <*> sourceRenameE body)
    UApp arr f x -> UApp arr <$> sourceRenameE f <*> sourceRenameE x
    UDecl (UDeclExpr decl rest) ->
      withSourceRenameB decl \decl' ->
        UDecl <$> UDeclExpr decl' <$> sourceRenameE rest
    UFor d (UForExpr pat body) ->
      withSourceRenameB pat \pat' ->
        UFor d <$> UForExpr pat' <$> sourceRenameE body
    UCase scrut alts ->
      UCase <$> sourceRenameE scrut <*> mapM sourceRenameE alts
    UHole -> return UHole
    UTypeAnn e ty -> UTypeAnn <$> sourceRenameE e <*> sourceRenameE ty
    UTabCon xs -> UTabCon <$> mapM sourceRenameE xs
    UIndexRange low high ->
      UIndexRange <$> mapM sourceRenameE low <*> mapM sourceRenameE high
    UPrimExpr e -> UPrimExpr <$> mapM sourceRenameE e
    URecord (Ext tys ext) -> URecord <$>
      (Ext <$> mapM sourceRenameE tys <*> mapM sourceRenameE ext)
    UVariant types label val ->
      -- Do we not need to source-rename the types?  Their type is
      -- type :: LabeledItems ()
      UVariant types <$> return label <*> sourceRenameE val
    UVariantLift labels val -> UVariantLift labels <$> sourceRenameE val
    URecordTy (Ext tys ext) -> URecordTy <$>
      (Ext <$> mapM sourceRenameE tys <*> mapM sourceRenameE ext)
    UVariantTy (Ext tys ext) -> UVariantTy <$>
      (Ext <$> mapM sourceRenameE tys <*> mapM sourceRenameE ext)
    UIntLit   x -> return $ UIntLit x
    UFloatLit x -> return $ UFloatLit x

instance SourceRenamableE UAlt where
  sourceRenameE (UAlt pat body) =
    withSourceRenameB pat \pat' ->
      UAlt pat' <$> sourceRenameE body

instance ((forall n. Ord (a n)), SourceRenamableE a) => SourceRenamableE (EffectRowP a) where
  sourceRenameE (EffectRow row tailVar) =
    EffectRow <$> row' <*> mapM sourceRenameE tailVar
    where row' = S.fromList <$> traverse sourceRenameE (S.toList row)

instance SourceRenamableE a => SourceRenamableE (EffectP a) where
  sourceRenameE (RWSEffect rws (Just name)) = RWSEffect rws <$> Just <$> sourceRenameE name
  sourceRenameE (RWSEffect rws Nothing) = return $ RWSEffect rws Nothing
  sourceRenameE ExceptionEffect = return ExceptionEffect
  sourceRenameE IOEffect = return IOEffect

instance SourceRenamableE a => SourceRenamableE (WithSrcE a) where
  sourceRenameE (WithSrcE pos e) = addSrcContext pos $
    WithSrcE pos <$> sourceRenameE e

instance SourceRenamableB a => SourceRenamableB (WithSrcB a) where
  sourceRenameB (WithSrcB pos b) = RenamerNameGenT $ addSrcContext pos $
    runRenamerNameGenT $ (WithSrcB pos) `fmapG` sourceRenameB b

instance SourceRenamableB UDecl where
  sourceRenameB decl = RenamerNameGenT $ case decl of
    ULet ann pat expr -> do
      expr' <- sourceRenameE expr
      runRenamerNameGenT $ flip (ULet ann) expr' `fmapG` sourceRenameB pat
    UDataDefDecl dataDef tyConName dataConNames -> do
      dataDef' <- sourceRenameE dataDef
      runRenamerNameGenT $ sourceRenameUBinder tyConName `bindG` \tyConName' ->
        sourceRenameUBinderNest dataConNames `bindG` \dataConNames' ->
        returnG $ UDataDefDecl dataDef' tyConName' dataConNames'
    UInterface paramBs superclasses methodTys className methodNames -> do
      Abs paramBs' (PairE (ListE superclasses') (ListE methodTys')) <-
        withSourceRenameB paramBs \paramBs' -> do
          superclasses' <- mapM sourceRenameE superclasses
          methodTys' <- zipWithM (renameMethodType paramBs) methodTys methodSourceNames
          return $ Abs paramBs' (PairE (ListE superclasses') (ListE methodTys'))
      runRenamerNameGenT $ sourceRenameUBinder className `bindG` \className' ->
        sourceRenameUBinderNest methodNames `bindG` \methodNames' ->
        returnG $ UInterface paramBs' superclasses' methodTys' className' methodNames'
      where methodSourceNames = nestToList (\(UBindSource n) -> n) methodNames
    UInstance className conditions params methodDefs instanceName -> do
      className' <- sourceRenameE className
      Abs conditions' (PairE (ListE params') (ListE methodDefs')) <-
        sourceRenameE $ Abs conditions (PairE (ListE params) $ ListE methodDefs)
      runRenamerNameGenT $ UInstance className' conditions' params' methodDefs' `fmapG` sourceRenameB instanceName

renameMethodType :: (Fallible1 m, Renamer m)
                 => Nest (UAnnBinder AtomNameC) i' i
                 -> UMethodType i
                 -> SourceName
                 -> m o (UMethodType o)
renameMethodType paramBinders (UMethodType ~(Left explicitNames) ty) methodName = do
  explicitFlags <- case explicitNames of
    [] -> return $ replicate (nestLength paramBinders) False
    _ | paramNames == explicitNames -> return $ replicate (nestLength paramBinders) True
    _ -> case unexpected of
      []    -> throw NotImplementedErr "Permuted or incomplete explicit type binders are not supported yet."
      (h:_) -> throw TypeErr $ "Explicit type binder `" ++ pprint h ++ "` in method " ++
                                pprint methodName ++ " is not a type parameter of its interface"
      where unexpected = filter (not . (`elem` paramNames)) explicitNames
  UMethodType (Right explicitFlags) <$> sourceRenameE ty
  where
    paramNames = nestToList (\(UAnnBinder (UBindSource n) _) -> n) paramBinders

instance SourceRenamableB UnitB where
  sourceRenameB UnitB = returnG UnitB

instance (SourceRenamableB b1, SourceRenamableB b2) => SourceRenamableB (EitherB b1 b2) where
  sourceRenameB (LeftB  b) = LeftB  `fmapG` sourceRenameB b
  sourceRenameB (RightB b) = RightB `fmapG` sourceRenameB b

sourceRenameUBinderNest :: (Renamer m, NameColor c)
                        => Nest (UBinder c) i i'
                        -> RenamerNameGenT m (Nest (UBinder c) o) o
sourceRenameUBinderNest Empty = returnG Empty
sourceRenameUBinderNest (Nest b bs) =
  sourceRenameUBinder b `bindG` \b' ->
  sourceRenameUBinderNest bs `bindG` \bs' ->
  returnG $ Nest b' bs'

sourceRenameUBinder :: (Renamer m, NameColor c)
                    => UBinder c i i' -> RenamerNameGenT m (UBinder c o) o
sourceRenameUBinder ubinder = case ubinder of
  UBindSource b -> RenamerNameGenT do
    SourceMap sourceMap <- askSourceMap
    mayShadow <- askMayShadow
    unless (mayShadow || not (M.member b sourceMap)) $
      throw RepeatedVarErr $ pprint b
    withFreshM (getNameHint b) nameColorRep \freshName -> do
      Distinct <- getDistinct
      let sourceMap' = SourceMap (M.singleton b (WithColor nameColorRep $ nameBinderName freshName))
      return $ RenamerContent (toScopeFrag freshName) sourceMap' $ UBind freshName
  UBind _ -> error "Shouldn't be source-renaming internal names"
  UIgnore -> returnG UIgnore

instance SourceRenamableE UDataDef where
  sourceRenameE (UDataDef (tyConName, paramBs) dataCons) = do
    (RenamerContent frag sourceMap paramBs') <- runRenamerNameGenT $ sourceRenameB paramBs
    extendScope frag $ extendSourceMap sourceMap $ do
      dataCons' <- forM dataCons \(dataConName, argBs) -> do
        argBs' <- sourceRenameE argBs
        return (dataConName, argBs')
      return $ UDataDef (tyConName, paramBs') dataCons'

instance SourceRenamableE UDataDefTrail where
  sourceRenameE (UDataDefTrail args) = withSourceRenameB args \args' ->
    return $ UDataDefTrail args'

instance (SourceRenamableE e1, SourceRenamableE e2) => SourceRenamableE (PairE e1 e2) where
  sourceRenameE (PairE x y) = PairE <$> sourceRenameE x <*> sourceRenameE y

instance SourceRenamableE e => SourceRenamableE (ListE e) where
  sourceRenameE (ListE xs) = ListE <$> mapM sourceRenameE xs

instance SourceRenamableE UMethodDef where
  sourceRenameE (UMethodDef ~(SourceName v) expr) = do
    lookupSourceName v >>= \case
      WithColor MethodNameRep v' -> UMethodDef (InternalName v') <$> sourceRenameE expr
      _ -> throw TypeErr $ "not a method name: " ++ pprint v

instance SourceRenamableB b => SourceRenamableB (Nest b) where
  sourceRenameB (Nest b bs) =
    sourceRenameB b `bindG` \b' ->
    sourceRenameB bs `bindG` \bs' ->
    returnG $ Nest b' bs'
  sourceRenameB Empty = returnG Empty

-- -- === renaming patterns ===

-- We want to ensure that pattern siblings don't shadow each other, so we carry
-- the set of in-scope siblings' names along with the normal renaming env.

type SiblingSet = S.Set SourceName

data PatRenamerNameGenT (m::MonadKind1) (e::E) (n::S) = PatRenamerNameGenT
  { runPatRenamerNameGenT :: SiblingSet -> m n (SiblingSet, RenamerContent e n) }

liftPatRenamerNameGenT :: Monad1 m => PatRenamerNameGenT m e n -> RenamerNameGenT m e n
liftPatRenamerNameGenT m = RenamerNameGenT $ snd <$> runPatRenamerNameGenT m mempty

instance (Renamer m) => NameGen (PatRenamerNameGenT m) where
  returnG expr = PatRenamerNameGenT \_ ->
                   fmap (mempty,) $ runRenamerNameGenT $ returnG expr
  bindG (PatRenamerNameGenT action) cont = PatRenamerNameGenT \sibs -> do
    (extraSibs1, RenamerContent frag sourceMap expr) <- action sibs
    extendScope frag $ extendSourceMap sourceMap $ do
      (extraSibs2, RenamerContent frag' sourceMap' expr') <-
          runPatRenamerNameGenT (cont expr) (sibs <> extraSibs1)
      withExtEvidence frag' do
        let sourceMap'' = sink sourceMap <> sourceMap'
        return (extraSibs1 <> extraSibs2, RenamerContent (frag >>> frag') sourceMap'' expr')

  getDistinctEvidenceG = PatRenamerNameGenT \_ -> do
    Distinct <- getDistinct
    return (mempty, RenamerContent id mempty Distinct)

class SourceRenamablePat (pat::B) where
  sourceRenamePat :: Renamer m
                  => pat i i'
                  -> PatRenamerNameGenT m (pat o) o

instance SourceRenamablePat (UBinder AtomNameC) where
  sourceRenamePat ubinder = PatRenamerNameGenT \siblingNames -> do
    newSibs <- case ubinder of
      UBindSource b -> do
        when (S.member b siblingNames) $ throw RepeatedPatVarErr $ pprint b
        return $ S.singleton b
      UIgnore -> return mempty
      UBind _ -> error "Shouldn't be source-renaming internal names"
    ubinder' <- runRenamerNameGenT $ sourceRenameB ubinder
    return $ (newSibs, ubinder')

instance SourceRenamablePat UPat' where
  sourceRenamePat pat = case pat of
    UPatBinder b -> UPatBinder `fmapG` sourceRenamePat b
    UPatCon ~(SourceName con) bs -> PatRenamerNameGenT \sibs -> do
      -- TODO Deduplicate this against the code for sourceRenameE of
      -- the SourceName case of SourceNameOr
      SourceMap sourceMap <- askSourceMap
      con' <- case M.lookup con sourceMap of
        Nothing    -> throw UnboundVarErr $ pprint con
        Just (WithColor DataConNameRep name) -> return $ InternalName name
        Just _ -> throw TypeErr $ "Not a data constructor: " ++ pprint con
      runPatRenamerNameGenT (UPatCon con' `fmapG` sourceRenamePat bs) sibs
    UPatPair (PairB p1 p2) ->
      sourceRenamePat p1 `bindG` \p1' ->
      sourceRenamePat p2 `bindG` \p2' ->
      returnG $ UPatPair $ PairB p1' p2'
    UPatUnit UnitB -> returnG $ UPatUnit UnitB
    UPatRecord labels ps -> UPatRecord labels `fmapG` sourceRenamePat ps
    UPatVariant labels label p -> UPatVariant labels label `fmapG` sourceRenamePat p
    UPatVariantLift labels p -> UPatVariantLift labels `fmapG` sourceRenamePat p
    UPatTable ps -> UPatTable `fmapG` sourceRenamePat ps

instance SourceRenamablePat UnitB where
  sourceRenamePat UnitB = returnG UnitB

instance (SourceRenamablePat p1, SourceRenamablePat p2)
         => SourceRenamablePat (PairB p1 p2) where
  sourceRenamePat (PairB p1 p2) =
    sourceRenamePat p1 `bindG` \p1' ->
    sourceRenamePat p2 `bindG` \p2' ->
    returnG $ PairB p1' p2'

instance (SourceRenamablePat p1, SourceRenamablePat p2)
         => SourceRenamablePat (EitherB p1 p2) where
  sourceRenamePat (LeftB p) =
    sourceRenamePat p `bindG` \p' ->
    returnG $ LeftB p'
  sourceRenamePat (RightB p) =
    sourceRenamePat p `bindG` \p' ->
    returnG $ RightB p'

instance SourceRenamablePat p => SourceRenamablePat (WithSrcB p) where
   sourceRenamePat (WithSrcB pos pat) = PatRenamerNameGenT \sibs ->
     addSrcContext pos $
       runPatRenamerNameGenT (WithSrcB pos `fmapG` sourceRenamePat pat) sibs

instance SourceRenamablePat p => SourceRenamablePat (Nest p) where
  sourceRenamePat (Nest b bs) =
    sourceRenamePat b `bindG` \b' ->
    sourceRenamePat bs `bindG` \bs' ->
    returnG $ Nest b' bs'
  sourceRenamePat Empty = returnG Empty

instance SourceRenamableB UPat' where
  sourceRenameB pat = liftPatRenamerNameGenT $ sourceRenamePat pat

-- === misc instance ===

instance SinkableE RenamerSubst where
  sinkingProofE = undefined
