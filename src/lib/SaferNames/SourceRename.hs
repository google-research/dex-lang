-- Copyright 2021 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module SaferNames.SourceRename (renameSourceNames) where

import Prelude hiding (id, (.))
import Control.Category
import Control.Monad.Except hiding (Except)
import qualified Data.Set        as S
import qualified Data.Map.Strict as M

-- import Env
import Err
import LabeledItems
import SaferNames.NameCore
import SaferNames.Name
import SaferNames.ResolveImplicitNames
import SaferNames.Syntax

renameSourceNames :: Fallible m => Scope (n::S) -> SourceMap n -> SourceUModule -> m (UModule n)
-- renameSourceNames scope sourceMap m =
--   runReaderT (runReaderT (renameSourceNames' m) (scope, sourceMap)) False
renameSourceNames = undefined

-- type RenameEnv (n::S) = (Scope n, SourceMap n)

-- We have this class because we want to read some extra context (whether
-- shadowing is allowed) but we've already used up the MonadReader
-- (we can't add a field because we want it to be monoidal).
class (Monad1 m, ScopeExtender m, Fallible1 m) => Renamer m where
  askMayShadow :: m n Bool
  setMayShadow :: Bool -> m n a -> m n a
  askSourceMap :: m n (SourceMap n)
  extendSourceMap :: (SourceMap n) -> m n a -> m n a

-- -- Will implement Renamer directly (with a newtype)
-- data RenamerData (n::S) a

-- instance Functor (RenamerData n) where

-- instance Applicative (RenamerData n) where

-- instance Monad (RenamerData n) where

-- instance ScopeReader RenamerData where

-- instance ScopeExtender RenamerData where

-- instance Fallibleor Err (RenamerData n) where

-- instance Renamer RenamerData where

-- instance Fallible m => Renamer n (ReaderT (RenameEnv n) (ReaderT Bool m)) where
--   askMayShadow = lift ask
--   setMayShadow mayShadow cont = do
--     env <- ask
--     lift $ local (const mayShadow) (runReaderT cont env)

_renameSourceNames' :: Renamer m => SourceUModule -> m o (UModule o)
_renameSourceNames' (SourceUModule decl) = do
  (RenamerContent _ sourceMap decl') <- runRenamerNameGenT $
    sourceRenameB $ resolveImplicitTopDecl decl
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
        let sourceMap' = inject sourceMap <> sourceMap2
        return $ RenamerContent (frag >>> frag2) sourceMap' expr2
  getDistinctEvidenceG = RenamerNameGenT do
    Distinct <- getDistinct
    return $ RenamerContent id mempty getDistinctEvidence

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
      Just (EnvVal AtomNameRep    name) -> return $ InternalName $ UAtomVar name
      Just (EnvVal TyConNameRep   name) -> return $ InternalName $ UTyConVar name
      Just (EnvVal DataConNameRep name) -> return $ InternalName $ UDataConVar name
      Just (EnvVal ClassNameRep   name) -> return $ InternalName $ UClassVar name
      Just (EnvVal MethodNameRep  name) -> return $ InternalName $ UMethodVar name
      Just (EnvVal DataDefNameRep _   ) -> error "Shouldn't find these in source map"
      Just (EnvVal SuperclassNameRep _) -> error "Shouldn't find these in source map"
  sourceRenameE _ = error "Shouldn't be source-renaming internal names"

instance NameColor c => SourceRenamableE (SourceNameOr (Name c)) where
  sourceRenameE (SourceName sourceName) = do
    SourceMap sourceMap <- askSourceMap
    case M.lookup sourceName sourceMap of
      Nothing    -> throw UnboundVarErr $ pprint sourceName
      Just (EnvVal rep val) ->
        case eqNameColorRep rep (nameColorRep :: NameColorRep c) of
          Just EqNameColor -> return $ InternalName val
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
  sourceRenameE (RWSEffect rws name) = RWSEffect rws <$> sourceRenameE name
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
        sourceRenameE $ Abs paramBs $ PairE (ListE superclasses) (ListE methodTys)
      runRenamerNameGenT $ sourceRenameUBinder className `bindG` \className' ->
        sourceRenameUBinderNest methodNames `bindG` \methodNames' ->
        returnG $ UInterface paramBs' superclasses' methodTys' className' methodNames'
    UInstance className conditions params methodDefs instanceName -> do
      className' <- sourceRenameE className
      Abs conditions' (PairE (ListE params') (ListE methodDefs')) <-
        sourceRenameE $ Abs conditions (PairE (ListE params) $ ListE methodDefs)
      runRenamerNameGenT $ UInstance className' conditions' params' methodDefs' `fmapG` sourceRenameB instanceName

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
      let frag = (singletonScope freshName)
      let sourceMap' = SourceMap (M.singleton b (EnvVal nameColorRep $ nameBinderName freshName))
      return $ RenamerContent frag sourceMap' $ UBind freshName
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
  sourceRenameE (UMethodDef v expr) =
    UMethodDef <$> sourceRenameE v <*> sourceRenameE expr

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

-- TODO It seems this monad actually has no way for a downstream action
-- to check for membership in the sibling set produced by an upstream action?
-- Do we already have an ask/extend type of monad for this sort of thing?
-- Does it need to be re-kinded?
-- Alternately, should I just raise the error in `bindG` and be done with it?
data PatRenamerNameGenT (m::MonadKind1) (e::E) (n::S) =
  PatRenamerNameGenT { runPatRenamerNameGenT :: (m n (SiblingSet, RenamerContent e n)) }

instance (Renamer m) => NameGen (PatRenamerNameGenT m) where
  returnG expr = PatRenamerNameGenT $ fmap (mempty,) $ runRenamerNameGenT $ returnG expr
  bindG (PatRenamerNameGenT action) cont = PatRenamerNameGenT do
    (sibs, RenamerContent frag sourceMap expr) <- action
    extendScope frag $ extendSourceMap sourceMap $ do
      (sibs', RenamerContent frag' sourceMap' expr') <- runPatRenamerNameGenT $ cont expr
      withExtEvidence frag' do
        let sourceMap'' = inject sourceMap <> sourceMap'
        return (sibs <> sibs', RenamerContent (frag >>> frag') sourceMap'' expr')
  getDistinctEvidenceG = PatRenamerNameGenT do
    Distinct <- getDistinct
    return (mempty, RenamerContent id mempty getDistinctEvidence)

class SourceRenamablePat (pat::B) where
  sourceRenamePat :: Renamer m
                  => SiblingSet
                  -> pat i i'
                  -> PatRenamerNameGenT m (pat o) o

instance SourceRenamablePat (UBinder AtomNameC) where
  sourceRenamePat siblingNames ubinder = PatRenamerNameGenT do
    newSibs <- case ubinder of
      UBindSource b -> do
        when (S.member b siblingNames) $ throw RepeatedPatVarErr $ pprint b
        return $ S.singleton b
      UIgnore -> return mempty
      UBind _ -> error "Shouldn't be source-renaming internal names"
    ubinder' <- runRenamerNameGenT $ sourceRenameB ubinder
    return $ (newSibs, ubinder')

instance SourceRenamablePat UPat' where
  sourceRenamePat siblingNames pat = case pat of
    UPatBinder b -> UPatBinder `fmapG` sourceRenamePat siblingNames b
    UPatCon ~(SourceName con) bs -> PatRenamerNameGenT do
      -- TODO Deduplicate this against the code for sourceRenameE of
      -- the SourceName case of SourceNameOr
      SourceMap sourceMap <- askSourceMap
      con' <- case M.lookup con sourceMap of
        Nothing    -> throw UnboundVarErr $ pprint con
        Just (EnvVal DataConNameRep name) -> return $ InternalName name
        Just _ -> throw TypeErr $ "Not a data constructor: " ++ pprint con
      runPatRenamerNameGenT $ UPatCon con' `fmapG` sourceRenamePat siblingNames bs
    UPatPair (PairB p1 p2) ->
      sourceRenamePat siblingNames p1 `bindG` \p1' ->
      sourceRenamePat siblingNames p2 `bindG` \p2' ->
      returnG $ UPatPair $ PairB p1' p2'
    UPatUnit UnitB -> returnG $ UPatUnit UnitB
    UPatRecord labels ps -> UPatRecord labels `fmapG` sourceRenamePat siblingNames ps
    UPatVariant labels label p -> UPatVariant labels label `fmapG` sourceRenamePat siblingNames p
    UPatVariantLift labels p -> UPatVariantLift labels `fmapG` sourceRenamePat siblingNames p
    UPatTable ps -> UPatTable `fmapG` sourceRenamePat siblingNames ps

instance SourceRenamablePat UnitB where
  sourceRenamePat _ UnitB = returnG UnitB

instance (SourceRenamablePat p1, SourceRenamablePat p2)
         => SourceRenamablePat (PairB p1 p2) where
  sourceRenamePat sibs (PairB p1 p2) =
    sourceRenamePat sibs p1 `bindG` \p1' ->
    sourceRenamePat sibs p2 `bindG` \p2' ->
    returnG $ PairB p1' p2'

instance (SourceRenamablePat p1, SourceRenamablePat p2)
         => SourceRenamablePat (EitherB p1 p2) where
  sourceRenamePat sibs (LeftB p) =
    sourceRenamePat sibs p `bindG` \p' ->
    returnG $ LeftB p'
  sourceRenamePat sibs (RightB p) =
    sourceRenamePat sibs p `bindG` \p' ->
    returnG $ RightB p'

instance SourceRenamablePat p => SourceRenamablePat (WithSrcB p) where
  sourceRenamePat sibs (WithSrcB pos pat) = PatRenamerNameGenT $ addSrcContext pos $
    runPatRenamerNameGenT $ (WithSrcB pos) `fmapG` sourceRenamePat sibs pat

instance SourceRenamablePat p => SourceRenamablePat (Nest p) where
  sourceRenamePat sibs (Nest b bs) =
    sourceRenamePat sibs b `bindG` \b' ->
    sourceRenamePat sibs bs `bindG` \bs' ->
    returnG $ Nest b' bs'
  sourceRenamePat _ Empty = returnG Empty

instance SourceRenamableB UPat' where
  sourceRenameB pat = RenamerNameGenT $ snd <$> action where
    action = runPatRenamerNameGenT $ sourceRenamePat mempty pat
