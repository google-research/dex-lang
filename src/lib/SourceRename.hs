-- Copyright 2021 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PartialTypeSignatures #-}

module SourceRename ( renameSourceNamesTopUDecl, uDeclErrSourceMap
                    , renameSourceNamesUExpr) where

import Prelude hiding (id, (.))
import Data.List (sort)
import Control.Category
import Control.Monad.Except hiding (Except)
import qualified Data.Set        as S
import qualified Data.Map.Strict as M

import Err
import LabeledItems
import Name
import Syntax
import PPrint()

renameSourceNamesTopUDecl
  :: (Fallible1 m, EnvReader m)
  => ModuleSourceName -> UDecl VoidS VoidS -> m n (Abs UDecl SourceMap n)
renameSourceNamesTopUDecl mname decl = do
  Distinct <- getDistinct
  Abs renamedDecl sourceMapLocalNames <- liftRenamer $ sourceRenameTopUDecl decl
  let sourceMap = SourceMap $ fmap (fmap (\(LocalVar v) -> ModuleVar mname (Just v))) $
                    fromSourceMap sourceMapLocalNames
  return $ Abs renamedDecl sourceMap

uDeclErrSourceMap:: ModuleSourceName -> UDecl VoidS VoidS -> SourceMap n
uDeclErrSourceMap mname decl =
  SourceMap $ M.fromSet (const [ModuleVar mname Nothing]) (sourceNames decl)

renameSourceNamesUExpr :: (Fallible1 m, EnvReader m) => UExpr VoidS -> m n (UExpr n)
renameSourceNamesUExpr expr = do
  Distinct <- getDistinct
  liftRenamer $ sourceRenameE expr

sourceRenameTopUDecl
  :: (Renamer m, Distinct o)
  => UDecl i i' -> m o (Abs UDecl SourceMap o)
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

instance SourceRenamableE (SourceNameOr (Name AtomNameC)) where
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

instance (SourceRenamableE e, SourceRenamableB b) => SourceRenamableE (Abs b e) where
  sourceRenameE (Abs b e) = sourceRenameB b \b' -> Abs b' <$> sourceRenameE e

instance SourceRenamableB (UBinder AtomNameC) where
  sourceRenameB b cont = sourceRenameUBinder UAtomVar b cont

instance SourceRenamableB UPatAnn where
  sourceRenameB (UPatAnn b ann) cont = do
    ann' <- mapM sourceRenameE ann
    sourceRenameB b \b' ->
      cont $ UPatAnn b' ann'

instance SourceRenamableB (UAnnBinder AtomNameC) where
  sourceRenameB (UAnnBinder b ann) cont = do
    ann' <- sourceRenameE ann
    sourceRenameB b \b' ->
      cont $ UAnnBinder b' ann'

instance SourceRenamableB UPatAnnArrow where
  sourceRenameB (UPatAnnArrow b arrow) cont =
    sourceRenameB b \b' -> cont $ UPatAnnArrow b' arrow

instance SourceRenamableE UExpr' where
  sourceRenameE expr = setMayShadow True case expr of
    UVar v -> UVar <$> sourceRenameE v
    ULam (ULamExpr arr pat body) ->
      sourceRenameB pat \pat' ->
        ULam <$> ULamExpr arr pat' <$> sourceRenameE body
    UPi (UPiExpr arr pat eff body) ->
      sourceRenameB pat \pat' ->
        UPi <$> (UPiExpr arr pat' <$> sourceRenameE eff <*> sourceRenameE body)
    UApp arr f x -> UApp arr <$> sourceRenameE f <*> sourceRenameE x
    UDecl (UDeclExpr decl rest) ->
      sourceRenameB decl \decl' ->
        UDecl <$> UDeclExpr decl' <$> sourceRenameE rest
    UFor d (UForExpr pat body) ->
      sourceRenameB pat \pat' ->
        UFor d <$> UForExpr pat' <$> sourceRenameE body
    UCase scrut alts ->
      UCase <$> sourceRenameE scrut <*> mapM sourceRenameE alts
    UHole -> return UHole
    UTypeAnn e ty -> UTypeAnn <$> sourceRenameE e <*> sourceRenameE ty
    UTabCon xs -> UTabCon <$> mapM sourceRenameE xs
    UIndexRange low high ->
      UIndexRange <$> mapM sourceRenameE low <*> mapM sourceRenameE high
    UPrimExpr e -> UPrimExpr <$> mapM sourceRenameE e
    ULabel name -> return $ ULabel name
    URecord elems -> URecord <$> mapM sourceRenameE elems
    UVariant types label val ->
      UVariant types <$> return label <*> sourceRenameE val
    UVariantLift labels val -> UVariantLift labels <$> sourceRenameE val
    ULabeledRow elems -> ULabeledRow <$> mapM sourceRenameE elems
    URecordTy elems -> URecordTy <$> mapM sourceRenameE elems
    UVariantTy (Ext tys ext) -> UVariantTy <$>
      (Ext <$> mapM sourceRenameE tys <*> mapM sourceRenameE ext)
    UIntLit   x -> return $ UIntLit x
    UFloatLit x -> return $ UFloatLit x

instance SourceRenamableE UFieldRowElem where
  sourceRenameE = \case
    UStaticField l e -> UStaticField l <$> sourceRenameE e
    UDynField    v e -> UDynField  <$> sourceRenameE v <*> sourceRenameE e
    UDynFields   v   -> UDynFields <$> sourceRenameE v

instance SourceRenamableE UAlt where
  sourceRenameE (UAlt pat body) =
    sourceRenameB pat \pat' ->
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
  sourceRenameB (WithSrcB pos b) cont = addSrcContext pos $
    sourceRenameB b \b' -> cont $ WithSrcB pos b'

instance SourceRenamableB UDecl where
  sourceRenameB decl cont = case decl of
    ULet ann pat expr -> do
      expr' <- sourceRenameE expr
      sourceRenameB pat \pat' ->
        cont $ ULet ann pat' expr'
    UDataDefDecl dataDef tyConName dataConNames -> do
      dataDef' <- sourceRenameE dataDef
      sourceRenameUBinder UTyConVar tyConName \tyConName' ->
        sourceRenameUBinderNest UDataConVar dataConNames \dataConNames' ->
           cont $ UDataDefDecl dataDef' tyConName' dataConNames'
    UInterface paramBs superclasses methodTys className methodNames -> do
      Abs paramBs' (PairE (ListE superclasses') (ListE methodTys')) <-
        sourceRenameB paramBs \paramBs' -> do
          superclasses' <- mapM sourceRenameE superclasses
          methodTys' <- zipWithM (renameMethodType paramBs) methodTys methodSourceNames
          return $ Abs paramBs' (PairE (ListE superclasses') (ListE methodTys'))
      sourceRenameUBinder UClassVar className \className' ->
        sourceRenameUBinderNest UMethodVar methodNames \methodNames' ->
          cont $ UInterface paramBs' superclasses' methodTys' className' methodNames'
      where methodSourceNames = nestToList (\(UBindSource n) -> n) methodNames
    UInstance className conditions params methodDefs instanceName -> do
      className' <- sourceRenameE className
      Abs conditions' (PairE (ListE params') (ListE methodDefs')) <-
        sourceRenameE $ Abs conditions (PairE (ListE params) $ ListE methodDefs)
      sourceRenameB instanceName \instanceName' ->
        cont $ UInstance className' conditions' params' methodDefs' instanceName'

renameMethodType :: (Fallible1 m, Renamer m, Distinct o)
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
  :: (Renamer m, Color c, Distinct o)
  => (forall l. Name c l -> UVar l)
  -> Nest (UBinder c) i i'
  -> (forall o'. DExt o o' => Nest (UBinder c) o o' ->  m o' a)
  -> m o a
sourceRenameUBinderNest _ Empty cont = cont Empty
sourceRenameUBinderNest asUVar (Nest b bs) cont =
  sourceRenameUBinder asUVar b \b' ->
    sourceRenameUBinderNest asUVar bs \bs' ->
      cont $ Nest b' bs'

sourceRenameUBinder :: (Distinct o, Renamer m, Color c)
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
  sourceRenameE (UDataDef (tyConName, paramBs) clsBs dataCons) = do
    sourceRenameB paramBs \paramBs' -> do
      sourceRenameB clsBs \clsBs' -> do
        dataCons' <- forM dataCons \(dataConName, argBs) -> do
          argBs' <- sourceRenameE argBs
          return (dataConName, argBs')
        return $ UDataDef (tyConName, paramBs') clsBs' dataCons'

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
  sourceRenameE (UMethodDef ~(SourceName v) expr) = do
    lookupSourceName v >>= \case
      UMethodVar v' -> UMethodDef (InternalName v v') <$> sourceRenameE expr
      _ -> throw TypeErr $ "not a method name: " ++ pprint v

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

instance SourceRenamablePat (UBinder AtomNameC) where
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
    UPatPair (PairB p1 p2) ->
      sourceRenamePat sibs  p1 \sibs' p1' ->
        sourceRenamePat sibs' p2 \sibs'' p2' ->
          cont sibs'' $ UPatPair $ PairB p1' p2'
    UPatUnit UnitB -> cont sibs $ UPatUnit UnitB
    UPatRecord rpat -> sourceRenamePat sibs rpat \sibs' rpat' -> cont sibs' (UPatRecord rpat')
    UPatVariant labels label p ->
      sourceRenamePat sibs p \sibs' p' ->
        cont sibs' $ UPatVariant labels label p'
    UPatVariantLift labels p ->
      sourceRenamePat sibs p \sibs' p' ->
        cont sibs' $ UPatVariantLift labels p'
    UPatTable ps -> sourceRenamePat sibs ps \sibs' ps' -> cont sibs' $ UPatTable ps'

instance SourceRenamablePat UFieldRowPat where
  sourceRenamePat sibs pat cont = case pat of
    UEmptyRowPat    -> cont sibs UEmptyRowPat
    URemFieldsPat b -> sourceRenamePat sibs b \sibs' b' -> cont sibs' (URemFieldsPat b')
    UDynFieldsPat v p rest -> do
      v' <- sourceRenameE v
      sourceRenamePat sibs p \sibs' p' ->
        sourceRenamePat sibs' rest \sibs'' rest' ->
          cont sibs'' $ UDynFieldsPat v' p' rest'
    UStaticFieldPat l p rest -> do
      sourceRenamePat sibs p \sibs' p' ->
        sourceRenamePat sibs' rest \sibs'' rest' ->
          cont sibs'' $ UStaticFieldPat l p' rest'
    UDynFieldPat    v p rest -> do
      v' <- sourceRenameE v
      sourceRenamePat sibs p \sibs' p' ->
        sourceRenamePat sibs' rest \sibs'' rest' ->
          cont sibs'' $ UDynFieldPat v' p' rest'

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

instance HasSourceNames UDecl where
  sourceNames decl = case decl of
    ULet _ (UPatAnn pat _) _ -> sourceNames pat
    UDataDefDecl _ ~(UBindSource tyConName) dataConNames -> do
      S.singleton tyConName <> sourceNames dataConNames
    UInterface _ _ _ ~(UBindSource className) methodNames -> do
      S.singleton className <> sourceNames methodNames
    UInstance _ _ _ _ instanceName -> sourceNames instanceName

instance HasSourceNames UPat where
  sourceNames (WithSrcB _ pat) = case pat of
    UPatBinder b -> sourceNames b
    UPatCon _ bs -> sourceNames bs
    UPatPair (PairB p1 p2) -> sourceNames p1 <> sourceNames p2
    UPatUnit UnitB -> mempty
    UPatRecord p -> sourceNames p
    UPatVariant _ _ p -> sourceNames p
    UPatVariantLift _ p -> sourceNames p
    UPatTable ps -> sourceNames ps

instance HasSourceNames UFieldRowPat where
  sourceNames = \case
    UEmptyRowPat             -> mempty
    URemFieldsPat b          -> sourceNames b
    UDynFieldsPat   _ p rest -> sourceNames p <> sourceNames rest
    UStaticFieldPat _ p rest -> sourceNames p <> sourceNames rest
    UDynFieldPat    _ p rest -> sourceNames p <> sourceNames rest  -- Shouldn't we include v?

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
