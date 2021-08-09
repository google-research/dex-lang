-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# OPTIONS_GHC -w #-}

module SaferNames.Bridge
  ( TopStateEx (..), JointTopState (..), initTopState
  , toSafe, fromSafe, extendTopStateD
  , HasSafeVersionE (..), HasSafeVersionB (..))  where

import Control.Monad.Identity
import Control.Monad.Reader

import Data.Foldable (toList)
import qualified Data.Set as Set

import LabeledItems
import Syntax
import Env
import Type
import Data.String (fromString)
import Data.Proxy
import Data.Maybe (fromJust)
import Data.Store (Store)
import Data.Text.Prettyprint.Doc
import GHC.Generics (Generic (..))
import GHC.Stack

import Type.Reflection

import qualified Data.Map.Strict as M

import SaferNames.NameCore
import SaferNames.Name
import SaferNames.Syntax
import SaferNames.LazyMap as LM
import SaferNames.PPrint

import Serialize (HasPtrs (..))

import qualified Syntax as D  -- D for Danger
import qualified Type   as D
import qualified Env    as D

import qualified SaferNames.NameCore  as S
import qualified SaferNames.Name      as S
import qualified SaferNames.Syntax    as S

import PPrint

-- Hides the `n` parameter as an existential
data TopStateEx where
  TopStateEx :: JointTopState n -> TopStateEx

initTopState :: TopStateEx
initTopState = TopStateEx $ JointTopState
    D.emptyTopState
    S.emptyTopState
    (ToSafeNameMap mempty)
    emptyEnv

data JointTopState n = JointTopState
  { topStateD   :: D.TopState
  , topStateS   :: S.TopState n
  , topToSafeMap   :: ToSafeNameMap n
  , topFromSafeMap :: FromSafeNameMap n }

extendTopStateD :: JointTopState n -> D.EvaluatedModule -> TopStateEx
extendTopStateD jointTopState evaluated = do
  let D.TopState bindingsD scsD sourceMapD = topStateD jointTopState
  case topStateS jointTopState of
    S.TopState (TopBindings bindingsS) scsS sourceMapS -> do
      -- ensure the internal bindings are fresh wrt top bindings
      let D.EvaluatedModule bindingsD' scsD' sourceMapD' = D.subst (mempty, bindingsD) evaluated
      runToSafeM (topToSafeMap jointTopState) (envAsScope bindingsS) do
        nameBijectionFromDBindings (topFromSafeMap jointTopState) bindingsD'
         \bindingsFrag toSafeMap' fromSafeMap' -> do
           let scopeFrag = envAsScope bindingsFrag
           scsS'       <- toSafeE scsD'
           sourceMapS' <- toSafeE sourceMapD'
           sourceMapSInj <- injectM scopeFrag sourceMapS
           bindingsSInj  <- injectM scopeFrag bindingsS
           scsSInj       <- injectM scopeFrag scsS
           return $ TopStateEx $ JointTopState
             (D.TopState (bindingsD <> bindingsD') (scsD <> scsD') (sourceMapD <> sourceMapD'))
             (S.TopState (TopBindings (bindingsSInj <.> bindingsFrag))
                         (scsSInj <> scsS') (sourceMapSInj <> sourceMapS'))
             toSafeMap'
             fromSafeMap'

-- This is pretty horrible. The name system isn't really designed for creating
-- bijections, so we have to do a lot of things manually.
nameBijectionFromDBindings
    :: MonadToSafe m => FromSafeNameMap n -> D.Bindings
    -> (forall l. Distinct l => TopBindingsFrag n l -> ToSafeNameMap l -> FromSafeNameMap l -> m l a)
    -> m n a
nameBijectionFromDBindings fromSafeMap bindings cont = do
  withFreshSafeRec fromSafeMap (envPairs bindings) \scopeFrag fromSafeMap' -> do
    toSafeMap' <- getToSafeNameMap
    Distinct scope <- getScope
    let bindingsFrag = makeBindingsFrag scope bindings toSafeMap' fromSafeMap' scopeFrag
    cont bindingsFrag toSafeMap' fromSafeMap'

type ConstEnv n l = EnvFrag (ConstE UnitE) n l VoidS

makeBindingsFrag :: forall n l. Distinct l
                 => S.Scope l -> D.Bindings -> ToSafeNameMap l -> FromSafeNameMap l
                 -> ConstEnv n l -> TopBindingsFrag n l
makeBindingsFrag scope bindings toSafeMap fromSafeMap constEnv =
  fmapEnvFrag (\name _ -> getSafeBinding name) constEnv
  where
    getSafeBinding :: S.Name s (n:=>:l) -> TopBinding s l
    getSafeBinding name = do
      let Just name' = getName $ fromUnsafeNameE
            ((emptyNameFunction <>> fromSafeMap) S.! injectNamesR name)
      let binderInfo = bindings D.! name'
      case runToSafeM toSafeMap scope $ toSafeE binderInfo of
        SomeTopBinding binding -> withNameClasses name $ fromJust $ castSName binding

withFreshSafeRec :: MonadToSafe m
                 => FromSafeNameMap n
                 -> [(D.Name, D.AnyBinderInfo)]
                 -> (forall l. Distinct l => ConstEnv n l -> FromSafeNameMap l -> m l a)
                 -> m n a
withFreshSafeRec fromSafeMap [] cont = do
  Distinct _ <- getScope
  cont emptyEnv fromSafeMap
withFreshSafeRec fromSafeMap ((vD,info):rest) cont = do
  withFreshBijectionD vD info \b valD -> do
    frag <- return $ b S.@> ConstE UnitE
    withFreshSafeRec (fromSafeMap <.> (b S.@> UnsafeNameE valD)) rest
      \frag' fromSafeMap' -> do
        cont (frag <.> frag') fromSafeMap'

withFreshBijectionD :: MonadToSafe m => D.Name -> D.AnyBinderInfo
                    -> (forall l s. S.NameBinder s n l -> UnsafeName s -> m l a)
                    -> m n a
withFreshBijectionD name info cont =
  asUnsafeNameFromBinderInfo info name \name' ->
    withFreshM name \b ->
      extendToSafeNameMap name' (binderName b) $
        cont b name'

extendTopStateS :: JointTopState n -> S.EvaluatedModule n -> TopStateEx
extendTopStateS = error "not implemented"

toSafe :: HasSafeVersionE e => JointTopState n -> e -> SafeVersionE e n
toSafe jointTopState e =
  case S.topBindings $ topStateS $ jointTopState of
    TopBindings bindings ->
      runToSafeM (topToSafeMap jointTopState) (envAsScope bindings) $ toSafeE e

fromSafe :: HasSafeVersionE e => JointTopState n -> SafeVersionE e n -> e
fromSafe jointTopState e =
  runFromSafeM (topFromSafeMap jointTopState) bindings $ fromSafeE e
  where bindings = D.topBindings $ topStateD $ jointTopState

-- === monad for translating from unsafe to safe names ===

class ( S.ScopeReader m, S.ScopeExtender m
      , MonadFail1 m, Monad1 m)
      => MonadToSafe (m::MonadKind1) where
  getToSafeNameMap :: m o (ToSafeNameMap o)
  extendToSafeNameMap :: UnsafeName s -> S.Name s o -> m o a -> m o a

data SafeNameHidden (n::S) where SafeNameHidden :: S.Name s n -> SafeNameHidden n
newtype ToSafeNameMap (o::S) = ToSafeNameMap (D.Env (SafeNameHidden o))

newtype ToSafeM o a =
  ToSafeM { runToSafeM' :: ReaderT (ToSafeNameMap o) (ScopeReaderT Identity o) a }
  deriving (Functor, Applicative, Monad)

runToSafeM :: Distinct o => ToSafeNameMap o -> S.Scope o -> ToSafeM o a -> a
runToSafeM nameMap scope m =
  runIdentity $ runScopeReaderT scope $
    flip runReaderT nameMap $
      runToSafeM' m

instance MonadToSafe ToSafeM where
  getToSafeNameMap = ToSafeM ask
  extendToSafeNameMap v v' (ToSafeM m) = ToSafeM $ flip withReaderT m
    \(ToSafeNameMap env) -> ToSafeNameMap $ env <> (v D.@> SafeNameHidden v')

-- === monad for translating from safe to unsafe names ===

class (MonadFail1 m, Monad1 m) => MonadFromSafe (m::MonadKind1) where
  lookupFromSafeNameMap :: S.Name s i -> m i (UnsafeName s)
  getUnsafeBindings :: m i (D.Bindings)
  withFreshUnsafeName :: S.HasNameHint hint
                      => hint -> D.AnyBinderInfo
                      -> (D.Name -> m i a) -> m i a
  extendFromSafeMap :: S.NameBinder s i i'
                    -> UnsafeName s -> m i' a -> m i a

data UnsafeNameE (s::E) (n::S) = UnsafeNameE { fromUnsafeNameE :: UnsafeName s}

type FromSafeNameMap i = S.Env UnsafeNameE i VoidS

newtype FromSafeM i a =
  FromSafeM { runFromSafeM' :: ReaderT (FromSafeNameMap i) (Reader D.Bindings) a }
  deriving (Functor, Applicative, Monad)

runFromSafeM :: FromSafeNameMap i -> D.Bindings -> FromSafeM i a -> a
runFromSafeM nameMap bindings m =
  flip runReader bindings $ flip runReaderT nameMap $ runFromSafeM' m

instance MonadFromSafe FromSafeM where
  lookupFromSafeNameMap v = FromSafeM do
    env <- ask
    return $ fromUnsafeNameE $ ((emptyNameFunction <>> env) S.! v)
  getUnsafeBindings = FromSafeM $ lift ask
  withFreshUnsafeName hint info f =
    FromSafeM $ ReaderT \m -> do
      scope <- ask
      let v' = genFresh (getNameHint hint) scope  -- TODO: preverse name hints
      withReaderT (<> (v' D.@> info)) $
        runReaderT (runFromSafeM' (f v')) m

  extendFromSafeMap b v (FromSafeM m) = FromSafeM $ flip withReaderT m
    \env -> env <.> b S.@> UnsafeNameE v

-- === --- ===

class HasSafeVersionE (e:: *) where
  type SafeVersionE e :: S.E
  toSafeE   :: HasCallStack => MonadToSafe   m => e -> m o (SafeVersionE e o)
  fromSafeE :: MonadFromSafe m => SafeVersionE e i -> m i e

class HasSafeVersionB (b:: *) where
  type SafeVersionB b :: S.B
  toSafeB   :: MonadToSafe   m => b -> (forall o'. SafeVersionB b o o' -> m o' r) -> m o r
  fromSafeB :: MonadFromSafe m => SafeVersionB b i i' -> (b -> m i' r) -> m i r

-- full enumeration of all the `s` parameters we use in safe names
data UnsafeName (s::E) where
  UnsafeAtomName    :: D.Name -> UnsafeName S.AtomNameDef
  UnsafeTyConName   :: D.Name -> UnsafeName S.TyConNameDef
  UnsafeDataConName :: D.Name -> UnsafeName S.DataConNameDef
  UnsafeClassName   :: D.Name -> UnsafeName S.ClassDef
  UnsafeMethodName  :: D.Name -> UnsafeName S.MethodDef
  UnsafeDataDefName :: D.Name -> UnsafeName S.DataDef
  UnsafeSuperclassName  :: D.Name -> UnsafeName S.SuperclassDef

fromUnsafeAtomName :: UnsafeName S.AtomNameDef -> D.Name
fromUnsafeAtomName (UnsafeAtomName v) = v

fromSafeAtomName :: MonadFromSafe m => S.AtomName i -> m i D.Name
fromSafeAtomName v = fromUnsafeAtomName <$> fromSafeE v

toSafeAtomName :: MonadToSafe m => D.Name -> m o (S.AtomName o)
toSafeAtomName v = toSafeE (UnsafeAtomName v)

fromSafeAtomNameVar :: MonadFromSafe m => S.AtomName i -> m i D.Var
fromSafeAtomNameVar name = do
  UnsafeAtomName name' <- fromSafeE name
  AtomBinderInfo ty _ <- (D.! name') <$> getUnsafeBindings
  return $ name' D.:> ty

instance Typeable s => HasSafeVersionE (UnsafeName s) where
  type SafeVersionE (UnsafeName s) = S.Name s
  toSafeE name = do
    let Just name' = getName name
    ToSafeNameMap m <- getToSafeNameMap
    case m D.! name' of
      SafeNameHidden safeName ->
        withNameClasses safeName $
          case castSName safeName of
            Just safeName' -> return safeName'
            Nothing -> error $ "Bad cast: " ++ pprint (name', safeName)
  fromSafeE name = lookupFromSafeNameMap name

castSName :: forall (s1::E) (s2::E) (v::E->E) (n::S).
              HasCallStack => (Typeable s1, Typeable s2) => v s1 n -> Maybe (v s2 n)
castSName name = case typeRep1 `eqTypeRep` typeRep2 of
  Just HRefl -> Just name
  _ -> Nothing -- error $ show typeRep1 ++ "  to  " ++ show typeRep2
  where
    typeRep1 :: TypeRep s1
    typeRep1 = typeRep

    typeRep2 :: TypeRep s2
    typeRep2 = typeRep

instance HasSafeVersionE D.EvaluatedModule where
  type SafeVersionE D.EvaluatedModule = S.EvaluatedModule
  toSafeE (D.EvaluatedModule bindings scs sourceMap) =
    toSafeB (DRecEnvFrag bindings) \(S.RecEnvFrag bindings') ->
      S.EvaluatedModule bindings' <$> toSafeE scs <*> toSafeE sourceMap

  fromSafeE (S.EvaluatedModule bindings scs sourceMap) =
    fromSafeB (S.RecEnvFrag bindings) \(DRecEnvFrag bindings') ->
      D.EvaluatedModule bindings' <$> fromSafeE scs <*> fromSafeE sourceMap

newtype DRecEnvFrag = DRecEnvFrag D.Bindings

asUnsafeNameFromBinderInfo
  :: D.AnyBinderInfo -> D.Name
  -> (forall s. Typeable s => InjectableE s => UnsafeName s -> a )
  -> a
asUnsafeNameFromBinderInfo info name cont = case info of
  AtomBinderInfo _ _ -> cont $ UnsafeAtomName    name
  DataDefName  _     -> cont $ UnsafeDataDefName name
  TyConName    _     -> cont $ UnsafeTyConName   name
  DataConName  _ _   -> cont $ UnsafeDataConName name
  ClassDefName _     -> cont $ UnsafeClassName   name
  MethodName   _ _ _ -> cont $ UnsafeMethodName  name
  SuperclassName _ _ _ -> cont $ UnsafeSuperclassName name

asUnsafeNameFromTopBinding :: TopBinding s n -> D.Name -> UnsafeName s
asUnsafeNameFromTopBinding (TopBinding val) name =
  let tyRep = repFromEVal val
  in case tyRep `eqTypeRep` (typeRep :: TypeRep S.AtomNameDef) of
    Just HRefl -> UnsafeAtomName name
    Nothing -> case tyRep `eqTypeRep` (typeRep :: TypeRep S.TyConNameDef) of
     Just HRefl -> UnsafeTyConName name
     Nothing -> case tyRep `eqTypeRep` (typeRep :: TypeRep S.DataConNameDef) of
      Just HRefl -> UnsafeDataConName name
      Nothing -> case tyRep `eqTypeRep` (typeRep :: TypeRep S.ClassDef) of
       Just HRefl -> UnsafeClassName name
       Nothing -> case tyRep `eqTypeRep` (typeRep :: TypeRep S.MethodDef) of
        Just HRefl -> UnsafeMethodName name
        Nothing -> case tyRep `eqTypeRep` (typeRep :: TypeRep S.DataDef) of
         Just HRefl -> UnsafeDataDefName name
         Nothing -> case tyRep `eqTypeRep` (typeRep :: TypeRep S.SuperclassDef) of
          Just HRefl -> UnsafeSuperclassName name

instance HasSafeVersionB DRecEnvFrag where
  type SafeVersionB DRecEnvFrag = RecEnvFrag S.TopBinding
  toSafeB (DRecEnvFrag env) cont =
    renameBinders (envPairs env) \nest -> do
      nest' <- forEachNestItem nest \(TempPair b info) -> do
        SomeTopBinding info' <- toSafeE info
        return $ EnvPair b $ fromJust $ castSName info'
      cont $ RecEnvFrag $ fromEnvPairs nest'
    where
      renameBinders
        :: MonadToSafe m
         => [(D.Name, D.AnyBinderInfo)]
         -> (forall o'. S.Nest TempPair o o' -> m o' r)
         -> m o r
      renameBinders [] cont = cont S.Empty
      renameBinders ((b,info):rest) cont = do
        renameBindersEnvPair b info \pair ->
          renameBinders rest \rest' ->
            cont $ S.Nest pair rest'

      renameBindersEnvPair
        :: MonadToSafe m
        => D.Name -> AnyBinderInfo
        -> (forall o'. TempPair o o' -> m o' r)
        -> m o r
      renameBindersEnvPair name info cont =
        asUnsafeNameFromBinderInfo info name \name' ->
          withFreshM name \b ->
            extendToSafeNameMap name' (binderName b) $
              cont $ TempPair b info

  fromSafeB (RecEnvFrag env) cont = do
    renameBinders (S.toEnvPairs env) \pairs -> do
      (newNames, vals) <- unzip <$> forM pairs \(DEnvPair v binding) -> do
        info <- fromSafeE $ SomeTopBinding binding
        let Just name = getName v
        return (name, info)
      cont $ DRecEnvFrag $ D.newEnv newNames vals

    where
      renameBinders
        :: MonadFromSafe m
        => S.Nest (EnvPair TopBinding i') i i'
        -> ([DEnvPair i'] -> m i' r)
        -> m i r
      renameBinders S.Empty cont = cont []
      renameBinders (S.Nest (EnvPair b binderInfo) rest) cont =
        withFreshUnsafeName b TrulyUnknownBinder \v -> do
          let v' = asUnsafeNameFromTopBinding binderInfo v
          withNameClasses (S.binderName b) $
            extendFromSafeMap b v' $ do
              renameBinders rest \rest' -> do
                cont $ (DEnvPair v' binderInfo) : rest'

data DEnvPair n where
  DEnvPair :: Typeable s => UnsafeName s -> TopBinding s n -> DEnvPair n

data SomeTopBinding (n::S) where
  SomeTopBinding :: Typeable s => TopBinding s n -> SomeTopBinding n

instance HasSafeVersionE AnyBinderInfo where
  type SafeVersionE AnyBinderInfo = SomeTopBinding
  toSafeE anyInfo = case anyInfo of
    AtomBinderInfo ty info ->
      SomeTopBinding <$> (TopBinding <$> (S.AtomNameDef <$> toSafeE ty <*> toSafeE info))
    DataDefName def ->
      SomeTopBinding <$> (TopBinding <$> toSafeE def)
    TyConName def ->
      SomeTopBinding <$> (TopBinding <$> (S.TyConNameDef <$> toSafeE (UnsafeDataDefName def)))
    DataConName def idx ->
      SomeTopBinding <$> (TopBinding <$> (S.DataConNameDef <$> toSafeE (UnsafeDataDefName def) <*> pure idx))
    ClassDefName (D.ClassDef def@(_, D.DataDef className _ _ ) methodNames) ->
      SomeTopBinding <$> (TopBinding <$>
        (S.ClassDef className methodNames <$> toSafeNamedDataDef def))
    MethodName def idx val ->
      SomeTopBinding <$> (TopBinding <$>
        (S.MethodDef <$> toSafeE (UnsafeClassName def) <*> pure idx <*> toSafeE val))
    SuperclassName def idx val ->
      SomeTopBinding <$> (TopBinding <$>
        (S.SuperclassDef <$> toSafeE (UnsafeClassName def) <*> pure idx <*> toSafeE val))
    _ -> error $ "Not recognized: " ++ pprint anyInfo
  fromSafeE (SomeTopBinding info) = topBindingToAnyBinderInfo info

topBindingToAnyBinderInfo :: MonadFromSafe m => TopBinding s n -> m n D.AnyBinderInfo
topBindingToAnyBinderInfo (TopBinding val) = do
  let tyRep = repFromEVal val
  case tyRep `eqTypeRep` (typeRep :: TypeRep S.AtomNameDef) of
    Just HRefl -> AtomBinderInfo <$> fromSafeE ty <*> fromSafeE info
      where AtomNameDef ty info = val
    Nothing -> case tyRep `eqTypeRep` (typeRep :: TypeRep S.TyConNameDef) of
     Just HRefl -> TyConName <$> ((\(UnsafeDataDefName v)->v) <$> fromSafeE dataDefName)
       where TyConNameDef dataDefName = val
     Nothing -> case tyRep `eqTypeRep` (typeRep :: TypeRep S.DataConNameDef) of
      Just HRefl -> DataConName <$> ((\(UnsafeDataDefName v)->v) <$> fromSafeE dataDefName) <*> pure idx
        where DataConNameDef dataDefName idx = val
      Nothing -> case tyRep `eqTypeRep` (typeRep :: TypeRep S.ClassDef) of
       Just HRefl -> ClassDefName <$> fromSafeE val
       Nothing -> case tyRep `eqTypeRep` (typeRep :: TypeRep S.MethodDef) of
        Just HRefl -> MethodName <$> ((\(UnsafeClassName v)->v) <$> fromSafeE methodName)
                        <*> pure idx <*> fromSafeE methodGetter
          where MethodDef methodName idx methodGetter = val
        Nothing -> case tyRep `eqTypeRep` (typeRep :: TypeRep S.DataDef) of
         Just HRefl -> D.DataDefName <$> fromSafeE val
         Nothing -> case tyRep `eqTypeRep` (typeRep :: TypeRep S.SuperclassDef) of
          Just HRefl -> SuperclassName <$> ((\(UnsafeClassName v)->v) <$> fromSafeE superclassName)
                          <*> pure idx <*> fromSafeE getter
            where SuperclassDef superclassName idx getter = val

repFromEVal :: forall (e::E) (n::S). Typeable e => e n -> TypeRep e
repFromEVal _ = typeRep

-- used to hold a partially-to-safed env pair. The challenge is that we have to
-- do two passes when we process recursive bindings, but we can't split up the
-- `s` parameter for the binder from the corresponding `s` parameter for the
-- payload. This GADT hides `s` existentially but ensures that the bindings and
-- the not-yet-fully-evaluated payload are the same.
data TempPair (n::S) (l::S) where
  TempPair :: Typeable s => NameBinder s n l -> AnyBinderInfo -> TempPair n l

instance HasSafeVersionE D.Module where
  type SafeVersionE D.Module = S.Module
  toSafeE (D.Module ir decls evaluated) =
    toSafeB decls \decls' -> do
      evaluated' <- toSafeE evaluated
      return $ S.Module ir decls' evaluated'
  fromSafeE (S.Module ir decls evaluated) =
    fromSafeB decls \decls' -> do
      evaluated' <- fromSafeE evaluated
      return $ D.Module ir decls' evaluated'

instance HasSafeVersionE D.SourceMap where
  type SafeVersionE D.SourceMap = S.SourceMap
  toSafeE   (D.SourceMap m) = S.SourceMap <$> mapM toSafeE   m
  fromSafeE (S.SourceMap m) = D.SourceMap <$> mapM fromSafeE m

instance HasSafeVersionE D.SourceNameDef where
  type SafeVersionE (D.SourceNameDef) = S.SourceNameDef
  toSafeE name = case name of
    D.SrcAtomName    v -> S.SrcAtomName    <$> toSafeE (UnsafeAtomName    v)
    D.SrcTyConName   v -> S.SrcTyConName   <$> toSafeE (UnsafeTyConName   v)
    D.SrcDataConName v -> S.SrcDataConName <$> toSafeE (UnsafeDataConName v)
    D.SrcClassName   v -> S.SrcClassName   <$> toSafeE (UnsafeClassName   v)
    D.SrcMethodName  v -> S.SrcMethodName  <$> toSafeE (UnsafeMethodName  v)

  fromSafeE name = case name of
    S.SrcAtomName    v -> D.SrcAtomName    <$> ((\(UnsafeAtomName    v')->v') <$> fromSafeE v)
    S.SrcTyConName   v -> D.SrcTyConName   <$> ((\(UnsafeTyConName   v')->v') <$> fromSafeE v)
    S.SrcDataConName v -> D.SrcDataConName <$> ((\(UnsafeDataConName v')->v') <$> fromSafeE v)
    S.SrcClassName   v -> D.SrcClassName   <$> ((\(UnsafeClassName   v')->v') <$> fromSafeE v)
    S.SrcMethodName  v -> D.SrcMethodName  <$> ((\(UnsafeMethodName  v')->v') <$> fromSafeE v)

instance HasSafeVersionE D.SynthCandidates where
  type SafeVersionE D.SynthCandidates = S.SynthCandidates
  toSafeE (D.SynthCandidates xs ys zs) =
    S.SynthCandidates <$> mapM toSafeE xs <*> mapM toSafeE ys <*> mapM toSafeE zs
  fromSafeE (S.SynthCandidates xs ys zs) =
    D.SynthCandidates <$> mapM fromSafeE xs <*> mapM fromSafeE ys <*> mapM fromSafeE zs

instance HasSafeVersionE D.Atom where
  type SafeVersionE D.Atom = S.Atom

  toSafeE atom = case atom of
    D.Var (v D.:> _) -> S.Var <$> toSafeAtomName v
    D.Lam (D.Abs b (arr, body)) -> do
      toSafeB b \b' -> do
        (arr', eff') <- toSafeArrow arr
        body' <- toSafeE body
        return $ S.Lam $ S.LamExpr arr' b' eff' body'
    D.Pi (D.Abs b (arr, body)) ->
      toSafeB b \b' -> do
        (arr', eff') <- toSafeArrow arr
        body' <- toSafeE body
        return $ S.Pi $ S.PiType arr' b' eff' body'
    D.DataCon def@(_, D.DataDef printName _ _) params con args ->
      S.DataCon printName <$>
        toSafeNamedDataDef def <*>
        mapM toSafeE params <*> pure con <*> mapM toSafeE args
    D.TypeCon def params ->
      S.TypeCon <$> toSafeNamedDataDef def <*> mapM toSafeE params
    D.LabeledRow (Ext items t) ->
      S.LabeledRow <$> (Ext <$> mapM toSafeE items <*> mapM toSafeAtomName t)
    D.Record items -> S.Record <$> mapM toSafeE items
    D.RecordTy (Ext items t) -> S.RecordTy <$>
       (Ext <$> mapM toSafeE items <*> mapM toSafeAtomName t)
    D.Variant (Ext items t) label idx val -> S.Variant <$>
      (Ext <$> mapM toSafeE items <*> mapM toSafeAtomName t) <*>
      pure label <*> pure idx <*> toSafeE val
    D.VariantTy (Ext items t) -> S.VariantTy <$>
      (Ext <$> mapM toSafeE items <*> mapM toSafeAtomName t)
    D.Con con  -> S.Con <$> mapM toSafeE con
    D.TC  tc   -> S.TC  <$> mapM toSafeE tc
    D.Eff effs -> S.Eff <$> toSafeE effs
    D.ACase scrut alts ty -> S.ACase <$> toSafeE scrut <*> mapM toSafeE alts <*> toSafeE ty
    D.DataConRef def params args ->
      S.DataConRef <$> toSafeNamedDataDef def <*>
        mapM toSafeE params <*> toSafeE (D.Abs args ())
    D.BoxedRef b ptr size body ->
      S.BoxedRef <$> toSafeE ptr <*> toSafeE size <*> toSafeE (D.Abs b body)
    D.ProjectElt idxs (v D.:> _) -> S.ProjectElt idxs <$> toSafeAtomName v

  fromSafeE atom = case atom of
    S.Var v -> D.Var <$> fromSafeAtomNameVar v
    S.Lam (S.LamExpr arr b eff body) -> do
      fromSafeB b \b' -> do
        arr' <- fromSafeArrow arr eff
        body' <- fromSafeE body
        return $ D.Lam $ D.Abs b' (arr', body')
    S.Pi (S.PiType arr b eff body) -> do
      fromSafeB b \b' -> do
        arr' <- fromSafeArrow arr eff
        body' <- fromSafeE body
        return $ D.Pi $ D.Abs b' (arr', body')
    S.DataCon _ def params con args -> do
      D.DataCon <$> fromSafeNamedDataDef def <*> mapM fromSafeE params <*> pure con <*> mapM fromSafeE args
    S.TypeCon def params ->
      D.TypeCon <$> fromSafeNamedDataDef def <*> mapM fromSafeE params
    S.LabeledRow (Ext items t) -> D.LabeledRow <$>
      (Ext <$> mapM fromSafeE items <*> mapM fromSafeAtomName t)
    S.Record items -> D.Record <$> mapM fromSafeE items
    S.RecordTy (Ext items t) -> D.RecordTy <$>
      (Ext <$> mapM fromSafeE items <*> mapM fromSafeAtomName t)
    S.Variant (Ext items t) label idx val -> D.Variant <$>
      (Ext <$> mapM fromSafeE items <*> mapM fromSafeAtomName t) <*>
      pure label <*> pure idx <*> fromSafeE val
    S.VariantTy (Ext items t) -> D.VariantTy <$>
      (Ext <$> mapM fromSafeE items <*> mapM fromSafeAtomName t)
    S.Con con  -> D.Con <$> mapM fromSafeE con
    S.TC  tc   -> D.TC  <$> mapM fromSafeE tc
    S.Eff effs -> D.Eff <$> fromSafeE effs
    S.ACase scrut alts ty -> D.ACase <$> fromSafeE scrut <*> mapM fromSafeE alts <*> fromSafeE ty
    S.DataConRef def params ab -> do
      def' <- fromSafeNamedDataDef def
      params' <- mapM fromSafeE params
      D.Abs bs () <- fromSafeE ab
      return $ D.DataConRef def' params' bs
    S.BoxedRef ptr size ab -> do
      ptr' <- fromSafeE ptr
      size' <- fromSafeE size
      D.Abs b body <- fromSafeE ab
      return $ D.BoxedRef b ptr' size' body
    S.ProjectElt idxs v -> D.ProjectElt idxs <$> fromSafeAtomNameVar v

instance HasSafeVersionB D.Binder where
  type SafeVersionB D.Binder = S.Binder

  toSafeB (Ignore ty) cont = do
    ty' <- toSafeE ty
    withFreshM IgnoreHint \b' -> do
      cont (b' S.:> ty')
  toSafeB (Bind (b D.:> ty)) cont = do
    ty' <- toSafeE ty
    withFreshM b \b' -> do
      extendToSafeNameMap (UnsafeAtomName b) (S.binderName b') $
        cont (b' S.:> ty')

  fromSafeB (b S.:> ty) cont = do
    ty' <- fromSafeE ty
    withFreshUnsafeName b (AtomBinderInfo ty' UnknownBinder) \v' ->
      extendFromSafeMap b (UnsafeAtomName v') $
        cont (Bind (v' D.:> ty'))

instance HasSafeVersionE D.DataDef where
  type SafeVersionE D.DataDef = S.DataDef
  toSafeE (D.DataDef sourceName paramBs dataCons) = do
    toSafeB paramBs \paramBs' -> do
      dataCons' <- mapM toSafeE dataCons
      return $ S.DataDef sourceName paramBs' dataCons'
  fromSafeE (S.DataDef sourceName paramBs dataCons) = do
    fromSafeB paramBs \paramBs' -> do
      dataCons' <- mapM fromSafeE dataCons
      return $ D.DataDef sourceName paramBs' dataCons'

instance HasSafeVersionE D.DataConDef where
  type SafeVersionE D.DataConDef = S.DataConDef
  toSafeE (D.DataConDef sourceName bs) =
    toSafeB bs \bs' -> return $ S.DataConDef sourceName (S.Abs bs' UnitE)
  fromSafeE (S.DataConDef sourceName (S.Abs bs UnitE)) =
    fromSafeB bs \bs' -> return $ D.DataConDef sourceName bs'

data DMethodDef = DMethodDef ClassDefName Int D.Atom
instance HasSafeVersionE DMethodDef where
  type SafeVersionE DMethodDef = S.MethodDef
  toSafeE (DMethodDef name idx val) =
    S.MethodDef <$> toSafeE (UnsafeClassName name) <*> pure idx <*> toSafeE val
  fromSafeE (S.MethodDef name idx val) =
    DMethodDef <$> ((\(UnsafeClassName name)->name) <$> fromSafeE name)
      <*> pure idx <*> fromSafeE val

instance HasSafeVersionE D.ClassDef where
  type SafeVersionE D.ClassDef = S.ClassDef
  toSafeE (D.ClassDef def@(_, D.DataDef sourceName _ _) methodNames) =
    S.ClassDef sourceName methodNames <$> toSafeNamedDataDef def
  fromSafeE (S.ClassDef _ methodNames def) =
    D.ClassDef <$> fromSafeNamedDataDef def <*> pure methodNames

toSafeNamedDataDef :: MonadToSafe m => D.NamedDataDef -> m o (S.NamedDataDef o)
toSafeNamedDataDef (name, def) =
  (,) <$> toSafeE (UnsafeDataDefName name) <*> toSafeE def

fromSafeNamedDataDef :: MonadFromSafe m => S.NamedDataDef i -> m i D.NamedDataDef
fromSafeNamedDataDef (name, def) = do
  UnsafeDataDefName name' <- lookupFromSafeNameMap name
  def' <- fromSafeE def
  return (name', def')

toSafeArrow :: MonadToSafe m => D.Arrow -> m o (S.Arrow, S.EffectRow o)
toSafeArrow arr = case arr of
  D.PlainArrow eff -> do
    eff' <- toSafeE eff
    return $ (S.PlainArrow, eff')
  D.TabArrow      -> return (S.TabArrow, S.Pure)
  D.LinArrow      -> return (S.LinArrow, S.Pure)
  D.ImplicitArrow -> return (S.ImplicitArrow, S.Pure)
  D.ClassArrow    -> return (S.ClassArrow, S.Pure)

fromSafeArrow :: MonadFromSafe m => S.Arrow -> S.EffectRow i -> m i D.Arrow
fromSafeArrow arr eff = case arr of
  S.PlainArrow -> do
    eff' <- fromSafeE eff
    return $ D.PlainArrow eff'
  S.TabArrow      -> return D.TabArrow
  S.LinArrow      -> return D.LinArrow
  S.ImplicitArrow -> return D.ImplicitArrow
  S.ClassArrow    -> return D.ClassArrow

instance HasSafeVersionE () where
  type SafeVersionE () = S.UnitE
  toSafeE () = return UnitE
  fromSafeE UnitE = return ()

instance HasSafeVersionB D.DataConRefBinding where
  type SafeVersionB D.DataConRefBinding = S.DataConRefBinding
  toSafeB (D.DataConRefBinding b ann) cont = do
    ann' <- toSafeE ann
    toSafeB b \b' -> cont $ S.DataConRefBinding b' ann'
  fromSafeB (S.DataConRefBinding b ann) cont = do
    ann' <- fromSafeE ann
    fromSafeB b \b' -> cont $ D.DataConRefBinding b' ann'

instance HasSafeVersionE D.Expr where
  type SafeVersionE D.Expr = S.Expr
  toSafeE expr = case expr of
    D.App f x -> S.App  <$> toSafeE f <*> toSafeE x
    D.Case scrut alts ty -> S.Case <$> toSafeE scrut <*> mapM toSafeE alts <*>  toSafeE ty
    D.Atom x  -> S.Atom <$> toSafeE x
    D.Op op   -> S.Op   <$> mapM toSafeE op
    D.Hof hof -> S.Hof  <$> mapM toSafeE hof

  fromSafeE expr = case expr of
    S.App f x -> D.App  <$> fromSafeE f <*> fromSafeE x
    S.Case scrut alts ty -> D.Case <$> fromSafeE scrut <*>  mapM fromSafeE alts <*>  fromSafeE ty
    S.Atom x  -> D.Atom <$> fromSafeE x
    S.Op op   -> D.Op   <$> mapM fromSafeE op
    S.Hof hof -> D.Hof  <$> mapM fromSafeE hof

instance HasSafeVersionE D.Block where
  type SafeVersionE D.Block = S.Block
  toSafeE (D.Block decls result) = do
    S.Abs decls' result' <- toSafeE $ D.Abs decls result
    ty <- toSafeE $ D.getType result
    return $ S.Block ty decls' result'
  fromSafeE (S.Block _ decls result) = do
    D.Abs decls' result' <- fromSafeE $ S.Abs decls result
    return $ D.Block decls' result'

instance HasSafeVersionB D.Decl where
  type SafeVersionB D.Decl = S.Decl
  toSafeB (D.Let ann b expr) cont = do
    expr' <- toSafeE expr
    toSafeB b \b' ->
      cont $ S.Let ann b' expr'

  fromSafeB (S.Let ann b expr) cont = do
    expr' <- fromSafeE expr
    fromSafeB b \b' -> do
      cont $ D.Let ann b' expr'

data AnnBinderP (ann::E) (n::S) (l::S) =
  AnnBinderP (S.NameBinder S.AtomNameDef n l) (ann n)

instance HasSafeVersionE D.Effect where
  type SafeVersionE D.Effect = S.Effect
  toSafeE eff = case eff of
    D.RWSEffect rws h -> S.RWSEffect rws <$> toSafeE (UnsafeAtomName h)
    D.ExceptionEffect -> return S.ExceptionEffect
    D.IOEffect        -> return S.IOEffect
  fromSafeE eff = case eff of
    S.RWSEffect rws h -> D.RWSEffect rws <$> ((fromUnsafeAtomName <$>) . fromSafeE) h
    S.ExceptionEffect -> return D.ExceptionEffect
    S.IOEffect        -> return D.IOEffect

instance HasSafeVersionE D.EffectRow where
  type SafeVersionE D.EffectRow = S.EffectRow
  toSafeE   (D.EffectRow effs v) =
    S.EffectRow <$> traverseSet toSafeE   effs <*> mapM (toSafeE . UnsafeAtomName) v
  fromSafeE (S.EffectRow effs v) =
    D.EffectRow <$> traverseSet fromSafeE effs <*> mapM ((fromUnsafeAtomName <$>) . fromSafeE) v

instance (HasSafeVersionB b, HasSafeVersionE e) => HasSafeVersionE (D.Abs b e) where
  type SafeVersionE (D.Abs b e) = S.Abs (SafeVersionB b) (SafeVersionE e)
  toSafeE   (D.Abs b e) = toSafeB   b \b' -> S.Abs b' <$> toSafeE e
  fromSafeE (S.Abs b e) = fromSafeB b \b' -> D.Abs b' <$> fromSafeE e

instance HasSafeVersionB b => HasSafeVersionB (D.Nest b) where
  type SafeVersionB (D.Nest b) = S.Nest (SafeVersionB b)
  toSafeB nest cont = case nest of
    D.Empty -> cont S.Empty
    D.Nest b rest ->
      toSafeB b \b' ->
        toSafeB rest \rest' ->
           cont $ S.Nest b' rest'

  fromSafeB nest cont = case nest of
    S.Empty -> cont D.Empty
    S.Nest b rest ->
      fromSafeB b \b' ->
        fromSafeB rest \rest' ->
           cont $ D.Nest b' rest'

instance HasSafeVersionE BinderInfo where
  type SafeVersionE BinderInfo = AtomBinderInfo
  toSafeE = undefined
  fromSafeE = undefined

traverseSet :: (Ord a, Ord b, Monad m) => (a -> m b) -> Set.Set a -> m (Set.Set b)
traverseSet f s = Set.fromList <$> mapM f (Set.toList s)

-- === boilerplate instances ===

instance Store TopStateEx

-- TODO!
instance Generic TopStateEx where
  type Rep TopStateEx = Rep ()
  to = undefined
  from = undefined

instance HasPtrs TopStateEx where
  -- TODO: rather than implementing HasPtrs for safer names, let's just switch
  --       to using names for pointers.
  traversePtrs _ s = pure s

instance ScopeReader ToSafeM where
  getScope = ToSafeM $ ReaderT \_ -> getScope

instance ScopeExtender ToSafeM where
  extendScope frag (ToSafeM (ReaderT f)) =
    ToSafeM $ ReaderT \env ->
      extendScope frag do
        env' <- injectM frag env
        f env'

instance MonadFail (ToSafeM o) where
  fail s = error s

instance MonadFail (FromSafeM i) where
  fail s = error s

instance InjectableE ToSafeNameMap

instance InjectableE S.SynthCandidates
instance InjectableE S.SourceMap

instance D.HasName (UnsafeName s) where
  getName (UnsafeAtomName       v) = Just v
  getName (UnsafeTyConName      v) = Just v
  getName (UnsafeDataConName    v) = Just v
  getName (UnsafeClassName      v) = Just v
  getName (UnsafeMethodName     v) = Just v
  getName (UnsafeDataDefName    v) = Just v
  getName (UnsafeSuperclassName v) = Just v

instance Pretty (UnsafeNameE s n) where
  pretty (UnsafeNameE name) = pretty name

instance Pretty (UnsafeName n) where
  pretty name = case name of
    UnsafeAtomName       v -> pretty v <+> "(atom name)"
    UnsafeTyConName      v -> pretty v <+> "(ty con name)"
    UnsafeDataConName    v -> pretty v <+> "(data con name)"
    UnsafeClassName      v -> pretty v <+> "(class name name)"
    UnsafeMethodName     v -> pretty v <+> "(method name)"
    UnsafeDataDefName    v -> pretty v <+> "(data def name)"
    UnsafeSuperclassName v -> pretty v <+> "(superclas name)"

instance Pretty (SafeNameHidden n) where
  pretty (SafeNameHidden name) = pretty name

instance Pretty (ToSafeNameMap n) where
  pretty (ToSafeNameMap env) = pretty env

instance Pretty (JointTopState n) where
  pretty s =
    "topState (unsafe):"   <> nest 2 (hardline <> pretty (topStateD s))      <> hardline <>
    "topState (safe):"     <> nest 2 (hardline <> pretty (topStateS s))      <> hardline <>
    "unsafe-to-safe map:"  <> nest 2 (hardline <> pretty (topToSafeMap   s)) <> hardline <>
    "safe-to-unsafe map:"  <> nest 2 (hardline <> pretty (topFromSafeMap s)) <> hardline
