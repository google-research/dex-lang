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
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DeriveGeneric #-}
{-# OPTIONS_GHC -w #-}

module SaferNames.Bridge
  ( TopStateEx (..), JointTopState (..), emptyTopStateEx
  , toSafe, fromSafe, extendTopStateD
  , HasSafeVersionE (..), HasSafeVersionB (..))  where

import Control.Monad.Identity
import Control.Monad.Reader

import Data.Foldable (toList)
import qualified Data.Set as Set

import LabeledItems
import Syntax
import Subst
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

import SaferNames.Name
import SaferNames.Syntax
import SaferNames.LazyMap as LM
import SaferNames.PPrint

import Serialize (HasPtrs (..))

import qualified Syntax as D  -- D for Danger
import qualified Type   as D
import qualified Subst    as D

import qualified SaferNames.Name      as S
import qualified SaferNames.Syntax    as S

import PPrint

-- Hides the `n` parameter as an existential
data TopStateEx where
  TopStateEx :: Distinct n => JointTopState n -> TopStateEx

data JointTopState n = JointTopState
  { topStateD   :: D.TopState
  , topStateS   :: S.Bindings n
  , topToSafeMap   :: ToSafeSubst n
  , topFromSafeMap :: FromSafeSubst n }

emptyTopStateEx :: TopStateEx
emptyTopStateEx = TopStateEx $ JointTopState
    D.emptyTopState
    S.emptyOutMap
    (ToSafeSubst mempty)
    (FromSafeSubst emptyInMap)

extendTopStateD :: Distinct n => JointTopState n -> D.EvaluatedModule -> TopStateEx
extendTopStateD jointTopState evaluated = do
  let D.TopState bindingsD scsD sourceMapD = topStateD jointTopState
  case topStateS jointTopState of
    -- We ignore the effects because there are none at the top level
    S.Bindings bindingsS scsS sourceMapS _ -> do
      -- ensure the internal bindings are fresh wrt top bindings
      let D.EvaluatedModule bindingsD' scsD' sourceMapD' = D.subst (mempty, bindingsD) evaluated
      runToSafeM (topToSafeMap jointTopState) (toScope bindingsS) do
        nameBijectionFromDBindings (topFromSafeMap jointTopState) bindingsD'
         \(BindingsFrag bindingsFrag _) toSafeMap' fromSafeMap' -> do
           withExtEvidence (toExtEvidence bindingsFrag) do
             scsS'         <- toSafeE scsD'
             sourceMapS'   <- toSafeE sourceMapD'
             sourceMapSInj <- sinkM sourceMapS
             scsSInj       <- sinkM scsS
             return $ TopStateEx $ JointTopState
               (D.TopState (bindingsD <> bindingsD')
                           (scsD <> scsD')
                           (sourceMapD <> sourceMapD'))
               (S.Bindings (bindingsS `extendOutMap` bindingsFrag)
                           (scsSInj <> scsS')
                           (sourceMapSInj <> sourceMapS')
                           S.Pure)
               toSafeMap'
               fromSafeMap'

instance Pretty (JointTopState n) where
  pretty s =
    "topState (unsafe):"   <> nest 2 (hardline <> pretty (topStateD s))      <> hardline <>
    "topState (safe):"     <> nest 2 (hardline <> pretty (topStateS s))      <> hardline <>
    "unsafe-to-safe map:"  <> nest 2 (hardline <> pretty (topToSafeMap   s)) <> hardline <>
    "safe-to-unsafe map:"  <> nest 2 (hardline <> pretty (topFromSafeMap s)) <> hardline

instance GenericE JointTopState where
  type RepE JointTopState = LiftE D.TopState `PairE`
                            S.Bindings       `PairE`
                            ToSafeSubst        `PairE`
                            FromSafeSubst
  fromE (JointTopState stateD stateS toSafeMap fromSafeMap) =
    (LiftE stateD `PairE` stateS `PairE` toSafeMap `PairE` fromSafeMap)
  toE (LiftE stateD `PairE` stateS `PairE` toSafeMap `PairE` fromSafeMap) =
    JointTopState stateD stateS toSafeMap fromSafeMap

toSafe :: (Distinct n, HasSafeVersionE e)
       => JointTopState n -> e -> SafeVersionE e n
toSafe jointTopState e =
  let scope = toScope $ S.getNameBindings $ topStateS $ jointTopState
  in runToSafeM (topToSafeMap jointTopState) scope $ toSafeE e

fromSafe :: HasSafeVersionE e => JointTopState n -> SafeVersionE e n -> e
fromSafe jointTopState e =
  runFromSafeM (topFromSafeMap jointTopState) bindings $ fromSafeE e
  where bindings = D.topBindings $ topStateD $ jointTopState

-- This is pretty horrible. The name system isn't really designed for creating
-- bijections, so we have to do a lot of things manually.
nameBijectionFromDBindings
    :: MonadToSafe m => FromSafeSubst n -> D.Bindings
    -> (forall l. Distinct l => BindingsFrag n l -> ToSafeSubst l -> FromSafeEnv l -> m l a)
    -> m n a
nameBijectionFromDBindings fromSafeMap bindings cont = do
  withFreshSafeRec fromSafeMap (envPairs bindings) \scopeFrag fromSafeMap' -> do
    toSafeMap' <- getToSafeSubst
    Distinct <- getDistinct
    Immut <- getImmut
    scope <- getScope
    let bindingsFrag = makeBindingsFrag scope bindings toSafeMap' fromSafeMap' scopeFrag
    cont bindingsFrag toSafeMap' fromSafeMap'

type ConstSubst n l = EnvFrag (ConstE UnitE) n l VoidS

makeBindingsFrag :: forall n l. Distinct l
                 => S.Scope l -> D.Bindings -> ToSafeSubst l -> FromSafeEnv l
                 -> ConstSubst n l -> BindingsFrag n l
makeBindingsFrag scope bindings toSafeMap (FromSafeSubst fromSafeMap) constEnv =
  BindingsFrag (RecSubstFrag $ fmapEnvFrag (\name _ -> getSafeBinding name) constEnv) Nothing
  where
    getSafeBinding :: S.Name c (n:=>:l) -> Binding c l
    getSafeBinding name = do
      let Just name' = getName $ fromUnsafeNameE
                         (lookupMaterializedSubst fromSafeMap (sinkR name))
      let binderInfo = bindings D.! name'
      case runToSafeM toSafeMap scope $ toSafeE binderInfo of
        WithColor rep binding ->
          case eqNameColorRep rep (getNameColor name) of
            Just ColorsEqual -> binding

withFreshSafeRec :: MonadToSafe m
                 => FromSafeSubst n
                 -> [(D.Name, D.AnyBinderInfo)]
                 -> (forall l. Distinct l => ConstSubst n l -> FromSafeEnv l -> m l a)
                 -> m n a
withFreshSafeRec fromSafeMap [] cont = do
  Distinct <- getDistinct
  cont emptyInFrag fromSafeMap
withFreshSafeRec (FromSafeSubst fromSafeMap) ((vD,info):rest) cont = do
  withFreshBijectionD vD info \b valD -> do
    frag <- return $ b S.@> ConstE UnitE
    withFreshSafeRec (FromSafeSubst $ fromSafeMap <>> (b S.@> UnsafeNameE valD)) rest
      \frag' fromSafeMap' -> do
        cont (frag <.> frag') fromSafeMap'

withFreshBijectionD :: MonadToSafe m => D.Name -> D.AnyBinderInfo
                    -> (forall l c. S.NameBinder c n l -> UnsafeName c -> m l a)
                    -> m n a
withFreshBijectionD name info cont =
  asUnsafeNameFromBinderInfo info name \name'@(UnsafeName rep _) -> do
    Immut <- getImmut
    withFreshM (getNameHint name) rep \b ->
      extendToSafeSubst name' (binderName b) $
        cont b name'

extendTopStateS :: JointTopState n -> S.EvaluatedModule n -> TopStateEx
extendTopStateS = error "not implemented"

-- === monad for translating from unsafe to safe names ===

class ( S.ScopeReader m, S.ScopeExtender m, S.AlwaysImmut m
      , MonadFail1 m, Monad1 m)
      => MonadToSafe (m::MonadKind1) where
  getToSafeSubst :: m o (ToSafeEnv o)
  extendToSafeSubst :: UnsafeName c -> S.Name c o -> m o a -> m o a

newtype ToSafeSubst (o::S) = ToSafeEnv (D.Env (WithColor S.Name o))
  deriving (Show, Pretty, Generic)

newtype ToSafeM o a =
  ToSafeM { runToSafeM' :: ReaderT (ToSafeSubst o) (ScopeReaderT Identity o) a }
  deriving (Functor, Applicative, Monad)

runToSafeM :: Distinct o => ToSafeSubst o -> S.Scope o -> ToSafeM o a -> a
runToSafeM nameMap scope m =
  runIdentity $ runScopeReaderT scope $
    flip runReaderT nameMap $
      runToSafeM' m

instance MonadToSafe ToSafeM where
  getToSafeSubst = ToSafeM ask
  extendToSafeSubst (UnsafeName rep v) v' (ToSafeM m) = ToSafeM $ flip withReaderT m
    \(ToSafeSubst env) -> ToSafeEnv $ env <> (v D.@> WithColor rep v')

instance AlwaysImmut ToSafeM where
  getImmut = ToSafeM $ lift $ getImmut

-- === monad for translating from safe to unsafe names ===

class (MonadFail1 m, Monad1 m) => MonadFromSafe (m::MonadKind1) where
  lookupFromSafeSubst :: S.Name c i -> m i (UnsafeName c)
  getUnsafeBindings :: m i (D.Bindings)
  withFreshUnsafeName :: S.NameHint -> D.AnyBinderInfo
                      -> (D.Name -> m i a) -> m i a
  extendFromSafeMap :: S.NameBinder c i i'
                    -> UnsafeName c -> m i' a -> m i a

data UnsafeNameE (c::C) (n::S) = UnsafeNameE { fromUnsafeNameE :: UnsafeName c}

newtype FromSafeSubst i = FromSafeEnv (S.MaterializedEnv UnsafeNameE i VoidS)
  deriving (Generic, Pretty)

newtype FromSafeM i a =
  FromSafeM { runFromSafeM' :: ReaderT (FromSafeSubst i) (Reader D.Bindings) a }
  deriving (Functor, Applicative, Monad)

runFromSafeM :: FromSafeSubst i -> D.Bindings -> FromSafeM i a -> a
runFromSafeM nameMap bindings m =
  flip runReader bindings $ flip runReaderT nameMap $ runFromSafeM' m

instance MonadFromSafe FromSafeM where
  lookupFromSafeSubst v = FromSafeM do
    FromSafeSubst env <- ask
    return $ fromUnsafeNameE $ lookupMaterializedSubst env v
  getUnsafeBindings = FromSafeM $ lift ask
  withFreshUnsafeName hint info f =
    FromSafeM $ ReaderT \m -> do
      scope <- ask
      let hint' = case hint of S.Hint rawName -> rawName
                               S.NoHint -> "v"
      let v' = genFresh hint' scope
      withReaderT (<> (v' D.@> info)) $
        runReaderT (runFromSafeM' (f v')) m

  extendFromSafeMap b v (FromSafeM m) = FromSafeM $ flip withReaderT m
    \(FromSafeSubst env) -> FromSafeEnv $ env <>> b S.@> UnsafeNameE v

-- === --- ===

class HasSafeVersionE (e:: *) where
  type SafeVersionE e :: S.E
  toSafeE   :: HasCallStack => MonadToSafe   m => e -> m o (SafeVersionE e o)
  fromSafeE :: MonadFromSafe m => SafeVersionE e i -> m i e

class HasSafeVersionB (b:: *) where
  type SafeVersionB b :: S.B
  toSafeB   :: MonadToSafe   m => b -> (forall o'. SafeVersionB b o o' -> m o' r) -> m o r
  fromSafeB :: MonadFromSafe m => SafeVersionB b i i' -> (b -> m i' r) -> m i r

data UnsafeName (c::C) = UnsafeName (NameColorRep c) D.Name

fromUnsafeName :: UnsafeName c -> D.Name
fromUnsafeName (UnsafeName _ name) = name

fromSafeAtomName :: MonadFromSafe m => S.AtomName i -> m i D.Name
fromSafeAtomName v = fromUnsafeName <$> fromSafeE v

toSafeAtomName :: MonadToSafe m => D.Name -> m o (S.AtomName o)
toSafeAtomName v = toSafeE (UnsafeName AtomNameRep v)

fromSafeAtomNameVar :: MonadFromSafe m => S.AtomName i -> m i D.Var
fromSafeAtomNameVar name = do
  UnsafeName AtomNameRep name' <- fromSafeE name
  AtomBinderInfo ty _ <- (D.! name') <$> getUnsafeBindings
  return $ name' D.:> ty

instance HasSafeVersionE (UnsafeName c) where
  type SafeVersionE (UnsafeName c) = S.Name c
  toSafeE (UnsafeName rep name) = do
    let Just name' = getName name
    ToSafeSubst m <- getToSafeEnv
    case m D.! name' of
      WithColor rep' safeName ->
        case eqNameColorRep rep rep' of
          Just ColorsEqual -> return safeName
          Nothing -> error "mismatched name colors!"
  fromSafeE name = lookupFromSafeSubst name

instance HasSafeVersionE D.EvaluatedModule where
  type SafeVersionE D.EvaluatedModule = S.EvaluatedModule
  toSafeE = undefined
  fromSafeE = undefined

newtype DRecSubstFrag = DRecEnvFrag D.Bindings

asUnsafeNameFromBinderInfo
  :: D.AnyBinderInfo -> D.Name
  -> (forall c. UnsafeName c -> a )
  -> a
asUnsafeNameFromBinderInfo info name cont = case info of
  AtomBinderInfo _ _ -> cont $ UnsafeName AtomNameRep    name
  DataDefName  _     -> cont $ UnsafeName DataDefNameRep name
  TyConName    _ _   -> cont $ UnsafeName TyConNameRep   name
  DataConName  _ _ _ -> cont $ UnsafeName DataConNameRep name
  ClassDefName _ _   -> cont $ UnsafeName ClassNameRep   name
  MethodName   _ _ _ -> cont $ UnsafeName MethodNameRep  name
  SuperclassName _ _ _ -> cont $ UnsafeName SuperclassNameRep name

instance HasSafeVersionB DRecSubstFrag where
  type SafeVersionB DRecSubstFrag = RecEnvFrag S.Binding
  toSafeB (DRecSubstFrag env) cont =
    renameBinders (envPairs env) \nest -> do
      nest' <- forEachNestItemM nest \(TempPair b info) -> do
        WithColor rep info' <- toSafeE info
        case eqNameColorRep rep (getNameColor b) of
          Just ColorsEqual ->
            withNameColorRep rep $ return $ SubstPair b $ info'
          Nothing -> error $ "color mismatch: " <> pprint rep <> " vs " <> pprint (getNameColor b)
      cont $ RecSubstFrag $ fromEnvPairs nest'
    where
      renameBinders
        :: MonadToSafe m
         => [(D.Name, D.AnyBinderInfo)]
         -> (forall o'. S.Nest TempPair o o' -> m o' r)
         -> m o r
      renameBinders [] cont = cont S.Empty
      renameBinders ((b,info):rest) cont = do
        renameBindersSubstPair b info \pair ->
          renameBinders rest \rest' ->
            cont $ S.Nest pair rest'

      renameBindersSubstPair
        :: MonadToSafe m
        => D.Name -> AnyBinderInfo
        -> (forall o'. TempPair o o' -> m o' r)
        -> m o r
      renameBindersSubstPair name info cont =
        asUnsafeNameFromBinderInfo info name \name'@(UnsafeName rep _) -> do
          Immut <- getImmut
          withFreshM (S.Hint name) rep \b ->
            extendToSafeSubst name' (binderName b) $
              cont $ TempPair b info

  fromSafeB (RecSubstFrag env) cont = do
    renameBinders (S.toSubstPairs env) \pairs -> do
      (newNames, vals) <- unzip <$> forM pairs
         \(DSubstPair v@(UnsafeName rep _) binding) -> do
            info <- fromSafeE $ WithColor rep binding
            let Just name = getName v
            return (name, info)
      cont $ DRecSubstFrag $ D.newEnv newNames vals

    where
      renameBinders
        :: MonadFromSafe m
        => S.Nest (SubstPair Binding i') i i'
        -> ([DSubstPair i'] -> m i' r)
        -> m i r
      renameBinders S.Empty cont = cont []
      renameBinders (S.Nest (SubstPair b binderInfo) rest) cont =
        withFreshUnsafeName (getNameHint b) TrulyUnknownBinder \v -> do
          let v' = UnsafeName (getNameColor b) v
          extendFromSafeMap b v' $ do
            renameBinders rest \rest' -> do
              cont $ (DSubstPair v' binderInfo) : rest'

data DSubstPair n where
  DSubstPair :: UnsafeName c -> Binding c n -> DEnvPair n

instance HasSafeVersionE AnyBinderInfo where
  type SafeVersionE AnyBinderInfo = WithColor Binding
  toSafeE anyInfo = case anyInfo of
    AtomBinderInfo ty info  -> WithColor nameColorRep <$> (AtomNameBinding <$> toSafeE (TypedBinderInfo ty info))
    DataDefName def         -> WithColor nameColorRep <$> (DataDefBinding  <$> toSafeE def)
    TyConName def e         -> WithColor nameColorRep <$> (TyConBinding    <$> toSafeE (UnsafeName nameColorRep def) <*> toSafeE e)
    DataConName def idx e   -> WithColor nameColorRep <$> (DataConBinding  <$> toSafeE (UnsafeName nameColorRep def) <*> pure idx <*> toSafeE e)
    ClassDefName classDef e -> WithColor nameColorRep <$> (ClassBinding    <$> (S.ClassDef className methods <$> toSafeNamedDataDef def) <*> toSafeE e)
      where D.ClassDef def@(_, D.DataDef className _ _) methods = classDef
    MethodName def idx val -> WithColor nameColorRep <$> (MethodBinding   <$> toSafeE (UnsafeName nameColorRep def) <*> pure idx <*> toSafeE val)
    SuperclassName def idx val -> WithColor nameColorRep <$> (SuperclassBinding <$> toSafeE (UnsafeName nameColorRep def) <*> pure idx <*> toSafeE val)
    _ -> error $ "Not recognized: " ++ pprint anyInfo
  fromSafeE (WithColor rep info) = topBindingToAnyBinderInfo rep info

topBindingToAnyBinderInfo :: MonadFromSafe m => NameColorRep c -> Binding c n -> m n D.AnyBinderInfo
topBindingToAnyBinderInfo rep binding = case binding of
  AtomNameBinding info -> do
    TypedBinderInfo ty' info' <- fromSafeE info
    return $ AtomBinderInfo ty' info'
  DataDefBinding def           -> DataDefName <$> fromSafeE def
  TyConBinding   defName     e -> TyConName <$> (fromUnsafeName <$> fromSafeE defName) <*> fromSafeE e
  DataConBinding defName idx e -> DataConName <$> (fromUnsafeName <$> fromSafeE defName) <*> pure idx <*> fromSafeE e
  ClassBinding   def         e -> ClassDefName <$> fromSafeE def <*> fromSafeE e
  SuperclassBinding superclassName idx getter ->
    SuperclassName <$> (fromUnsafeName <$> fromSafeE superclassName) <*> pure idx <*> fromSafeE getter
  MethodBinding className idx getter ->
    MethodName <$> (fromUnsafeName <$> fromSafeE className) <*> pure idx <*> fromSafeE getter

-- used to hold a partially-to-safed env pair. The challenge is that we have to
-- do two passes when we process recursive bindings, but we can't split up the
-- `s` parameter for the binder from the corresponding `s` parameter for the
-- payload. This GADT hides `s` existentially but ensures that the bindings and
-- the not-yet-fully-evaluated payload are the same.
data TempPair (n::S) (l::S) where
  TempPair :: NameBinder c n l -> AnyBinderInfo -> TempPair n l

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
  type SafeVersionE (D.SourceNameDef) = S.WithColor S.Name
  toSafeE name = case name of
    D.SrcAtomName    v -> WithColor nameColorRep <$> toSafeE (UnsafeName AtomNameRep    v)
    D.SrcTyConName   v -> WithColor nameColorRep <$> toSafeE (UnsafeName TyConNameRep   v)
    D.SrcDataConName v -> WithColor nameColorRep <$> toSafeE (UnsafeName DataConNameRep v)
    D.SrcClassName   v -> WithColor nameColorRep <$> toSafeE (UnsafeName ClassNameRep   v)
    D.SrcMethodName  v -> WithColor nameColorRep <$> toSafeE (UnsafeName MethodNameRep  v)

  fromSafeE (WithColor rep v) = case rep of
    AtomNameRep    -> D.SrcAtomName    <$> fromUnsafeName <$> fromSafeE v
    TyConNameRep   -> D.SrcTyConName   <$> fromUnsafeName <$> fromSafeE v
    DataConNameRep -> D.SrcDataConName <$> fromUnsafeName <$> fromSafeE v
    ClassNameRep   -> D.SrcClassName   <$> fromUnsafeName <$> fromSafeE v
    MethodNameRep  -> D.SrcMethodName  <$> fromUnsafeName <$> fromSafeE v

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
      toSafeB b \(b' S.:> ty') -> do
        (arr', eff') <- toSafeArrow arr
        body' <- toSafeE body
        return $ S.Lam $ S.LamExpr (S.LamBinder b' ty' arr' eff') body'
    D.Pi (D.Abs b (arr, body)) ->
      toSafeB b \(b' S.:> argTy) -> do
        (arr', eff') <- toSafeArrow arr
        body' <- toSafeE body
        return $ S.Pi $ S.PiType (S.PiBinder b' argTy arr') eff' body'
    D.DataCon def@(_, D.DataDef _ _ cons) params con args -> do
      let (D.DataConDef name _) = cons !! con
      S.DataCon name <$>
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
    S.Lam (S.LamExpr (LamBinder b ty arr eff) body) -> do
      fromSafeB (b S.:> ty) \b' -> do
        arr' <- fromSafeArrow arr eff
        body' <- fromSafeE body
        return $ D.Lam $ D.Abs b' (arr', body')
    S.Pi (S.PiType (S.PiBinder b argTy arr) eff body) -> do
      fromSafeB (b S.:> argTy) \b' -> do
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

instance HasSafeVersionB D.DataConRefBinding where
  type SafeVersionB D.DataConRefBinding = S.DataConRefBinding
  toSafeB (D.DataConRefBinding b ann) cont = do
    ann' <- toSafeE ann
    toSafeB b \b' -> cont $ S.DataConRefBinding b' ann'
  fromSafeB (S.DataConRefBinding b ann) cont = do
    ann' <- fromSafeE ann
    fromSafeB b \b' -> cont $ D.DataConRefBinding b' ann'

instance HasSafeVersionB D.Binder where
  type SafeVersionB D.Binder = S.Binder

  toSafeB (Ignore ty) cont = do
    ty' <- toSafeE ty
    Immut <- getImmut
    withFreshM S.NoHint nameColorRep \b' -> do
      cont (b' S.:> ty')
  toSafeB (Bind (b D.:> ty)) cont = do
    ty' <- toSafeE ty
    Immut <- getImmut
    withFreshM (getNameHint b) nameColorRep \b' -> do
      extendToSafeSubst (UnsafeName AtomNameRep b) (S.binderName b') $
        cont (b' S.:> ty')

  fromSafeB (b S.:> ty) cont = do
    ty' <- fromSafeE ty
    withFreshUnsafeName (getNameHint b) (AtomBinderInfo ty' UnknownBinder) \v' ->
      extendFromSafeMap b (UnsafeName AtomNameRep v') $
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

instance HasSafeVersionE D.ClassDef where
  type SafeVersionE D.ClassDef = S.ClassDef
  toSafeE (D.ClassDef def@(_, D.DataDef sourceName _ _) methodNames) =
    S.ClassDef sourceName methodNames <$> toSafeNamedDataDef def
  fromSafeE (S.ClassDef _ methodNames def) =
    D.ClassDef <$> fromSafeNamedDataDef def <*> pure methodNames

toSafeNamedDataDef :: MonadToSafe m => D.NamedDataDef -> m o (S.NamedDataDef o)
toSafeNamedDataDef (name, def) =
  (,) <$> toSafeE (UnsafeName DataDefNameRep name) <*> toSafeE def

fromSafeNamedDataDef :: MonadFromSafe m => S.NamedDataDef i -> m i D.NamedDataDef
fromSafeNamedDataDef (name, def) = do
  UnsafeName DataDefNameRep name' <- lookupFromSafeSubst name
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
    toSafeB b \(b' S.:> ty') ->
      cont $ S.Let b' (S.DeclBinding ann ty' expr')

  fromSafeB (S.Let b (S.DeclBinding ann ty expr)) cont = do
    expr' <- fromSafeE expr
    fromSafeB (b S.:>ty) \b' -> do
      cont $ D.Let ann b' expr'

instance HasSafeVersionE D.Effect where
  type SafeVersionE D.Effect = S.Effect
  toSafeE eff = case eff of
    D.RWSEffect rws h -> S.RWSEffect rws <$> toSafeE (UnsafeName AtomNameRep h)
    D.ExceptionEffect -> return S.ExceptionEffect
    D.IOEffect        -> return S.IOEffect
  fromSafeE eff = case eff of
    S.RWSEffect rws h -> D.RWSEffect rws <$> ((fromUnsafeName <$>) . fromSafeE) h
    S.ExceptionEffect -> return D.ExceptionEffect
    S.IOEffect        -> return D.IOEffect

instance HasSafeVersionE D.EffectRow where
  type SafeVersionE D.EffectRow = S.EffectRow
  toSafeE   (D.EffectRow effs v) =
    S.EffectRow <$> traverseSet toSafeE   effs <*> mapM (toSafeE . UnsafeName AtomNameRep) v
  fromSafeE (S.EffectRow effs v) =
    D.EffectRow <$> traverseSet fromSafeE effs <*> mapM ((fromUnsafeName <$>) . fromSafeE) v

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

data TypedBinderInfo = TypedBinderInfo D.Type D.BinderInfo

instance HasSafeVersionE TypedBinderInfo where
  type SafeVersionE TypedBinderInfo = AtomBinding
  toSafeE (TypedBinderInfo ty info) = do
    ty' <- toSafeE ty
    case info of
      D.LetBound ann expr -> do
        expr' <- toSafeE expr
        return $ S.LetBound $ S.DeclBinding ann ty' expr'
      D.LamBound arr -> return $ S.LamBound $ S.LamBinding (toSafeUnitArrow arr) ty'
      D.PiBound arr   -> return $ S.PiBound $ S.PiBinding  (toSafeUnitArrow arr) ty'
      D.UnknownBinder -> return $ S.MiscBound ty'
  fromSafeE info = case info of
    S.LetBound (S.DeclBinding ann ty expr) -> do
      ty'   <- fromSafeE ty
      expr' <- fromSafeE expr
      return $ TypedBinderInfo ty' $ D.LetBound ann expr'
    S.LamBound (S.LamBinding arr ty) -> do
      ty' <- fromSafeE ty
      return $ TypedBinderInfo ty' $ D.LamBound $ fromSafeUnitArrow arr
    S.MiscBound ty -> do
      ty' <- fromSafeE ty
      return $ TypedBinderInfo ty' D.UnknownBinder

toSafeUnitArrow :: D.ArrowP () -> S.Arrow
toSafeUnitArrow arr = case arr of
  D.PlainArrow () -> S.PlainArrow
  D.ImplicitArrow -> S.ImplicitArrow
  D.LinArrow      -> S.LinArrow
  D.TabArrow      -> S.TabArrow
  D.ClassArrow    -> S.ClassArrow

fromSafeUnitArrow :: S.Arrow -> D.ArrowP ()
fromSafeUnitArrow arr = case arr of
  S.PlainArrow    -> D.PlainArrow ()
  S.ImplicitArrow -> D.ImplicitArrow
  S.LinArrow      -> D.LinArrow
  S.TabArrow      -> D.TabArrow
  S.ClassArrow    -> D.ClassArrow

traverseSet :: (Ord a, Ord b, Monad m) => (a -> m b) -> Set.Set a -> m (Set.Set b)
traverseSet f s = Set.fromList <$> mapM f (Set.toList s)

-- === boilerplate instances ===

instance Store TopStateEx

deriving via (WrapE JointTopState n) instance Generic (JointTopState n)

instance Generic TopStateEx where
  type Rep TopStateEx = Rep (JointTopState UnsafeS)
  from (TopStateEx topState) = from (unsafeCoerceE topState :: JointTopState UnsafeS)
  to rep = do
    case fabricateDistinctEvidence :: DistinctEvidence UnsafeS of
      Distinct -> TopStateEx (to rep :: JointTopState UnsafeS)

instance HasPtrs TopStateEx where
  -- TODO: rather than implementing HasPtrs for safer names, let's just switch
  --       to using names for pointers.
  traversePtrs _ s = pure s

instance ScopeReader ToSafeM where
  getScope = ToSafeM $ lift $ getScope
  getDistinct = ToSafeM $ lift $ getDistinct

instance ScopeExtender ToSafeM where
  extendScope frag m  =
    ToSafeM $ ReaderT \env ->
      extendScope frag do
        let ToSafeM (ReaderT f) =m
        env' <- sinkM env
        f env'

instance MonadFail (ToSafeM o) where
  fail s = error s

instance MonadFail (FromSafeM i) where
  fail s = error s

instance D.HasName (UnsafeName s) where
  getName (UnsafeName _ v) = Just v

instance Pretty (UnsafeNameE s n) where
  pretty (UnsafeNameE name) = pretty name

instance Pretty (UnsafeName n) where
  pretty (UnsafeName _ name) = pretty name

instance Store (ToSafeSubst n)
instance SinkableE ToSafeSubst where
  sinkionProofE = undefined
instance Store (FromSafeSubst n)

deriving instance NameColor c => Generic (UnsafeName  c)
deriving instance NameColor c => Generic (UnsafeNameE c n)

instance NameColor c => Store (UnsafeName  c)
instance NameColor c => Store (UnsafeNameE c n)

