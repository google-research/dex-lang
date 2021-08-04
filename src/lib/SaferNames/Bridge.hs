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
import Data.Maybe (fromJust)
import Data.Store (Store)
import GHC.Generics (Generic (..))

import qualified Data.Map.Strict as M

import SaferNames.NameCore
import SaferNames.Name
import SaferNames.Syntax
import SaferNames.LazyMap as LM

import Serialize (HasPtrs (..))

import qualified Syntax as D  -- D for Danger
import qualified Type   as D
import qualified Env    as D

import qualified SaferNames.Name      as S
import qualified SaferNames.Syntax    as S


-- Hides the `n` parameter as an existential
data TopStateEx where
  TopStateEx :: JointTopState n -> TopStateEx

initTopState :: TopStateEx
initTopState = TopStateEx $ JointTopState
    D.emptyTopState
    S.emptyTopState
    (ToSafeNameMap mempty)
    voidEnv

data JointTopState n = JointTopState
  { topStateD   :: D.TopState
  , topStateS   :: S.TopState n
  , topToSafeMap   :: ToSafeNameMap n
  , topFromSafeMap :: FromSafeNameMap n }

extendTopStateD :: JointTopState n -> D.EvaluatedModule -> TopStateEx
extendTopStateD jointTopState evaluated = do
  let D.TopState bindingsD scsD sourceMapD = topStateD jointTopState
  let S.TopState bindingsS scsS sourceMapS = topStateS jointTopState
  -- ensure the internal bindings are fresh wrt top bindings
  let D.EvaluatedModule bindingsD' scsD' sourceMapD' = D.subst (mempty, bindingsD) evaluated
  runToSafeM (topToSafeMap jointTopState) (bindingsAsScope bindingsS) do
    nameBijectionFromDBindings (topFromSafeMap jointTopState) bindingsD'
     \bindingsFrag toSafeMap' fromSafeMap' -> do
       scsS'       <- toSafeE scsD'
       sourceMapS' <- toSafeE sourceMapD'
       sourceMapSInj <- injectM bindingsFrag sourceMapS
       scsSInj       <- injectM bindingsFrag scsS
       return $ TopStateEx $ JointTopState
         (D.TopState (bindingsD <> bindingsD') (scsD <> scsD') (sourceMapD <> sourceMapD'))
         (S.TopState (appendBindings bindingsS bindingsFrag)
                     (scsSInj <> scsS') (sourceMapSInj <> sourceMapS'))
         toSafeMap'
         fromSafeMap'

-- This is pretty horrible. The name system isn't really designed for creating
-- bijections, so we have to do a lot of things manually.
nameBijectionFromDBindings
    :: MonadToSafe m => FromSafeNameMap n -> D.Bindings
    -> (forall l. BindingsFrag n l -> ToSafeNameMap l -> FromSafeNameMap l -> m l a)
    -> m n a
nameBijectionFromDBindings fromSafeMap bindings cont = do
  withFreshSafeRec fromSafeMap (envPairs bindings) \scopeFrag fromSafeMap' -> do
    toSafeMap' <- getToSafeNameMap
    scope <- getScope
    let bindingsFrag = makeBindingsFrag scope bindings toSafeMap' fromSafeMap' scopeFrag
    cont bindingsFrag toSafeMap' fromSafeMap'

type ConstNameMap n l = NameMap (ConstE UnitE) (n:=>:l) VoidS

makeBindingsFrag :: forall n l. Distinct l =>
                    S.Scope l -> D.Bindings -> ToSafeNameMap l -> FromSafeNameMap l
                 -> ConstNameMap n l -> BindingsFrag n l
makeBindingsFrag scope bindings toSafeMap fromSafeMap constNameMap =
  BindingsFrag $ fmapNameMap (\name _ -> getSafeBinding name) constNameMap
  where
    getSafeBinding :: S.Name s (n:=>:l) -> IdE s l
    getSafeBinding name =
      case fromSafeMap S.! injectNamesR name of
        UnsafeAtomName name' -> case bindings D.! name' of
          AtomBinderInfo ty info ->
            let (ty', info') = runToSafeM toSafeMap scope $
                                 (,) <$> toSafeE ty <*> toSafeE info
            in IdE $ S.TypedBinderInfo ty' info'

withFreshSafeRec :: MonadToSafe m
                 => FromSafeNameMap n
                 -> [(D.Name, D.AnyBinderInfo)]
                 -> (forall l. Distinct l => ConstNameMap n l -> FromSafeNameMap l -> m l a)
                 -> m n a
withFreshSafeRec fromSafeMap [] cont = do
  withDistinct $ cont emptyNameMap fromSafeMap
withFreshSafeRec fromSafeMap ((vD,info):rest) cont = do
  withFreshBijectionD vD info \b valD -> do
    frag <- return $ singletonNameMap b (ConstE UnitE)
    withFreshSafeRec (fromSafeMap <>> (b S.@> valD)) rest
      \frag' fromSafeMap' -> do
        cont (frag `concatNameMaps` frag') fromSafeMap'

withFreshBijectionD :: MonadToSafe m => D.Name -> D.AnyBinderInfo
                    -> (forall l s. S.NameBinder s n l -> UnsafeName s -> m l a)
                    -> m n a
withFreshBijectionD name info cont = case info of
  AtomBinderInfo _ _ ->
    withFreshM \b ->
      extendToSafeNameMap name (SafeAtomName $ S.binderName b) $
        cont b (UnsafeAtomName name)

extendTopStateS :: JointTopState n -> S.EvaluatedModule n -> TopStateEx
extendTopStateS = error "not implemented"

toSafe :: HasSafeVersionE e => JointTopState n -> e -> SafeVersionE e n
toSafe jointTopState e =
  runToSafeM (topToSafeMap jointTopState) scope $ toSafeE e
  where scope = S.bindingsAsScope $ S.topBindings $ topStateS $ jointTopState

fromSafe :: HasSafeVersionE e => JointTopState n -> SafeVersionE e n -> e
fromSafe jointTopState e =
  runFromSafeM (topFromSafeMap jointTopState) bindings $ fromSafeE e
  where bindings = D.topBindings $ topStateD $ jointTopState

-- === monad for translating from unsafe to safe names ===

class ( S.ScopeReader m, S.ScopeExtender m
      , MonadFail1 m, Monad1 m)
      => MonadToSafe (m::MonadKind1) where
  getToSafeNameMap :: m o (ToSafeNameMap o)
  extendToSafeNameMap :: D.Name -> SafeName o -> m o a -> m o a


data SafeName (n::S) =
   SafeAtomName    (S.AtomName n)
 | SafeDataDefName (S.Name S.DataDef n)

newtype ToSafeNameMap o = ToSafeNameMap (D.Env (SafeName o))

newtype ToSafeM o a =
  ToSafeM { runToSafeM' :: ReaderT (ToSafeNameMap o) (ScopeReaderT Identity o) a }
  deriving (Functor, Applicative, Monad)

runToSafeM :: ToSafeNameMap o -> S.Scope o -> ToSafeM o a -> a
runToSafeM nameMap scope m =
  runIdentity $ runScopeReaderT scope $
    flip runReaderT nameMap $
      runToSafeM' m

instance MonadToSafe ToSafeM where
  getToSafeNameMap = ToSafeM ask
  extendToSafeNameMap v v' (ToSafeM m) = ToSafeM $ flip withReaderT m
    \(ToSafeNameMap env) -> ToSafeNameMap $ env <> (v D.@> v')

lookupToSafeNameMap :: MonadToSafe m => D.Name -> m o (SafeName o)
lookupToSafeNameMap v = do
  ToSafeNameMap env <- getToSafeNameMap
  return $ env D.! v

-- === monad for translating from safe to unsafe names ===

class (MonadFail1 m, Monad1 m) => MonadFromSafe (m::MonadKind1) where
  lookupFromSafeNameMap :: S.Name s i -> m i (UnsafeName s)
  getUnsafeBindings :: m i (D.Bindings)
  withFreshUnsafeName :: D.AnyBinderInfo
                      -> (D.Name -> m i a) -> m i a
  extendFromSafeMap :: S.NameBinder s i i'
                    -> UnsafeName s -> m i' a -> m i a

type UnsafeName s = UnsafeNameE s VoidS
data UnsafeNameE (s::E) (n::S) where
  UnsafeAtomName :: D.Name -> UnsafeNameE S.TypedBinderInfo VoidS

type FromSafeNameMap i = S.Env UnsafeNameE i VoidS

newtype FromSafeM i a =
  FromSafeM { runFromSafeM' :: ReaderT (FromSafeNameMap i) (Reader D.Bindings) a }
  deriving (Functor, Applicative, Monad)

runFromSafeM :: FromSafeNameMap i -> D.Bindings -> FromSafeM i a -> a
runFromSafeM nameMap bindings m =
  flip runReader bindings $ flip runReaderT nameMap $ runFromSafeM' m

instance MonadFromSafe FromSafeM where
  lookupFromSafeNameMap v = FromSafeM $ (S.! v) <$> ask
  getUnsafeBindings = FromSafeM $ lift ask
  withFreshUnsafeName info f =
    FromSafeM $ ReaderT \m -> do
      scope <- ask
      let v' = genFresh "v" scope  -- TODO: preverse name hints
      withReaderT (<> (v' D.@> info)) $
        runReaderT (runFromSafeM' (f v')) m

  extendFromSafeMap b v (FromSafeM m) = FromSafeM $ flip withReaderT m
    \env -> env <>> b S.@> v

-- === --- ===

class HasSafeVersionE (e:: *) where
  type SafeVersionE e :: S.E
  toSafeE   :: MonadToSafe   m => e -> m o (SafeVersionE e o)
  fromSafeE :: MonadFromSafe m => SafeVersionE e i -> m i e

class HasSafeVersionB (b:: *) where
  type SafeVersionB b :: S.B
  toSafeB   :: MonadToSafe   m => b -> (forall o'. SafeVersionB b o o' -> m o' r) -> m o r
  fromSafeB :: MonadFromSafe m => SafeVersionB b i i' -> (b -> m i' r) -> m i r

instance HasSafeVersionE D.Module where
  type SafeVersionE D.Module = S.Module

instance HasSafeVersionE D.SourceMap where
  type SafeVersionE D.SourceMap = S.SourceNameMap

instance HasSafeVersionE D.SynthCandidates where
  type SafeVersionE D.SynthCandidates = S.SynthCandidates

instance HasSafeVersionE D.Atom where
  type SafeVersionE D.Atom = S.Atom

  toSafeE atom = case atom of
    D.Var (v D.:> _) -> S.Var <$> toSafeAtomName v
    D.Lam (D.Abs b (arr, body)) -> do
      withFreshAtomBinderS b \b' -> do
        (arr', eff') <- toSafeArrow arr
        body' <- toSafeE body
        return $ S.Lam $ S.LamExpr arr' b' eff' body'
    D.Pi (D.Abs b (arr, body)) ->
      withFreshAtomBinderS b \b' -> do
        (arr', eff') <- toSafeArrow arr
        body' <- toSafeE body
        return $ S.Pi $ S.PiType arr' b' eff' body'
    D.DataCon dataDef@(D.DataDef printName _ _ ) params con args ->
      S.DataCon (rawName GenName $ fromString printName) <$>
        toSafeE (DataDefRef dataDef) <*>
        mapM toSafeE params <*> pure con <*> mapM toSafeE args
    D.TypeCon dataDef params ->
      S.TypeCon <$> toSafeE (DataDefRef dataDef) <*> mapM toSafeE params
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
    D.DataConRef dataDef params args ->
      S.DataConRef <$> toSafeE (DataDefRef dataDef) <*>
        mapM toSafeE params <*> toSafeE (D.Abs args ())
    D.BoxedRef b ptr size body ->
      S.BoxedRef <$> toSafeE ptr <*> toSafeE size <*> toSafeE (D.Abs b body)
    D.ProjectElt idxs (v D.:> _) -> S.ProjectElt idxs <$> toSafeAtomName v

  fromSafeE atom = case atom of
    S.Var v -> D.Var <$> fromSafeAtomNameVar v
    S.Lam (S.LamExpr arr b eff body) -> do
      withFreshAtomBinderD b \b' -> do
        arr' <- fromSafeArrow arr eff
        body' <- fromSafeE body
        return $ D.Lam $ D.Abs b' (arr', body')
    S.Pi (S.PiType arr b eff body) -> do
      withFreshAtomBinderD b \b' -> do
        arr' <- fromSafeArrow arr eff
        body' <- fromSafeE body
        return $ D.Pi $ D.Abs b' (arr', body')
    S.DataCon _ dataDefName params con args -> do
      dataDef <- fromDataDefRef <$> fromSafeE dataDefName
      D.DataCon dataDef <$> mapM fromSafeE params <*> pure con <*> mapM fromSafeE args
    S.TypeCon dataDefName params -> do
      dataDef <- fromDataDefRef <$> fromSafeE dataDefName
      D.TypeCon dataDef <$> mapM fromSafeE params
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
    S.DataConRef dataDef params ab -> do
      dataDef <- fromDataDefRef <$> fromSafeE dataDef
      params' <- mapM fromSafeE params
      D.Abs bs () <- fromSafeE ab
      return $ D.DataConRef dataDef params' bs
    S.BoxedRef ptr size ab -> do
      ptr' <- fromSafeE ptr
      size' <- fromSafeE size
      D.Abs b body <- fromSafeE ab
      return $ D.BoxedRef b ptr' size' body
    S.ProjectElt idxs v -> D.ProjectElt idxs <$> fromSafeAtomNameVar v

instance HasSafeVersionB D.Binder where
  type SafeVersionB D.Binder = S.Binder

withFreshAtomBinderS :: MonadToSafe m
                     => D.Binder
                     -> (forall o'. S.Binder o o' -> m o' r)
                     -> m o r
withFreshAtomBinderS (Ignore ty) cont = do
  ty' <- toSafeE ty
  withFreshM \b' -> do
    cont (b' S.:> ty')
withFreshAtomBinderS (Bind (b D.:> ty)) cont = do
  ty' <- toSafeE ty
  withFreshM \b' -> do
    extendToSafeNameMap b (SafeAtomName $ S.binderName b') $
      cont (b' S.:> ty')

withFreshAtomBinderD :: MonadFromSafe m
                     => S.Binder i i'
                     -> (D.Binder -> m i' r)
                     -> m i r
withFreshAtomBinderD (b S.:> ty) cont = do
  ty' <- fromSafeE ty
  withFreshUnsafeName (AtomBinderInfo ty' UnknownBinder) \v' ->
    extendFromSafeMap b (UnsafeAtomName v') $
      cont (Bind (v' D.:> ty'))

toSafeAtomName :: MonadToSafe m => D.Name -> m o (S.AtomName o)
toSafeAtomName name = do
  SafeAtomName name' <- lookupToSafeNameMap name
  return name'

fromSafeAtomName :: MonadFromSafe m => S.AtomName i -> m i D.Name
fromSafeAtomName name = do
  name' <- lookupFromSafeNameMap name
  case name' of
    UnsafeAtomName v -> return v

fromSafeAtomNameVar :: MonadFromSafe m => S.AtomName i -> m i D.Var
fromSafeAtomNameVar name = do
  name' <- fromSafeAtomName name
  AtomBinderInfo ty _ <- (D.! name') <$> getUnsafeBindings
  return $ name' D.:> ty

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

newtype DataDefRef = DataDefRef { fromDataDefRef :: D.DataDef }
instance HasSafeVersionE DataDefRef where
  type SafeVersionE DataDefRef = S.Name S.DataDef
  -- TODO: to handle these we need the unsafe IR to keep around the data def
  -- names rather than just inlining the definition.
  toSafeE = undefined
  fromSafeE = undefined

instance HasSafeVersionE () where
  type SafeVersionE () = S.UnitE

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
  AnnBinderP (S.NameBinder S.TypedBinderInfo n l) (ann n)

instance HasSafeVersionE D.Effect where
  type SafeVersionE D.Effect = S.Effect
  toSafeE eff = case eff of
    D.RWSEffect rws h -> S.RWSEffect rws <$> toSafeAtomName h
    D.ExceptionEffect -> return S.ExceptionEffect
    D.IOEffect        -> return S.IOEffect
  fromSafeE eff = case eff of
    S.RWSEffect rws h -> D.RWSEffect rws <$> fromSafeAtomName h
    S.ExceptionEffect -> return D.ExceptionEffect
    S.IOEffect        -> return D.IOEffect

instance HasSafeVersionE D.EffectRow where
  type SafeVersionE D.EffectRow = S.EffectRow
  toSafeE   (D.EffectRow effs v) = S.EffectRow <$> traverseSet toSafeE   effs <*> mapM toSafeAtomName   v
  fromSafeE (S.EffectRow effs v) = D.EffectRow <$> traverseSet fromSafeE effs <*> mapM fromSafeAtomName v

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

instance HasSafeVersionE BinderInfo where
  type SafeVersionE BinderInfo = AtomBinderInfo

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
instance InjectableE S.SourceNameMap

