-- Copyright 2021 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Inference
  ( inferTopUDecl, checkTopUType, inferTopUExpr
  , trySynthTerm, generalizeDict, asTopBlock
  , synthTopE, UDeclInferenceResult (..), asFFIFunType) where

import Prelude hiding ((.), id)
import Control.Category
import Control.Applicative
import Control.Monad
import Control.Monad.State.Strict
import Control.Monad.Writer.Strict hiding (Alt)
import Control.Monad.Reader
import Data.Either (partitionEithers)
import Data.Foldable (toList, asum)
import Data.Functor ((<&>))
import Data.List (sortOn)
import Data.Maybe (fromJust, fromMaybe, catMaybes)
import Data.Text.Prettyprint.Doc (Pretty (..), (<+>), vcat, group, line, nest)
import Data.Word
import qualified Data.HashMap.Strict as HM
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Unsafe.Coerce as TrulyUnsafe
import GHC.Generics (Generic (..))

import Builder
import CheapReduction
import CheckType
import Core
import Err
import IRVariants
import MTL1
import Name
import SourceInfo
import Subst
import QueryType
import Types.Core
import Types.Imp
import Types.Primitives
import Types.Source
import Util hiding (group)
import PPrint (prettyBlock)

-- === Top-level interface ===

checkTopUType :: (Fallible1 m, EnvReader m) => UType n -> m n (CType n)
checkTopUType ty = liftInfererM $ solveLocal $ withApplyDefaults $ checkUType ty
{-# SCC checkTopUType #-}

inferTopUExpr :: (Fallible1 m, EnvReader m) => UExpr n -> m n (TopBlock CoreIR n)
inferTopUExpr e = asTopBlock =<< liftInfererM do
  solveLocal $ buildBlockInf $ withApplyDefaults $ inferSigma noHint e
{-# SCC inferTopUExpr #-}

data UDeclInferenceResult e n =
   UDeclResultDone (e n)  -- used for UDataDefDecl, UInterface and UInstance
 | UDeclResultBindName LetAnn (TopBlock CoreIR n) (Abs (UBinder (AtomNameC CoreIR)) e n)
 | UDeclResultBindPattern NameHint (TopBlock CoreIR n) (ReconAbs CoreIR e n)

inferTopUDecl :: (Mut n, Fallible1 m, TopBuilder m, SinkableE e, HoistableE e, RenameE e)
              => UTopDecl n l -> e l -> m n (UDeclInferenceResult e n)
inferTopUDecl (UStructDecl tc def) result = do
  tc' <- emitBinding (getNameHint tc) $ TyConBinding Nothing (DotMethods mempty)
  def' <- liftInfererM $ solveLocal do
    extendRenamer (tc@>sink tc') $ inferStructDef def
  def'' <- synthTyConDef def'
  updateTopEnv $ UpdateTyConDef tc' def''
  UStructDef _ (_, paramBs) _ methods <- return def
  forM_ methods \(letAnn, methodName, methodDef) -> do
    method <- liftInfererM $ solveLocal $
      extendRenamer (tc@>sink tc') $
        inferDotMethod (sink tc') (Abs paramBs methodDef)
    methodSynth <- synthTopE (Lam method)
    method' <- emitTopLet (getNameHint methodName) letAnn (Atom methodSynth)
    updateTopEnv $ UpdateFieldDef tc' methodName (atomVarName method')
  UDeclResultDone <$> applyRename (tc @> tc') result
inferTopUDecl (UDataDefDecl def tc dcs) result = do
  tcDef <- liftInfererM $ solveLocal $ inferTyConDef def
  tcDef'@(TyConDef _ _ _ (ADTCons dataCons)) <- synthTyConDef tcDef
  tc' <- emitBinding (getNameHint tcDef') $ TyConBinding (Just tcDef') (DotMethods mempty)
  dcs' <- forM (enumerate dataCons) \(i, dcDef) ->
    emitBinding (getNameHint dcDef) $ DataConBinding tc' i
  let subst = tc @> tc' <.> dcs @@> dcs'
  UDeclResultDone <$> applyRename subst result
inferTopUDecl (UInterface paramBs methodTys className methodNames) result = do
  let sn = getSourceName className
  let methodSourceNames = nestToList getSourceName methodNames
  classDef <- liftInfererM $ solveLocal $ inferClassDef sn methodSourceNames paramBs methodTys
  className' <- emitBinding (getNameHint sn) $ ClassBinding classDef
  methodNames' <-
    forM (enumerate methodSourceNames) \(i, prettyName) -> do
      emitBinding (getNameHint prettyName) $ MethodBinding className' i
  let subst = className @> className' <.> methodNames @@> methodNames'
  UDeclResultDone <$> applyRename subst result
inferTopUDecl (UInstance className instanceBs params methods maybeName expl) result = do
  let (InternalName _ _ className') = className
  ab <- liftInfererM $ solveLocal do
    withRoleUBinders instanceBs do
      ClassDef _ _ _ roleExpls paramBinders _ _ <- lookupClassDef (sink className')
      let expls = snd <$> roleExpls
      params' <- checkInstanceParams expls paramBinders params
      className'' <- sinkM className'
      body <- checkInstanceBody className'' params' methods
      return (ListE params' `PairE` body)
  Abs bs' (ListE params' `PairE` body) <- return ab
  let (roleExpls, bs'') = unzipAttrs bs'
  let def = InstanceDef className' roleExpls bs'' params' body
  UDeclResultDone <$> case maybeName of
    RightB UnitB  -> do
      void $ synthInstanceDefAndAddSynthCandidate def
      return result
    JustB instanceName' -> do
      def' <- synthInstanceDef def
      instanceName <- emitInstanceDef def'
      lam <- instanceFun instanceName expl
      instanceAtomName <- emitTopLet (getNameHint instanceName') PlainLet $ Atom lam
      applyRename (instanceName' @> atomVarName instanceAtomName) result
    _ -> error "impossible"
inferTopUDecl (UDerivingInstance className instanceBs params) result = do
  let (InternalName _ _ className') = className
  -- Extract the following:
  --   1) type parameter (`newTy`) for this instance,
  --   2) the underlying type (`wrappedTy`) that is wrapped by `newTy`,
  --   3) superclasses and method definitions from the instance definition for
  --      `wrappedTy`.
  --      (Note that in order to find the instance definition for `wrappedTy`
  --      and instance dictionary for `wrappedTy` is synthesized first.)
  -- All of 1-3 are valid under the binders `instanceBs`. Hence we create an
  -- abstraction whose body contains 1), 2), and 3).
  ab :: Abs (Nest (WithRoleExpl CBinder))
            (CType `PairE` CType `PairE` (ListE CAtom) `PairE` (ListE CAtom))
            n
    <- liftInfererM $ solveLocal do
      withRoleUBinders instanceBs do
        ClassDef classSourceName _ _ roleExpls paramBinders _ _ <- lookupClassDef (sink className')
        let expls = snd <$> roleExpls
        params' <- checkInstanceParams expls paramBinders params
        case params' of
          [param] -> do
            case param of
              TypeAsAtom newTy@(NewtypeTyCon (UserADTType _ tcName (TyConParams _ tcParams))) -> do
                tcDef <- lookupTyCon tcName
                case tcDef of
                  TyConDef _ _ conBs (ADTCons [DataConDef _ (EmptyAbs (Nest (_:>wrappedTy) Empty)) _ _]) -> do
                    wrappedTy' <- applySubst (conBs @@> map SubstVal tcParams) wrappedTy
                    let wrappedDictTy = DictType classSourceName (sink className') [TypeAsAtom wrappedTy']
                    -- Synthesize the dictionary for `wrappedTy'`
                    synthWrappedDict <- trySynthTerm (DictTy wrappedDictTy) Full
                    -- Extract superclasses and methods from the synthesized dictionary for `wrappedTy'`:
                    DictCon _ (InstanceDict wrappedInstName wrappedInstParams) <- return synthWrappedDict
                    InstanceDef _ _ wrappedBinders _ body <- lookupInstanceDef wrappedInstName
                    InstanceBody scs methods <- applySubst (wrappedBinders @@> map SubstVal wrappedInstParams) body
                    return $ newTy `PairE` wrappedTy' `PairE` (ListE scs) `PairE` (ListE methods)
                  TyConDef _ _ _ _ ->
                    throw TypeErr $ "User-defined ADT " ++ pprint newTy ++
                                    " does not have exactly one (data) constructor" ++
                                    " that takes exactly one (data) argument"
              _ -> throw TypeErr $ "Parameter " ++ pprint param ++ " not a user-defined ADT"
          _ -> throw TypeErr $ "More than one parameter when deriving instance of class " ++ pprint className ++
                              "\nparameters: " ++ pprint params'
  -- Check that the class method types mention neither `newTy` nor `wrappedTy`.
  -- There is no fundamental reason for disallowing occurrences of `newTy` or
  -- `wrappedTy` in the class method types, but the current implementation of
  -- `convertAtom` necessitates that neither `newTy` nor `wrappedTy` appears in
  -- any of the class method types. The function `convertAtom` is used below to
  -- synthesize instance methods for `newTy`, and this synthesis is guided by
  -- occurrences of `newTy` and `wrappedTy` in the _instance_ method types of
  -- `wrappedTy`. For `convertAtom` to work correctly, the types `newTy` and
  -- `wrappedTy` may only occur in the _instance_ method types in those positions
  -- where `clParamBinders` (defined by a pattern match below) occur in the
  -- corresponding _class_ method types.
  -- (Note that at this point, `clParamBinders` necessarily  consists of exactly
  -- one binder, corresponding to `param` that has been scrutinized in the nested
  -- `case` expressions above.)
  liftExceptEnvReaderM $ refreshAbs ab \_ body -> do
    let newTy `PairE` wrappedTy `PairE` _ `PairE` _ = body
    ClassDef _ methodNames _ _ clParamBinders clScs methodTys <- lookupClassDef (sink className')
    refreshAbs (concatAbs (Abs clParamBinders (Abs clScs (ListE methodTys)))) \_ (ListE methodTys') ->
      foldM (\_ (mty, mname) -> do whenM (corePiTypeMentionsType mty (sink wrappedTy))
                                         (throw TypeErr $ "Cannot derive instance of " ++ pprint className' ++ ": " ++
                                                          "interface method `" ++ pprint mname ++ "` has type `" ++
                                                          pprint mty ++ "`, which mentions the wrapped instance type `" ++
                                                          pprint wrappedTy ++ "`")
                                   whenM (corePiTypeMentionsType mty (sink newTy))
                                         (throw TypeErr $ "Cannot derive instance of " ++ pprint className' ++ ": " ++
                                                          "interface method `" ++ pprint mname ++ "` has type `" ++
                                                          pprint mty ++ "`, which mentions the new instance type `" ++
                                                          pprint newTy ++ "`")
                                   return ())
            ()
            (zip methodTys' methodNames)
  -- Finally, synthesize an instance definition for `newTy`. This requires, in
  -- particular, that instance method definitions are synthesized for `newTy`.
  -- The function `convertAtom` is used below to synthesize method definitions for
  -- `newTy` from the corresponding instance methods for `wrappedTy` (the definitions
  -- of which are held in the variable `methods` that is bound by a pattern match
  -- on `body` below). In order to call `convertAtom`, an isomorphism (variable
  -- `iso` below) between the types `newTy` and `wrappedTy` is first set up below.
  def <- liftEnvReaderM $ refreshAbs ab \bs body -> do
    let newTy `PairE` wrappedTy `PairE` ListE scs `PairE` ListE methods = body
    case newTy of
      NewtypeTyCon (UserADTType sName tcName tcParams) -> do
        -- Forward isomorphism:
        fwdAbs <- buildAbs noHint wrappedTy \x ->
          return $ NewtypeCon (sink $ UserADTData sName tcName tcParams) (Var x)
        -- Backward isomorphism:
        bwdAbs <- buildAbs noHint newTy \x ->
          return $ ProjectElt (sink newTy) UnwrapNewtype (Var x)
        -- Bundled up isomorphisms:
        let iso = Iso wrappedTy newTy fwdAbs bwdAbs
        -- Convert methods with the constructed isomorphism between `wrappedTy'` and `newTy'`:
        methods' <- liftBuilder $ mapM (convertAtom iso) methods
        let (roleExpls, bs') = unzipAttrs bs
        return $ InstanceDef className' roleExpls bs' [TypeAsAtom newTy] $ InstanceBody scs methods'
      _ -> error "internal error"
  instanceName <- emitInstanceDef def
  addInstanceSynthCandidate className' instanceName
  UDeclResultDone <$> return result
inferTopUDecl (ULocalDecl (WithSrcB src decl)) result = addSrcContext src case decl of
  UPass -> return $ UDeclResultDone result
  UExprDecl _ -> error "Shouldn't have this at the top level (should have become a command instead)"
  ULet letAnn p tyAnn rhs -> case p of
    WithSrcB _ (UPatBinder b) -> do
      block <- liftInfererM $ solveLocal $ buildBlockInf do
        checkMaybeAnnExpr (getNameHint b) tyAnn rhs <* applyDefaults
      topBlock <- asTopBlock block
      return $ UDeclResultBindName letAnn topBlock (Abs b result)
    _ -> do
      PairE block recon <- liftInfererM $ solveLocal $ buildBlockInfWithRecon do
        val <- checkMaybeAnnExpr (getNameHint p) tyAnn rhs
        v <- emitHinted (getNameHint p) $ Atom val
        bindLetPat p v do
          applyDefaults
          renameM result
      topBlock <- asTopBlock block
      return $ UDeclResultBindPattern (getNameHint p) topBlock recon
inferTopUDecl (UEffectDecl _ _ _) _ = error "not implemented"
inferTopUDecl (UHandlerDecl _ _ _ _ _ _ _) _ = error "not implemented"
{-# SCC inferTopUDecl #-}

asTopBlock :: EnvReader m => CBlock n -> m n (TopBlock CoreIR n)
asTopBlock block = do
  effTy <- blockEffTy block
  return $ TopLam False (PiType Empty effTy) (LamExpr Empty block)

getInstanceType :: EnvReader m => InstanceDef n -> m n (CorePiType n)
getInstanceType (InstanceDef className roleExpls bs params _) = liftEnvReaderM do
  refreshAbs (Abs bs (ListE params)) \bs' (ListE params') -> do
    className' <- sinkM className
    ClassDef classSourceName _ _ _ _ _ _ <- lookupClassDef className'
    let dTy = DictTy $ DictType classSourceName className' params'
    return $ CorePiType ImplicitApp (snd <$> roleExpls) bs' $ EffTy Pure dTy

absMentionsType :: (EnvReader m, ScopeReader m) => Abs (Nest CBinder) CType n -> CType n -> m n Bool
absMentionsType (Abs Empty scrut) ty = typeMentionsType scrut ty
absMentionsType (Abs (Nest b@(_ :> bty) rest) scrut) ty = do
  btyMentions <- typeMentionsType bty ty
  restMentions <- liftEnvReaderM $ refreshAbs (Abs b (Abs rest scrut)) \_ ab -> absMentionsType ab (sink ty)
  return $ btyMentions || restMentions

corePiTypeMentionsType :: (EnvReader m, ScopeReader m) => CorePiType n -> CType n -> m n Bool
corePiTypeMentionsType (CorePiType _ _ bs (EffTy _ scrut)) ty = absMentionsType (Abs bs scrut) ty

typeMentionsType :: (EnvReader m, ScopeReader m) => CType n -> CType n -> m n Bool
typeMentionsType scrutinee ty = do
  isAlphaEq <- alphaEq scrutinee ty
  if isAlphaEq then return True
  else case scrutinee of
    TC (BaseType _) -> return False
    TC (ProdType scruts) -> anyM (flip typeMentionsType $ ty) scruts
    TC (SumType scruts) -> anyM (flip typeMentionsType $ ty) scruts
    TC (RefType _ scrut) -> typeMentionsType scrut ty
    TC TypeKind -> return False
    TC HeapType -> return False
    TabPi (TabPiType _ b scrut) -> absMentionsType (Abs (Nest b Empty) scrut) ty
    DepPairTy (DepPairType _ b scrut) -> absMentionsType (Abs (Nest b Empty) scrut) ty
    TyVar _ -> return False
    DictTy _ -> return False
    Pi corePiType -> corePiTypeMentionsType corePiType ty
    NewtypeTyCon _ -> return False
    ProjectEltTy scrut _ _ -> typeMentionsType scrut ty

data Iso n = Iso { inType :: CType n
                 , outType :: CType n
                 , fwd :: Abs CBinder CAtom n  -- single-argument abstraction that implements forward isomorphism
                 , bwd :: Abs CBinder CAtom n  -- single-argument abstraction that implements backward isomorphism
                 }

instance GenericE Iso where
  type RepE Iso = (CType `PairE` CType `PairE` (Abs CBinder CAtom) `PairE` (Abs CBinder CAtom))
  fromE (Iso inType outType fwd bwd) = inType `PairE` outType `PairE` fwd `PairE` bwd
  {-# INLINE fromE #-}
  toE (inType `PairE` outType `PairE` fwd `PairE` bwd) = Iso inType outType fwd bwd
  {-# INLINE toE #-}

instance HoistableE Iso
instance SinkableE Iso
instance RenameE Iso

instance Show (Iso n) where
  show (Iso inType outType _ _) = "Iso " ++ pprint inType ++ " -> " ++ pprint outType

instance Pretty (Iso n) where
  pretty (Iso inType outType fwd bwd) = "Iso" <+> pretty inType <+> pretty outType <+>
                                                  pretty (show fwd) <+> pretty (show bwd)

invert :: Iso n -> Iso n
invert iso = Iso inType' outType' fwd' bwd'
  where inType' = outType iso
        outType' = inType iso
        fwd' = bwd iso
        bwd' = fwd iso

convertType :: EnvExtender m
             => Iso o -> CType o -> m o (CType o)
convertType iso ty = do
  isTyEqualToInType <- alphaEq (inType iso) ty
  if isTyEqualToInType then return $ outType iso
  else case ty of
    Pi (CorePiType appExpl expls bs (EffTy effs resultTy)) -> do
      (Abs bs' (effs' `PairE` resultTy')) <- convertBinders iso (Abs (zipAttrs expls bs) (effs `PairE` resultTy))
      let (_, bs'') = unzipAttrs bs'
      return $ Pi $ CorePiType appExpl expls bs'' (EffTy effs' resultTy')
    _ -> return ty

convertBinders :: EnvExtender m
               => Iso o
               -> Abs (Nest (WithExpl CBinder)) (EffectRow 'CoreIR `PairE` CType) o
               -> m o (Abs (Nest (WithExpl CBinder)) (EffectRow 'CoreIR `PairE` CType) o)
convertBinders iso (Abs Empty (eff `PairE` ty)) = do
  ty' <- convertType iso ty
  return $ Abs Empty (eff `PairE` ty')
convertBinders iso (Abs (Nest (WithAttrB expl (b:>bTy)) rest) x) = do
  bTy' <- convertType iso bTy
  refreshAbs (Abs (WithAttrB expl (b:>bTy')) (Abs rest x))
    \(WithAttrB expl' (b':>bTy'')) ab -> do
      Abs rest' x' <- convertBinders (sink iso) ab
      return $ Abs (Nest (WithAttrB expl' (b':>bTy'')) rest') x'

convertAtom :: (EnvExtender m, ScopableBuilder CoreIR m)
         => Iso i
         -> CAtom i ->  m i (CAtom i)
convertAtom iso atom = do
  let ty = getType atom
  isTyEqualToInType <- alphaEq (inType iso) ty
  if isTyEqualToInType
    then applyAbs (fwd iso) (SubstVal atom)
    else case ty of
      Pi (CorePiType appExpl expl bs (EffTy effs bodyTy)) -> case atom of
        Lam (CoreLamExpr _ _) -> do
          Abs bs' (effs' `PairE` bodyTy') <- convertBinders iso (Abs (zipAttrs expl bs) (effs `PairE` bodyTy))
          let (_, bs'') = unzipAttrs bs'
          lamExpr <- buildCoreLam (CorePiType appExpl expl bs'' (EffTy effs' bodyTy')) \binderNames -> do
            let args = map Var binderNames
            args' <- mapM (convertAtom (sink $ invert iso)) args
            -- Note that `App atom args'` (two lines down) has the unconverted
            -- type `bodyTy` (and unconverted effects `effs`). After the recursive
            -- call to `convertMethodAtom` (three lines down), the resulting
            -- `atom''` will have the correct converted type and effects (i.e.
            -- type and effects equivalent to `bodyTy'` and `effs'`).
            effTy <- applyRename (bs @@> (map atomVarName binderNames)) $ EffTy effs bodyTy
            atom' <- emitExpr $ App effTy (sink atom) args'
            atom'' <- convertAtom (sink iso) atom'
            emitExpr $ Atom atom''
          return $ Lam lamExpr
        _ -> error "should not occur"
      _ -> return atom

-- === Inferer interface ===

class ( MonadFail1 m, Fallible1 m, Catchable1 m, CtxReader1 m, Builder CoreIR m )
      => InfBuilder (m::MonadKind1) where

  -- XXX: we should almost always used the zonking `buildDeclsInf` ,
  -- except where it's not possible because the result isn't atom-substitutable,
  -- such as the source map at the top level.
  buildDeclsInfUnzonked
    :: (SinkableE e, HoistableE e, RenameE e)
    => EmitsInf n
    => (forall l. (EmitsBoth l, DExt n l) => m l (e l))
    -> m n (Abs (Nest CDecl) e n)

  buildAbsInf
    :: (SinkableE e, HoistableE e, RenameE e, SubstE AtomSubstVal e)
    => EmitsInf n
    => NameHint -> Explicitness -> CType n
    -> (forall l. (EmitsInf l, DExt n l) => CAtomVar l -> m l (e l))
    -> m n (Abs CBinder e n)

buildAbsInfWithExpl
  :: (InfBuilder m, SinkableE e, HoistableE e, RenameE e, SubstE AtomSubstVal e)
  => EmitsInf n
  => NameHint -> Explicitness -> CType n
  -> (forall l. (EmitsInf l, DExt n l) => CAtomVar l -> m l (e l))
  -> m n (Abs (WithExpl CBinder) e n)
buildAbsInfWithExpl hint expl ty cont = do
  Abs b e <- buildAbsInf hint expl ty cont
  return $ Abs (WithAttrB expl b) e

buildNaryAbsInfWithExpl
  :: (Inferer m, SinkableE e, HoistableE e, RenameE e, SubstE AtomSubstVal e, Inferer m)
  => EmitsInf n
  => [Explicitness] -> EmptyAbs (Nest CBinder) n
  -> (forall l. (EmitsInf l, DExt n l) => [CAtomVar l] -> m i l (e l))
  -> m i n (Abs (Nest (WithExpl CBinder)) e n)
buildNaryAbsInfWithExpl expls bs cont = do
  Abs bs' e <- buildNaryAbsInf expls bs cont
  return $ Abs (zipAttrs expls bs') e

buildNaryAbsInf
  :: (SinkableE e, HoistableE e, RenameE e, SubstE AtomSubstVal e, Inferer m)
  => EmitsInf n
  => [Explicitness] -> EmptyAbs (Nest CBinder) n
  -> (forall l. (EmitsInf l, DExt n l) => [CAtomVar l] -> m i l (e l))
  -> m i n (Abs (Nest CBinder) e n)
buildNaryAbsInf [] (Abs Empty UnitE) cont = getDistinct >>= \Distinct -> Abs Empty <$> cont []
buildNaryAbsInf (expl:expls) (Abs (Nest (b:>ty) bs) UnitE) cont =
  prependAbs <$> buildAbsInf (getNameHint b) expl ty \v -> do
    bs' <- applyRename (b@>atomVarName v) (Abs bs UnitE)
    buildNaryAbsInf expls bs' \vs -> cont (sink v:vs)
buildNaryAbsInf _ _ _ = error "zip error"

buildDeclsInf
  :: (SubstE AtomSubstVal e, RenameE e, Solver m, InfBuilder m)
  => (SinkableE e, HoistableE e)
  => EmitsInf n
  => (forall l. (EmitsBoth l, DExt n l) => m l (e l))
  -> m n (Abs (Nest CDecl) e n)
buildDeclsInf cont = buildDeclsInfUnzonked $ cont >>= zonk

type InfBuilder2 (m::MonadKind2) = forall i. InfBuilder (m i)

class (SubstReader Name m, InfBuilder2 m, Solver2 m)
      => Inferer (m::MonadKind2) where
  liftSolverMInf :: EmitsInf o => SolverM o a -> m i o a
  addDefault :: CAtomName o -> DefaultType -> m i o ()
  getDefaults :: m i o (Defaults o)

applyDefaults :: EmitsInf o => InfererM i o ()
applyDefaults = do
  defaults <- getDefaults
  applyDefault (intDefaults defaults) (BaseTy $ Scalar Int32Type)
  applyDefault (natDefaults defaults) NatTy
  where
    applyDefault ds ty =
      forM_ (nameSetToList ds) \v -> do
        v' <- toAtomVar v
        tryConstrainEq (Var v') (Type ty)

withApplyDefaults :: EmitsInf o => InfererM i o a -> InfererM i o a
withApplyDefaults cont = cont <* applyDefaults
{-# INLINE withApplyDefaults #-}

-- === Concrete Inferer monad ===

data InfOutMap (n::S) =
  InfOutMap
    (Env n)
    (SolverSubst n)
    (Defaults n)
    -- the subset of the names in the bindings whose definitions may contain
    -- inference vars (this is so we can avoid zonking everything in scope when
    -- we zonk bindings)
    (UnsolvedEnv n)
    -- allowed effects
    (EffectRow CoreIR n)

data DefaultType = IntDefault | NatDefault

data Defaults (n::S) = Defaults
  { intDefaults :: NameSet n   -- Set of names that should be defaulted to Int32
  , natDefaults :: NameSet n } -- Set of names that should be defaulted to Nat32

instance Semigroup (Defaults n) where
  Defaults d1 d2 <> Defaults d1' d2' = Defaults (d1 <> d1') (d2 <> d2')

instance Monoid (Defaults n) where
  mempty = Defaults mempty mempty

instance SinkableE Defaults where
  sinkingProofE _ _ = todoSinkableProof
instance HoistableE Defaults where
  freeVarsE (Defaults d1 d2) = d1 <> d2
instance RenameE Defaults where
  renameE env (Defaults d1 d2) = Defaults (substDefaultSet d1) (substDefaultSet d2)
    where
      substDefaultSet d = freeVarsE $ renameE env $ ListE $ nameSetToList @(AtomNameC CoreIR) d

instance Pretty (Defaults n) where
  pretty (Defaults ints nats) =
    attach "Names defaulting to Int32" (nameSetToList @(AtomNameC CoreIR) ints)
    <+> attach "Names defaulting to Nat32" (nameSetToList @(AtomNameC CoreIR) nats)
    where
      attach _ [] = mempty
      attach s l = s <+> pretty l

zonkDefaults :: SolverSubst n -> Defaults n -> Defaults n
zonkDefaults s (Defaults d1 d2) =
  Defaults (zonkDefaultSet d1) (zonkDefaultSet d2)
  where
    zonkDefaultSet d = flip foldMap (nameSetToList @(AtomNameC CoreIR) d) \v ->
      case lookupSolverSubst s v of
        Rename   v'       -> freeVarsE v'
        SubstVal (Var v') -> freeVarsE v'
        _ -> mempty

data InfOutFrag (n::S) (l::S) = InfOutFrag (InfEmissions n l) (Defaults l) (Constraints l)

instance Pretty (InfOutFrag n l) where
  pretty (InfOutFrag emissions defaults solverSubst) =
    vcat [ "Pending emissions:" <+> pretty (unRNest emissions)
         , "Defaults:" <+> pretty defaults
         , "Solver substitution:" <+> pretty solverSubst
         ]

type InfEmission  = EitherE (DeclBinding CoreIR) SolverBinding
type InfEmissions = RNest (BinderP (AtomNameC CoreIR) InfEmission)

instance GenericB InfOutFrag where
  type RepB InfOutFrag = PairB InfEmissions (LiftB (PairE Defaults Constraints))
  fromB (InfOutFrag emissions defaults solverSubst) =
    PairB emissions (LiftB (PairE defaults solverSubst))
  toB (PairB emissions (LiftB (PairE defaults solverSubst))) =
    InfOutFrag emissions defaults solverSubst

instance ProvesExt   InfOutFrag
instance RenameB InfOutFrag
instance BindsNames  InfOutFrag
instance SinkableB InfOutFrag
instance HoistableB  InfOutFrag

instance OutFrag InfOutFrag where
  emptyOutFrag = InfOutFrag REmpty mempty mempty
  catOutFrags (InfOutFrag em ds ss) (InfOutFrag em' ds' ss') =
    withExtEvidence em' $
      InfOutFrag (em >>> em') (sink ds <> ds') (sink ss <> ss')

instance HasScope InfOutMap where
  toScope (InfOutMap bindings _ _ _ _) = toScope bindings

instance OutMap InfOutMap where
  emptyOutMap = InfOutMap emptyOutMap emptySolverSubst mempty mempty Pure

instance ExtOutMap InfOutMap EnvFrag where
  extendOutMap (InfOutMap bindings ss dd oldUn effs) frag =
    withExtEvidence frag do
      let newUn = UnsolvedEnv $ getAtomNames frag
      let newEnv = bindings `extendOutMap` frag
      -- As an optimization, only do the zonking for the new stuff.
      let (zonkedUn, zonkedEnv) = zonkUnsolvedEnv (sink ss) newUn newEnv
      InfOutMap zonkedEnv (sink ss) (sink dd) (sink oldUn <> zonkedUn) (sink effs)

newtype UnsolvedEnv (n::S) =
  UnsolvedEnv { fromUnsolvedEnv :: S.Set (CAtomName n) }
  deriving (Semigroup, Monoid)

instance SinkableE UnsolvedEnv where
  sinkingProofE = todoSinkableProof

getAtomNames :: Distinct l => EnvFrag n l -> S.Set (CAtomName l)
getAtomNames frag = S.fromList $ nameSetToList $ toNameSet $ toScopeFrag frag

-- TODO: zonk the allowed effects and synth candidates in the bindings too
-- TODO: the reason we need this is that `getType` uses the bindings to obtain
-- type information, and we need this information when we emit decls. For
-- example, if we emit `f x` and we don't know that `f` has a type of the form
-- `a -> b` then `getType` will crash. But we control the inference-specific
-- implementation of `emitDecl`, so maybe we could instead do something like
-- emit a fresh inference variable in the case thea `getType` fails.
-- XXX: It might be tempting to add a check for empty solver substs here,
-- but please don't do that! We use this function to filter overestimates of
-- UnsolvedEnv, and for performance reasons we should do that even when the
-- SolverSubst is empty.
zonkUnsolvedEnv :: Distinct n => SolverSubst n -> UnsolvedEnv n -> Env n
                -> (UnsolvedEnv n, Env n)
zonkUnsolvedEnv ss unsolved env =
  flip runState env $ execWriterT do
    forM_ (S.toList $ fromUnsolvedEnv unsolved) \v -> do
      flip lookupEnvPure v . topEnv <$> get >>= \case
        AtomNameBinding rhs -> do
          let rhs' = zonkAtomBindingWithOutMap (InfOutMap env ss mempty mempty Pure) rhs
          modify \e -> e {topEnv = updateEnv v (AtomNameBinding rhs') (topEnv e)}
          let rhsHasInfVars = runEnvReaderM env $ hasInferenceVars rhs'
          when rhsHasInfVars $ tell $ UnsolvedEnv $ S.singleton v

-- TODO: we need this shim because top level emissions can't implement `SubstE
-- AtomSubstVal` so GHC doesn't know how to zonk them. If we split up top-level
-- emissions from local ones in the name color system then we won't have this
-- problem.
zonkAtomBindingWithOutMap
  :: Distinct n => InfOutMap n -> AtomBinding CoreIR n -> AtomBinding CoreIR n
zonkAtomBindingWithOutMap outMap = \case
 LetBound    e -> LetBound    $ zonkWithOutMap outMap e
 MiscBound   e -> MiscBound   $ zonkWithOutMap outMap e
 SolverBound e -> SolverBound $ zonkWithOutMap outMap e
 NoinlineFun t e -> NoinlineFun (zonkWithOutMap outMap t) (zonkWithOutMap outMap e)
 FFIFunBound x y -> FFIFunBound (zonkWithOutMap outMap x) (zonkWithOutMap outMap y)

-- TODO: Wouldn't it be faster to carry the set of inference-emitted names in the out map?
hasInferenceVars :: (EnvReader m, HoistableE e) => e n -> m n Bool
hasInferenceVars e = liftEnvReaderM $ anyInferenceVars $ freeAtomVarsList e
{-# INLINE hasInferenceVars #-}

anyInferenceVars :: [CAtomName n] -> EnvReaderM n Bool
anyInferenceVars = \case
  [] -> return False
  (v:vs) -> isInferenceVar v >>= \case
    True  -> return True
    False -> anyInferenceVars vs

isInferenceVar :: EnvReader m => CAtomName n -> m n Bool
isInferenceVar v = lookupEnv v >>= \case
  AtomNameBinding (SolverBound _) -> return True
  _                               -> return False

instance ExtOutMap InfOutMap InfOutFrag where
  extendOutMap m (InfOutFrag em ds' cs) = do
    let InfOutMap env ss ds us effs = m `extendOutMap` toEnvFrag em
    let ds'' = sink ds <> ds'
    let (env', us', ss') = extendOutMapWithConstraints env us ss cs
    InfOutMap env' ss' ds'' us' effs

extendOutMapWithConstraints
  :: Distinct n => Env n -> UnsolvedEnv n -> SolverSubst n -> Constraints n
  -> (Env n, UnsolvedEnv n, SolverSubst n)
extendOutMapWithConstraints env us ss (Constraints allCs) = case tryUnsnoc allCs of
  Nothing -> (env, us, ss)
  Just (cs, (v, x)) -> do
    let (env', us', SolverSubst ss') = extendOutMapWithConstraints env us ss (Constraints cs)
    let s = M.singleton v x
    let (us'', env'') = zonkUnsolvedEnv (SolverSubst s) us' env'
    let ss'' = fmap (applySolverSubstE env'' (SolverSubst s)) ss'
    let ss''' = SolverSubst $ ss'' <> s
    (env'', us'', ss''')

newtype InfererM (i::S) (o::S) (a:: *) = InfererM
  { runInfererM' :: SubstReaderT Name (InplaceT InfOutMap InfOutFrag FallibleM) i o a }
  deriving (Functor, Applicative, Monad, MonadFail,
            ScopeReader, Fallible, Catchable, CtxReader, SubstReader Name)

liftInfererMSubst :: (Fallible2 m, SubstReader Name m, EnvReader2 m)
                  => InfererM i o a -> m i o a
liftInfererMSubst cont = do
  env <- unsafeGetEnv
  subst <- getSubst
  Distinct <- getDistinct
  (InfOutFrag REmpty _ _, result) <-
    liftExcept $ runFallibleM $ runInplaceT (initInfOutMap env) $
      runSubstReaderT subst $ runInfererM' $ cont
  return result

liftInfererM :: (EnvReader m, Fallible1 m)
             => InfererM n n a -> m n a
liftInfererM cont = runSubstReaderT idSubst $ liftInfererMSubst $ cont
{-# INLINE liftInfererM #-}

runLocalInfererM
  :: SinkableE e
  => (forall l. (EmitsInf l, DExt n l) => InfererM i l (e l))
  -> InfererM i n (Abs InfOutFrag e n)
runLocalInfererM cont = InfererM $ SubstReaderT $ ReaderT \env -> do
  locallyMutableInplaceT (do
    Distinct <- getDistinct
    EmitsInf <- fabricateEmitsInfEvidenceM
    runSubstReaderT (sink env) $ runInfererM' cont)
    (\d e -> return $ Abs d e)
{-# INLINE runLocalInfererM #-}

initInfOutMap :: Env n -> InfOutMap n
initInfOutMap bindings =
  InfOutMap bindings emptySolverSubst mempty (UnsolvedEnv mempty) Pure

newtype InfDeclEmission (n::S) (l::S) = InfDeclEmission (BinderP (AtomNameC CoreIR) InfEmission n l)
instance ExtOutMap InfOutMap InfDeclEmission where
  extendOutMap env (InfDeclEmission d) = env `extendOutMap` toEnvFrag d
  {-# INLINE extendOutMap #-}
instance ExtOutFrag InfOutFrag InfDeclEmission where
  extendOutFrag (InfOutFrag ems ds ss) (InfDeclEmission em) =
    withSubscopeDistinct em $ InfOutFrag (RNest ems em) (sink ds) (sink ss)
  {-# INLINE extendOutFrag #-}

emitInfererM :: Mut o => NameHint -> InfEmission o -> InfererM i o (CAtomVar o)
emitInfererM hint emission = do
  v <- InfererM $ SubstReaderT $ lift $ freshExtendSubInplaceT hint \b ->
    (InfDeclEmission (b :> emission), binderName b)
  return $ AtomVar v $ getType emission
{-# INLINE emitInfererM #-}

instance Solver (InfererM i) where
  extendSolverSubst v ty = do
   InfererM $ SubstReaderT $ lift $
     void $ extendTrivialInplaceT $
       InfOutFrag REmpty mempty (singleConstraint v ty)
  {-# INLINE extendSolverSubst #-}

  zonk e = InfererM $ SubstReaderT $ lift do
    Distinct <- getDistinct
    solverOutMap <- getOutMapInplaceT
    return $ zonkWithOutMap solverOutMap e
  {-# INLINE zonk #-}

  emitSolver binding = emitInfererM (getNameHint @String "?") $ RightE binding
  {-# INLINE emitSolver #-}

  solveLocal cont = do
    Abs (InfOutFrag unsolvedInfVars _ _) result <- dceInfFrag =<< runLocalInfererM cont
    case unRNest unsolvedInfVars of
      Empty -> return result
      Nest (b:>RightE (InfVarBound ty (ctx, desc))) _ -> addSrcContext ctx $
        throw TypeErr $ formatAmbiguousVarErr (binderName b) ty desc
      _ -> error "shouldn't be possible"

formatAmbiguousVarErr :: CAtomName n -> CType n' -> InfVarDesc -> String
formatAmbiguousVarErr infVar ty = \case
  AnnotationInfVar v ->
    "Couldn't infer type of unannotated binder " <> v
  ImplicitArgInfVar (f, argName) ->
    "Couldn't infer implicit argument " <> argName <> " of " <> f
  TypeInstantiationInfVar t ->
    "Couldn't infer instantiation of type " <> t
  MiscInfVar ->
    "Ambiguous type variable: " ++ pprint infVar ++ ": " ++ pprint ty

instance InfBuilder (InfererM i) where
  buildDeclsInfUnzonked cont = do
    InfererM $ SubstReaderT $ ReaderT \env -> do
      Abs frag result <- locallyMutableInplaceT (do
        Emits    <- fabricateEmitsEvidenceM
        EmitsInf <- fabricateEmitsInfEvidenceM
        runSubstReaderT (sink env) $ runInfererM' cont)
        (\d e -> return $ Abs d e)
      extendInplaceT =<< hoistThroughDecls frag result

  buildAbsInf hint expl ty cont = do
    ab <- InfererM $ SubstReaderT $ ReaderT \env -> do
      extendInplaceT =<< withFreshBinder hint ty \bWithTy@(b:>_) -> do
        ab <- locallyMutableInplaceT (do
          v <- sinkM $ binderVar bWithTy
          extendInplaceTLocal (extendSynthCandidatesInf expl $ atomVarName v) do
            EmitsInf <- fabricateEmitsInfEvidenceM
            -- zonking is needed so that dceInfFrag works properly
            runSubstReaderT (sink env) (runInfererM' $ cont v >>= zonk))
          (\d e -> return $ Abs d e)
        ab' <- dceInfFrag ab
        refreshAbs ab' \infFrag result -> do
          case exchangeBs $ PairB b infFrag of
            HoistSuccess (PairB infFrag' b') -> do
              return $ withSubscopeDistinct b' $
                Abs infFrag' $ Abs b' result
            HoistFailure vs -> do
              throw EscapedNameErr $ (pprint vs)
                ++ "\nFailed to exchange binders in buildAbsInf"
                ++ "\n" ++ pprint infFrag
    Abs b e <- return ab
    ty' <- zonk ty
    return $ Abs (b:>ty') e

dceInfFrag
  :: (EnvReader m, EnvExtender m, Fallible1 m, RenameE e, HoistableE e)
  => Abs InfOutFrag e n -> m n (Abs InfOutFrag e n)
dceInfFrag ab@(Abs frag@(InfOutFrag bs _ _) e) =
  case bs of
    REmpty -> return ab
    _ -> hoistThroughDecls frag e >>= \case
      Abs frag' (Abs Empty e') -> return $ Abs frag' e'
      _ -> error "Shouldn't have any decls without `Emits` constraint"

instance Inferer InfererM where
  liftSolverMInf m = InfererM $ SubstReaderT $ lift $
    liftBetweenInplaceTs (liftExcept . liftM fromJust . runSearcherM) id liftSolverOutFrag $
      runSolverM' m
  {-# INLINE liftSolverMInf #-}

  addDefault v defaultType =
    InfererM $ SubstReaderT $ lift $
      extendTrivialInplaceT $ InfOutFrag REmpty defaults mempty
    where
      defaults = case defaultType of
        IntDefault -> Defaults (freeVarsE v) mempty
        NatDefault -> Defaults mempty (freeVarsE v)

  getDefaults = InfererM $ SubstReaderT $ lift do
    InfOutMap _ _ defaults _ _ <- getOutMapInplaceT
    return defaults

instance Builder CoreIR (InfererM i) where
  rawEmitDecl hint ann expr = do
    -- This zonking, and the zonking of the bindings elsewhere, is only to
    -- prevent `getType` from failing. But maybe we should just catch the
    -- failure if it occurs and generate a fresh inference name for the type in
    -- that case?
    expr' <- zonk expr
    emitInfererM hint $ LeftE $ DeclBinding ann expr'
  {-# INLINE rawEmitDecl #-}

getAllowedEffects :: InfererM i n (EffectRow CoreIR n)
getAllowedEffects = do
  InfOutMap _ _ _ _ effs <- InfererM $ SubstReaderT $ lift $ getOutMapInplaceT
  return effs

withoutEffects :: InfererM i o a -> InfererM i o a
withoutEffects cont = withAllowedEffects Pure cont

withAllowedEffects :: EffectRow CoreIR o -> InfererM i o a -> InfererM i o a
withAllowedEffects effs cont = do
  InfererM $ SubstReaderT $ ReaderT \env -> do
    extendInplaceTLocal (\(InfOutMap x y z w _) -> InfOutMap x y z w effs) do
      runSubstReaderT env $ runInfererM' do
        cont

type InferenceNameBinders = Nest (BinderP (AtomNameC CoreIR) SolverBinding)

-- When we finish building a block of decls we need to hoist the local solver
-- information into the outer scope. If the local solver state mentions local
-- variables which are about to go out of scope then we emit a "escaped scope"
-- error. To avoid false positives, we clean up as much dead (i.e. solved)
-- solver state as possible.
hoistThroughDecls
  :: ( RenameE e, HoistableE e, Fallible1 m, ScopeReader m, EnvExtender m)
  => InfOutFrag n l
  ->   e l
  -> m n (Abs InfOutFrag (Abs (Nest CDecl) e) n)
hoistThroughDecls outFrag result = do
  env <- unsafeGetEnv
  refreshAbs (Abs outFrag result) \outFrag' result' -> do
    liftExcept $ hoistThroughDecls' env outFrag' result'
{-# INLINE hoistThroughDecls #-}

hoistThroughDecls'
  :: (HoistableE e, Distinct l)
  => Env n
  -> InfOutFrag n l
  ->   e l
  -> Except (Abs InfOutFrag (Abs (Nest CDecl) e) n)
hoistThroughDecls' env (InfOutFrag emissions defaults constraints) result = do
  withSubscopeDistinct emissions do
    let subst = constraintsToSubst (env `extendOutMap` toEnvFrag emissions) constraints
    HoistedSolverState infVars defaults' subst' decls result' <-
      hoistInfStateRec env emissions emptyInferenceNameBindersFV
        (zonkDefaults subst defaults) (UnhoistedSolverSubst emptyOutFrag subst) Empty result
    let constraints' = substToConstraints subst'
    let hoistedInfFrag = InfOutFrag (infNamesToEmissions infVars) defaults' constraints'
    return $ Abs hoistedInfFrag $ Abs decls result'

constraintsToSubst :: Distinct n => Env n -> Constraints n -> SolverSubst n
constraintsToSubst env (Constraints csTop) = case tryUnsnoc csTop of
  Nothing -> emptySolverSubst
  Just (cs, (v, x)) -> do
    let SolverSubst m = constraintsToSubst env (Constraints cs)
    let s = M.singleton v x
    SolverSubst $ fmap (applySolverSubstE env (SolverSubst s)) m <> s

substToConstraints :: SolverSubst n -> Constraints n
substToConstraints (SolverSubst m) = Constraints $ toSnocList $ M.toList m

data HoistedSolverState e n where
  HoistedSolverState
    :: InferenceNameBinders n l1
    ->   Defaults l1
    ->   SolverSubst l1
    ->   Nest CDecl l1 l2
    ->     e l2
    -> HoistedSolverState e n

-- XXX: Be careful how you construct DelayedSolveNests! When the substitution is
-- applied, the pieces are concatenated through regular map concatenation, not
-- through recursive substitutions as in catSolverSubsts! This is safe to do when
-- the individual SolverSubsts come from a projection of a larger SolverSubst,
-- which is how we use them in `hoistInfStateRec`.
type DelayedSolveNest (b::B) (n::S) (l::S) = Nest (EitherB b (LiftB SolverSubst)) n l

resolveDelayedSolve :: Distinct l => Env n -> SolverSubst n -> DelayedSolveNest CDecl n l -> Nest CDecl n l
resolveDelayedSolve env subst = \case
  Empty -> Empty
  Nest (RightB (LiftB sfrag)) rest -> resolveDelayedSolve env (subst `unsafeCatSolverSubst` sfrag) rest
  Nest (LeftB  (Let b rhs)  ) rest ->
    withSubscopeDistinct rest $ withSubscopeDistinct b $
      Nest (Let b (applySolverSubstE env subst rhs)) $
        resolveDelayedSolve (env `extendOutMap` toEnvFrag (b:>rhs)) (sink subst) rest
  where
    unsafeCatSolverSubst :: SolverSubst n -> SolverSubst n -> SolverSubst n
    unsafeCatSolverSubst (SolverSubst a) (SolverSubst b) = SolverSubst $ a <> b

data InferenceNameBindersFV (n::S) (l::S) = InferenceNameBindersFV (NameSet n) (InferenceNameBinders n l)
instance BindsNames InferenceNameBindersFV where
  toScopeFrag = toScopeFrag . dropInferenceNameBindersFV
instance BindsEnv InferenceNameBindersFV where
  toEnvFrag = toEnvFrag . dropInferenceNameBindersFV
instance ProvesExt InferenceNameBindersFV where
  toExtEvidence = toExtEvidence . dropInferenceNameBindersFV
instance HoistableB InferenceNameBindersFV where
  freeVarsB (InferenceNameBindersFV fvs _) = fvs

emptyInferenceNameBindersFV :: InferenceNameBindersFV n n
emptyInferenceNameBindersFV = InferenceNameBindersFV mempty Empty

dropInferenceNameBindersFV :: InferenceNameBindersFV n l -> InferenceNameBinders n l
dropInferenceNameBindersFV (InferenceNameBindersFV _ bs) = bs

prependNameBinder
  :: BinderP (AtomNameC CoreIR) SolverBinding n q
  -> InferenceNameBindersFV q l -> InferenceNameBindersFV n l
prependNameBinder b (InferenceNameBindersFV fvs bs) =
  InferenceNameBindersFV (freeVarsB b <> hoistFilterNameSet b fvs) (Nest b bs)

-- XXX: Stashing Distinct here is a little naughty, since that's generally not allowed.
-- Here it should be ok, because it's only used in hoistInfStateRec, which doesn't emit.
data UnhoistedSolverSubst (n::S) where
  UnhoistedSolverSubst :: Distinct l => ScopeFrag n l -> SolverSubst l -> UnhoistedSolverSubst n

delayedHoistSolverSubst :: BindsNames b => b n l -> UnhoistedSolverSubst l -> UnhoistedSolverSubst n
delayedHoistSolverSubst b (UnhoistedSolverSubst frag s) = UnhoistedSolverSubst (toScopeFrag b >>> frag) s

hoistSolverSubst :: UnhoistedSolverSubst n -> HoistExcept (SolverSubst n)
hoistSolverSubst (UnhoistedSolverSubst frag s) = hoist frag s

-- TODO: Instead of delaying the solve, compute the most-nested scope once
-- and then use it for all _eager_ substitutions while hoisting! Using a super-scope
-- for substitution shouldn't be a problem!
hoistInfStateRec
  :: forall n l l1 l2 e. (Distinct n, Distinct l2, HoistableE e)
  => Env n -> InfEmissions n l
  -> InferenceNameBindersFV l l1 -> Defaults l1 -> UnhoistedSolverSubst l1
  -> DelayedSolveNest CDecl l1 l2 -> e l2
  -> Except (HoistedSolverState e n)
hoistInfStateRec env emissions !infVars defaults !subst decls e = case emissions of
 REmpty -> do
  subst' <- liftHoistExcept' "Failed to hoist solver substitution in hoistInfStateRec"
    $ hoistSolverSubst subst
  let decls' = withSubscopeDistinct decls $
                 resolveDelayedSolve (env `extendOutMap` toEnvFrag infVars) subst' decls
  return $ HoistedSolverState (dropInferenceNameBindersFV infVars) defaults subst' decls' e
 RNest rest (b :> infEmission) -> do
  withSubscopeDistinct decls do
    case infEmission of
      RightE binding@(InfVarBound _ _) -> do
        UnhoistedSolverSubst frag (SolverSubst substMap) <- return subst
        let vHoist :: CAtomName l1 = withSubscopeDistinct infVars $ sink $ binderName b  -- binder name at l1
        let vUnhoist = withExtEvidence frag $ sink vHoist                               -- binder name below frag
        case M.lookup vUnhoist substMap of
          -- Unsolved inference variables are just gathered as they are.
          Nothing ->
            hoistInfStateRec env rest (prependNameBinder (b:>binding) infVars)
                             defaults subst decls e
          -- If a variable is solved, we eliminate it.
          Just bSolutionUnhoisted -> do
            bSolution <-
              liftHoistExcept' "Failed to eliminate solved variable in hoistInfStateRec "
                $ hoist frag bSolutionUnhoisted
            case exchangeBs $ PairB b infVars of
              -- This used to be accepted by the code at some point (and handled the same way
              -- as the Nothing) branch above, but I don't understand why. We don't even seem
              -- to be exercising it anyway, so throw a not implemented error for now.
              HoistFailure _ -> throw NotImplementedErr "Unzonked unsolved variables"
              HoistSuccess (PairB infVars' b') -> do
                let defaults' = hoistDefaults b' defaults
                let bZonkedDecls = Nest (RightB (LiftB $ SolverSubst $ M.singleton vHoist bSolution)) decls
#ifdef DEX_DEBUG
                -- Hoist the subst eagerly, unlike the unsafe implementation.
                hoistedSubst@(SolverSubst hoistMap) <- liftHoistExcept $ hoistSolverSubst subst
                let subst' = withSubscopeDistinct b' $ UnhoistedSolverSubst (toScopeFrag b') $
                               SolverSubst $ M.delete vHoist hoistMap
                -- Zonk the decls with `v @> bSolution` to make sure hoisting will succeed.
                -- This is quadratic, which is why we don't do this in the fast implementation!
                let allEmissions = RNest rest (b :> infEmission)
                let declsScope = withSubscopeDistinct infVars $
                      (env `extendOutMap` toEnvFrag allEmissions) `extendOutMap` toEnvFrag infVars
                let resolvedDecls = resolveDelayedSolve declsScope hoistedSubst bZonkedDecls
                PairB resolvedDecls' b'' <- liftHoistExcept $ exchangeBs $ PairB b' resolvedDecls
                let decls' = fmapNest LeftB resolvedDecls'
                -- NB: We assume that e is hoistable above e! This has to be taken
                -- care of by zonking the result before this function is entered.
                e' <- liftHoistExcept $ hoist b'' e
                withSubscopeDistinct b'' $
                  hoistInfStateRec env rest infVars' defaults' subst' decls' e'
#else
                -- SolverSubst should be recursively zonked, so any v that's a member
                -- should never appear in an rhs. Hence, deleting the entry corresponding to
                -- v should hoist the substitution above b'.
                let subst' = unsafeCoerceE $ UnhoistedSolverSubst frag $ SolverSubst $ M.delete vUnhoist substMap
                -- Applying the substitution `v @> bSolution` would eliminate `b` from decls, so this
                -- is equivalent to hoisting above b'. This is of course not reflected in the type
                -- system, which is why we use unsafe coercions.
                let decls' = unsafeCoerceB bZonkedDecls
                -- This is much more sketchy, but it reflects the e-hoistability assumption
                -- that our safe implementation makes as well. Except here it's obviously unchecked.
                let e' :: e UnsafeS = unsafeCoerceE e
                Distinct <- return $ fabricateDistinctEvidence @UnsafeS
                hoistInfStateRec env rest infVars' defaults' subst' decls' e'
#endif
      RightE (SkolemBound _) -> do
#ifdef DEX_DEBUG
        PairB infVars' b' <- liftHoistExcept' "Skolem leak?" $ exchangeBs $ PairB b infVars
        defaults' <- liftHoistExcept' "Skolem leak?" $ hoist b' defaults
        let subst' = delayedHoistSolverSubst b' subst
        PairB decls' b'' <- liftHoistExcept' "Skolem leak?" $ exchangeBs $ PairB b' decls
        e' <- liftHoistExcept' "Skolem leak?" $ hoist b'' e
        withSubscopeDistinct b'' $ hoistInfStateRec env rest infVars' defaults' subst' decls' e'
#else
        -- Skolem vars are only instantiated in unification, and we're very careful to
        -- never let them leak into the types of inference vars emitted while unifying
        -- and into the solver subst.
        Distinct <- return $ fabricateDistinctEvidence @UnsafeS
        hoistInfStateRec @n @UnsafeS @UnsafeS @UnsafeS
          env
          (unsafeCoerceB rest) (unsafeCoerceB infVars)
          (unsafeCoerceE defaults) (unsafeCoerceE subst)
          (unsafeCoerceB decls) (unsafeCoerceE e)
#endif
      LeftE emission -> do
        -- Move the binder below all unsolved inference vars. Failure to do so is
        -- an inference error --- a variable cannot be solved once we exit the env
        -- of all variables it mentions in its type.
        -- TODO: Shouldn't this be an ambiguous type error?
        PairB infVars' (b':>emission') <-
          liftHoistExcept' "Failed to move binder below unsovled inference vars"
            $ exchangeBs (PairB (b:>emission) infVars)
        -- Now, those are real leakage errors. We never want to leak this var through a solution!
        -- But since we delay hoisting, they will only be raised later.
        let subst' = delayedHoistSolverSubst b' subst
        let defaults' = hoistDefaults b' defaults
        let decls' = Nest (LeftB (Let b' emission')) decls
        hoistInfStateRec env rest infVars' defaults' subst' decls' e

hoistDefaults :: BindsNames b => b n l -> Defaults l -> Defaults n
hoistDefaults b (Defaults d1 d2) = Defaults (hoistFilterNameSet b d1)
                                            (hoistFilterNameSet b d2)

infNamesToEmissions :: InferenceNameBinders n l -> InfEmissions n l
infNamesToEmissions = go REmpty
 where
   go :: InfEmissions n q -> InferenceNameBinders q l -> InfEmissions n l
   go acc = \case
     Empty -> acc
     Nest (b:>binding) rest -> go (RNest acc (b:>RightE binding)) rest

instance EnvReader (InfererM i) where
  unsafeGetEnv = do
    InfOutMap bindings _ _ _ _ <- InfererM $ SubstReaderT $ lift $ getOutMapInplaceT
    return bindings
  {-# INLINE unsafeGetEnv #-}

instance EnvExtender (InfererM i) where
  refreshAbs ab cont = InfererM $ SubstReaderT $ ReaderT \env -> do
    refreshAbs ab \b e -> runSubstReaderT (sink env) $ runInfererM' $ cont b e
  {-# INLINE refreshAbs #-}

-- === helpers for extending synthesis candidates ===

-- TODO: we should pull synth candidates out of the Env and then we can treat it
-- like an ordinary reader without all this ceremony.

extendSynthCandidatesInf :: Explicitness -> CAtomName n -> InfOutMap n -> InfOutMap n
extendSynthCandidatesInf c v (InfOutMap env x y z w) =
  InfOutMap (extendSynthCandidates c v env) x y z w
{-# INLINE extendSynthCandidatesInf #-}

extendSynthCandidates :: Explicitness -> CAtomName n -> Env n -> Env n
extendSynthCandidates (Inferred _ (Synth _)) v (Env topEnv (ModuleEnv a b scs)) =
  Env topEnv (ModuleEnv a b scs')
  where scs' = scs <> SynthCandidates [v] mempty
extendSynthCandidates _ _ env = env
{-# INLINE extendSynthCandidates #-}

extendSynthCandidatess :: Distinct n => [Explicitness] -> Nest CBinder n' n -> Env n -> Env n
extendSynthCandidatess (expl:expls) (Nest b bs) env =
  extendSynthCandidatess expls bs env'
  where env' = extendSynthCandidates expl (withExtEvidence bs $ sink $ binderName b) env
extendSynthCandidatess [] Empty env = env
extendSynthCandidatess _ _ _ = error "zip error"
{-# INLINE extendSynthCandidatess #-}

-- === actual inference pass ===

data RequiredTy (e::E) (n::S) =
   Check (e n)
 | Infer
   deriving Show

checkSigma :: EmitsBoth o
           => NameHint -> UExpr i -> CType o -> InfererM i o (CAtom o)
checkSigma hint expr sTy = confuseGHC >>= \_ -> case sTy of
  Pi piTy@(CorePiType _ expls _ _) -> do
    if all (== Explicit) expls
      then fallback
      else case expr of
        WithSrcE src (ULam lam) -> addSrcContext src $ Lam <$> checkULam lam piTy
        _ -> Lam <$> buildLamInf piTy \args resultTy -> do
          explicits <- return $ catMaybes $ args <&> \case
            (Explicit, arg) -> Just arg
            _ -> Nothing
          expr' <- inferWithoutInstantiation expr >>= zonk
          dropSubst $ checkOrInferApp expr' explicits [] (Check resultTy)
  DepPairTy depPairTy -> case depPairTy of
    DepPairType ImplicitDepPair (_ :> lhsTy) _ -> do
      -- TODO: check for the case that we're given some of the implicit dependent pair args explicitly
      lhsVal <- Var <$> freshInferenceName MiscInfVar lhsTy
      -- TODO: make an InfVarDesc case for dep pair instantiation
      rhsTy <- instantiate depPairTy [lhsVal]
      rhsVal <- checkSigma noHint expr rhsTy
      return $ DepPair lhsVal rhsVal depPairTy
    _ -> fallback
  _ -> fallback
  where fallback = checkOrInferRho hint expr (Check sTy)

inferSigma :: EmitsBoth o => NameHint -> UExpr i -> InfererM i o (CAtom o)
inferSigma hint (WithSrcE pos expr) = case expr of
  ULam lam -> addSrcContext pos $ Lam <$> inferULam lam
  _ -> inferRho hint (WithSrcE pos expr)

checkRho :: EmitsBoth o =>
  NameHint -> UExpr i -> CType o -> InfererM i o (CAtom o)
checkRho hint expr ty = checkOrInferRho hint expr (Check ty)
{-# INLINE checkRho #-}

inferRho :: EmitsBoth o =>
  NameHint -> UExpr i -> InfererM i o (CAtom o)
inferRho hint expr = checkOrInferRho hint expr Infer
{-# INLINE inferRho #-}

getImplicitArg :: EmitsInf o => InferenceArgDesc -> InferenceMechanism -> CType o -> InfererM i o (CAtom o)
getImplicitArg desc inf argTy = case inf of
  Unify -> Var <$> freshInferenceName (ImplicitArgInfVar desc) argTy
  Synth reqMethodAccess -> do
    ctx <- srcPosCtx <$> getErrCtx
    return $ DictHole (AlwaysEqual ctx) argTy reqMethodAccess

withBlockDecls
  :: EmitsBoth o
  => UBlock i -> (forall i'. UExpr i' -> InfererM i' o a) -> InfererM i o a
withBlockDecls (WithSrcE src (UBlock declsTop result)) contTop =
  addSrcContext src $ go declsTop $ contTop result where
  go :: EmitsBoth o => Nest UDecl i i' -> InfererM i' o a -> InfererM i  o a
  go decls cont = case decls of
    Empty -> cont
    Nest d ds -> withUDecl d $ go ds $ cont

withUDecl
  :: EmitsBoth o
  => UDecl i i'
  -> InfererM i' o a
  -> InfererM i  o a
withUDecl (WithSrcB src d) cont = addSrcContext src case d of
  UPass -> cont
  UExprDecl e -> inferSigma noHint e >> cont
  ULet letAnn p ann rhs -> do
    val <- checkMaybeAnnExpr (getNameHint p) ann rhs
    var <- emitDecl (getNameHint p) letAnn $ Atom val
    bindLetPat p var cont

-- "rho" means the required type here should not be (at the top level) an implicit pi type or
-- an implicit dependent pair type. We don't want to unify those directly.
-- The name hint names the object being computed
checkOrInferRho
  :: forall i o. EmitsBoth o
  => NameHint -> UExpr i -> RequiredTy CType o -> InfererM i o (CAtom o)
checkOrInferRho hint uExprWithSrc@(WithSrcE pos expr) reqTy = do
 addSrcContext pos $ confuseGHC >>= \_ -> case expr of
  UVar _ -> inferAndInstantiate
  ULit l -> matchRequirement $ Con $ Lit l
  ULam lamExpr -> do
    case reqTy of
      Check (Pi piTy) -> Lam <$> checkULam lamExpr piTy
      Check _ -> Lam <$> inferULam lamExpr >>= matchRequirement
      Infer   -> Lam <$> inferULam lamExpr
  UFor dir uFor -> do
    lam@(UnaryLamExpr b' _) <- case reqTy of
      Check (TabPi tabPiTy) -> do checkUForExpr uFor tabPiTy
      Check _ -> inferUForExpr uFor
      Infer   -> inferUForExpr uFor
    ixTy <- asIxType $ binderType b'
    result <- emitHof $ For dir ixTy lam
    matchRequirement result
  UApp f posArgs namedArgs -> do
    f' <- inferWithoutInstantiation f >>= zonk
    checkOrInferApp f' posArgs namedArgs reqTy
  UTabApp tab args -> do
    tab' <- inferRho noHint tab >>= zonk
    inferTabApp (srcPos tab) tab' args >>= matchRequirement
  UPi (UPiExpr bs appExpl effs ty) -> do
    -- TODO: check explicitness constraints
    ab <- withUBinders bs \_ -> EffTy <$> checkUEffRow effs <*> checkUType ty
    Abs bs' effTy' <- return ab
    let (expls, bs'') = unzipAttrs bs'
    matchRequirement $ Type $ Pi $ CorePiType appExpl expls bs'' effTy'
  UTabPi (UTabPiExpr (UAnnBinder b ann cs) ty) -> do
    unless (null cs) $ throw TypeErr "`=>` shouldn't have constraints"
    ann' <- asIxType =<< checkAnn (getSourceName b) ann
    piTy <- case b of
      UIgnore ->
        buildTabPiInf noHint ann' \_ -> checkUType ty
      _ -> buildTabPiInf (getNameHint b) ann' \v -> extendRenamer (b@>atomVarName v) do
        let msg =  "Can't reduce type expression: " ++ docAsStr (pretty ty)
        Type rhs <- withReducibleEmissions msg $ Type <$> checkUType ty
        return rhs
    matchRequirement $ Type $ TabPi piTy
  UDepPairTy (UDepPairType expl (UAnnBinder b ann cs) rhs) -> do
    unless (null cs) $ throw TypeErr "Dependent pair binders shouldn't have constraints"
    ann' <- checkAnn (getSourceName b) ann
    matchRequirement =<< liftM (Type . DepPairTy) do
      buildDepPairTyInf (getNameHint b) expl ann' \v -> extendRenamer (b@>atomVarName v) do
        let msg =  "Can't reduce type expression: " ++ docAsStr (pretty rhs)
        withReducibleEmissions msg $ checkUType rhs
  UDepPair lhs rhs -> do
    case reqTy of
      Check (DepPairTy ty@(DepPairType _ (_ :> lhsTy) _)) -> do
        lhs' <- checkSigmaDependent noHint lhs lhsTy
        rhsTy <- instantiate ty [lhs']
        rhs' <- checkSigma noHint rhs rhsTy
        return $ DepPair lhs' rhs' ty
      _ -> throw TypeErr $ "Can't infer the type of a dependent pair; please annotate it"
  UCase scrut alts -> do
    scrut' <- inferRho noHint scrut
    scrutTy <- return $ getType scrut'
    reqTy' <- case reqTy of
      Infer -> freshType
      Check req -> return req
    alts' <- mapM (checkCaseAlt reqTy' scrutTy) alts
    scrut'' <- zonk scrut'
    buildSortedCase scrut'' alts' reqTy'
  UDo block -> withBlockDecls block \result -> checkOrInferRho hint result reqTy
  UTabCon xs -> inferTabCon hint xs reqTy >>= matchRequirement
  UHole -> case reqTy of
    Infer -> throw MiscErr "Can't infer type of hole"
    Check ty -> freshAtom ty
  UTypeAnn val ty -> do
    ty' <- zonk =<< checkUType ty
    val' <- checkSigma hint val ty'
    matchRequirement val'
  UPrim UTuple xs -> case reqTy of
    Check TyKind -> Type . ProdTy <$> mapM checkUType xs
    _ -> do
      xs' <- mapM (inferRho noHint) xs
      matchRequirement $ ProdVal xs'
  UPrim UMonoLiteral [WithSrcE _ l] -> case l of
    UIntLit x -> matchRequirement $ Con $ Lit $ Int32Lit $ fromIntegral x
    UNatLit x -> matchRequirement $ Con $ Lit $ Word32Lit $ fromIntegral x
    _ -> throw MiscErr "argument to %monoLit must be a literal"
  UPrim UExplicitApply (f:xs) -> do
    f' <- inferWithoutInstantiation f
    xs' <- mapM (inferRho noHint) xs
    applySigmaAtom f' xs' >>= matchRequirement
  UPrim UProjNewtype [x] -> do
    x' <- inferRho hint x >>= emitHinted hint . Atom
    unwrapNewtype $ Var x'
  UPrim prim xs -> do
    xs' <- forM xs \x -> do
      inferPrimArg x >>= \case
        Var v -> lookupAtomName (atomVarName v) >>= \case
          LetBound (DeclBinding _ (Atom e)) -> return e
          _ -> return $ Var v
        x' -> return x'
    matchRequirement =<< matchPrimApp prim xs'
  UFieldAccess _ _ -> inferAndInstantiate
  UNatLit x -> do
    let defaultVal = Con $ Lit $ Word32Lit $ fromIntegral x
    let litVal     = Con $ Lit $ Word64Lit $ fromIntegral x
    matchRequirement =<< applyFromLiteralMethod "from_unsigned_integer" defaultVal NatDefault litVal
  UIntLit x  -> do
    let defaultVal = Con $ Lit $ Int32Lit $ fromIntegral x
    let litVal     = Con $ Lit $ Int64Lit $ fromIntegral x
    matchRequirement =<< applyFromLiteralMethod "from_integer" defaultVal IntDefault litVal
  UFloatLit x -> matchRequirement $ Con $ Lit  $ Float32Lit $ realToFrac x
  -- TODO: Make sure that this conversion is not lossy!
  where
    matchRequirement :: CAtom o -> InfererM i o (CAtom o)
    matchRequirement x = return x <*
      case reqTy of
        Infer -> return ()
        Check req -> do
          ty <- return $ getType x
          constrainTypesEq req ty
    {-# INLINE matchRequirement #-}

    inferAndInstantiate :: InfererM i o (CAtom o)
    inferAndInstantiate = do
      sigmaAtom <- maybeInterpretPunsAsTyCons reqTy =<< inferWithoutInstantiation uExprWithSrc
      instantiateSigma sigmaAtom >>= matchRequirement
    {-# INLINE inferAndInstantiate #-}

applyFromLiteralMethod :: EmitsBoth n => SourceName -> CAtom n -> DefaultType -> CAtom n -> InfererM i n (CAtom n)
applyFromLiteralMethod methodName defaultVal defaultTy litVal = do
  lookupSourceMap methodName >>= \case
    Nothing -> return defaultVal
    Just ~(UMethodVar methodName') -> do
      MethodBinding className _ <- lookupEnv methodName'
      resultTyVar <- freshInferenceName MiscInfVar TyKind
      dictTy <- DictTy <$> dictType className [Var resultTyVar]
      addDefault (atomVarName resultTyVar) defaultTy
      emitExpr =<< mkApplyMethod (DictHole (AlwaysEqual emptySrcPosCtx) dictTy Full) 0 [litVal]

-- atom that requires instantiation to become a rho type
data SigmaAtom n =
    SigmaAtom (Maybe SourceName) (CAtom n)
  | SigmaUVar SourceName (CType n) (UVar n)
  | SigmaPartialApp (CType n) (CAtom n) [CAtom n]
    deriving (Show)

-- XXX: this gives the type of the atom in the absence of other type information.
-- So it interprets struct names as data constructors rather than type constructors.
instance HasType CoreIR SigmaAtom where
  getType = \case
    SigmaAtom _ x -> getType x
    SigmaUVar _ ty _ -> ty
    SigmaPartialApp ty _ _ -> ty

instance HasSourceName (SigmaAtom n) where
  getSourceName = \case
    SigmaAtom sn _ -> case sn of
      Just sn' -> sn'
      Nothing  -> "<expr>"
    SigmaUVar sn _ _ -> sn
    SigmaPartialApp _ _ _ -> "<dot method>"

instance SinkableE SigmaAtom where
  sinkingProofE = error "it's fine, trust me"

instance SubstE AtomSubstVal SigmaAtom where
  substE env (SigmaAtom sn x) = SigmaAtom sn $ substE env x
  substE env (SigmaUVar sn ty uvar) = case uvar of
    UAtomVar v -> substE env $ SigmaAtom (Just sn) $ Var (AtomVar v ty)
    UTyConVar   v -> SigmaUVar sn ty' $ UTyConVar   $ substE env v
    UDataConVar v -> SigmaUVar sn ty' $ UDataConVar $ substE env v
    UPunVar     v -> SigmaUVar sn ty' $ UPunVar     $ substE env v
    UClassVar   v -> SigmaUVar sn ty' $ UClassVar   $ substE env v
    UMethodVar  v -> SigmaUVar sn ty' $ UMethodVar  $ substE env v
    UEffectVar   _ -> error "not implemented"
    UEffectOpVar _ -> error "not implemented"
    where ty' = substE env ty
  substE env (SigmaPartialApp ty f xs) =
    SigmaPartialApp (substE env ty) (substE env f) (map (substE env) xs)

-- XXX: this must handle the complement of the cases that `checkOrInferRho`
-- handles directly or else we'll just keep bouncing between the two.
inferWithoutInstantiation
  :: forall i o. EmitsBoth o
  => UExpr i -> InfererM i o (SigmaAtom o)
inferWithoutInstantiation (WithSrcE pos expr) =
 addSrcContext pos $ confuseGHC >>= \_ -> case expr of
   UVar ~(InternalName _ sn v) ->  do
     v' <- renameM v
     ty <- getUVarType v'
     return $ SigmaUVar sn ty v'
   UFieldAccess x (WithSrc pos' field) -> addSrcContext pos' do
     x' <- inferRho noHint x >>= zonk
     ty <- return $ getType x'
     fields <- getFieldDefs ty
     case M.lookup field fields of
       Just def -> case def of
         FieldProj i -> SigmaAtom Nothing <$> projectField i x'
         FieldDotMethod method (TyConParams _ params) -> do
           method' <- toAtomVar method
           resultTy <- partialAppType (getType method') (params ++ [x'])
           return $ SigmaPartialApp resultTy (Var method') (params ++ [x'])
       Nothing -> throw TypeErr $
         "Can't resolve field " ++ pprint field ++ " of type " ++ pprint ty ++
         "\nKnown fields are: " ++ pprint (M.keys fields)
   _ -> SigmaAtom Nothing <$> inferRho noHint (WithSrcE pos expr)

data FieldDef (n::S) =
   FieldProj Int
 | FieldDotMethod (CAtomName n) (TyConParams n)
   deriving (Show, Generic)

getFieldDefs :: CType n -> InfererM i n (M.Map FieldName' (FieldDef n))
getFieldDefs ty = case ty of
  NewtypeTyCon (UserADTType _ tyName params) -> do
    TyConBinding ~(Just tyDef) (DotMethods dotMethods) <- lookupEnv tyName
    instantiateTyConDef tyDef params >>= \case
      StructFields fields -> do
        let projFields = enumerate fields <&> \(i, (field, _)) ->
              [(FieldName field, FieldProj i), (FieldNum i, FieldProj i)]
        let methodFields = M.toList dotMethods <&> \(field, f) ->
              (FieldName field, FieldDotMethod f params)
        return $ M.fromList $ concat projFields ++ methodFields
      ADTCons _ -> noFields ""
  RefTy _ valTy -> case valTy of
    RefTy _ _ -> noFields ""
    _ -> do
      valFields <- getFieldDefs valTy
      return $ M.filter isProj valFields
      where isProj = \case
              FieldProj _ -> True
              _ -> False
  ProdTy ts -> return $ M.fromList $ enumerate ts <&> \(i, _) -> (FieldNum i, FieldProj i)
  TabPi _ -> noFields "\nArray indexing uses [] now."
  _ -> noFields ""
  where
    noFields s = throw TypeErr $ "Can't get fields for type " ++ pprint ty ++ s

instantiateSigma :: forall i o. EmitsBoth o => SigmaAtom o -> InfererM i o (CAtom o)
instantiateSigma sigmaAtom = case getType sigmaAtom of
  Pi piTy@(CorePiType ExplicitApp _ _ _) -> do
    Lam <$> etaExpandExplicits fDesc piTy \args ->
      applySigmaAtom (sink sigmaAtom) args
  Pi (CorePiType ImplicitApp expls bs (EffTy _ resultTy)) -> do
    args <- inferMixedArgs @UExpr fDesc expls (Abs bs resultTy) [] []
    applySigmaAtom sigmaAtom args
  DepPairTy (DepPairType ImplicitDepPair _ _) ->
    -- TODO: we should probably call instantiateSigma again here in case
    -- we have nested dependent pairs. Also, it looks like this doesn't
    -- get called after function application. We probably want to fix that.
    fallback >>= getSnd
  _ -> fallback
  where
   fallback = case sigmaAtom of
     SigmaAtom _ x -> return x
     SigmaUVar _ _ v -> case v of
       UAtomVar v' -> do
         v'' <- toAtomVar v'
         return $ Var v''
       _ -> applySigmaAtom sigmaAtom []
     SigmaPartialApp _ _ _ -> error "shouldn't hit this case because we should have a pi type here"
   fDesc :: SourceName
   fDesc = getSourceName sigmaAtom

projectField :: Emits o => Int -> CAtom o -> InfererM i o (CAtom o)
projectField i x = case getType x of
  ProdTy _ -> projectTuple i x
  NewtypeTyCon _ -> projectStruct i x
  RefTy _ valTy -> case valTy of
    ProdTy _ -> getProjRef (ProjectProduct i) x
    NewtypeTyCon _ -> projectStructRef i x
    _ -> bad
  _ -> bad
  where bad = error $ "bad projection: " ++ pprint (i, x)

-- creates a lambda term with just the explicit binders, but provides
-- args corresponding to all the binders (explicit and implicit)
etaExpandExplicits
  :: EmitsInf o => SourceName -> CorePiType o
  -> (forall o'. (EmitsBoth o', DExt o o') => [CAtom o'] -> InfererM i o' (CAtom o'))
  -> InfererM i o (CoreLamExpr o)
etaExpandExplicits fSourceName (CorePiType _ explsTop bsTop (EffTy effs _)) contTop = do
  Abs bs body <- go explsTop bsTop \xs -> do
    effs' <- applySubst (bsTop@@>(SubstVal<$>xs)) effs
    withAllowedEffects effs' do
      body <- buildBlockInf $ contTop $ sinkList xs
      return $ PairE effs' body
  let (expls, bs') = unzipAttrs bs
  coreLamExpr ExplicitApp expls $ Abs bs' body
 where
  go :: (EmitsInf o, SinkableE e, RenameE e, SubstE AtomSubstVal e, HoistableE e )
     => [Explicitness] -> Nest CBinder o any
     -> (forall o'. (EmitsInf o', DExt o o') => [CAtom o'] -> InfererM i o' (e o'))
     -> InfererM i o (Abs (Nest (WithExpl CBinder)) e o)
  go [] Empty cont = getDistinct >>= \Distinct -> Abs Empty <$> cont []
  go (expl:expls) (Nest (b:>ty) rest) cont = case expl of
    Explicit -> do
      prependAbs <$> buildAbsInfWithExpl (getNameHint b) expl ty \v -> do
        Abs rest' UnitE <- applyRename (b@>atomVarName v) $ Abs rest UnitE
        go expls rest' \args -> cont (sink (Var v) : args)
    Inferred argSourceName infMech -> do
      arg <- getImplicitArg (fSourceName, fromMaybe "_" argSourceName) infMech ty
      Abs rest' UnitE <- applySubst (b@>SubstVal arg) $ Abs rest UnitE
      go expls rest' \args -> cont (sink arg : args)
  go _ _ _ = error "zip error"

buildLamInf
  :: EmitsInf o => CorePiType o
  -> (forall o' .  (EmitsBoth o', DExt o o')
                => [(Explicitness, CAtom o')] -> CType o' -> InfererM i o' (CAtom o'))
  -> InfererM i o (CoreLamExpr o)
buildLamInf (CorePiType appExpl explsTop bsTop effTy) contTop = do
  ab <- go explsTop bsTop \xs -> do
    let (expls, xs') = unzip xs
    EffTy effs' resultTy' <- applySubst (bsTop@@>(SubstVal<$>xs')) effTy
    withAllowedEffects effs' do
      body <- buildBlockInf $ contTop (zip expls $ sinkList xs') (sink resultTy')
      return $ PairE effs' body
  coreLamExpr appExpl explsTop ab
 where
  go :: (EmitsInf o, HoistableE e, SinkableE e, SubstE AtomSubstVal e, RenameE e)
     => [Explicitness] -> Nest CBinder o any
     -> (forall o'. (EmitsInf o', DExt o o') => [(Explicitness, CAtom o')] -> InfererM i o' (e o'))
     -> InfererM i o (Abs (Nest CBinder) e o)
  go [] Empty cont = getDistinct >>= \Distinct -> Abs Empty <$> cont []
  go (expl:expls) (Nest b rest) cont = do
    prependAbs <$> buildAbsInf (getNameHint b) expl (binderType b) \v -> do
      Abs rest' UnitE <- applyRename (b@>atomVarName v) $ Abs rest UnitE
      go expls rest' \args -> cont $ (expl, sink $ Var v) : args
  go _ _ _ = error "zip error"

class ExplicitArg (e::E) where
  checkExplicitArg :: EmitsBoth o => IsDependent -> e i -> CType o -> InfererM i o (CAtom o)
  inferExplicitArg :: EmitsBoth o => e i -> InfererM i o (CAtom o)

instance ExplicitArg UExpr where
  checkExplicitArg isDependent arg argTy =
    if isDependent
      then checkSigmaDependent noHint arg argTy
      else checkSigma noHint arg argTy

  inferExplicitArg arg = inferRho noHint arg

instance ExplicitArg CAtom where
  checkExplicitArg _ arg argTy = do
    arg' <- renameM arg
    constrainTypesEq argTy $ getType arg'
    return arg'
  inferExplicitArg arg = renameM arg

checkOrInferApp
  :: forall i o arg
  . (EmitsBoth o, ExplicitArg arg)
  => SigmaAtom o -> [arg i] -> [(SourceName, arg i)]
  -> RequiredTy CType o
  -> InfererM i o (CAtom o)
checkOrInferApp f' posArgs namedArgs reqTy = do
  f <- maybeInterpretPunsAsTyCons reqTy f'
  case getType f of
    Pi (CorePiType appExpl expls bs effTy) -> case appExpl of
      ExplicitApp -> do
        checkArity expls posArgs
        args' <- inferMixedArgs fDesc expls (Abs bs effTy) posArgs namedArgs
        applySigmaAtom f args' >>= matchRequirement
      ImplicitApp -> do
        -- TODO: should this already have been done by the time we get `f`?
        implicitArgs <- inferMixedArgs @UExpr fDesc expls (Abs bs effTy) [] []
        f'' <- SigmaAtom (Just fDesc) <$> applySigmaAtom f implicitArgs
        checkOrInferApp f'' posArgs namedArgs Infer >>= matchRequirement
    -- TODO: special-case error for when `fTy` can't possibly be a function
    fTy -> do
      when (not $ null namedArgs) do
        throw TypeErr "Can't infer function types with named arguments"
      args' <- mapM inferExplicitArg posArgs
      argTys <- return $ map getType args'
      resultTy <- getResultTy
      let expected = nonDepPiType argTys Pure resultTy
      constrainTypesEq (Pi expected) fTy
      f'' <- zonk f
      applySigmaAtom f'' args'
 where
  fDesc :: SourceName
  fDesc = getSourceName f'

  getResultTy :: InfererM i o (CType o)
  getResultTy = case reqTy of
    Infer -> freshType
    Check req -> return req

  matchRequirement :: CAtom o -> InfererM i o (CAtom o)
  matchRequirement x = return x <*
    case reqTy of
      Infer -> return ()
      Check req -> do
        ty <- return $ getType x
        constrainTypesEq req ty

maybeInterpretPunsAsTyCons :: RequiredTy CType n -> SigmaAtom n -> InfererM i n (SigmaAtom n)
maybeInterpretPunsAsTyCons (Check TyKind) (SigmaUVar sn _ (UPunVar v)) = do
  let v' = UTyConVar v
  ty <- getUVarType v'
  return $ SigmaUVar sn ty v'
maybeInterpretPunsAsTyCons _ x = return x

type IsDependent = Bool

applySigmaAtom :: EmitsBoth o => SigmaAtom o -> [CAtom o] -> InfererM i o (CAtom o)
applySigmaAtom (SigmaAtom _ f) args = emitExprWithEffects =<< mkApp f args
applySigmaAtom (SigmaUVar _ _ f) args = case f of
  UAtomVar f' -> do
    f'' <- toAtomVar f'
    emitExprWithEffects =<< mkApp (Var f'') args
  UTyConVar f' -> do
    TyConDef sn roleExpls _ _ <- lookupTyCon f'
    let expls = snd <$> roleExpls
    return $ Type $ NewtypeTyCon $ UserADTType sn f' (TyConParams expls args)
  UDataConVar v -> do
    (tyCon, i) <- lookupDataCon v
    applyDataCon tyCon i args
  UPunVar tc -> do
    TyConDef sn _ _ _ <- lookupTyCon tc
    -- interpret as a data constructor by default
    (params, dataArgs) <- splitParamPrefix tc args
    repVal <- makeStructRepVal tc dataArgs
    return $ NewtypeCon (UserADTData sn tc params) repVal
  UClassVar   f' -> do
    ClassDef sourceName _ _ _ _ _ _ <- lookupClassDef f'
    return $ Type $ DictTy $ DictType sourceName f' args
  UMethodVar  f' -> do
    MethodBinding className methodIdx <- lookupEnv f'
    ClassDef _ _ _ _ paramBs _ _ <- lookupClassDef className
    let numParams = nestLength paramBs
    -- params aren't needed because they're already implied by the dict argument
    let (dictArg:args') = drop numParams args
    emitExprWithEffects =<< mkApplyMethod dictArg methodIdx args'
  UEffectVar   _ -> error "not implemented"
  UEffectOpVar _ -> error "not implemented"
applySigmaAtom (SigmaPartialApp _ f prevArgs) args =
  emitExprWithEffects =<< mkApp f (prevArgs ++ args)

splitParamPrefix :: EnvReader m => TyConName n -> [CAtom n] -> m n (TyConParams n, [CAtom n])
splitParamPrefix tc args = do
  TyConDef _ _ paramBs _ <- lookupTyCon tc
  let (paramArgs, dataArgs) = splitAt (nestLength paramBs) args
  params <- makeTyConParams tc paramArgs
  return (params, dataArgs)

applyDataCon :: Emits o => TyConName o -> Int -> [CAtom o] -> InfererM i o (CAtom o)
applyDataCon tc conIx topArgs = do
  tyDef@(TyConDef sn _ _ _) <- lookupTyCon tc
  (params, dataArgs) <- splitParamPrefix tc topArgs
  ADTCons conDefs <- instantiateTyConDef tyDef params
  DataConDef _ _ repTy _ <- return $ conDefs !! conIx
  conProd <- wrap repTy dataArgs
  repVal <- return case conDefs of
    []  -> error "unreachable"
    [_] -> conProd
    _   -> SumVal conTys conIx conProd
      where conTys = conDefs <&> \(DataConDef _ _ rty _) -> rty
  return $ NewtypeCon (UserADTData sn tc params) repVal
  where
    wrap :: EnvReader m => CType n -> [CAtom n] -> m n (CAtom n)
    wrap _ [arg] = return $ arg
    wrap rty args = case rty of
      ProdTy tys  ->
        if nargs == ntys
          then return $ ProdVal args
          else ProdVal . (curArgs ++) . (:[]) <$> wrap (last tys) remArgs
        where
          nargs = length args; ntys = length tys
          (curArgs, remArgs) = splitAt (ntys - 1) args
      DepPairTy dpt@(DepPairType _ b rty') -> do
        rty'' <- applySubst (b@>SubstVal h) rty'
        ans <- wrap rty'' t
        return $ DepPair h ans dpt
        where h:t = args
      _ -> error $ "Unexpected data con representation type: " ++ pprint rty

emitExprWithEffects :: EmitsBoth o => CExpr o -> InfererM i o (CAtom o)
emitExprWithEffects expr = do
  addEffects $ getEffects expr
  emitExpr expr

checkArity :: [Explicitness] -> [a] -> InfererM i o ()
checkArity expls args = do
  let arity = length [() | Explicit <- expls]
  let numArgs = length args
  when (numArgs /= arity) do
    throw TypeErr $ "Wrong number of positional arguments provided. Expected " ++
      pprint arity ++ " but got " ++ pprint numArgs

-- TODO: check that there are no extra named args provided
inferMixedArgs
  :: forall arg i o e
  .  (ExplicitArg arg, EmitsBoth o, SubstE (SubstVal Atom) e, SinkableE e, HoistableE e)
  => SourceName -> [Explicitness]
  -> Abs (Nest CBinder) e o -> [arg i] -> [(SourceName, arg i)]
  -> InfererM i o [CAtom o]
inferMixedArgs fSourceName explsTop bsAbs posArgs namedArgs = do
  checkNamedArgValidity explsTop (map fst namedArgs)
  liftM fst $ runStreamReaderT1 posArgs $ go explsTop bsAbs
 where
  go :: (EmitsBoth o, SubstE (SubstVal Atom) e, SinkableE e, HoistableE e)
     => [Explicitness] -> Abs (Nest CBinder) e o
    -> StreamReaderT1 (arg i) (InfererM i) o [CAtom o]
  go [] (Abs Empty _) = return []
  go (expl:expls) (Abs (Nest b bs) result) = do
    let rest = Abs bs result
    let isDependent = binderName b `isFreeIn` rest
    arg <- inferMixedArg isDependent (binderType b) expl
    arg' <- lift11 $ zonk arg
    rest' <- applySubst (b @> SubstVal arg') rest
    (arg:) <$> go expls rest'
  go _ _ = error "zip error"

  inferMixedArg :: EmitsBoth o => IsDependent -> CType o -> Explicitness
                -> StreamReaderT1 (arg i) (InfererM i) o (CAtom o)
  inferMixedArg isDependent argTy = \case
    Explicit -> do
      -- this should succeed because we've already done the arity check
      Just arg <- readStream
      lift11 $ checkExplicitArg isDependent arg argTy
    Inferred argName infMech -> lift11 do
      case lookupNamedArg argName of
        Nothing -> getImplicitArg (fSourceName, fromMaybe "_" argName) infMech argTy
        Just arg -> checkExplicitArg isDependent arg argTy

  lookupNamedArg :: Maybe SourceName -> Maybe (arg i)
  lookupNamedArg Nothing = Nothing
  lookupNamedArg (Just v) = lookup v namedArgs

checkNamedArgValidity :: Fallible m => [Explicitness] -> [SourceName] -> m ()
checkNamedArgValidity expls offeredNames = do
  let explToMaybeName = \case
        Explicit -> Nothing
        Inferred v _ -> v
  let acceptedNames = catMaybes $ map explToMaybeName expls
  let duplicates = repeated offeredNames
  when (not $ null duplicates) do
    throw TypeErr $ "Repeated names offered" ++ pprint duplicates
  let unrecognizedNames = filter (not . (`elem` acceptedNames)) offeredNames
  when (not $ null unrecognizedNames) do
    throw TypeErr $ "Unrecognized named arguments: " ++ pprint unrecognizedNames
      ++ "\nShould be one of: " ++ pprint acceptedNames

inferPrimArg :: EmitsBoth o => UExpr i -> InfererM i o (CAtom o)
inferPrimArg x = do
  xBlock <- buildBlockInf $ inferRho noHint x
  EffTy _ ty <- blockEffTy xBlock
  case ty of
    TyKind -> cheapReduce xBlock >>= \case
      Just reduced -> return reduced
      _ -> throw CompilerErr "Type args to primops must be reducible"
    _ -> emitBlock xBlock

matchPrimApp :: Emits o => PrimName -> [CAtom o] -> InfererM i o (CAtom o)
matchPrimApp = \case
 UNat                -> \case ~[]  -> return $ Type $ NewtypeTyCon Nat
 UFin                -> \case ~[n] -> return $ Type $ NewtypeTyCon (Fin n)
 UEffectRowKind      -> \case ~[]  -> return $ Type $ NewtypeTyCon EffectRowKind
 UBaseType b         -> \case ~[]  -> return $ Type $ TC $ BaseType b
 UNatCon             -> \case ~[x] -> return $ NewtypeCon NatCon x
 UPrimTC op -> \x -> Type . TC  <$> matchGenericOp (Right op) x
 UCon    op -> \x -> Con <$> matchGenericOp (Right op) x
 UMiscOp op -> \x -> emitOp =<< MiscOp <$> matchGenericOp op x
 UMemOp  op -> \x -> emitOp =<< MemOp  <$> matchGenericOp op x
 UBinOp op -> \case ~[x, y] -> emitOp $ BinOp op x y
 UUnOp  op -> \case ~[x]    -> emitOp $ UnOp  op x
 UMAsk      -> \case ~[r]    -> emitOp $ RefOp r MAsk
 UMGet      -> \case ~[r]    -> emitOp $ RefOp r MGet
 UMPut      -> \case ~[r, x] -> emitOp $ RefOp r $ MPut x
 UIndexRef  -> \case ~[r, i] -> indexRef r i
 UApplyMethod i -> \case ~(d:args) -> emitExpr =<< mkApplyMethod d i args
 ULinearize -> \case ~[f, x]  -> do f' <- lam1 f; emitHof $ Linearize f' x
 UTranspose -> \case ~[f, x]  -> do f' <- lam1 f; emitHof $ Transpose f' x
 URunReader -> \case ~[x, f]  -> do f' <- lam2 f; emitHof $ RunReader x f'
 URunState  -> \case ~[x, f]  -> do f' <- lam2 f; emitHof $ RunState  Nothing x f'
 UWhile     -> \case ~[f]     -> do f' <- lam0 f; emitHof $ While f'
 URunIO     -> \case ~[f]     -> do f' <- lam0 f; emitHof $ RunIO f'
 UCatchException-> \case ~[f] -> do f' <- lam0 f; emitHof =<< mkCatchException f'
 UMExtend   -> \case ~[r, z, f, x] -> do f' <- lam2 f; emitOp $ RefOp r $ MExtend (BaseMonoid z f') x
 URunWriter -> \args -> do
   [idVal, combiner, f] <- return args
   combiner' <- lam2 combiner
   f' <- lam2 f
   emitHof $ RunWriter Nothing (BaseMonoid idVal combiner') f'
 p -> \case xs -> throw TypeErr $ "Bad primitive application: " ++ show (p, xs)
 where
   lam2 :: Fallible m => CAtom n -> m (LamExpr CoreIR n)
   lam2 x = do
     ExplicitCoreLam (BinaryNest b1 b2) body <- return x
     return $ BinaryLamExpr b1 b2 body

   lam1 :: Fallible m => CAtom n -> m (LamExpr CoreIR n)
   lam1 x = do
     ExplicitCoreLam (UnaryNest b) body <- return x
     return $ UnaryLamExpr b body

   lam0 :: Fallible m => CAtom n -> m (CBlock n)
   lam0 x = do
     ExplicitCoreLam Empty body <- return x
     return body

   matchGenericOp :: GenericOp op => OpConst op CoreIR -> [CAtom n] -> InfererM i n (op CoreIR n)
   matchGenericOp op xs = do
     (tyArgs, dataArgs) <- partitionEithers <$> forM xs \x -> do
       case getType x of
         TyKind -> do
           Type x' <- return x
           return $ Left x'
         _ -> return $ Right x
     return $ fromJust $ toOp $ GenericOpRep op tyArgs dataArgs []

pattern ExplicitCoreLam :: Nest CBinder n l -> CBlock l -> CAtom n
pattern ExplicitCoreLam bs body <- Lam (CoreLamExpr _ (LamExpr bs body))

-- === n-ary applications ===

inferTabApp :: EmitsBoth o => SrcPosCtx -> CAtom o -> [UExpr i] -> InfererM i o (CAtom o)
inferTabApp tabCtx tab args = addSrcContext tabCtx do
  tabTy <- return $ getType tab
  args' <- inferNaryTabAppArgs tabTy args
  tab' <- zonk tab
  emitExpr =<< mkTabApp tab' args'

inferNaryTabAppArgs
  :: EmitsBoth o
  => CType o -> [UExpr i] -> InfererM i o [CAtom o]
inferNaryTabAppArgs _ [] = return []
inferNaryTabAppArgs tabTy (arg:rest) = do
  TabPiType _ b resultTy <- fromTabPiType True tabTy
  let ixTy = binderType b
  let isDependent = binderName b `isFreeIn` resultTy
  arg' <- if isDependent
    then checkSigmaDependent (getNameHint b) arg ixTy
    else checkSigma (getNameHint b) arg ixTy
  arg'' <- zonk arg'
  resultTy' <- applySubst (b @> SubstVal arg'') resultTy
  rest' <- inferNaryTabAppArgs resultTy' rest
  return $ arg'':rest'

checkSigmaDependent :: EmitsBoth o
                    => NameHint -> UExpr i -> CType o -> InfererM i o (CAtom o)
checkSigmaDependent hint e@(WithSrcE ctx _) ty = addSrcContext ctx $
  withReducibleEmissions depFunErrMsg $ checkSigma hint e (sink ty)
  where
    depFunErrMsg =
      "Dependent functions can only be applied to fully evaluated expressions. " ++
      "Bind the argument to a name before you apply the function."

withReducibleEmissions
  :: ( EmitsInf o, SinkableE e, RenameE e, SubstE AtomSubstVal e
     , HoistableE e, CheaplyReducibleE CoreIR e e)
  => String
  -> (forall o' . (EmitsBoth o', DExt o o') => InfererM i o' (e o'))
  -> InfererM i o (e o)
withReducibleEmissions msg cont = do
  Abs decls result <- buildDeclsInf cont
  cheapReduceWithDecls decls result >>= \case
    Just t -> return t
    _ -> throw TypeErr msg

-- === sorting case alternatives ===

data IndexedAlt n = IndexedAlt CaseAltIndex (Alt CoreIR n)

instance SinkableE IndexedAlt where
  sinkingProofE = todoSinkableProof

buildNthOrderedAlt :: (Emits n, Builder CoreIR m)
                   => [IndexedAlt n] -> CType n -> CType n -> Int -> CAtom n
                   -> m n (CAtom n)
buildNthOrderedAlt alts scrutTy resultTy i v = do
  case lookup (nthCaseAltIdx scrutTy i) [(idx, alt) | IndexedAlt idx alt <- alts] of
    Nothing -> do
      resultTy' <- sinkM resultTy
      emitOp $ MiscOp $ ThrowError resultTy'
    Just alt -> applyAbs alt (SubstVal v) >>= emitBlock

-- converts from the ordinal index used in the core IR to the more complicated
-- `CaseAltIndex` used in the surface IR.
nthCaseAltIdx :: CType n -> Int -> CaseAltIndex
nthCaseAltIdx ty i = case ty of
  TypeCon _ _ _ -> i
  _ -> error $ "can't pattern-match on: " <> pprint ty

buildMonomorphicCase
  :: (Emits n, ScopableBuilder CoreIR m)
  => [IndexedAlt n] -> CAtom n -> CType n -> m n (CAtom n)
buildMonomorphicCase alts scrut resultTy = do
  scrutTy <- return $ getType scrut
  buildCase scrut resultTy \i v -> do
    ListE alts' <- sinkM $ ListE alts
    scrutTy'    <- sinkM scrutTy
    resultTy'   <- sinkM resultTy
    buildNthOrderedAlt alts' scrutTy' resultTy' i v

buildSortedCase :: (Fallible1 m, Builder CoreIR m, Emits n)
                 => CAtom n -> [IndexedAlt n] -> CType n
                 -> m n (CAtom n)
buildSortedCase scrut alts resultTy = do
  scrutTy <- return $ getType scrut
  case scrutTy of
    TypeCon _ defName _ -> do
      TyConDef _ _ _ (ADTCons cons) <- lookupTyCon defName
      case cons of
        [] -> error "case of void?"
        -- Single constructor ADTs are not sum types, so elide the case.
        [_] -> do
          let [IndexedAlt _ alt] = alts
          scrut' <- unwrapNewtype scrut
          emitBlock =<< applyAbs alt (SubstVal scrut')
        _ -> liftEmitBuilder $ buildMonomorphicCase alts scrut resultTy
    _ -> fail $ "Unexpected case expression type: " <> pprint scrutTy

-- TODO: cache this with the instance def (requires a recursive binding)
instanceFun :: EnvReader m => InstanceName n -> AppExplicitness -> m n (CAtom n)
instanceFun instanceName appExpl = do
  InstanceDef _ expls bs _ _ <- lookupInstanceDef instanceName
  ab <- liftEnvReaderM $ refreshAbs (Abs bs UnitE) \bs' UnitE -> do
    args <- mapM toAtomVar $ nestToNames bs'
    result <- mkDictAtom $ InstanceDict (sink instanceName) (Var <$> args)
    return $ Abs bs' (PairE Pure (WithoutDecls result))
  Lam <$> coreLamExpr appExpl (snd<$>expls) ab

checkMaybeAnnExpr :: EmitsBoth o
  => NameHint -> Maybe (UType i) -> UExpr i -> InfererM i o (CAtom o)
checkMaybeAnnExpr hint ty expr = confuseGHC >>= \_ -> case ty of
  Nothing -> inferSigma hint expr
  Just ty' -> checkSigma hint expr =<< zonk =<< checkUType ty'

inferRole :: CType o -> Explicitness -> InfererM i o ParamRole
inferRole ty = \case
  Inferred _ (Synth _) -> return DictParam
  _ -> do
    zonk ty >>= \case
      TyKind -> return TypeParam
      ty' -> isData ty' >>= \case
        True -> return DataParam
        -- TODO(dougalm): the `False` branch should throw an error but that's
        -- currently too conservative. e.g. `data RangeFrom q:Type i:q = ...`
        -- fails because `q` isn't data. We should be able to fix it once we
        -- have a `Data a` class (see issue #680).
        False -> return DataParam
{-# INLINE inferRole #-}

inferTyConDef :: EmitsInf o => UDataDef i -> InfererM i o (TyConDef o)
inferTyConDef (UDataDef tyConName paramBs dataCons) = do
  Abs paramBs' dataCons' <-
    withRoleUBinders paramBs do
      ADTCons <$> mapM inferDataCon dataCons
  let (roleExpls, paramBs'') = unzipAttrs paramBs'
  return (TyConDef tyConName roleExpls paramBs'' dataCons')

inferStructDef :: EmitsInf o => UStructDef i -> InfererM i o (TyConDef o)
inferStructDef (UStructDef tyConName paramBs fields _) = do
  let (fieldNames, fieldTys) = unzip fields
  Abs paramBs' dataConDefs <- withRoleUBinders paramBs do
    tys <- mapM checkUType fieldTys
    return $ StructFields $ zip fieldNames tys
  let (roleExpls, paramBs'') = unzipAttrs paramBs'
  return $ TyConDef tyConName roleExpls paramBs'' dataConDefs

inferDotMethod
  :: EmitsInf o => TyConName o
  -> Abs (Nest UOptAnnBinder) (Abs UAtomBinder ULamExpr) i
  -> InfererM i o (CoreLamExpr o)
inferDotMethod tc (Abs uparamBs (Abs selfB lam)) = do
  TyConDef sn roleExpls paramBs _ <- lookupTyCon tc
  let expls = snd <$> roleExpls
  ab <- buildNaryAbsInfWithExpl expls (Abs paramBs UnitE) \paramVs -> do
    let paramVs' = catMaybes $ zip expls paramVs <&> \(expl, v) -> case expl of
                     Inferred _ (Synth _) -> Nothing
                     _ -> Just v
    extendRenamer (uparamBs @@> (atomVarName <$> paramVs')) do
      let selfTy = NewtypeTyCon $ UserADTType sn (sink tc) (TyConParams expls (Var <$> paramVs))
      buildAbsInfWithExpl "self" Explicit selfTy \vSelf ->
        extendRenamer (selfB @> atomVarName vSelf) $ inferULam lam
  Abs paramBs'' (Abs selfB' lam') <- return ab
  return $ prependCoreLamExpr (paramBs'' >>> UnaryNest selfB') lam'

prependCoreLamExpr :: Nest (WithExpl CBinder) n l -> CoreLamExpr l -> CoreLamExpr n
prependCoreLamExpr bs e = case e of
  CoreLamExpr (CorePiType appExpl piExpls piBs effTy) (LamExpr lamBs body) -> do
    let (expls, bs') = unzipAttrs bs
    let piType  = CorePiType appExpl (expls <> piExpls) (bs' >>> piBs) effTy
    let lamExpr = LamExpr (fmapNest withoutAttr bs >>> lamBs) body
    CoreLamExpr piType lamExpr

inferDataCon :: EmitsInf o => (SourceName, UDataDefTrail i) -> InfererM i o (DataConDef o)
inferDataCon (sourceName, UDataDefTrail argBs) = do
  let expls = nestToList (const Explicit) argBs
  Abs argBs' UnitE <- withUBinders (expls, argBs) \_ -> return UnitE
  let argBs'' = Abs (fmapNest withoutAttr argBs') UnitE
  let (repTy, projIdxs) = dataConRepTy argBs''
  return $ DataConDef sourceName argBs'' repTy projIdxs

dataConRepTy :: EmptyAbs (Nest CBinder) n -> (CType n, [[Projection]])
dataConRepTy (Abs topBs UnitE) = case topBs of
  Empty -> (UnitTy, [])
  _ -> go [] [UnwrapNewtype] topBs
  where
    go :: [CType l] -> [Projection] -> Nest (Binder CoreIR) l p -> (CType l, [[Projection]])
    go revAcc projIdxs = \case
      Empty -> case revAcc of
        []   -> error "should never happen"
        [ty] -> (ty, [projIdxs])
        _    -> ( ProdTy $ reverse revAcc
                , iota (length revAcc) <&> \i -> ProjectProduct i:projIdxs )
      Nest b bs -> case hoist b (EmptyAbs bs) of
        HoistSuccess (Abs bs' UnitE) -> go (binderType b:revAcc) projIdxs bs'
        HoistFailure _ -> (fullTy, idxs)
          where
            accSize = length revAcc
            (fullTy, depTyIdxs) = case revAcc of
              [] -> (depTy, [])
              _  -> (ProdTy $ reverse revAcc ++ [depTy], [ProjectProduct accSize])
            (tailTy, tailIdxs) = go [] (ProjectProduct 1 : (depTyIdxs ++ projIdxs)) bs
            idxs = (iota accSize <&> \i -> ProjectProduct i : projIdxs) ++
                   ((ProjectProduct 0 : (depTyIdxs ++ projIdxs)) : tailIdxs)
            depTy = DepPairTy $ DepPairType ExplicitDepPair b tailTy

inferClassDef
  :: EmitsInf o
  => SourceName -> [SourceName]
  -> UOptAnnExplBinders i i'
  -> [UType i']
  -> InfererM i o (ClassDef o)
inferClassDef className methodNames paramBs@(expls, paramBs') methods = do
  let paramBsWithAttrBs = zipWithNest paramBs' expls \b expl -> WithAttrB expl b
  let paramNames = catMaybes $ nestToList
        (\(WithAttrB expl (UAnnBinder b _ _)) -> case expl of
             Inferred _ (Synth _) -> Nothing
             _ -> Just $ Just $ getSourceName b) paramBsWithAttrBs
  ab <- withRoleUBinders paramBs do
     ListE <$> forM methods \m -> do
       checkUType m >>= \case
         Pi t -> return t
         t -> return $ CorePiType ImplicitApp [] Empty (EffTy Pure t)
  Abs (PairB bs scs) (ListE mtys) <- identifySuperclasses ab
  let (roleExpls, bs') = unzipAttrs bs
  return $ ClassDef className methodNames paramNames roleExpls bs' scs mtys

identifySuperclasses
  :: RenameE e => Abs (Nest (WithRoleExpl CBinder)) e n
  -> InfererM i n (Abs (PairB (Nest (WithRoleExpl CBinder)) (Nest CBinder)) e n)
identifySuperclasses ab = do
  refreshAbs ab \bs e -> do
    bs' <- partitionBinders bs \b@(WithAttrB (_, expl) b') -> case expl of
      Explicit -> return $ LeftB b
      Inferred _ Unify -> throw TypeErr "Interfaces can't have implicit parameters"
      Inferred _ (Synth _) -> return $ RightB b'
    return $ Abs bs' e

withUBinders
  :: (EmitsInf o, HasNamesE e, SubstE AtomSubstVal e, SinkableE e)
  => UAnnExplBinders req i i'
  -> (forall o'. (EmitsInf o', DExt o o') => [CAtomVar o'] -> InfererM i' o' (e o'))
  -> InfererM i o (Abs (Nest (WithExpl CBinder)) e o)
withUBinders bs cont = case bs of
  ([], Empty) -> getDistinct >>= \Distinct -> Abs Empty <$> cont []
  (expl:expls, Nest (UAnnBinder b ann cs) rest) -> do
    ann' <- checkAnn (getSourceName b) ann
    prependAbs <$> buildAbsInfWithExpl (getNameHint b) expl ann' \v ->
      concatAbs <$> withConstraintBinders cs v do
        extendSubst (b@>sink (atomVarName v)) $ withUBinders (expls, rest) \vs ->
          cont (sink v : vs)
  _ -> error "zip error"

withConstraintBinders
  :: (EmitsInf o, HasNamesE e, SubstE AtomSubstVal e, RenameE e, SinkableE e)
  => [UConstraint i]
  -> CAtomVar o
  -> (forall o'. (EmitsInf o', DExt o o') => InfererM i o' (e o'))
  -> InfererM i o (Abs (Nest (WithExpl CBinder)) e o)
withConstraintBinders [] _ cont = getDistinct >>= \Distinct -> Abs Empty <$> cont
withConstraintBinders (c:cs) v cont = do
  Type dictTy <- withReducibleEmissions "Can't reduce interface constraint" do
    c' <- inferWithoutInstantiation c >>= zonk
    dropSubst $ checkOrInferApp c' [Var $ sink v] [] (Check TyKind)
  prependAbs <$> buildAbsInfWithExpl "d" (Inferred Nothing (Synth Full)) dictTy \_ ->
    withConstraintBinders cs (sink v) cont

withRoleUBinders
  :: forall i i' o e req. (EmitsInf o, HasNamesE e, SubstE AtomSubstVal e, SinkableE e)
  => UAnnExplBinders req i i'
  -> (forall o'. (EmitsInf o', DExt o o') => InfererM i' o' (e o'))
  -> InfererM i o (Abs (Nest (WithRoleExpl CBinder)) e o)
withRoleUBinders roleBs cont = case roleBs of
  ([], Empty) -> getDistinct >>= \Distinct -> Abs Empty <$> cont
  (expl:expls, Nest (UAnnBinder b ann cs) rest) -> do
    ann' <- checkAnn (getSourceName b) ann
    Abs b' (Abs bs' e) <- buildAbsInf (getNameHint b) expl ann' \v -> do
      Abs ds (Abs bs' e) <- withConstraintBinders cs v $
        extendSubst (b@>sink (atomVarName v)) $ withRoleUBinders (expls, rest) cont
      let ds' = fmapNest (\(WithAttrB expl' b') -> WithAttrB (DictParam, expl') b') ds
      return $ Abs (ds' >>> bs') e
    role <- inferRole (binderType b') expl
    return $ Abs (Nest (WithAttrB (role,expl) b') bs') e
  _ -> error "zip error"

inferULam :: EmitsInf o => ULamExpr i -> InfererM i o (CoreLamExpr o)
inferULam (ULamExpr bs appExpl effs resultTy body) = do
  ab <- withUBinders bs \_ -> do
    effs' <- fromMaybe Pure <$> mapM checkUEffRow effs
    resultTy' <- mapM checkUType resultTy
    body' <- buildBlockInf $ withAllowedEffects (sink effs') do
      case resultTy' of
        Nothing -> withBlockDecls body \result -> inferSigma noHint result
        Just resultTy'' ->
          withBlockDecls body \result ->
            checkSigma noHint result (sink resultTy'')
    return (PairE effs' body')
  Abs bs' (PairE effs' body') <- return ab
  let (expls, bs'') = unzipAttrs bs'
  case appExpl of
    ImplicitApp -> checkImplicitLamRestrictions bs'' effs'
    ExplicitApp -> return ()
  coreLamExpr appExpl expls $ Abs bs'' $ PairE effs' body'

checkImplicitLamRestrictions :: Nest CBinder o o' -> EffectRow CoreIR o' -> InfererM i o ()
checkImplicitLamRestrictions _ _ = return () -- TODO

checkUForExpr :: EmitsBoth o => UForExpr i -> TabPiType CoreIR o -> InfererM i o (LamExpr CoreIR o)
checkUForExpr (UForExpr (UAnnBinder bFor ann cs) body) tabPi@(TabPiType _ bPi _) = do
  unless (null cs) $ throw TypeErr "`for` binders shouldn't have constraints"
  let iTy = binderAnn bPi
  case ann of
    UNoAnn -> return ()
    UAnn forAnn -> checkUType forAnn >>= constrainTypesEq iTy
  Abs b body' <- buildAbsInf (getNameHint bFor) Explicit iTy \i -> do
    extendRenamer (bFor@>atomVarName i) do
      TabPiType _ bPi' resultTy <- sinkM tabPi
      resultTy' <- applyRename (bPi'@>atomVarName i) resultTy
      buildBlockInf do
        withBlockDecls body \result ->
          checkSigma noHint result $ sink resultTy'
  return $ LamExpr (UnaryNest b) body'

inferUForExpr :: EmitsBoth o => UForExpr i -> InfererM i o (LamExpr CoreIR o)
inferUForExpr (UForExpr (UAnnBinder bFor ann cs) body) = do
  unless (null cs) $ throw TypeErr "`for` binders shouldn't have constraints"
  iTy <- checkAnn (getSourceName bFor) ann
  Abs b body' <- buildAbsInf (getNameHint bFor) Explicit iTy \i ->
    extendRenamer (bFor@>atomVarName i) $ buildBlockInf $
      withBlockDecls body \result ->
        checkOrInferRho noHint result Infer
  return $ LamExpr (UnaryNest b) body'

checkULam :: EmitsInf o => ULamExpr i -> CorePiType o -> InfererM i o (CoreLamExpr o)
checkULam (ULamExpr (_, lamBs) lamAppExpl lamEffs lamResultTy body)
          (CorePiType piAppExpl expls piBs effTy) = do
  checkArity expls (nestToList (const ()) lamBs)
  when (piAppExpl /= lamAppExpl) $ throw TypeErr $ "Wrong arrow. Expected "
     ++ pprint piAppExpl ++ " got " ++ pprint lamAppExpl
  Abs explBs body' <- checkLamBinders expls piBs lamBs \vs -> do
    EffTy piEffs' piResultTy' <- applyRename (piBs@@>map atomVarName vs) effTy
    case lamResultTy of
      Nothing -> return ()
      Just t -> checkUType t >>= constrainTypesEq piResultTy'
    forM_ lamEffs \lamEffs' -> do
      lamEffs'' <- checkUEffRow lamEffs'
      constrainEq (Eff piEffs') (Eff lamEffs'')
    withAllowedEffects piEffs' do
      body' <- buildBlockInf do
        piResultTy'' <- sinkM piResultTy'
        withBlockDecls body \result ->
          checkSigma noHint result piResultTy''
      return $ PairE piEffs' body'
  let (expls', bs') = unzipAttrs explBs
  coreLamExpr piAppExpl expls' $ Abs bs' body'

checkLamBinders
  :: (EmitsInf o, SinkableE e, HoistableE e, SubstE AtomSubstVal e, RenameE e)
  => [Explicitness] -> Nest CBinder o any
  -> Nest UOptAnnBinder i i'
  -> (forall o'. (EmitsInf o', DExt o o') => [CAtomVar o'] -> InfererM i' o' (e o'))
  -> InfererM i o (Abs (Nest (WithExpl CBinder)) e o)
checkLamBinders [] Empty Empty cont = getDistinct >>= \Distinct -> Abs Empty <$> cont []
checkLamBinders (piExpl:piExpls) (Nest (piB:>piAnn) piBs) lamBs cont = do
  prependAbs <$> case piExpl of
    Inferred _ _ ->
      buildAbsInfWithExpl (getNameHint piB) piExpl piAnn \v -> do
        Abs piBs' UnitE <- applyRename (piB@>atomVarName v) $ Abs piBs UnitE
        checkLamBinders piExpls piBs' lamBs \vs ->
          cont (sink v:vs)
    Explicit -> case lamBs of
      Nest (UAnnBinder lamB ann cs) lamBsRest -> do
        case ann of
          UAnn lamAnn -> checkUType lamAnn >>= constrainTypesEq piAnn
          UNoAnn -> return ()
        buildAbsInfWithExpl (getNameHint lamB) Explicit piAnn \v -> do
          concatAbs <$> withConstraintBinders cs v do
            Abs piBs' UnitE <- applyRename (piB@>sink (atomVarName v)) $ Abs piBs UnitE
            extendRenamer (lamB@>sink (atomVarName v)) $ checkLamBinders piExpls piBs' lamBsRest \vs ->
              cont (sink v:vs)
      Empty -> error "zip error"
checkLamBinders _ _ _ _ = error "zip error"

checkInstanceParams :: EmitsInf o => [Explicitness] -> Nest CBinder o any -> [UExpr i] -> InfererM i o [CAtom o]
checkInstanceParams expls bsTop paramsTop = do
  checkArity expls paramsTop
  go bsTop paramsTop
 where
  go :: EmitsInf o => Nest CBinder o any -> [UExpr i] -> InfererM i o [CAtom o]
  go Empty [] = return []
  go (Nest (b:>ty) bs) (x:xs) = do
    x' <- checkUParam ty x
    Abs bs' UnitE <- applySubst (b@>SubstVal x') $ Abs bs UnitE
    (x':) <$> go bs' xs
  go _ _ = error "zip error"

checkInstanceBody
  :: EmitsInf o => ClassName o -> [CAtom o]
  -> [UMethodDef i] -> InfererM i o (InstanceBody o)
checkInstanceBody className params methods = do
  ClassDef _ methodNames _ _ paramBs scBs methodTys <- lookupClassDef className
  Abs scBs' methodTys' <- applySubst (paramBs @@> (SubstVal <$> params)) $ Abs scBs $ ListE methodTys
  superclassTys <- superclassDictTys scBs'
  superclassDicts <- mapM (flip trySynthTerm Full) superclassTys
  ListE methodTys'' <- applySubst (scBs'@@>(SubstVal<$>superclassDicts)) methodTys'
  methodsChecked <- mapM (checkMethodDef className methodTys'') methods
  let (idxs, methods') = unzip $ sortOn fst $ methodsChecked
  forM_ (repeated idxs) \i ->
    throw TypeErr $ "Duplicate method: " ++ pprint (methodNames!!i)
  forM_ ([0..(length methodTys'' - 1)] `listDiff` idxs) \i ->
    throw TypeErr $ "Missing method: " ++ pprint (methodNames!!i)
  return $ InstanceBody superclassDicts methods'

superclassDictTys :: Nest CBinder o o' -> InfererM i o [CType o]
superclassDictTys Empty = return []
superclassDictTys (Nest b bs) = do
  Abs bs' UnitE <- liftHoistExcept $ hoist b $ Abs bs UnitE
  (binderType b:) <$> superclassDictTys bs'

checkMethodDef :: EmitsInf o
               => ClassName o -> [CorePiType o] -> UMethodDef i -> InfererM i o (Int, CAtom o)
checkMethodDef className methodTys (WithSrcE src m) = addSrcContext src do
  UMethodDef ~(InternalName _ sourceName v) rhs <- return m
  MethodBinding className' i <- renameM v >>= lookupEnv
  when (className /= className') do
    ClassBinding (ClassDef classSourceName _ _ _ _ _ _) <- lookupEnv className
    throw TypeErr $ pprint sourceName ++ " is not a method of " ++ pprint classSourceName
  (i,) <$> Lam <$> checkULam rhs (methodTys !! i)

checkUEffRow :: EmitsInf o => UEffectRow i -> InfererM i o (EffectRow CoreIR o)
checkUEffRow (UEffectRow effs t) = do
   effs' <- liftM eSetFromList $ mapM checkUEff $ toList effs
   t' <- case t of
     Nothing -> return NoTail
     Just (~(SIInternalName _ v _ _)) -> do
       v' <- toAtomVar =<< renameM v
       constrainVarTy v' EffKind
       return $ EffectRowTail v'
   return $ EffectRow effs' t'

checkUEff :: EmitsInf o => UEffect i -> InfererM i o (Effect CoreIR o)
checkUEff eff = case eff of
  URWSEffect rws (~(SIInternalName _ region _ _)) -> do
    region' <- renameM region >>= toAtomVar
    constrainVarTy region' (TC HeapType)
    return $ RWSEffect rws (Var region')
  UExceptionEffect -> return ExceptionEffect
  UIOEffect        -> return IOEffect

constrainVarTy :: EmitsInf o => CAtomVar o -> CType o -> InfererM i o ()
constrainVarTy v tyReq = do
  varTy <- return $ getType $ Var v
  constrainTypesEq tyReq varTy

type CaseAltIndex = Int

checkCaseAlt :: EmitsBoth o
             => CType o -> CType o -> UAlt i -> InfererM i o (IndexedAlt o)
checkCaseAlt reqTy scrutineeTy (UAlt pat body) = do
  alt <- checkCasePat pat scrutineeTy do
    reqTy' <- sinkM reqTy
    withBlockDecls body \result ->
      checkOrInferRho noHint result (Check reqTy')
  idx <- getCaseAltIndex pat
  return $ IndexedAlt idx alt

getCaseAltIndex :: UPat i i' -> InfererM i o CaseAltIndex
getCaseAltIndex (WithSrcB _ pat) = case pat of
  UPatCon ~(InternalName _ _ conName) _ -> do
    (_, con) <- renameM conName >>= lookupDataCon
    return con
  _ -> throw TypeErr $ "Case patterns must start with a data constructor or variant pattern"

checkCasePat :: EmitsBoth o
             => UPat i i'
             -> CType o
             -> (forall o'. (EmitsBoth o', Ext o o') => InfererM i' o' (CAtom o'))
             -> InfererM i o (Alt CoreIR o)
checkCasePat (WithSrcB pos pat) scrutineeTy cont = addSrcContext pos $ case pat of
  UPatCon ~(InternalName _ _ conName) ps -> do
    (dataDefName, con) <- renameM conName >>= lookupDataCon
    TyConDef sourceName roleExpls paramBs (ADTCons cons) <- lookupTyCon dataDefName
    DataConDef _ _ repTy idxs <- return $ cons !! con
    when (length idxs /= nestLength ps) $ throw TypeErr $
      "Unexpected number of pattern binders. Expected " ++ show (length idxs)
                                             ++ " got " ++ show (nestLength ps)
    (params, repTy') <- inferParams sourceName roleExpls (Abs paramBs repTy)
    constrainTypesEq scrutineeTy $ TypeCon sourceName dataDefName params
    buildAltInf repTy' \arg -> do
      args <- forM idxs \projs -> do
        ans <- normalizeNaryProj (init projs) (Var arg)
        emit $ Atom ans
      bindLetPats ps args $ cont
  _ -> throw TypeErr $ "Case patterns must start with a data constructor or variant pattern"

inferParams :: (EmitsBoth o, HasNamesE e, SinkableE e, SubstE AtomSubstVal e)
            => SourceName -> [RoleExpl] -> Abs (Nest CBinder) e o -> InfererM i o (TyConParams o, e o)
inferParams sourceName roleExpls (Abs paramBs bodyTop) = do
  let expls = snd <$> roleExpls
  (params, e') <- go expls (Abs paramBs bodyTop)
  return (TyConParams expls params, e')
 where
  go :: (EmitsBoth o, HasNamesE e, SinkableE e, SubstE AtomSubstVal e)
     => [Explicitness] -> Abs (Nest CBinder) e o -> InfererM i o ([CAtom o], e o)
  go [] (Abs Empty body) = return ([], body)
  go (expl:expls) (Abs (Nest (b:>ty) bs) body) = do
    x <- case expl of
      Explicit -> Var <$> freshInferenceName (TypeInstantiationInfVar sourceName) ty
      Inferred argName infMech -> getImplicitArg (sourceName, fromMaybe "_" argName) infMech ty
    rest <- applySubst (b@>SubstVal x) $ Abs bs body
    (params, body') <- go expls rest
    return (x:params, body')
  go _ _ = error "zip error"

bindLetPats :: EmitsBoth o
            => Nest UPat i i' -> [CAtomVar o] -> InfererM i' o a -> InfererM i o a
bindLetPats Empty [] cont = cont
bindLetPats (Nest p ps) (x:xs) cont = bindLetPat p x $ bindLetPats ps xs cont
bindLetPats _ _ _ = error "mismatched number of args"

bindLetPat :: EmitsBoth o => UPat i i' -> CAtomVar o -> InfererM i' o a -> InfererM i o a
bindLetPat (WithSrcB pos pat) v cont = addSrcContext pos $ case pat of
  UPatBinder b -> extendSubst (b @> atomVarName v) cont
  UPatProd ps -> do
    let n = nestLength ps
    ty <- return $ getType v
    _  <- fromProdType n ty
    x <- zonk $ Var v
    xs <- forM (iota n) \i -> do
      normalizeProj (ProjectProduct i) x >>= emit . Atom
    bindLetPats ps xs cont
  UPatDepPair (PairB p1 p2) -> do
    let x = Var v
    ty <- return $ getType x
    _  <- fromDepPairType ty
    x' <- zonk x  -- ensure it has a dependent pair type before unpacking
    x1 <- getFst x' >>= zonk >>= emit . Atom
    bindLetPat p1 x1 do
      x2  <- getSnd x' >>= zonk >>= emit . Atom
      bindLetPat p2 x2 do
        cont
  UPatCon ~(InternalName _ _ conName) ps -> do
    (dataDefName, _) <- lookupDataCon =<< renameM conName
    TyConDef sourceName roleExpls paramBs cons <- lookupTyCon dataDefName
    case cons of
      ADTCons [DataConDef _ _ _ idxss] -> do
        when (length idxss /= nestLength ps) $ throw TypeErr $
          "Unexpected number of pattern binders. Expected " ++ show (length idxss)
                                                 ++ " got " ++ show (nestLength ps)
        (params, UnitE) <- inferParams sourceName roleExpls (Abs paramBs UnitE)
        constrainVarTy v $ TypeCon sourceName dataDefName params
        x <- cheapNormalize =<< zonk (Var v)
        xs <- forM idxss \idxs -> normalizeNaryProj idxs x >>= emit . Atom
        bindLetPats ps xs cont
      _ -> throw TypeErr $ "sum type constructor in can't-fail pattern"
  UPatTable ps -> do
    elemTy <- freshType
    let n = fromIntegral (nestLength ps) :: Word32
    let iTy = FinConst n
    idxTy <- asIxType iTy
    ty <- return $ getType $ Var v
    constrainTypesEq ty (idxTy ==> elemTy)
    v' <- zonk $ Var v
    xs <- forM [0 .. n - 1] \i -> do
      emit =<< mkTabApp v' [NewtypeCon (FinCon (NatVal n)) (NatVal $ fromIntegral i)]
    bindLetPats ps xs cont

checkAnn :: EmitsInf o => SourceName -> UAnn req i -> InfererM i o (CType o)
checkAnn binderSourceName ann = case ann of
  UAnn ty -> checkUType ty
  UNoAnn  -> do
    let desc = AnnotationInfVar binderSourceName
    TyVar <$> freshInferenceName desc TyKind

checkUType :: EmitsInf o => UType i -> InfererM i o (CType o)
checkUType t = do
  Type t' <- checkUParam TyKind t
  return t'

checkUParam :: EmitsInf o => Kind CoreIR o -> UType i -> InfererM i o (CAtom o)
checkUParam k uty@(WithSrcE pos _) = addSrcContext pos $
  withReducibleEmissions msg $ withoutEffects $ checkRho noHint uty (sink k)
  where msg = "Can't reduce type expression: " ++ pprint uty

inferTabCon :: forall i o. EmitsBoth o
  => NameHint -> [UExpr i] -> RequiredTy CType o -> InfererM i o (CAtom o)
inferTabCon hint xs reqTy = do
  let n = fromIntegral (length xs) :: Word32
  let finTy = FinConst n
  ctx <- srcPosCtx <$> getErrCtx
  let dataDictHole dTy = Just $ WhenIRE $ DictHole (AlwaysEqual ctx) dTy Full
  case reqTy of
    Infer -> do
      elemTy <- case xs of
        []    -> freshType
        (x:_) -> getType <$> inferRho noHint x
      ixTy <- asIxType finTy
      let tabTy = ixTy ==> elemTy
      xs' <- forM xs \x -> checkRho noHint x elemTy
      dTy <- DictTy <$> dataDictType elemTy
      liftM Var $ emitHinted hint $ TabCon (dataDictHole dTy) tabTy xs'
    Check tabTy -> do
      TabPiType _ b elemTy <- fromTabPiType True tabTy
      constrainTypesEq (binderType b) finTy
      xs' <- forM (enumerate xs) \(i, x) -> do
        let i' = NewtypeCon (FinCon (NatVal n)) (NatVal $ fromIntegral i) :: CAtom o
        elemTy' <- applySubst (b@>SubstVal i') elemTy
        checkRho noHint x elemTy'
      dTy <- case hoist b elemTy of
        HoistSuccess elemTy' -> DictTy <$> dataDictType elemTy'
        HoistFailure _ -> ignoreExcept <$> liftEnvReaderT do
          withFreshBinder noHint finTy \b' ->  do
            elemTy' <- applyRename (b@>binderName b') elemTy
            dTy <- DictTy <$> dataDictType elemTy'
            return $ Pi $ CorePiType ImplicitApp [Inferred Nothing Unify] (UnaryNest b') (EffTy Pure dTy)
      liftM Var $ emitHinted hint $ TabCon (dataDictHole dTy) tabTy xs'

-- Bool flag is just to tweak the reported error message
fromTabPiType :: EmitsBoth o => Bool -> CType o -> InfererM i o (TabPiType CoreIR o)
fromTabPiType _ (TabPi piTy) = return piTy
fromTabPiType expectPi ty = do
  a <- freshType
  b <- freshType
  a' <- asIxType a
  let piTy = nonDepTabPiType a' b
  if expectPi then  constrainTypesEq (TabPi piTy) ty
              else  constrainTypesEq ty (TabPi piTy)
  return piTy

fromProdType :: EmitsBoth o => Int -> CType o -> InfererM i o [CType o]
fromProdType n (ProdTy ts) | length ts == n = return ts
fromProdType n ty = do
  ts <- mapM (const $ freshType) (replicate n ())
  constrainTypesEq (ProdTy ts) ty
  return ts

fromDepPairType :: EmitsBoth o => CType o -> InfererM i o (DepPairType CoreIR o)
fromDepPairType (DepPairTy t) = return t
fromDepPairType ty = throw TypeErr $ "Expected a dependent pair, but got: " ++ pprint ty

addEffects :: EmitsBoth o => EffectRow CoreIR o -> InfererM i o ()
addEffects eff = do
  allowed <- checkAllowedUnconditionally eff
  unless allowed $ do
    effsAllowed <- getAllowedEffects
    eff' <- openEffectRow eff
    constrainEq (Eff effsAllowed) (Eff eff')

checkAllowedUnconditionally :: EffectRow CoreIR o -> InfererM i o Bool
checkAllowedUnconditionally Pure = return True
checkAllowedUnconditionally eff = do
  eff' <- zonk eff
  effAllowed <- getAllowedEffects >>= zonk
  return $ case checkExtends effAllowed eff' of
    Failure _  -> False
    Success () -> True

openEffectRow :: EmitsBoth o => EffectRow CoreIR o -> InfererM i o (EffectRow CoreIR o)
openEffectRow (EffectRow effs NoTail) = extendEffRow effs <$> freshEff
openEffectRow effRow = return effRow

asIxType :: CType o -> InfererM i o (IxType CoreIR o)
asIxType ty = do
  dictTy <- DictTy <$> ixDictType ty
  ctx <- srcPosCtx <$> getErrCtx
  return $ IxType ty $ IxDictAtom $ DictHole (AlwaysEqual ctx) dictTy Full
{-# SCC asIxType #-}

-- === Solver ===

newtype SolverSubst n = SolverSubst (M.Map (CAtomName n) (CAtom n))

instance Pretty (SolverSubst n) where
  pretty (SolverSubst m) = pretty $ M.toList m

class (CtxReader1 m, EnvReader m) => Solver (m::MonadKind1) where
  zonk :: (SubstE AtomSubstVal e, SinkableE e) => e n -> m n (e n)
  extendSolverSubst :: CAtomName n -> CAtom n -> m n ()
  emitSolver :: EmitsInf n => SolverBinding n -> m n (CAtomVar n)
  solveLocal :: (SinkableE e, HoistableE e, RenameE e)
             => (forall l. (EmitsInf l, Ext n l, Distinct l) => m l (e l))
             -> m n (e n)

type SolverOutMap = InfOutMap

data SolverOutFrag (n::S) (l::S) =
  SolverOutFrag (SolverEmissions n l) (Constraints l)
newtype Constraints n = Constraints (SnocList (CAtomName n, CAtom n))
        deriving (Monoid, Semigroup)
type SolverEmissions = RNest (BinderP (AtomNameC CoreIR) SolverBinding)

instance GenericE Constraints where
  type RepE Constraints = ListE (CAtomName `PairE` CAtom)
  fromE (Constraints xs) = ListE [PairE x y | (x,y) <- toList xs]
  {-# INLINE fromE #-}
  toE (ListE xs) = Constraints $ toSnocList $ [(x,y) | PairE x y <- xs]
  {-# INLINE toE #-}

instance SinkableE  Constraints
instance RenameE    Constraints
instance HoistableE Constraints
instance Pretty (Constraints n) where
  pretty (Constraints xs) = pretty $ unsnoc xs

instance GenericB SolverOutFrag where
  type RepB SolverOutFrag = PairB SolverEmissions (LiftB Constraints)
  fromB (SolverOutFrag em subst) = PairB em (LiftB subst)
  toB   (PairB em (LiftB subst)) = SolverOutFrag em subst

instance ProvesExt   SolverOutFrag
instance RenameB     SolverOutFrag
instance BindsNames  SolverOutFrag
instance SinkableB   SolverOutFrag

instance OutFrag SolverOutFrag where
  emptyOutFrag = SolverOutFrag REmpty mempty
  catOutFrags (SolverOutFrag em ss) (SolverOutFrag em' ss') =
    withExtEvidence em' $
      SolverOutFrag (em >>> em') (sink ss <> ss')

instance ExtOutMap InfOutMap SolverOutFrag where
  extendOutMap infOutMap outFrag =
    extendOutMap infOutMap $ liftSolverOutFrag outFrag

newtype SolverM (n::S) (a:: *) =
  SolverM { runSolverM' :: InplaceT SolverOutMap SolverOutFrag SearcherM n a }
  deriving (Functor, Applicative, Monad, MonadFail, Alternative, Searcher,
            ScopeReader, Fallible, CtxReader)

liftSolverM :: EnvReader m => SolverM n a -> m n (Except a)
liftSolverM cont = do
  env <- unsafeGetEnv
  Distinct <- getDistinct
  return do
    maybeResult <- runSearcherM $ runInplaceT (initInfOutMap env) $
                   runSolverM' $ cont
    case maybeResult of
      Nothing -> throw TypeErr "No solution"
      Just (_, result) -> return result
{-# INLINE liftSolverM #-}

instance EnvReader SolverM where
  unsafeGetEnv = SolverM do
    InfOutMap env _ _ _ _ <- getOutMapInplaceT
    return env
  {-# INLINE unsafeGetEnv #-}

newtype SolverEmission (n::S) (l::S) = SolverEmission (BinderP (AtomNameC CoreIR) SolverBinding n l)
instance ExtOutMap SolverOutMap SolverEmission where
  extendOutMap env (SolverEmission e) = env `extendOutMap` toEnvFrag e
instance ExtOutFrag SolverOutFrag SolverEmission where
  extendOutFrag (SolverOutFrag es substs) (SolverEmission e) =
    withSubscopeDistinct e $ SolverOutFrag (RNest es e) (sink substs)

instance Solver SolverM where
  extendSolverSubst v ty = SolverM $
    void $ extendTrivialInplaceT $
      SolverOutFrag REmpty (singleConstraint v ty)
  {-# INLINE extendSolverSubst #-}

  zonk e = SolverM do
    Distinct <- getDistinct
    solverOutMap <- getOutMapInplaceT
    return $ zonkWithOutMap solverOutMap $ sink e
  {-# INLINE zonk #-}

  emitSolver binding = do
    v <- SolverM $ freshExtendSubInplaceT (getNameHint @String "?") \b ->
      (SolverEmission (b:>binding), binderName b)
    toAtomVar v
  {-# INLINE emitSolver #-}

  solveLocal cont = SolverM do
    results <- locallyMutableInplaceT (do
      Distinct <- getDistinct
      EmitsInf <- fabricateEmitsInfEvidenceM
      runSolverM' cont) (\d e -> return $ Abs d e)
    Abs (SolverOutFrag unsolvedInfNames _) result <- return results
    case unsolvedInfNames of
      REmpty -> return result
      _      -> case hoist unsolvedInfNames result of
        HoistSuccess result' -> return result'
        HoistFailure vs ->
          throw TypeErr $ "Ambiguous type variables: " ++ pprint vs
  {-# INLINE solveLocal #-}

instance Unifier SolverM

freshInferenceName :: (EmitsInf n, Solver m) => InfVarDesc -> Kind CoreIR n -> m n (CAtomVar n)
freshInferenceName desc k = do
  ctx <- srcPosCtx <$> getErrCtx
  emitSolver $ InfVarBound k (ctx, desc)
{-# INLINE freshInferenceName #-}

freshSkolemName :: (EmitsInf n, Solver m) => Kind CoreIR n -> m n (CAtomVar n)
freshSkolemName k = emitSolver $ SkolemBound k
{-# INLINE freshSkolemName #-}

type Solver2 (m::MonadKind2) = forall i. Solver (m i)

emptySolverSubst :: SolverSubst n
emptySolverSubst = SolverSubst mempty

singleConstraint :: CAtomName n -> CAtom n -> Constraints n
singleConstraint v ty = Constraints $ toSnocList [(v, ty)]

-- TODO: put this pattern and friends in the Name library? Don't really want to
-- have to think about `eqNameColorRep` just to implement a partial map.
lookupSolverSubst :: forall c n. Color c => SolverSubst n -> Name c n -> AtomSubstVal c n
lookupSolverSubst (SolverSubst m) name =
  case eqColorRep of
    Nothing -> Rename name
    Just (ColorsEqual :: ColorsEqual c (AtomNameC CoreIR))-> case M.lookup name m of
      Nothing -> Rename name
      Just ty -> SubstVal ty

applySolverSubstE :: (SubstE AtomSubstVal e, Distinct n)
                  => Env n -> SolverSubst n -> e n -> e n
applySolverSubstE env solverSubst@(SolverSubst m) e =
  if M.null m then e else fmapNames env (lookupSolverSubst solverSubst) e

zonkWithOutMap :: (SubstE AtomSubstVal e, Distinct n)
               => InfOutMap n -> e n -> e n
zonkWithOutMap (InfOutMap bindings solverSubst _ _ _) e =
  applySolverSubstE bindings solverSubst e

liftSolverOutFrag :: Distinct l => SolverOutFrag n l -> InfOutFrag n l
liftSolverOutFrag (SolverOutFrag emissions subst) =
  InfOutFrag (liftSolverEmissions emissions) mempty subst

liftSolverEmissions :: Distinct l => SolverEmissions n l -> InfEmissions n l
liftSolverEmissions emissions =
  fmapRNest (\(b:>emission) -> (b:>RightE emission)) emissions

fmapRNest :: (forall ii ii'. b ii ii' -> b' ii ii')
          -> RNest b  i i'
          -> RNest b' i i'
fmapRNest _ REmpty = REmpty
fmapRNest f (RNest rest b) = RNest (fmapRNest f rest) (f b)

instance GenericE SolverSubst where
  -- XXX: this is a bit sketchy because it's not actually bijective...
  type RepE SolverSubst = ListE (PairE CAtomName CAtom)
  fromE (SolverSubst m) = ListE $ map (uncurry PairE) $ M.toList m
  {-# INLINE fromE #-}
  toE (ListE pairs) = SolverSubst $ M.fromList $ map fromPairE pairs
  {-# INLINE toE #-}

instance SinkableE SolverSubst where
instance RenameE SolverSubst where
instance HoistableE SolverSubst

constrainTypesEq :: EmitsInf o => CType o -> CType o -> InfererM i o ()
constrainTypesEq t1 t2 = constrainEq (Type t1) (Type t2) -- TODO: use a type class instead?

constrainEq :: EmitsInf o => CAtom o -> CAtom o -> InfererM i o ()
constrainEq t1 t2 = do
  t1' <- zonk t1
  t2' <- zonk t2
  msg <- liftEnvReaderM $ do
    ab <- renameForPrinting $ PairE t1' t2'
    return $ canonicalizeForPrinting ab \(Abs infVars (PairE t1Pretty t2Pretty)) ->
              "Expected: " ++ pprint t1Pretty
         ++ "\n  Actual: " ++ pprint t2Pretty
         ++ (case infVars of
               Empty -> ""
               _ -> "\n(Solving for: " ++ pprint (nestToList pprint infVars) ++ ")")
  void $ addContext msg $ liftSolverMInf $ unify t1' t2'

class (Alternative1 m, Searcher1 m, Fallible1 m, Solver m) => Unifier m

class (AlphaEqE e, SinkableE e, SubstE AtomSubstVal e) => Unifiable (e::E) where
  unifyZonked :: EmitsInf n => e n -> e n -> SolverM n ()

tryConstrainEq :: EmitsInf o => CAtom o -> CAtom o -> InfererM i o ()
tryConstrainEq t1 t2 = do
  constrainEq t1 t2 `catchErr` \errs -> case errs of
    Errs [Err TypeErr _ _] -> return ()
    _ -> throwErrs errs

unify :: (EmitsInf n, Unifiable e) => e n -> e n -> SolverM n ()
unify e1 e2 = do
  e1' <- zonk e1
  e2' <- zonk e2
  (unifyZonked e1' e2' <!> throw TypeErr "")
{-# INLINE unify #-}
{-# SCC unify #-}

instance Unifiable (Atom CoreIR) where
  unifyZonked e1 e2 = confuseGHC >>= \_ -> case sameConstructor e1 e2 of
    False -> case (e1, e2) of
      (t, Var (AtomVar v _)) -> extendSolution v t
      (Var (AtomVar v _), t) -> extendSolution v t
      _ -> empty
    True -> case (e1, e2) of
      (Var (AtomVar v' _), Var (AtomVar v _)) ->
        if v == v' then return () else extendSolution v e1 <|> extendSolution v' e2
      (Eff eff, Eff eff') -> unify eff eff'
      (Type t, Type t') -> case (t, t') of
        (Pi piTy, Pi piTy') -> unify piTy piTy'
        (TabPi piTy, TabPi piTy') -> unifyTabPiType piTy piTy'
        (TC con, TC con') -> do
          GenericOpRep name  ts  xs  [] <- return $ fromEGenericOpRep con
          GenericOpRep name' ts' xs' [] <- return $ fromEGenericOpRep con'
          guard $ name == name' && length ts == length ts' && length xs == length xs'
          zipWithM_ unify (Type <$> ts) (Type <$> ts')
          zipWithM_ unify xs xs'
        (DictTy d, DictTy d') -> unify d d'
        (NewtypeTyCon con, NewtypeTyCon con') -> unify con con'
        _ -> unifyEq t t'
      _ -> unifyEq e1 e2

instance Unifiable DictType where
  unifyZonked (DictType _ c params) (DictType _ c' params') =
    guard (c == c') >> zipWithM_ unify params params'
  {-# INLINE unifyZonked #-}

instance Unifiable NewtypeTyCon where
  unifyZonked e1 e2 = case (e1, e2) of
    (Nat, Nat) -> return ()
    (Fin n, Fin n') -> unify n n'
    (EffectRowKind, EffectRowKind) -> return ()
    (UserADTType _ c params, UserADTType _ c' params') -> guard (c == c') >> unify params params'
    _ -> empty

instance Unifiable (IxType CoreIR) where
  -- We ignore the dictionaries because we assume coherence
  unifyZonked (IxType t _) (IxType t' _) = unifyZonked t t'

-- TODO: do this directly rather than going via `CAtom` using `Type`. We just
-- need to deal with `TyVar`.
instance Unifiable (Type CoreIR) where
  unifyZonked t t' = unifyZonked (Type t) (Type t')

instance Unifiable TyConParams where
  -- We ignore the dictionaries because we assume coherence
  unifyZonked ps ps' = zipWithM_ unify (ignoreSynthParams ps) (ignoreSynthParams ps')

instance Unifiable (EffectRow CoreIR) where
  unifyZonked x1 x2 =
        unifyDirect x1 x2
    <|> unifyDirect x2 x1
    <|> unifyZip x1 x2

   where
     unifyDirect :: EmitsInf n => EffectRow CoreIR n -> EffectRow CoreIR n -> SolverM n ()
     unifyDirect r@(EffectRow effs' mv') (EffectRow effs (EffectRowTail v)) | null (eSetToList effs) =
       case mv' of
         EffectRowTail v' | v == v' -> guard $ null $ eSetToList effs'
         _ -> extendSolution (atomVarName v) (Eff r)
     unifyDirect _ _ = empty
     {-# INLINE unifyDirect #-}

     unifyZip :: EmitsInf n => EffectRow CoreIR n -> EffectRow CoreIR n -> SolverM n ()
     unifyZip r1 r2 = case (r1, r2) of
       (EffectRow effs1 t1, EffectRow effs2 t2) | not (eSetNull effs1 || eSetNull effs2) -> do
         let extras1 = effs1 `eSetDifference` effs2
         let extras2 = effs2 `eSetDifference` effs1
         newRow <- freshEff
         unify (EffectRow mempty t1) (extendEffRow extras2 newRow)
         unify (extendEffRow extras1 newRow) (EffectRow mempty t2)
       _ -> unifyEq r1 r2

unifyEq :: AlphaEqE e => e n -> e n -> SolverM n ()
unifyEq e1 e2 = guard =<< alphaEq e1 e2
{-# INLINE unifyEq #-}

instance Unifiable CorePiType where
  unifyZonked (CorePiType appExpl1 expls1 bsTop1 effTy1)
              (CorePiType appExpl2 expls2 bsTop2 effTy2) = do
    unless (appExpl1 == appExpl2) empty
    unless (expls1 == expls2) empty
    go (Abs bsTop1 effTy1) (Abs bsTop2 effTy2)
   where
    go :: EmitsInf n
       => Abs (Nest CBinder) (EffTy CoreIR) n
       -> Abs (Nest CBinder) (EffTy CoreIR) n
       -> SolverM n ()
    go (Abs Empty (EffTy e1 t1)) (Abs Empty (EffTy e2 t2)) = unify t1 t2 >> unify e1 e2
    go (Abs (Nest (b1:>t1) bs1) rest1)
       (Abs (Nest (b2:>t2) bs2) rest2) = do
      unify t1 t2
      v <- freshSkolemName t1
      ab1 <- zonk =<< applySubst (b1@>SubstVal (Var v)) (Abs bs1 rest1)
      ab2 <- zonk =<< applySubst (b2@>SubstVal (Var v)) (Abs bs2 rest2)
      go ab1 ab2
    go _ _ = empty

unifyTabPiType :: EmitsInf n => TabPiType CoreIR n -> TabPiType CoreIR n -> SolverM n ()
unifyTabPiType (TabPiType _ b1 ty1) (TabPiType _ b2 ty2) = do
  let ann1 = binderType b1
  let ann2 = binderType b2
  unify ann1 ann2
  v <- freshSkolemName ann1
  ty1' <- applySubst (b1@>SubstVal (Var v)) ty1
  ty2' <- applySubst (b2@>SubstVal (Var v)) ty2
  unify ty1'  ty2'

extendSolution :: CAtomName n -> CAtom n -> SolverM n ()
extendSolution v t =
  isInferenceName v >>= \case
    True -> do
      when (v `isFreeIn` t) $ throw TypeErr $ "Occurs check failure: " ++ pprint (v, t)
      -- When we unify under a pi binder we replace its occurrences with a
      -- skolem variable. We don't want to unify with terms containing these
      -- variables because that would mean inferring dependence, which is a can
      -- of worms.
      forM_ (freeAtomVarsList t) \fv ->
        whenM (isSkolemName fv) $ throw TypeErr $ "Can't unify with skolem vars"
      extendSolverSubst v t
    False -> empty

isInferenceName :: EnvReader m => CAtomName n -> m n Bool
isInferenceName v = lookupEnv v >>= \case
  AtomNameBinding (SolverBound (InfVarBound _ _)) -> return True
  _ -> return False
{-# INLINE isInferenceName #-}

isSkolemName :: EnvReader m => CAtomName n -> m n Bool
isSkolemName v = lookupEnv v >>= \case
  AtomNameBinding (SolverBound (SkolemBound _)) -> return True
  _ -> return False
{-# INLINE isSkolemName #-}

freshType :: (EmitsInf n, Solver m) => m n (CType n)
freshType = TyVar <$> freshInferenceName MiscInfVar TyKind
{-# INLINE freshType #-}

freshAtom :: (EmitsInf n, Solver m) => Type CoreIR n -> m n (CAtom n)
freshAtom t = Var <$> freshInferenceName MiscInfVar t
{-# INLINE freshAtom #-}

freshEff :: (EmitsInf n, Solver m) => m n (EffectRow CoreIR n)
freshEff = EffectRow mempty . EffectRowTail <$> freshInferenceName MiscInfVar EffKind
{-# INLINE freshEff #-}

renameForPrinting :: (EnvReader m, HoistableE e, SinkableE e, RenameE e)
                   => e n -> m n (Abs (Nest (AtomNameBinder CoreIR)) e n)
renameForPrinting e = do
  infVars <- filterM isInferenceVar $ freeAtomVarsList e
  let ab = abstractFreeVarsNoAnn infVars e
  let hints = take (length infVars) $ map getNameHint $
                map (:[]) ['a'..'z'] ++ map show [(0::Int)..]
  Distinct <- getDistinct
  scope <- toScope <$> unsafeGetEnv  -- TODO: figure out how to do it safely
  return $ withManyFresh hints scope \bs' ->
    runScopeReaderM (scope `extendOutMap` toScopeFrag bs') do
      Abs bsAbs eAbs <- sinkM ab
      e' <- applyRename (bsAbs@@>nestToNames bs') eAbs
      return $ Abs bs' e'

-- === dictionary synthesis ===

synthTopE :: (EnvReader m, Fallible1 m, DictSynthTraversable e) => e n -> m n (e n)
synthTopE block = do
  (liftExcept =<<) $ liftDictSynthTraverserM $ dsTraverse block
{-# SCC synthTopE #-}

synthTyConDef :: (EnvReader m, Fallible1 m) => TyConDef n -> m n (TyConDef n)
synthTyConDef (TyConDef sn roleExpls bs body) = (liftExcept =<<) $ liftDictSynthTraverserM do
  dsTraverseExplBinders (snd <$> roleExpls) bs \bs' ->
    TyConDef sn roleExpls bs' <$> dsTraverse body
{-# SCC synthTyConDef #-}

-- Given a simplified dict (an Atom of type `DictTy _` in the
-- post-simplification IR), and a requested, more general, dict type, generalize
-- the dict to match the more general type. This is only possible because we
-- require that instances are polymorphic in data-role parameters. It would be
-- valid to implement `generalizeDict` by re-synthesizing the whole dictionary,
-- but we know that the derivation tree has to be the same, so we take the
-- shortcut of just generalizing the data parameters.
generalizeDict :: (EnvReader m) => CType n -> Dict n -> m n (Dict n)
generalizeDict ty dict = do
  result <- liftSolverM $ solveLocal $ generalizeDictAndUnify (sink ty) (sink dict)
  case result of
    Failure e -> error $ "Failed to generalize " ++ pprint dict
      ++ " to " ++ pprint ty ++ " because " ++ pprint e
    Success ans -> return ans

generalizeDictAndUnify :: EmitsInf n => CType n -> Dict n -> SolverM n (Dict n)
generalizeDictAndUnify ty dict = do
  dict' <- generalizeDictRec dict
  dictTy <- return $ getType dict'
  unify ty dictTy
  zonk dict'

generalizeDictRec :: EmitsInf n => Dict n -> SolverM n (Dict n)
generalizeDictRec dict = do
  -- TODO: we should be able to avoid the normalization here . We only need it
  -- because we sometimes end up with superclass projections. But they shouldn't
  -- really be allowed to occur in the post-simplification IR.
  DictCon _ dict' <- cheapNormalize dict
  mkDictAtom =<< case dict' of
    InstanceDict instanceName args -> do
      InstanceDef _ roleExpls bs _ _ <- lookupInstanceDef instanceName
      args' <- generalizeInstanceArgs roleExpls bs args
      return $ InstanceDict instanceName args'
    IxFin _ -> IxFin <$> Var <$> freshInferenceName MiscInfVar NatTy
    InstantiatedGiven _ _ -> notSimplifiedDict
    SuperclassProj _ _    -> notSimplifiedDict
    DataData ty           -> DataData <$> TyVar <$> freshInferenceName MiscInfVar ty
    where notSimplifiedDict = error $ "Not a simplified dict: " ++ pprint dict

generalizeInstanceArgs :: EmitsInf n => [RoleExpl] -> Nest CBinder n l -> [CAtom n] -> SolverM n [CAtom n]
generalizeInstanceArgs [] Empty [] = return []
generalizeInstanceArgs ((role,_):expls) (Nest (b:>ty) bs) (arg:args) = do
  arg' <- case role of
    -- XXX: for `TypeParam` we can just emit a fresh inference name rather than
    -- traversing the whole type like we do in `Generalize.hs`. The reason is
    -- that it's valid to implement `generalizeDict` by synthesizing an entirely
    -- fresh dictionary, and if we were to do that, we would infer this type
    -- parameter exactly as we do here, using inference.
    TypeParam -> Var <$> freshInferenceName MiscInfVar TyKind
    DictParam -> generalizeDictAndUnify ty arg
    DataParam -> Var <$> freshInferenceName MiscInfVar ty
  Abs bs' UnitE <- applySubst (b@>SubstVal arg') (Abs bs UnitE)
  args' <- generalizeInstanceArgs expls bs' args
  return $ arg':args'
generalizeInstanceArgs _ _ _ = error "zip error"

synthInstanceDefAndAddSynthCandidate
  :: (Mut n, TopBuilder m, EnvReader m,  Fallible1 m) => InstanceDef n -> m n (InstanceName n)
synthInstanceDefAndAddSynthCandidate def@(InstanceDef className expls bs params (InstanceBody superclasses _)) = do
  let emptyDef = InstanceDef className expls bs params $ InstanceBody superclasses []
  instanceName <- emitInstanceDef emptyDef
  addInstanceSynthCandidate className instanceName
  synthInstanceDefRec instanceName def
  return instanceName

emitInstanceDef :: (Mut n, TopBuilder m) => InstanceDef n -> m n (Name InstanceNameC n)
emitInstanceDef instanceDef@(InstanceDef className _ _ _ _) = do
  ty <- getInstanceType instanceDef
  emitBinding (getNameHint className) $ InstanceBinding instanceDef ty

type InstanceDefAbsBodyT =
      ((ListE CAtom) `PairE` (ListE CAtom) `PairE` (ListE CAtom) `PairE` (ListE CAtom))

pattern InstanceDefAbsBody :: [CAtom n] -> [CAtom n] -> [CAtom n] -> [CAtom n]
                           -> InstanceDefAbsBodyT n
pattern InstanceDefAbsBody params superclasses doneMethods todoMethods =
  ListE params `PairE` (ListE superclasses) `PairE` (ListE doneMethods) `PairE` (ListE todoMethods)

type InstanceDefAbsT n = ([RoleExpl], Abs (Nest CBinder) InstanceDefAbsBodyT n)

pattern InstanceDefAbs :: [RoleExpl] -> Nest CBinder h n -> [CAtom n] -> [CAtom n] -> [CAtom n] -> [CAtom n]
                       -> InstanceDefAbsT h
pattern InstanceDefAbs expls bs params superclasses doneMethods todoMethods =
  (expls, Abs bs (InstanceDefAbsBody params superclasses doneMethods todoMethods))

synthInstanceDefRec
  :: (Mut n, TopBuilder m, EnvReader m,  Fallible1 m) => InstanceName n -> InstanceDef n -> m n ()
synthInstanceDefRec instanceName def = do
  InstanceDef className roleExplsTop bs params (InstanceBody superclasses methods) <- return def
  let ab = InstanceDefAbs roleExplsTop bs params superclasses [] methods
  recur ab className instanceName
  where
    recur :: (Mut n, TopBuilder m, EnvReader m, Fallible1 m)
          => InstanceDefAbsT n -> ClassName n -> InstanceName n -> m n ()
    recur (InstanceDefAbs _ _ _ _ _ []) _ _ = return ()
    recur (roleExpls, ab) cname iname = do
      (def', ab') <- liftExceptEnvReaderM $ refreshAbs ab
        \bs' (InstanceDefAbsBody ps scs doneMethods (m:ms)) -> do
          EnvReaderT $ ReaderT \(Distinct, env) -> do
            let env' = extendSynthCandidatess (snd<$>roleExpls) bs' env
            flip runReaderT (Distinct, env') $ runEnvReaderT' do
              m' <- synthTopE m
              let doneMethods' = doneMethods ++ [m']
              let ab' = InstanceDefAbs roleExpls bs' ps scs doneMethods' ms
              let def' = InstanceDef cname roleExpls bs' ps $ InstanceBody scs doneMethods'
              return (def', ab')
      updateTopEnv $ UpdateInstanceDef iname def'
      recur ab' cname iname

synthInstanceDef
  :: (EnvReader m, Fallible1 m) => InstanceDef n -> m n (InstanceDef n)
synthInstanceDef (InstanceDef className expls bs params body) = do
  liftExceptEnvReaderM $ refreshAbs (Abs bs (ListE params `PairE` body))
    \bs' (ListE params' `PairE` InstanceBody superclasses methods) -> do
       EnvReaderT $ ReaderT \(Distinct, env) -> do
         let env' = extendSynthCandidatess (snd<$>expls) bs' env
         flip runReaderT (Distinct, env') $ runEnvReaderT' do
           methods' <- mapM synthTopE methods
           return $ InstanceDef className expls bs' params' $ InstanceBody superclasses methods'

-- main entrypoint to dictionary synthesizer
trySynthTerm :: (Fallible1 m, EnvReader m) => CType n -> RequiredMethodAccess -> m n (SynthAtom n)
trySynthTerm ty reqMethodAccess = do
  hasInferenceVars ty >>= \case
    True -> throw TypeErr "Can't synthesize a dictionary for a type with inference vars"
    False -> do
      synthTy <- liftExcept $ typeAsSynthType ty
      solutions <- liftSyntherM $ synthTerm synthTy reqMethodAccess
      case solutions of
        [] -> throw TypeErr $ "Couldn't synthesize a class dictionary for: " ++ pprint ty
        [d] -> cheapNormalize d -- normalize to reduce code size
        _ -> throw TypeErr $ "Multiple candidate class dictionaries for: " ++ pprint ty
{-# SCC trySynthTerm #-}

type SynthAtom = CAtom
type SynthPiType n = ([Explicitness], Abs (Nest CBinder) DictType n)
data SynthType n =
   SynthDictType (DictType n)
 | SynthPiType (SynthPiType n)
   deriving (Show, Generic)

data Givens n = Givens { fromGivens :: HM.HashMap (EKey SynthType n) (SynthAtom n) }

class (Alternative1 m, Searcher1 m, EnvReader m, EnvExtender m)
    => Synther m where
  getGivens :: m n (Givens n)
  withGivens :: Givens n -> m n a -> m n a

newtype SyntherM (n::S) (a:: *) = SyntherM
  { runSyntherM' :: OutReaderT Givens (EnvReaderT []) n a }
  deriving ( Functor, Applicative, Monad, EnvReader, EnvExtender
           , ScopeReader, MonadFail
           , Alternative, Searcher, OutReader Givens)

instance Synther SyntherM where
  getGivens = askOutReader
  {-# INLINE getGivens #-}
  withGivens givens cont = localOutReader givens cont
  {-# INLINE withGivens #-}

liftSyntherM :: EnvReader m => SyntherM n a -> m n [a]
liftSyntherM cont =
  liftEnvReaderT do
    initGivens <- givensFromEnv
    runOutReaderT initGivens $ runSyntherM' cont
{-# INLINE liftSyntherM #-}

givensFromEnv :: EnvReader m => m n (Givens n)
givensFromEnv = do
  env <- withEnv moduleEnv
  givens <- mapM toAtomVar $ lambdaDicts $ envSynthCandidates env
  getSuperclassClosure (Givens HM.empty) (Var <$> givens)
{-# SCC givensFromEnv #-}

extendGivens :: Synther m => [SynthAtom n] -> m n a -> m n a
extendGivens newGivens cont = do
  prevGivens <- getGivens
  finalGivens <- getSuperclassClosure prevGivens newGivens
  withGivens finalGivens cont
{-# INLINE extendGivens #-}

getSynthType :: SynthAtom n -> SynthType n
getSynthType x = ignoreExcept $ typeAsSynthType (getType x)
{-# INLINE getSynthType #-}

typeAsSynthType :: CType n -> Except (SynthType n)
typeAsSynthType = \case
  DictTy dictTy -> return $ SynthDictType dictTy
  Pi (CorePiType ImplicitApp expls bs (EffTy Pure (DictTy d))) -> return $ SynthPiType (expls, Abs bs d)
  ty -> Failure $ Errs [Err TypeErr mempty $ "Can't synthesize terms of type: " ++ pprint ty]
{-# SCC typeAsSynthType #-}

getSuperclassClosure :: EnvReader m => Givens n -> [SynthAtom n] -> m n (Givens n)
getSuperclassClosure givens newGivens = do
  Distinct <- getDistinct
  env <- unsafeGetEnv
  return $ getSuperclassClosurePure env givens newGivens
{-# INLINE getSuperclassClosure #-}

getSuperclassClosurePure
  :: Distinct n => Env n -> Givens n -> [SynthAtom n] -> Givens n
getSuperclassClosurePure env givens newGivens =
  snd $ runState (runEnvReaderT env (mapM_ visitGiven newGivens)) givens
  where
    visitGiven :: SynthAtom n -> EnvReaderT (State (Givens n)) n ()
    visitGiven x = alreadyVisited x >>= \case
      True -> return ()
      False -> do
        markAsVisited x
        parents <- getDirectSuperclasses x
        mapM_ visitGiven parents

    alreadyVisited :: SynthAtom n -> EnvReaderT (State (Givens n)) n Bool
    alreadyVisited x = do
      Givens m <- get
      ty <- return $ getSynthType x
      return $ EKey ty `HM.member` m

    markAsVisited :: SynthAtom n -> EnvReaderT (State (Givens n)) n ()
    markAsVisited x = do
      ty <- return $ getSynthType x
      modify \(Givens m) -> Givens $ HM.insert (EKey ty) x m

    getDirectSuperclasses :: SynthAtom n -> EnvReaderT (State (Givens n)) n [SynthAtom n]
    getDirectSuperclasses synthExpr = do
      synthTy <- return $ getSynthType synthExpr
      superclasses <- case synthTy of
        SynthPiType _ -> return []
        SynthDictType dTy -> getSuperclassTys dTy
      forM (enumerate superclasses) \(i, ty) -> do
        return $ DictCon ty $ SuperclassProj synthExpr i

synthTerm :: SynthType n -> RequiredMethodAccess -> SyntherM n (SynthAtom n)
synthTerm targetTy reqMethodAccess = confuseGHC >>= \_ -> case targetTy of
  SynthPiType (expls, ab) -> do
    ab' <- withGivenBinders expls ab \bs targetTy' -> do
      Abs bs <$> synthTerm (SynthDictType targetTy') reqMethodAccess
    Abs bs synthExpr <- return ab'
    liftM Lam $ coreLamExpr ImplicitApp expls $ Abs bs $ PairE Pure (WithoutDecls synthExpr)
  SynthDictType dictTy -> case dictTy of
    DictType "Ix" _ [Type (NewtypeTyCon (Fin n))] -> return $ DictCon (DictTy dictTy) $ IxFin n
    DictType "Data" _ [Type t] -> do
      void (synthDictForData dictTy <!> synthDictFromGiven dictTy)
      return $ DictCon (DictTy dictTy) $ DataData t
    _ -> do
      dict <- synthDictFromInstance dictTy <!> synthDictFromGiven dictTy
      case dict of
        DictCon _ (InstanceDict instanceName _) -> do
          isReqMethodAccessAllowed <- reqMethodAccess `isMethodAccessAllowedBy` instanceName
          if isReqMethodAccessAllowed
            then return dict
            else empty
        _ -> return dict
{-# SCC synthTerm #-}

coreLamExpr :: EnvReader m => AppExplicitness
            -> [Explicitness] -> Abs (Nest CBinder) (PairE (EffectRow CoreIR) CBlock) n
            -> m n (CoreLamExpr n)
coreLamExpr appExpl expls ab = liftEnvReaderM do
  refreshAbs ab \bs' (PairE effs' body') -> do
    EffTy _ resultTy <- blockEffTy body'
    return $ CoreLamExpr (CorePiType appExpl expls bs' (EffTy effs' resultTy)) (LamExpr bs' body')

withGivenBinders
  :: (SinkableE e, RenameE e) => [Explicitness] -> Abs (Nest CBinder) e n
  -> (forall l. DExt n l => Nest CBinder n l -> e l -> SyntherM l a)
  -> SyntherM n a
withGivenBinders explsTop (Abs bsTop e) contTop =
  runSubstReaderT idSubst $ go explsTop bsTop \bsTop' -> do
    e' <- renameM e
    liftSubstReaderT $ contTop bsTop' e'
 where
   go :: [Explicitness] -> Nest CBinder i i'
      -> (forall o'. DExt o o' => Nest CBinder o o' -> SubstReaderT Name SyntherM i' o' a)
      -> SubstReaderT Name SyntherM i o a
   go expls bs cont = case (expls, bs) of
     ([], Empty) -> getDistinct >>= \Distinct -> cont Empty
     (expl:explsRest, Nest b rest) -> do
       argTy <- renameM $ binderType b
       withFreshBinder (getNameHint b) argTy \b' -> do
         givens <- case expl of
           Inferred _ (Synth _) -> return [Var $ binderVar b']
           _ -> return []
         s <- getSubst
         liftSubstReaderT $ extendGivens givens $
           runSubstReaderT (s <>> b@>binderName b') $
             go explsRest rest \rest' -> cont (Nest b' rest')
     _ -> error "zip error"

isMethodAccessAllowedBy :: EnvReader m =>  RequiredMethodAccess -> InstanceName n -> m n Bool
isMethodAccessAllowedBy access instanceName = do
  InstanceDef className _ _ _ (InstanceBody _ methods) <- lookupInstanceDef instanceName
  let numInstanceMethods = length methods
  ClassDef _ _ _ _ _ _ methodTys <- lookupClassDef className
  let numClassMethods = length methodTys
  case access of
    Full                  -> return $ numClassMethods == numInstanceMethods
    Partial numReqMethods -> return $ numReqMethods   <= numInstanceMethods

synthDictFromGiven :: DictType n -> SyntherM n (SynthAtom n)
synthDictFromGiven targetTy = do
  givens <- ((HM.elems . fromGivens) <$> getGivens)
  asum $ givens <&> \given -> do
    case getSynthType given of
      SynthDictType givenDictTy -> do
        guard =<< alphaEq targetTy givenDictTy
        return given
      SynthPiType givenPiTy -> do
        args <- instantiateSynthArgs targetTy givenPiTy
        return $ DictCon (DictTy targetTy) $ InstantiatedGiven given args

synthDictFromInstance :: DictType n -> SyntherM n (SynthAtom n)
synthDictFromInstance targetTy@(DictType _ targetClass _) = do
  instances <- getInstanceDicts targetClass
  asum $ instances <&> \candidate -> do
    CorePiType _ expls bs (EffTy _ (DictTy candidateTy)) <- lookupInstanceTy candidate
    args <- instantiateSynthArgs targetTy (expls, Abs bs candidateTy)
    return $ DictCon (DictTy targetTy) $ InstanceDict candidate args

instantiateSynthArgs :: DictType n -> SynthPiType n -> SyntherM n [CAtom n]
instantiateSynthArgs targetTop (explsTop, Abs bsTop resultTyTop) = do
  ListE args <- (liftExceptAlt =<<) $ liftSolverM $ solveLocal do
    args <- runSubstReaderT idSubst $ go (sink targetTop) explsTop (sink $ Abs bsTop resultTyTop)
    zonk $ ListE args
  forM args \case
    DictHole _ argTy req -> liftExceptAlt (typeAsSynthType argTy) >>= flip synthTerm req
    arg -> return arg
 where
   go :: EmitsInf o
      => DictType o -> [Explicitness] -> Abs (Nest CBinder) DictType i
      -> SubstReaderT AtomSubstVal SolverM i o [CAtom o]
   go target allExpls (Abs bs proposed) = case (allExpls, bs) of
     ([], Empty) -> do
       proposed' <- substM proposed
       liftSubstReaderT $ unify target proposed'
       return []
     (expl:expls, Nest b rest) -> do
       argTy <- substM $ binderType b
       arg <- liftSubstReaderT case expl of
         Explicit -> error "instances shouldn't have explicit args"
         Inferred _ Unify -> Var <$> freshInferenceName MiscInfVar argTy
         Inferred _ (Synth req) -> return $ DictHole (AlwaysEqual emptySrcPosCtx) argTy req
       liftM (arg:) $ extendSubst (b@>SubstVal arg) $ go target expls (Abs rest proposed)
     _ -> error "zip error"

synthDictForData :: forall n. DictType n -> SyntherM n (SynthAtom n)
synthDictForData dictTy@(DictType "Data" dName [Type ty]) = case ty of
  -- TODO Deduplicate vs CheckType.checkDataLike
  -- The "Var" case is different
  TyVar _ -> synthDictFromGiven dictTy
  TabPi (TabPiType _ b eltTy) -> recurBinder (Abs b eltTy) >> success
  DepPairTy (DepPairType _ b@(_:>l) r) -> do
    recur l >> recurBinder (Abs b r) >> success
  NewtypeTyCon nt -> do
    (_, ty') <- unwrapNewtypeType nt
    recur ty' >> success
  TC con -> case con of
    BaseType _       -> success
    ProdType as      -> mapM_ recur as >> success
    SumType  cs      -> mapM_ recur cs >> success
    RefType _ _      -> success
    HeapType         -> success
    _ -> notData
  _   -> notData
  where
    recur ty' = synthDictForData $ DictType "Data" dName [Type ty']
    recurBinder :: (RenameB b, BindsEnv b) => Abs b CType n -> SyntherM n (SynthAtom n)
    recurBinder bAbs = refreshAbs bAbs \b' ty'' -> do
      ans <- synthDictForData $ DictType "Data" (sink dName) [Type ty'']
      return $ ignoreHoistFailure $ hoist b' ans
    notData = empty
    success = return $ DictCon (DictTy dictTy) $ DataData ty
synthDictForData dictTy = error $ "Malformed Data dictTy " ++ pprint dictTy

instance GenericE Givens where
  type RepE Givens = HashMapE (EKey SynthType) SynthAtom
  fromE (Givens m) = HashMapE m
  {-# INLINE fromE #-}
  toE (HashMapE m) = Givens m
  {-# INLINE toE #-}

instance SinkableE Givens where

-- === Dictionary synthesis traversal ===

liftDictSynthTraverserM
  :: EnvReader m
  => DictSynthTraverserM n n a
  -> m n (Except a)
liftDictSynthTraverserM m = do
  (ans, LiftE errs) <- liftM runHardFail $ liftBuilderT $
    runStateT1 (runSubstReaderT idSubst $ runDictSynthTraverserM m) (LiftE $ Errs [])
  return $ case errs of
    Errs [] -> Success ans
    _       -> Failure errs

newtype DictSynthTraverserM i o a =
  DictSynthTraverserM
  { runDictSynthTraverserM ::
      SubstReaderT Name (StateT1 (LiftE Errs) (BuilderM CoreIR)) i o a}
  deriving (MonadFail, Fallible, Functor, Applicative, Monad, ScopeReader,
            EnvReader, EnvExtender, Builder CoreIR, SubstReader Name,
            ScopableBuilder CoreIR, MonadState (LiftE Errs o))

instance NonAtomRenamer (DictSynthTraverserM i o) i o where renameN = renameM
instance Visitor (DictSynthTraverserM i o) CoreIR i o where
  visitType = dsTraverse
  visitAtom = dsTraverse
  visitPi   = visitPiDefault
  visitLam  = visitLamNoEmits
instance ExprVisitorNoEmits (DictSynthTraverserM i o) CoreIR i o where
  visitExprNoEmits = visitGeneric

class DictSynthTraversable (e::E) where
  dsTraverse :: e i -> DictSynthTraverserM i o (e o)

instance DictSynthTraversable (TopLam CoreIR) where
  dsTraverse (TopLam d ty lam) = TopLam d <$> visitPiDefault ty <*> visitLamNoEmits lam

instance DictSynthTraversable CAtom where
  dsTraverse atom = case atom of
    DictHole (AlwaysEqual ctx) ty access -> do
      ty' <- cheapNormalize =<< dsTraverse ty
      ans <- liftEnvReaderT $ addSrcContext ctx $ trySynthTerm ty' access
      case ans of
        Failure errs -> put (LiftE errs) >> renameM atom
        Success d    -> return d
    Lam (CoreLamExpr piTy@(CorePiType _ expls _ _) (LamExpr bsLam (Abs decls result))) -> do
      Pi piTy' <- dsTraverse $ Pi piTy
      lam' <- dsTraverseExplBinders expls bsLam \bsLam' -> do
        visitDeclsNoEmits decls \decls' -> do
          LamExpr bsLam' <$> Abs decls' <$> dsTraverse result
      return $ Lam $ CoreLamExpr piTy' lam'
    Var _          -> renameM atom
    SimpInCore _   -> renameM atom
    ProjectElt _ _ _ -> renameM atom
    _ -> visitAtomPartial atom

instance DictSynthTraversable CType where
  dsTraverse ty = case ty of
    Pi (CorePiType appExpl expls bs (EffTy effs resultTy)) -> Pi <$>
      dsTraverseExplBinders expls bs \bs' -> do
        CorePiType appExpl expls bs' <$> (EffTy <$> renameM effs <*> dsTraverse resultTy)
    TyVar _          -> renameM ty
    ProjectEltTy _ _ _ -> renameM ty
    _ -> visitTypePartial ty

instance DictSynthTraversable DataConDefs where dsTraverse = visitGeneric

dsTraverseExplBinders
  :: [Explicitness] -> Nest CBinder i i'
  -> (forall o'. DExt o o' => Nest CBinder o o' -> DictSynthTraverserM i' o' a)
  -> DictSynthTraverserM i o a
dsTraverseExplBinders [] Empty cont = getDistinct >>= \Distinct -> cont Empty
dsTraverseExplBinders (expl:expls) (Nest b bs) cont = do
  ty <- dsTraverse $ binderType b
  withFreshBinder (getNameHint b) ty \b' -> do
    let v = binderName b'
    extendSynthCandidatesDict expl v $ extendRenamer (b@>v) do
      dsTraverseExplBinders expls bs \bs' -> cont $ Nest b' bs'
dsTraverseExplBinders _ _ _ = error "zip error"

extendSynthCandidatesDict :: Explicitness -> CAtomName n -> DictSynthTraverserM i n a -> DictSynthTraverserM i n a
extendSynthCandidatesDict c v cont = DictSynthTraverserM do
  SubstReaderT $ ReaderT \env -> StateT1 \s -> BuilderT do
    extendInplaceTLocal (extendSynthCandidates c v) $ runBuilderT' $
      runStateT1 (runSubstReaderT env $ runDictSynthTraverserM $ cont) s
{-# INLINE extendSynthCandidatesDict #-}

-- === Inference-specific builder patterns ===

-- The higher-order functions in Builder, like `buildLam` can't be easily used
-- in inference because they don't allow for the emission of inference
-- variables, which must be handled each time we leave a scope. In an earlier
-- version we tried to put this logic in the implementation of InfererM's
-- instance of Builder, but it forced us to overfit the Builder API to satisfy
-- the needs of inference, like adding `SubstE AtomSubstVal e` constraints in
-- various places.

type WithExpl     = WithAttrB Explicitness
type WithRoleExpl = WithAttrB RoleExpl

buildBlockInf
  :: EmitsInf n
  => (forall l. (EmitsBoth l, DExt n l) => InfererM i l (CAtom l))
  -> InfererM i n (CBlock n)
buildBlockInf cont = do
  Abs decls (PairE result ty) <- buildDeclsInf do
    ans <- cont
    ty <- cheapNormalize $ getType ans
    return $ PairE ans ty
  let msg = "Block:" <> nest 1 (prettyBlock decls result) <> line
            <> group ("Of type:" <> nest 2 (line <> pretty ty)) <> line
  void $ liftHoistExcept' (docAsStr msg) $ hoist decls ty
  return $ Abs decls result
{-# INLINE buildBlockInf #-}

buildBlockInfWithRecon
  :: (EmitsInf n, RenameE e, HoistableE e, SinkableE e)
  => (forall l. (EmitsBoth l, DExt n l) => InfererM i l (e l))
  -> InfererM i n (PairE CBlock (ReconAbs CoreIR e) n)
buildBlockInfWithRecon cont = do
  ab <- buildDeclsInfUnzonked cont
  (block, recon) <- refreshAbs ab \decls result -> do
    (newResult, recon) <- telescopicCapture decls result
    return (Abs decls newResult, recon)
  return $ PairE block recon
{-# INLINE buildBlockInfWithRecon #-}

buildTabPiInf
  :: EmitsInf n
  => NameHint -> IxType CoreIR n
  -> (forall l. (EmitsInf l, Ext n l) => CAtomVar l -> InfererM i l (CType l))
  -> InfererM i n (TabPiType CoreIR n)
buildTabPiInf hint (IxType t d) body = do
  Abs b resultTy <- buildAbsInf hint Explicit t \v -> withoutEffects $ body v
  return $ TabPiType d b resultTy

buildDepPairTyInf
  :: EmitsInf n
  => NameHint -> DepPairExplicitness -> CType n
  -> (forall l. (EmitsInf l, Ext n l) => CAtomVar l -> InfererM i l (CType l))
  -> InfererM i n (DepPairType CoreIR n)
buildDepPairTyInf hint expl ty body = do
  Abs b resultTy <- buildAbsInf hint Explicit ty body
  return $ DepPairType expl b resultTy

buildAltInf
  :: EmitsInf n
  => CType n
  -> (forall l. (EmitsBoth l, Ext n l) => CAtomVar l -> InfererM i l (CAtom l))
  -> InfererM i n (Alt CoreIR n)
buildAltInf ty body = do
  buildAbsInf noHint Explicit ty \v ->
    buildBlockInf do
      Distinct <- getDistinct
      body $ sink v

-- === EmitsInf predicate ===

type EmitsBoth n = (EmitsInf n, Emits n)

class Mut n => EmitsInf (n::S)
data EmitsInfEvidence (n::S) where
  EmitsInf :: EmitsInf n => EmitsInfEvidence n
instance EmitsInf UnsafeS

fabricateEmitsInfEvidence :: forall n. EmitsInfEvidence n
fabricateEmitsInfEvidence = withFabricatedEmitsInf @n EmitsInf

fabricateEmitsInfEvidenceM :: forall m n. Monad1 m => m n (EmitsInfEvidence n)
fabricateEmitsInfEvidenceM = return fabricateEmitsInfEvidence

withFabricatedEmitsInf :: forall n a. (EmitsInf n => a) -> a
withFabricatedEmitsInf cont = fromWrapWithEmitsInf
 ( TrulyUnsafe.unsafeCoerce ( WrapWithEmitsInf cont :: WrapWithEmitsInf n       a
                                                  ) :: WrapWithEmitsInf UnsafeS a)
newtype WrapWithEmitsInf n r =
  WrapWithEmitsInf { fromWrapWithEmitsInf :: EmitsInf n => r }

-- === IFunType ===

asFFIFunType :: EnvReader m => CType n -> m n (Maybe (IFunType, CorePiType n))
asFFIFunType ty = return do
  Pi piTy <- return ty
  impTy <- checkFFIFunTypeM piTy
  return (impTy, piTy)

checkFFIFunTypeM :: Fallible m => CorePiType n -> m IFunType
checkFFIFunTypeM (CorePiType appExpl (_:expls) (Nest b bs) effTy) = do
  argTy <- checkScalar $ binderType b
  case bs of
    Empty -> do
      resultTys <- checkScalarOrPairType (etTy effTy)
      let cc = case length resultTys of
                 0 -> error "Not implemented"
                 1 -> FFICC
                 _ -> FFIMultiResultCC
      return $ IFunType cc [argTy] resultTys
    Nest b' rest -> do
      let naryPiRest = CorePiType appExpl expls (Nest b' rest) effTy
      IFunType cc argTys resultTys <- checkFFIFunTypeM naryPiRest
      return $ IFunType cc (argTy:argTys) resultTys
checkFFIFunTypeM _ = error "expected at least one argument"

checkScalar :: (IRRep r, Fallible m) => Type r n -> m BaseType
checkScalar (BaseTy ty) = return ty
checkScalar ty = throw TypeErr $ pprint ty

checkScalarOrPairType :: (IRRep r, Fallible m) => Type r n -> m [BaseType]
checkScalarOrPairType (PairTy a b) = do
  tys1 <- checkScalarOrPairType a
  tys2 <- checkScalarOrPairType b
  return $ tys1 ++ tys2
checkScalarOrPairType (BaseTy ty) = return [ty]
checkScalarOrPairType ty = throw TypeErr $ pprint ty

-- === instances ===

instance PrettyE e => Pretty (UDeclInferenceResult e l) where
  pretty = \case
    UDeclResultDone e -> pretty e
    UDeclResultBindName _ block _ -> pretty block
    UDeclResultBindPattern _ block _ -> pretty block

instance SinkableE e => SinkableE (UDeclInferenceResult e) where
  sinkingProofE = todoSinkableProof

instance (RenameE e, CheckableE CoreIR e) => CheckableE CoreIR (UDeclInferenceResult e) where
  checkE = \case
    UDeclResultDone e -> UDeclResultDone <$> checkE e
    UDeclResultBindName ann block ab ->
      UDeclResultBindName ann <$> checkE block <*> renameM ab -- TODO: check result
    UDeclResultBindPattern hint block recon ->
      UDeclResultBindPattern hint <$> checkE block <*> renameM recon -- TODO: check recon

instance HasType CoreIR InfEmission where
  getType = \case
    LeftE  (DeclBinding _ e) -> getType e
    RightE b -> case b of
      InfVarBound t _ -> t
      SkolemBound t   -> t

instance (Monad m, ExtOutMap InfOutMap decls, OutFrag decls)
        => EnvReader (InplaceT InfOutMap decls m) where
  unsafeGetEnv = do
    InfOutMap env _ _ _ _ <- getOutMapInplaceT
    return env

instance (Monad m, ExtOutMap InfOutMap decls, OutFrag decls)
         => EnvExtender (InplaceT InfOutMap decls m) where
  refreshAbs ab cont = UnsafeMakeInplaceT \env decls ->
    refreshAbsPure (toScope env) ab \_ b e -> do
      let subenv = extendOutMap env $ toEnvFrag b
      (ans, d, _) <- unsafeRunInplaceT (cont b e) subenv emptyOutFrag
      case fabricateDistinctEvidence @UnsafeS of
        Distinct -> do
          let env' = extendOutMap (unsafeCoerceE env) d
          return (ans, catOutFrags decls d, env')
  {-# INLINE refreshAbs #-}

instance BindsEnv InfOutFrag where
  toEnvFrag (InfOutFrag frag _ _) = toEnvFrag frag

instance GenericE SynthType where
  type RepE SynthType = EitherE2 DictType (PairE (LiftE [Explicitness]) (Abs (Nest CBinder) DictType))
  fromE (SynthDictType d) = Case0 d
  fromE (SynthPiType   (expl, t)) = Case1 (PairE (LiftE expl) t)
  toE (Case0 d) = SynthDictType d
  toE (Case1 (PairE (LiftE expl) t)) = SynthPiType (expl, t)
  toE _ = error "impossible"

instance AlphaEqE       SynthType
instance AlphaHashableE SynthType
instance SinkableE      SynthType
instance HoistableE     SynthType
instance RenameE        SynthType
instance SubstE AtomSubstVal SynthType

-- See Note [Confuse GHC] from Simplify.hs
confuseGHC :: EnvReader m => m n (DistinctEvidence n)
confuseGHC = getDistinct
{-# INLINE confuseGHC #-}
