-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DefaultSignatures #-}

module Syntax (
    Type, Kind, BaseType (..), ScalarBaseType (..), Except,
    EffectP (..), Effect, UEffect, RWS (..), EffectRowP (..), EffectRow, UEffectRow,
    Binder, Block (..), BlockAnn (..), Decl (..), Decls, DeclBinding (..),
    FieldRowElem (..), FieldRowElems, fromFieldRowElems,
    fieldRowElemsFromList, prependFieldRowElem, extRowAsFieldRowElems, fieldRowElemsAsExtRow,
    pattern StaticRecordTy, pattern RecordTyWithElems,
    Expr (..), Atom (..), Arrow (..), PrimTC (..), Abs (..),
    DictExpr (..), DictType (..),
    PrimExpr (..), PrimCon (..), LitVal (..), PtrLitVal (..), PtrSnapshot (..),
    AlwaysEqual (..),
    PrimEffect (..), PrimOp (..), PrimHof (..),
    LamBinding (..), LamBinder (..), LamExpr (..),
    PiBinding (..), PiBinder (..),
    PiType (..), DepPairType (..), LetAnn (..),
    BinOp (..), UnOp (..), CmpOp (..), SourceMap (..), SourceNameDef (..), LitProg,
    ForAnn, Val, Op, Con, Hof, TC, SuperclassBinders (..),
    ClassDef (..), InstanceDef (..), InstanceBody (..), MethodType (..),
    SynthCandidates (..), Env (..), TopEnv (..), ModuleEnv (..),
    ImportStatus (..), emptyModuleEnv,
    ModuleSourceName (..), LoadedModules (..), Cache (..), ObjectFiles (..),
    BindsEnv (..), BindsOneAtomName (..), AtomNameBinder,
    DataConRefBinding (..), AltP, Alt, AtomBinding (..),
    SolverBinding (..), TopFunBinding (..), SpecializationSpec (..),
    SubstE (..), SubstB (..), Ptr, PtrType,
    AddressSpace (..), Device (..),
    Direction (..), DataDefParams (..), DataDefBinders (..),
    DataDef (..), DataConDef (..), Nest (..),
    mkConsList, mkConsListTy, fromConsList, fromConsListTy, fromLeftLeaningConsListTy,
    mkBundle, mkBundleTy, BundleDesc,
    BaseMonoidP (..), BaseMonoid, getIntLit, getFloatLit, sizeOf, ptrSize,
    SubstVal (..), AtomName, DataDefName, ClassName, MethodName, InstanceName, AtomSubstVal,
    SourceName, SourceNameOr (..), UVar (..), UBinder (..), uBinderSourceName,
    UExpr, UExpr' (..), UConDef, UDataDef (..), UDataDefTrail (..), UDecl (..),
    UFieldRowElems, UFieldRowElem (..),
    ULamExpr (..), UPiExpr (..), UTabLamExpr (..), UTabPiExpr (..), IxBinder,
    TabLamExpr (..), TabPiType (..), IxType (..), IxDict,
    UDeclExpr (..), UForExpr (..), UAlt (..),
    UPat, UPat' (..), UPatAnn (..), UPatAnnArrow (..), UFieldRowPat (..),
    UMethodDef (..), UAnnBinder (..),
    WithSrcE (..), WithSrcB (..), srcPos,
    SourceBlock (..), SourceBlock' (..), EnvQuery (..),
    ModuleName, Module (..), UModule (..), UModulePartialParse (..),
    UMethodType(..), UEffectOpType(..), UResumePolicy(..), UEffectOpDef(..),
    UType, ExtLabeledItemsE (..),
    CmdName (..), LogLevel (..), OutFormat (..),
    EnvReader (..), EnvReaderI (..), EnvReaderIT (..), runEnvReaderIT,
    extendI, liftEnvReaderI, refreshAbsI, refreshLamI,
    EnvExtender (..),  Binding (..),
    TopEnvFrag (..), ToBinding (..), PartialTopEnvFrag (..), withFreshBinders,
    refreshBinders, substBinders, withFreshBinder,
    withFreshLamBinder, withFreshPureLamBinder,
    withFreshPiBinder, catEnvFrags, plainPiBinder,
    EnvFrag (..), lookupEnv, lookupDataDef, lookupClassDef, lookupInstanceDef,
    lookupAtomName, lookupImpFun, lookupModule,
    lookupEnvPure, lookupSourceMap, lookupSourceMapPure,
    withEnv, updateEnv, runEnvReaderT, liftEnvReaderM, liftExceptEnvReaderM,
    liftEnvReaderT, liftSubstEnvReaderM,
    SubstEnvReaderM,
    EnvReaderM, runEnvReaderM,
    EnvReaderT (..), EnvReader2, EnvExtender2,
    naryNonDepPiType, naryNonDepTabPiType, nonDepPiType, nonDepTabPiType,
    fromNonDepPiType, fromNaryNonDepPiType, fromNaryNonDepTabType,
    considerNonDepPiType, trySelectBranch,
    fromNonDepTabType, nonDepDataConTys, bindersTypes,
    atomBindingType, getProjection,
    HasArgType (..), extendEffRow,
    bindingsFragToSynthCandidates,
    getLambdaDicts, getInstanceDicts,
    getAllowedEffects, withAllowedEffects, todoSinkableProof,
    freeAtomVarsList,
    IExpr (..), IBinder (..), IPrimOp, IVal, IType, Size, IFunType (..),
    ImpFunction (..), ImpBlock (..), ImpDecl (..),
    ImpInstr (..), iBinderType,
    ImpFunName, IFunVar, CallingConvention (..), CUDAKernel (..), Backend (..),
    Output (..), PassName (..), Result (..), BenchStats,
    IsCUDARequired (..),
    NaryLamExpr (..), NaryPiType (..), fromNaryLam,
    fromNaryTabLam, fromNaryTabLamExact,
    fromNaryLamExact, fromNaryPiType,
    NonEmpty (..), nonEmpty,
    naryLamExprAsAtom, naryPiTypeAsType,
    ObjectFile (..), ObjectFileName, CFunName, CFun (..),
    pattern IdxRepTy, pattern IdxRepVal,
    pattern IIdxRepTy, pattern IIdxRepVal,
    pattern TagRepTy,
    pattern TagRepVal, pattern Word8Ty,
    pattern UnitTy, pattern PairTy,
    pattern FinConst, pattern RefTy, pattern RawRefTy,
    pattern BaseTy, pattern PtrTy, pattern UnitVal,
    pattern PairVal, pattern TyKind, pattern TabTy, pattern TabVal,
    pattern Pure, pattern LabeledRowKind, pattern EffKind, pattern UPatIgnore,
    pattern ProdTy, pattern ProdVal,
    pattern SumTy, pattern SumVal, pattern MaybeTy, pattern BinaryFunTy,
    pattern BinaryLamExpr,
    pattern NothingAtom, pattern JustAtom, pattern AtomicBlock,
    pattern BoolTy, pattern FalseAtom, pattern TrueAtom,
    (-->), (?-->), (--@), (==>)) where

import Data.List.NonEmpty (NonEmpty (..), nonEmpty)
import Foreign.Ptr

import GHC.Generics (Generic (..))

import Name
import Err

import Core
import Types.Core
import Types.Primitives
import Types.Source
import Types.Imp

-- === outputs ===

type LitProg = [(SourceBlock, Result)]

data Result = Result
                { resultOutputs :: [Output]
                , resultErrs    :: Except () }
              deriving (Show, Eq)

type BenchStats = (Int, Double) -- number of runs, total benchmarking time
data Output =
    TextOut String
  | HtmlOut String
  | PassInfo PassName String
  | EvalTime  Double (Maybe BenchStats)
  | TotalTime Double
  | BenchResult String Double Double (Maybe BenchStats) -- name, compile time, eval time
  | MiscLog String
  -- Used to have | ExportedFun String Atom
    deriving (Show, Eq, Generic)
