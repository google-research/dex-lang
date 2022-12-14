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
    Type, Kind, Dict, BaseType (..), ScalarBaseType (..), Except,
    EffectP (..), Effect, UEffect, RWS (..), EffectRowP (..), EffectRow, UEffectRow,
    Binder, Block (..), BlockAnn (..), Decl (..), Decls, DeclBinding (..),
    FieldRowElem (..), FieldRowElems, fromFieldRowElems,
    fieldRowElemsFromList, prependFieldRowElem, extRowAsFieldRowElems, fieldRowElemsAsExtRow,
    pattern StaticRecordTy, pattern RecordTyWithElems,
    Expr (..), Atom (..), Arrow (..), plainArrows, PrimTC (..), Abs (..),
    DictExpr (..), DictType (..),
    PrimExpr (..), PrimCon (..), LitVal (..), PtrLitVal (..), PtrSnapshot (..),
    AlwaysEqual (..),
    PrimEffect (..), PrimOp (..), Hof (..),
    LamBinding (..), LamExpr (..), EffAbs, lamExprToAtom, naryLamExprToAtom, blockEffects,
    PiBinding (..), PiBinder (..), RolePiBinder (..), ParamRole (..),
    PiType (..), DepPairType (..), LetAnn (..),
    BinOp (..), UnOp (..), CmpOp (..), SourceMap (..), SourceNameDef (..), LitProg,
    ForAnn, Val, Op, Con, TC, SuperclassBinders (..),
    ClassDef (..), InstanceDef (..), InstanceBody (..), MethodType (..),
    EffectDef (..), EffectOpType (..), EffectName,
    SynthCandidates (..), Env (..), TopEnv (..), ModuleEnv (..), SerializedEnv (..),
    ImportStatus (..), emptyModuleEnv,
    ModuleSourceName (..), LoadedModules (..), LoadedObjects (..), Cache (..),
    BindsEnv (..), BindsOneAtomName (..), AtomNameBinder, toBinderNest,
    AltP, Alt, AtomBinding (..),
    SolverBinding (..), TopFunBinding (..), SpecializationSpec (..),
    SubstE (..), SubstB (..), Ptr, PtrType,
    AddressSpace, Device (..),
    Direction (..), DataDefParams (..),
    DataDef (..), DataConDef (..), Nest (..),
    mkConsList, mkConsListTy, fromConsList, fromConsListTy, fromLeftLeaningConsListTy,
    mkBundle, mkBundleTy, BundleDesc,
    BaseMonoid (..), getIntLit, getFloatLit, sizeOf, ptrSize,
    SubstVal (..), AtomName, DataDefName, ClassName, MethodName, InstanceName, AtomSubstVal,
    SpecDictName, SourceName, SourceNameOr (..), UVar (..), UBinder (..), uBinderSourceName,
    SourceOrInternalName (..),
    UExpr, UExpr' (..), UConDef, UDataDef (..), UDataDefTrail (..), UDecl (..),
    UFieldRowElems, UFieldRowElem (..), PrimName (..),
    ULamExpr (..), UPiExpr (..), UTabLamExpr (..), UTabPiExpr (..), IxBinder,
    TabLamExpr (..), TabPiType (..), IxType (..), IxDict, IxMethod (..),
    UDepPairType (..),
    UDeclExpr (..), UForExpr (..), UAlt (..),
    UPat, UPat' (..), UPatAnn (..), UPatAnnArrow (..), UFieldRowPat (..),
    UMethodDef (..), UAnnBinder (..), UAnnBinderArrow (..),
    WithSrcE (..), WithSrcB (..), srcPos,
    SourceBlock, SourceBlockP (..), SourceBlock' (..), SourceBlockMisc (..), EnvQuery (..),
    ModuleName, Module (..), UModule (..), UModulePartialParse (..),
    UMethodType(..), UEffectOpType(..), UResumePolicy(..), UEffectOpDef(..),
    UType, ExtLabeledItemsE (..),
    CmdName (..), LogLevel (..), OutFormat (..),
    EnvReader (..), EnvReaderI (..), EnvReaderIT (..), runEnvReaderIT,
    extendI, liftEnvReaderI, refreshAbsI,
    EnvExtender (..),  Binding (..),
    TopEnvFrag (..), ToBinding (..), PartialTopEnvFrag (..), withFreshBinders,
    refreshBinders, substBinders, withFreshBinder, catEnvFrags,
    plainPiBinder, classPiBinder, piBinderAsBinder,
    EnvFrag (..), lookupEnv, lookupDataDef, lookupClassDef, lookupInstanceDef,
    lookupAtomName, lookupImpFun, lookupModule, lookupFunObjCode,
    lookupEnvPure, lookupSourceMap, lookupSourceMapPure, lookupEffectDef,
    lookupEffectOpDef,
    withEnv, updateEnv, runEnvReaderT, liftEnvReaderM, liftExceptEnvReaderM,
    liftEnvReaderT, liftSubstEnvReaderM,
    SubstEnvReaderM,
    EnvReaderM, runEnvReaderM,
    EnvReaderT (..), EnvReader2, EnvExtender2,
    nonDepPiType, nonDepTabPiType, fromNonDepPiType,
    considerNonDepPiType, trySelectBranch,
    fromNonDepTabType, nonDepDataConTys, bindersTypes,
    atomBindingType, getProjection,
    HasArgType (..), extendEffRow,
    bindingsFragToSynthCandidates,
    getLambdaDicts, getInstanceDicts,
    getAllowedEffects, withAllowedEffects, todoSinkableProof,
    freeAtomVarsList,
    IExpr (..), IBinder (..), IPrimOp, IVal, IType, Size, IFunType (..),
    ImpFunction (..), ImpBlock (..), ImpDecl (..), ClosedImpFunction (..),
    ImpInstr (..), iBinderType, ImpName, PtrBinder (..), RepVal (..), DRepVal (..),
    ImpFunName, IFunVar, CallingConvention (..), CUDAKernel (..), Backend (..),
    Output (..), PassLogger, PassName (..), Result (..), BenchStats,
    IsCUDARequired (..),
    NaryPiType (..), fromNaryLam,
    fromNaryTabLam,
    fromNaryLamExact, fromNaryPiType,
    NonEmpty (..), nonEmpty,
    naryPiTypeAsType,
    WithCNameInterface (..), FunObjCode, FunObjCodeName, IFunBinder (..),
    LinktimeNames (..), LinktimeVals (..),
    CName, NativeFunction (..), OptLevel (..),
    DynamicVarKeyPtrs, dynamicVarLinkMap, DynamicVar (..), dynamicVarCName,
    pattern IdxRepTy, pattern IdxRepVal,
    pattern IIdxRepTy, pattern IIdxRepVal, pattern IdxRepScalarBaseTy,
    pattern TagRepTy,
    pattern TagRepVal, pattern Word8Ty,
    pattern UnitTy, pattern PairTy, pattern NatTy, pattern NatVal,
    pattern FinConst, pattern RefTy, pattern RawRefTy,
    pattern BaseTy, pattern PtrTy, pattern UnitVal,
    pattern PairVal, pattern TyKind, pattern TabTy, pattern TabVal,
    pattern Pure, pattern LabeledRowKind, pattern EffKind, pattern UPatIgnore,
    pattern ProdTy, pattern ProdVal,
    pattern SumTy, pattern SumVal, pattern MaybeTy, pattern BinaryFunTy,
    pattern NothingAtom, pattern JustAtom, pattern AtomicBlock,
    pattern BoolTy, pattern FalseAtom, pattern TrueAtom,
    pattern SISourceName, pattern SIInternalName,
    pattern OneEffect, pattern UnaryLamExpr, pattern BinaryLamExpr,
    (-->), (?-->), (--@), (==>),
    IR (..), IRPredicate (..), Sat, Sat', IsCore, IsCore',
    unsafeCoerceIRE, unsafeCoerceFromAnyIR, unsafeCoerceIRB, injectIRE,
    CovariantInIR,
    CAtom, CType, CExpr, CBlock, CDecl, CDecls, CAtomSubstVal, CAtomName,
    SAtom, SType, SExpr, SBlock, SDecl, SDecls, SAtomSubstVal, SAtomName
    ) where

import Data.List.NonEmpty (NonEmpty (..), nonEmpty)
import Foreign.Ptr

import GHC.Generics (Generic (..))

import Name
import Err
import IRVariants
import Logging

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

type PassLogger = FilteredLogger PassName [Output]

data OptLevel = NoOptimize | Optimize
