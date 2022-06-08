-- Copyright 2022 Google LLC
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

module Types.Imp where

import Data.Hashable
import qualified Data.ByteString.Char8 as B

import GHC.Generics (Generic (..))
import Data.Store (Store (..))

import Name
import Util (IsBool (..))

import Types.Primitives

-- We use AtomName because we convert between atoms and imp
-- expressions without chaning names. Maybe we shouldn't do that.
type ImpName = Name AtomNameC

type ImpFunName = Name ImpFunNameC
data IExpr n = ILit LitVal
             | IVar (ImpName n) BaseType
               deriving (Show, Generic)

data IBinder n l = IBinder (NameBinder AtomNameC n l) IType
                   deriving (Show, Generic)

type IPrimOp n = PrimOp (IExpr n)
type IVal = IExpr  -- only ILit and IRef constructors
type IType = BaseType
type Size = IExpr
type IVectorType = BaseType -- has to be a vector type

type IFunName = String

type IFunVar = (IFunName, IFunType)
data IFunType = IFunType CallingConvention [IType] [IType] -- args, results
                deriving (Show, Eq, Generic)

data IsCUDARequired = CUDARequired | CUDANotRequired  deriving (Eq, Show, Generic)

instance IsBool IsCUDARequired where
  toBool CUDARequired = True
  toBool CUDANotRequired = False

data CallingConvention =
   CEntryFun
 | CInternalFun
 | EntryFun IsCUDARequired
 | FFIFun
 | FFIMultiResultFun
 | CUDAKernelLaunch
 | MCThreadLaunch
   deriving (Show, Eq, Generic)

data ImpFunction n =
   ImpFunction IFunType (Abs (Nest IBinder) ImpBlock n)
 | FFIFunction IFunType IFunName
   deriving (Show, Generic)

data ImpBlock n where
  ImpBlock :: Nest ImpDecl n l -> [IExpr l] -> ImpBlock n
deriving instance Show (ImpBlock n)

data ImpDecl n l = ImpLet (Nest IBinder n l) (ImpInstr n)
     deriving (Show, Generic)

data ImpInstr n =
   IFor Direction (Size n) (Abs IBinder ImpBlock n)
 | IWhile (ImpBlock n)
 | ICond (IExpr n) (ImpBlock n) (ImpBlock n)
 | IQueryParallelism IFunVar (IExpr n) -- returns the number of available concurrent threads
 | ISyncWorkgroup
 | ILaunch IFunVar (Size n) [IExpr n]
 | ICall (ImpFunName n) [IExpr n]
 | Store (IExpr n) (IExpr n)           -- dest, val
 | Alloc AddressSpace IType (Size n)
 | MemCopy (IExpr n) (IExpr n) (IExpr n)   -- dest, source, numel
 | Free (IExpr n)
 | IThrowError  -- TODO: parameterize by a run-time string
 | ICastOp IType (IExpr n)
 | IPrimOp (IPrimOp n)
 | IVectorBroadcast (IExpr n) IVectorType
 | IVectorIota                IVectorType
   deriving (Show, Generic)

iBinderType :: IBinder n l -> IType
iBinderType (IBinder _ ty) = ty
{-# INLINE iBinderType #-}

data Backend = LLVM | LLVMCUDA | LLVMMC | MLIR | Interpreter  deriving (Show, Eq)
newtype CUDAKernel = CUDAKernel B.ByteString deriving (Show)

-- === instances ===

instance GenericE ImpInstr where
  type RepE ImpInstr = EitherE5
      (EitherE4
  {- IFor -}    (LiftE Direction `PairE` Size `PairE` Abs IBinder ImpBlock)
  {- IWhile -}  (ImpBlock)
  {- ICond -}   (IExpr `PairE` ImpBlock `PairE` ImpBlock)
  {- IQuery -}  (LiftE IFunVar `PairE` IExpr)
    ) (EitherE4
  {- ISyncW -}  (UnitE)
  {- ILaunch -} (LiftE IFunVar `PairE` Size `PairE` ListE IExpr)
  {- ICall -}   (ImpFunName `PairE` ListE IExpr)
  {- Store -}   (IExpr `PairE` IExpr)
    ) (EitherE4
  {- Alloc -}   (LiftE (AddressSpace, IType) `PairE` Size)
  {- MemCopy -} (IExpr `PairE` IExpr `PairE` IExpr)
  {- Free -}    (IExpr)
  {- IThrowE -} (UnitE)
    ) (EitherE2
  {- ICastOp -} (LiftE IType `PairE` IExpr)
  {- IPrimOp -} (ComposeE PrimOp IExpr)
    ) (EitherE2
  {- IVectorBroadcast -} (IExpr `PairE` LiftE IVectorType)
  {- IVectorIota      -} (              LiftE IVectorType)
    )


  fromE instr = case instr of
    IFor d n ab           -> Case0 $ Case0 $ LiftE d `PairE` n `PairE` ab
    IWhile body           -> Case0 $ Case1 body
    ICond p cons alt      -> Case0 $ Case2 $ p `PairE` cons `PairE` alt
    IQueryParallelism f s -> Case0 $ Case3 $ LiftE f `PairE` s

    ISyncWorkgroup      -> Case1 $ Case0 UnitE
    ILaunch f n args    -> Case1 $ Case1 $ LiftE f `PairE` n `PairE` ListE args
    ICall f args        -> Case1 $ Case2 $ f `PairE` ListE args
    Store dest val      -> Case1 $ Case3 $ dest `PairE` val

    Alloc a t s            -> Case2 $ Case0 $ LiftE (a, t) `PairE` s
    MemCopy dest src numel -> Case2 $ Case1 $ dest `PairE` src `PairE` numel
    Free ptr               -> Case2 $ Case2 ptr
    IThrowError            -> Case2 $ Case3 UnitE

    ICastOp idt ix -> Case3 $ Case0 $ LiftE idt `PairE` ix
    IPrimOp op     -> Case3 $ Case1 $ ComposeE op
    IVectorBroadcast v vty -> Case4 $ Case0 $ v `PairE` LiftE vty
    IVectorIota vty        -> Case4 $ Case1 $ LiftE vty
  {-# INLINE fromE #-}

  toE instr = case instr of
    Case0 instr' -> case instr' of
      Case0 (LiftE d `PairE` n `PairE` ab) -> IFor d n ab
      Case1 body                           -> IWhile body
      Case2 (p `PairE` cons `PairE` alt)   -> ICond p cons alt
      Case3 (LiftE f `PairE` s)            -> IQueryParallelism f s
      _ -> error "impossible"

    Case1 instr' -> case instr' of
      Case0 UnitE                                     -> ISyncWorkgroup
      Case1 (LiftE f `PairE` n `PairE` ListE args)    -> ILaunch f n args
      Case2 (f `PairE` ListE args)                    -> ICall f args
      Case3 (dest `PairE` val )                       -> Store dest val
      _ -> error "impossible"

    Case2 instr' -> case instr' of
      Case0 (LiftE (a, t) `PairE` s )         -> Alloc a t s
      Case1 (dest `PairE` src `PairE` numel)  -> MemCopy dest src numel
      Case2 ptr                               -> Free ptr
      Case3 UnitE                             -> IThrowError
      _ -> error "impossible"

    Case3 instr' -> case instr' of
      Case0 (LiftE idt `PairE` ix ) -> ICastOp idt ix
      Case1 (ComposeE op )          -> IPrimOp op
      _ -> error "impossible"

    Case4 instr' -> case instr' of
      Case0 (v `PairE` LiftE vty) -> IVectorBroadcast v vty
      Case1 (          LiftE vty) -> IVectorIota vty
      _ -> error "impossible"

    _ -> error "impossible"
  {-# INLINE toE #-}

instance SinkableE ImpInstr
instance HoistableE  ImpInstr
instance AlphaEqE ImpInstr
instance AlphaHashableE ImpInstr
instance SubstE Name ImpInstr

instance GenericE ImpBlock where
  type RepE ImpBlock = Abs (Nest ImpDecl) (ListE IExpr)
  fromE (ImpBlock decls results) = Abs decls (ListE results)
  {-# INLINE fromE #-}
  toE   (Abs decls (ListE results)) = ImpBlock decls results
  {-# INLINE toE #-}

instance SinkableE ImpBlock
instance HoistableE  ImpBlock
instance AlphaEqE ImpBlock
instance AlphaHashableE ImpBlock
instance SubstE Name ImpBlock
deriving via WrapE ImpBlock n instance Generic (ImpBlock n)

instance GenericE IExpr where
  type RepE IExpr = EitherE2 (LiftE LitVal)
                             (PairE ImpName (LiftE BaseType))
  fromE iexpr = case iexpr of
    ILit x -> Case0 (LiftE x)
    IVar v ty -> Case1 (v `PairE` LiftE ty)
  {-# INLINE fromE #-}

  toE rep = case rep of
    Case0 (LiftE x) -> ILit x
    Case1 (v `PairE` LiftE ty) -> IVar v ty
    _ -> error "impossible"
  {-# INLINE toE #-}

instance SinkableE IExpr
instance HoistableE  IExpr
instance AlphaEqE IExpr
instance AlphaHashableE IExpr
instance SubstE Name IExpr

instance GenericB IBinder where
  type RepB IBinder = PairB (LiftB (LiftE IType)) (NameBinder AtomNameC)
  fromB (IBinder b ty) = PairB (LiftB (LiftE ty)) b
  toB   (PairB (LiftB (LiftE ty)) b) = IBinder b ty

instance HasNameHint (IBinder n l) where
  getNameHint (IBinder b _) = getNameHint b

instance BindsAtMostOneName IBinder AtomNameC where
  IBinder b _ @> x = b @> x

instance BindsOneName IBinder AtomNameC where
  binderName (IBinder b _) = binderName b

instance BindsNames IBinder where
  toScopeFrag (IBinder b _) = toScopeFrag b

instance ProvesExt  IBinder
instance SinkableB IBinder
instance HoistableB  IBinder
instance SubstB Name IBinder
instance AlphaEqB IBinder
instance AlphaHashableB IBinder

instance GenericB ImpDecl where
  type RepB ImpDecl = PairB (LiftB ImpInstr) (Nest IBinder)
  fromB (ImpLet bs instr) = PairB (LiftB instr) bs
  toB   (PairB (LiftB instr) bs) = ImpLet bs instr

instance SinkableB ImpDecl
instance HoistableB  ImpDecl
instance SubstB Name ImpDecl
instance AlphaEqB ImpDecl
instance AlphaHashableB ImpDecl
instance ProvesExt  ImpDecl
instance BindsNames ImpDecl

instance GenericE ImpFunction where
  type RepE ImpFunction = EitherE2 (LiftE IFunType `PairE` Abs (Nest IBinder) ImpBlock)
                                   (LiftE (IFunType, IFunName))
  fromE f = case f of
    ImpFunction ty ab   -> Case0 $ LiftE ty `PairE` ab
    FFIFunction ty name -> Case1 $ LiftE (ty, name)
  {-# INLINE fromE #-}

  toE f = case f of
    Case0 (LiftE ty `PairE` ab) -> ImpFunction ty ab
    Case1 (LiftE (ty, name))    -> FFIFunction ty name
    _ -> error "impossible"
  {-# INLINE toE #-}

instance SinkableE ImpFunction
instance HoistableE  ImpFunction
instance AlphaEqE    ImpFunction
instance AlphaHashableE    ImpFunction
instance SubstE Name ImpFunction

instance Store IsCUDARequired
instance Store CallingConvention
instance Store (IBinder n l)
instance Store (ImpDecl n l)
instance Store (IFunType)
instance Store (ImpInstr n)
instance Store (IExpr n)
instance Store (ImpBlock n)
instance Store (ImpFunction n)

instance Hashable IsCUDARequired
instance Hashable CallingConvention
instance Hashable IFunType
