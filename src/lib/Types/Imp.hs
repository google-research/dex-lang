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

import Foreign.Ptr
import Data.Hashable
import qualified Data.ByteString.Char8 as B
import qualified Data.ByteString       as BS

import GHC.Generics (Generic (..))
import Data.Store (Store (..))

import Name
import Util (IsBool (..))

import Types.Primitives

type ImpName = Name ImpNameC

type ImpFunName = Name TopFunNameC
data IExpr n = ILit LitVal
             | IVar (ImpName n) BaseType
             | IPtrVar (Name PtrNameC n) PtrType
               deriving (Show, Generic)

data IBinder n l = IBinder (NameBinder ImpNameC n l) IType
                   deriving (Show, Generic)

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
   -- - Args passed one by one (not packed).  Scalar args are passed by value,
   --   arrays by pointer.
   -- - Dests are allocated by caller and passed as pointers
   --   (also one by one).
   -- - Used for generating standalone functions and functions called from
   --   Python without XLA.
   -- - Used for generating calls to standalone functions.
   StandardCC
   -- - Args and dests are each packed into a buffer and passed as one pointer,
   --   dests first.
   -- - Used for generating functions called from within an XLA computation.
 | XLACC
   -- - Args are packed by the caller into a buffer and passed as a pointer
   --   to the buffer; unpacking is code-generated.
   -- - Dests are allocated within the function and passed back to the caller
   --   (packed in a number-of-results-length buffer supplied by the caller as a
   --   pointer).
   -- - Used for generating top-level blocks and other Dex code called from
   --   Haskell.
 | EntryFunCC IsCUDARequired
   -- - Scalars only. Args passed one by one, by value. Single result, passed by
   --   value.
   -- - Used for generating calls from Dex to C functions that return a single
   --   scalar.
 | FFICC
   -- - Results written to a buffer supplied by the caller (by pointer).
   -- - Used for generating calls from Dex to C functions that return multiple
   --   results.
 | FFIMultiResultCC
   -- - Was used for generating bodies and calls of CUDA kernels.
 | CUDAKernelLaunch
   -- - Was used for generating bodies and calls of multi-threaded CPU kernels.
 | MCThreadLaunch
   deriving (Show, Eq, Generic)

data ImpFunction n = ImpFunction IFunType (Abs (Nest IBinder) ImpBlock n)
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
 | StackAlloc IType (Size n)
 | MemCopy (IExpr n) (IExpr n) (IExpr n)   -- dest, source, numel
 | Free (IExpr n)
 | InitializeZeros (IExpr n) (IExpr n)  -- ptr, numel
 | GetAllocSize (IExpr n)  -- gives size in numel
 | IThrowError  -- TODO: parameterize by a run-time string
 | ICastOp IType (IExpr n)
 | IBitcastOp IType (IExpr n)
 | IVectorBroadcast (IExpr n) IVectorType
 | IVectorIota                IVectorType
 | IPtrLoad (IExpr n)
 | IPtrOffset (IExpr n) (IExpr n)
 | IBinOp BinOp (IExpr n) (IExpr n)
 | IUnOp  UnOp  (IExpr n)
 | ISelect (IExpr n) (IExpr n) (IExpr n)
 | IOutputStream
 | DebugPrint String (IExpr n) -- just prints an int64 value
 | IShowScalar (IExpr n) (IExpr n) -- pointer to result table, value
   deriving (Show, Generic)

iBinderType :: IBinder n l -> IType
iBinderType (IBinder _ ty) = ty
{-# INLINE iBinderType #-}

data Backend = LLVM | LLVMCUDA | LLVMMC | MLIR | Interpreter  deriving (Show, Eq)
newtype CUDAKernel = CUDAKernel B.ByteString deriving (Show)

-- === Closed Imp functions, LLVM and object file representation ===

-- Object files and LLVM modules expose ordinary C-toolchain names rather than
-- our internal scoped naming system. The `CNameInterface` data structure
-- describes how to interpret the names exposed by an LLVM module and its
-- corresponding object code. These names are all considered local to the
-- module. The module as a whole is a closed object corresponding to a
-- `ClosedImpFunction`.

-- TODO: consider adding more information here: types of required functions,
-- calling conventions etc.
type CName = String
data WithCNameInterface a = WithCNameInterface
  { cniCode         :: a       -- module itself (an LLVM.AST.Module or a bytestring of object code)
  , cniMainFunName  :: CName   -- name of function defined in this module
  , cniRequiredFuns :: [CName] -- names of functions required by this module
  , cniRequiredPtrs :: [CName] -- names of data pointers
  , cniDtorList     :: [CName] -- names of destructors (CUDA only) defined by this module
  } deriving (Show, Generic, Functor, Foldable, Traversable)

type RawObjCode = BS.ByteString
type FunObjCode = WithCNameInterface RawObjCode

data IFunBinder n l = IFunBinder (NameBinder TopFunNameC n l) IFunType

-- Imp function with link-time objects abstracted out, suitable for standalone
-- compilation. TODO: enforce actual `VoidS` as the scope parameter.
data ClosedImpFunction n where
  ClosedImpFunction
    :: Nest IFunBinder n1 n2 -- binders for required functions
    -> Nest PtrBinder  n2 n3 -- binders for required data pointers
    -> ImpFunction n3
    -> ClosedImpFunction n1

data PtrBinder n l = PtrBinder (NameBinder PtrNameC n l) PtrType
data LinktimeNames n = LinktimeNames [Name FunObjCodeNameC n] [Name PtrNameC n]  deriving (Show, Generic)
data LinktimeVals    = LinktimeVals  [FunPtr ()] [Ptr ()]                        deriving (Show, Generic)

data CFunction (n::S) = CFunction
  { nameHint :: NameHint
  , objectCode :: FunObjCode
  , linkerNames :: LinktimeNames n
  }
  deriving (Show, Generic)

instance BindsAtMostOneName IFunBinder TopFunNameC where
  IFunBinder b _ @> x = b @> x
  {-# INLINE (@>) #-}

instance BindsOneName IFunBinder TopFunNameC where
  binderName (IFunBinder b _) = binderName b
  {-# INLINE binderName #-}

instance HasNameHint (IFunBinder n l) where
  getNameHint (IFunBinder b _) = getNameHint b

instance GenericB IFunBinder where
  type RepB IFunBinder = BinderP TopFunNameC (LiftE IFunType)
  fromB (IFunBinder b ty) = b :> LiftE ty
  toB   (b :> LiftE ty) = IFunBinder b ty

instance ProvesExt  IFunBinder
instance BindsNames IFunBinder
instance SinkableB IFunBinder
instance HoistableB  IFunBinder
instance RenameB     IFunBinder
instance AlphaEqB IFunBinder
instance AlphaHashableB IFunBinder

instance GenericB PtrBinder where
  type RepB PtrBinder = BinderP PtrNameC (LiftE PtrType)
  fromB (PtrBinder b ty) = b :> LiftE ty
  toB   (b :> LiftE ty) = PtrBinder b ty

instance BindsAtMostOneName PtrBinder PtrNameC where
  PtrBinder b _ @> x = b @> x
  {-# INLINE (@>) #-}

instance HasNameHint (PtrBinder n l) where
  getNameHint (PtrBinder b _) = getNameHint b

instance ProvesExt   PtrBinder
instance BindsNames  PtrBinder
instance SinkableB   PtrBinder
instance HoistableB  PtrBinder
instance RenameB     PtrBinder
instance AlphaEqB    PtrBinder
instance AlphaHashableB PtrBinder

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
    ) (EitherE7
  {- Alloc -}   (LiftE (AddressSpace, IType) `PairE` Size)
  {- StackAlloc -} (LiftE IType `PairE` Size)
  {- MemCopy -} (IExpr `PairE` IExpr `PairE` IExpr)
  {- InitializeZeros -}  (IExpr `PairE` IExpr)
  {- GetAllocSize -} IExpr
  {- Free -}    (IExpr)
  {- IThrowE -} (UnitE)
    ) (EitherE6
  {- ICastOp    -} (LiftE IType `PairE` IExpr)
  {- IBitcastOp -} (LiftE IType `PairE` IExpr)
  {- IVectorBroadcast -} (IExpr `PairE` LiftE IVectorType)
  {- IVectorIota      -} (              LiftE IVectorType)
  {- DebugPrint       -} (LiftE String `PairE` IExpr)
  {- IShowScalar      -} (IExpr `PairE` IExpr)
    ) (EitherE6
  {- IPtrLoad -}      IExpr
  {- IPtrOffset -}    (IExpr `PairE` IExpr)
  {- IBinOp -}        (LiftE BinOp `PairE` IExpr `PairE` IExpr)
  {- IUnOp -}         (LiftE UnOp `PairE` IExpr)
  {- ISelect -}       (IExpr`PairE` IExpr `PairE`IExpr)
  {- IOutputStream -} UnitE
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
    StackAlloc t s         -> Case2 $ Case1 $ LiftE t `PairE` s
    MemCopy dest src numel -> Case2 $ Case2 $ dest `PairE` src `PairE` numel
    InitializeZeros ptr numel -> Case2 $ Case3 $ ptr `PairE` numel
    GetAllocSize ptr       -> Case2 $ Case4 $ ptr
    Free ptr               -> Case2 $ Case5 ptr
    IThrowError            -> Case2 $ Case6 UnitE

    ICastOp idt ix         -> Case3 $ Case0 $ LiftE idt `PairE` ix
    IBitcastOp idt ix      -> Case3 $ Case1 $ LiftE idt `PairE` ix
    IVectorBroadcast v vty -> Case3 $ Case2 $ v `PairE` LiftE vty
    IVectorIota vty        -> Case3 $ Case3 $ LiftE vty
    DebugPrint s x         -> Case3 $ Case4 $ LiftE s `PairE` x
    IShowScalar x  y       -> Case3 $ Case5 $ x `PairE` y

    IPtrLoad x     -> Case4 $ Case0 $ x
    IPtrOffset x y -> Case4 $ Case1 $ x `PairE` y
    IBinOp op x y  -> Case4 $ Case2 $ LiftE op `PairE` x `PairE` y
    IUnOp op x     -> Case4 $ Case3 $ LiftE op `PairE` x
    ISelect x y z  -> Case4 $ Case4 $ x `PairE` y `PairE` z
    IOutputStream  -> Case4 $ Case5 $ UnitE
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
      Case1 (LiftE t `PairE` s )              -> StackAlloc t s
      Case2 (dest `PairE` src `PairE` numel)  -> MemCopy dest src numel
      Case3 (ptr `PairE` numel)               -> InitializeZeros ptr numel
      Case4 ptr                               -> GetAllocSize ptr
      Case5 ptr                               -> Free ptr
      Case6 UnitE                             -> IThrowError
      _ -> error "impossible"

    Case3 instr' -> case instr' of
      Case0 (LiftE idt `PairE` ix ) -> ICastOp idt ix
      Case1 (LiftE idt `PairE` ix ) -> IBitcastOp idt ix
      Case2 (v `PairE` LiftE vty) -> IVectorBroadcast v vty
      Case3 (          LiftE vty) -> IVectorIota vty
      Case4 (LiftE s `PairE` x)   -> DebugPrint s x
      Case5 (x `PairE` y)         -> IShowScalar x y
      _ -> error "impossible"

    _ -> error "impossible"
  {-# INLINE toE #-}

instance SinkableE ImpInstr
instance HoistableE  ImpInstr
instance AlphaEqE ImpInstr
instance AlphaHashableE ImpInstr
instance RenameE     ImpInstr

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
instance RenameE     ImpBlock
deriving via WrapE ImpBlock n instance Generic (ImpBlock n)

instance GenericE IExpr where
  type RepE IExpr = EitherE3 (LiftE LitVal)
                             (PairE ImpName         (LiftE BaseType))
                             (PairE (Name PtrNameC) (LiftE PtrType))
  fromE iexpr = case iexpr of
    ILit x       -> Case0 (LiftE x)
    IVar    v ty -> Case1 (v `PairE` LiftE ty)
    IPtrVar v ty -> Case2 (v `PairE` LiftE ty)
  {-# INLINE fromE #-}

  toE rep = case rep of
    Case0 (LiftE x) -> ILit x
    Case1 (v `PairE` LiftE ty) -> IVar    v ty
    Case2 (v `PairE` LiftE ty) -> IPtrVar v ty
    _ -> error "impossible"
  {-# INLINE toE #-}

instance SinkableE IExpr
instance HoistableE  IExpr
instance AlphaEqE IExpr
instance AlphaHashableE IExpr
instance RenameE     IExpr

instance GenericB IBinder where
  type RepB IBinder = PairB (LiftB (LiftE IType)) (NameBinder ImpNameC)
  fromB (IBinder b ty) = PairB (LiftB (LiftE ty)) b
  toB   (PairB (LiftB (LiftE ty)) b) = IBinder b ty

instance HasNameHint (IBinder n l) where
  getNameHint (IBinder b _) = getNameHint b

instance BindsAtMostOneName IBinder ImpNameC where
  IBinder b _ @> x = b @> x

instance BindsOneName IBinder ImpNameC where
  binderName (IBinder b _) = binderName b

instance BindsNames IBinder where
  toScopeFrag (IBinder b _) = toScopeFrag b

instance ProvesExt  IBinder
instance SinkableB IBinder
instance HoistableB  IBinder
instance RenameB  IBinder
instance AlphaEqB IBinder
instance AlphaHashableB IBinder

instance GenericB ImpDecl where
  type RepB ImpDecl = PairB (LiftB ImpInstr) (Nest IBinder)
  fromB (ImpLet bs instr) = PairB (LiftB instr) bs
  toB   (PairB (LiftB instr) bs) = ImpLet bs instr

instance SinkableB ImpDecl
instance HoistableB  ImpDecl
instance RenameB     ImpDecl
instance AlphaEqB ImpDecl
instance AlphaHashableB ImpDecl
instance ProvesExt  ImpDecl
instance BindsNames ImpDecl

instance GenericE ImpFunction where
  type RepE ImpFunction = LiftE IFunType `PairE` Abs (Nest IBinder) ImpBlock
  fromE (ImpFunction ty ab) =LiftE ty `PairE` ab
  {-# INLINE fromE #-}

  toE (LiftE ty `PairE` ab) = ImpFunction ty ab
  {-# INLINE toE #-}

instance SinkableE ImpFunction
instance HoistableE  ImpFunction
instance AlphaEqE    ImpFunction
instance AlphaHashableE    ImpFunction
instance RenameE     ImpFunction

instance GenericE LinktimeNames where
  type RepE LinktimeNames = ListE  (Name FunObjCodeNameC)
                   `PairE`  ListE  (Name PtrNameC)
  fromE (LinktimeNames funs ptrs) = ListE funs `PairE` ListE ptrs
  {-# INLINE fromE #-}
  toE (ListE funs `PairE` ListE ptrs) = LinktimeNames funs ptrs
  {-# INLINE toE #-}

instance SinkableE      LinktimeNames
instance HoistableE     LinktimeNames
instance AlphaEqE       LinktimeNames
instance AlphaHashableE LinktimeNames
instance RenameE        LinktimeNames

instance GenericE CFunction where
  type RepE CFunction = (LiftE NameHint) `PairE`
    (LiftE FunObjCode) `PairE` LinktimeNames
  fromE (CFunction{..}) = LiftE nameHint `PairE`
    LiftE objectCode `PairE` linkerNames
  {-# INLINE fromE #-}
  toE (LiftE nameHint `PairE` LiftE objectCode `PairE` linkerNames) =
    CFunction{..}
  {-# INLINE toE #-}

instance SinkableE      CFunction
instance HoistableE     CFunction
instance RenameE        CFunction

instance Store IsCUDARequired
instance Store CallingConvention
instance Store a => Store (WithCNameInterface a)
instance Store (IBinder n l)
instance Store (ImpDecl n l)
instance Store (IFunType)
instance Store (ImpInstr n)
instance Store (IExpr n)
instance Store (ImpBlock n)
instance Store (ImpFunction n)
instance Store (LinktimeNames n)
instance Store (CFunction n)
instance Store LinktimeVals

instance Hashable IsCUDARequired
instance Hashable CallingConvention
instance Hashable IFunType
