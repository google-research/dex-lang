-- Copyright 2023 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module JAX.Concrete where

import GHC.Generics (Generic (..))

import Data.Aeson (ToJSON)

type NumConsts = Int
type NumCarry = Int
type Unroll = Int -- how many copies of the body to replicate

data Primitive =
    Sin | Cos | Add | Mul
  | Scan Bool -- reverse
         Int  -- length
         Jaxpr -- body
         NumConsts
         NumCarry
         [Bool] -- which arguments are we linear wrt?
         Unroll
  -- | others!
  deriving (Generic)

data EltType = F64 | F32 -- others
  deriving (Generic)

data DimSizeDeBrujin = LitDimSize Int
  | RefDimSizeInput Int  -- "de Brujin" index but counted from the left of the list
  | RefDimSizeOutput Int -- same
  deriving (Generic)
data JArgType = JArrayDeBrujin EltType [DimSizeDeBrujin]
-- On the output, can refer to input binders and preceding things in the output
  deriving (Generic)
data JFuncType = JFunc [JArgType] JEffects [JArgType]
-- The ints just count from the beginning of the list of inputs of the jaxpr
-- being typed by this JEffects datum
  deriving (Generic)

data DimSizeName = DimSizeName JAtom -- | polynomials? indexing operations?
  deriving (Generic)
data JVarType = JArrayName
  { shape :: [DimSizeName]
  , dtype :: EltType
  }
  deriving (Generic)
data JEffects = IO | Read Int | Write Int | Append Int
  deriving (Generic)

data JAtom = JVar JVar
           | JLitInt Int
           -- | others
  deriving (Generic)

data JVar = JVariable
  { name :: String
  , ty :: JVarType
  }
  deriving (Generic)

data Binder = Binder String JVarType
  deriving (Generic)

data JDecl = JDecl
  { outVars :: [Binder]
  , primitive :: Primitive
  , inAtoms :: [JAtom]
  }
  deriving (Generic)

-- examples of primitive parameters
--  * broadcast - data describing axes
--  * conv -- strides
--  * contraction dimensions etc in matmul-ish things
--  * scan -- direction, "unroll", num_carry, num_consts
--  * transpose -- permutation

-- other things
--  * effects
--  * dynamic shapes

data Jaxpr = Jaxpr
  { invars  :: [Binder]
  , outvars :: [JAtom]
  , eqns    :: [JDecl]
  }
  deriving (Generic)

instance ToJSON JAtom
instance ToJSON JVar
instance ToJSON Binder
instance ToJSON JVarType
instance ToJSON JEffects
instance ToJSON DimSizeName
instance ToJSON JFuncType
instance ToJSON Primitive
instance ToJSON EltType
instance ToJSON DimSizeDeBrujin
instance ToJSON JArgType
instance ToJSON Jaxpr
instance ToJSON JDecl
