-- Copyright 2023 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE DuplicateRecordFields #-}

module JAX.Concrete where

import GHC.Generics (Generic (..))

import Data.Aeson
import Data.Aeson.Types qualified as A

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

data DType = F64 | F32 | I64 | I32 -- others
  deriving (Generic)

data DimSizeDeBrujin = LitDimSize Int
  | RefDimSizeInput Int  -- "de Brujin" index but counted from the left of the list
  | RefDimSizeOutput Int -- same
  deriving (Generic)

data JArgType = JArrayDeBrujin DType [DimSizeDeBrujin]
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
  , dtype :: DType
  }
  deriving (Generic)

data JEffects = IO | Read Int | Write Int | Append Int
  deriving (Generic)

data JAtom = JVariable JVar
           | JLiteral JLit
           -- DropVar?
  deriving (Generic)

data JVar = JVar
  { name :: Int
  , count :: Int
  , suffix :: String
  , ty :: JVarType
  }
  deriving (Generic)

data JLit = JLit
  { val :: Int -- TODO What's the real type?
  , ty :: JVarType
  }
  deriving (Generic)

data JEqn = JEqn
  { outvars :: [JVar]
  , primitive :: Primitive
  , invars :: [JAtom]
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
  { invars    :: [JVar]
  , constvars :: [JVar]
  , outvars   :: [JAtom]
  , eqns      :: [JEqn]
  }
  deriving (Generic)

data ClosedJaxpr = ClosedJaxpr
  { jaxpr :: Jaxpr
  , consts :: [A.Value]
  }
  deriving (Generic)

instance ToJSON JEqn where
  toJSON JEqn {..} = object
    [ "primitive" .= name
    , "params" .= params
    , "invars" .= A.toJSON invars
    , "outvars" .= A.toJSON outvars
    ] where (name, params) = dumpPrimitive primitive

dumpPrimitive :: Primitive -> (String, A.Value)
dumpPrimitive = \case
  Sin -> ("sin", object [])

instance FromJSON JEqn where
  parseJSON = \case
    (A.Object obj) -> do
      invars <- obj .: "invars"
      outvars <- obj .: "outvars"
      primName <- obj .: "primitive"
      prim <- parsePrimitive primName =<< obj .: "params"
      return $ JEqn outvars prim invars
    invalid -> A.prependFailure "parsing eqn failed, " $
      A.typeMismatch "object" invalid

parsePrimitive :: String -> A.Value -> A.Parser Primitive
parsePrimitive name params = case name of
  "sin" -> return Sin
  _ -> fail $ "Unknown primitive " ++ name

instance ToJSON JAtom where
  toJSON (JVariable var) = object ["var" .= var]
  toJSON (JLiteral  lit) = object ["lit" .= lit]

instance FromJSON JAtom where
  parseJSON = \case
    o@(A.Object obj) -> do
      obj .:? "var" >>= \case
        Just var -> JVariable <$> A.parseJSON var
        Nothing -> do
          obj .:? "lit" >>= \case
            Just lit -> JLiteral <$> A.parseJSON lit
            Nothing -> wrong o
    invalid -> wrong invalid
    where
      wrong invalid = A.prependFailure "parsing atom failed, " $
        A.typeMismatch "object with a var or lit key" invalid

instance ToJSON DType where
  toJSON F64 = A.String "f64"
  toJSON F32 = A.String "f32"
  toJSON I64 = A.String "i64"
  toJSON I32 = A.String "i32"

instance FromJSON DType where
  parseJSON (A.String "f64") = pure F64
  parseJSON (A.String "f32") = pure F32
  parseJSON (A.String "i64") = pure I64
  parseJSON (A.String "i32") = pure I32
  parseJSON invalid = A.prependFailure "parsing dtype failed, " $
    A.typeMismatch "dtype string" invalid

instance ToJSON JVar
instance ToJSON JLit
instance ToJSON JVarType
instance ToJSON JEffects
instance ToJSON DimSizeName
instance ToJSON JFuncType
instance ToJSON Primitive
instance ToJSON DimSizeDeBrujin
instance ToJSON JArgType
instance ToJSON ClosedJaxpr
instance ToJSON Jaxpr

instance FromJSON JVar
instance FromJSON JLit
instance FromJSON JVarType
instance FromJSON JEffects
instance FromJSON DimSizeName
instance FromJSON JFuncType
instance FromJSON Primitive
instance FromJSON DimSizeDeBrujin
instance FromJSON JArgType
instance FromJSON ClosedJaxpr
instance FromJSON Jaxpr
