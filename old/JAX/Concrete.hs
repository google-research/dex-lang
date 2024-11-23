-- Copyright 2023 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE DuplicateRecordFields #-}

module JAX.Concrete where

import GHC.Generics (Generic (..))

import Control.Category hiding ((.))
import Prelude hiding (id)
import Data.Aeson
import Data.Aeson.Types qualified as A

import IRVariants
import Name

data Primitive =
    Sin | Add
  | Scan ScanParams
  | ConvertElementType ConvertElementTypeParams
  -- others!
  deriving (Generic)

data ScanParams = ScanParams
  { reverse :: Bool
  , length :: Int
  , jaxpr :: (ClosedJaxpr VoidS) -- The scan body
  , num_consts :: Int
  , num_carry :: Int
  , linear :: [Bool] -- which arguments are we linear wrt?
  , unroll :: Int -- how many copies of the body to replicate
  }
  deriving (Generic)

data ConvertElementTypeParams = ConvertElementTypeParams
  { new_dtype :: DType
  , weak_type :: Bool
  }
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

-- TODO Variable references, polynomials, etc
data DimSizeName = DimSize Int
  deriving (Generic)

data JVarType = JArrayName
  { shape :: [DimSizeName]
  , dtype :: DType
  }
  deriving (Generic)

data JEffects = IO | Read Int | Write Int | Append Int
  deriving (Generic)

data JAtom (n::S) =
    JVariable (JVar n)
  | JLiteral JLit
           -- DropVar?
  deriving (Generic)

data JSourceName = JSourceName
  { name :: Int
  , count :: Int
  , suffix :: String
  }
  deriving (Eq, Ord, Show)

instance HasNameHint JSourceName where
  getNameHint JSourceName{suffix=suffix} = getNameHint suffix

data JSourceNameOr (a::E) (n::S) where
  SourceName :: JSourceName -> JSourceNameOr a 'VoidS
  InternalName :: JSourceName -> a n -> JSourceNameOr a n

data JVar (n::S) = JVar
  { sourceName :: JSourceNameOr (Name (AtomNameC SimpIR)) n
  , ty :: JVarType
  }
  deriving (Generic)

data JLit = JLit
  { val :: A.Value -- TODO What's the real type?
  , ty :: JVarType
  }
  deriving (Generic)

data JBinder (n::S) (l::S) where
  JBindSource :: JSourceName -> JVarType -> JBinder n n
  JBind :: JSourceName -> JVarType -> NameBinder (AtomNameC SimpIR) n l -> JBinder n l

instance ProvesExt JBinder where

instance BindsNames JBinder where
  toScopeFrag = \case
    JBindSource _ _ -> id
    JBind _ _ b -> toScopeFrag b

instance BindsAtMostOneName JBinder (AtomNameC SimpIR) where
  b @> x = case b of
    JBindSource _ _ -> error "Unexpected source binder after parsing"
    JBind _ _ b' -> singletonSubst b' x
  {-# INLINE (@>) #-}

jBinderVar :: JBinder n l -> JVar 'VoidS
jBinderVar = \case
  JBindSource src ty -> JVar (SourceName src) ty
  JBind src ty _ -> JVar (SourceName src) ty

data JEqn (n::S) (l::S) = JEqn
  { outvars :: Nest JBinder n l
  , primitive :: Primitive
  , invars :: [JAtom n]
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

data Jaxpr (n::S) where
  Jaxpr ::
    Nest JBinder n n' -- invars
    -> Nest JBinder n' l -- constvars
    -> Nest JEqn l o -- eqns
    -> [JAtom o] -- outvars
    -> Jaxpr n

data ClosedJaxpr (n::S) = ClosedJaxpr
  { jaxpr :: Jaxpr n
  , consts :: [A.Value]
  }
  deriving (Generic)

instance ToJSON (JVar n) where
  toJSON JVar {sourceName, ty} = object
    [ "name" .= name
    , "count" .= count
    , "suffix" .= suffix
    , "ty" .= ty
    ] where JSourceName {name, count, suffix} = case sourceName of
              SourceName nm -> nm
              InternalName nm _ -> nm

instance FromJSON (JVar VoidS) where
  parseJSON = \case
    (A.Object obj) -> do
      name <- obj .: "name"
      count <- obj .: "count"
      suffix <- obj .: "suffix"
      ty <- obj .: "ty"
      return JVar { sourceName = SourceName $ JSourceName {..}
                  , ty = ty
                  }
    invalid -> A.prependFailure "parsing var failed, " $
      A.typeMismatch "Object" invalid

instance ToJSON (JEqn n l) where
  toJSON JEqn {..} = object
    [ "primitive" .= name
    , "params" .= params
    , "invars" .= A.toJSON invars
    , "outvars" .= A.toJSON (nestToList' jBinderVar outvars)
    ] where (name, params) = dumpPrimitive primitive

dumpPrimitive :: Primitive -> (String, A.Value)
dumpPrimitive = \case
  Add -> ("add", object [])
  Sin -> ("sin", object [])
  Scan params -> ("scan", A.toJSON params)
  ConvertElementType params -> ("convert_element_type", A.toJSON params)

instance FromJSON (JEqn 'VoidS 'VoidS) where
  parseJSON = \case
    (A.Object obj) -> do
      invars <- obj .: "invars"
      outvars <- obj .: "outvars"
      primName <- obj .: "primitive"
      prim <- parsePrimitive primName =<< obj .: "params"
      return $ JEqn (varsAsBinders outvars) prim invars
    invalid -> A.prependFailure "parsing eqn failed, " $
      A.typeMismatch "Object" invalid

voidNest :: [b 'VoidS 'VoidS] -> Nest b 'VoidS 'VoidS
voidNest = foldr Nest Empty

varsAsBinders :: [JVar 'VoidS] -> Nest JBinder 'VoidS 'VoidS
varsAsBinders = voidNest . map varAsBinder

varAsBinder :: JVar 'VoidS -> JBinder 'VoidS 'VoidS
varAsBinder JVar{sourceName, ty} = case sourceName of
  SourceName srcName -> JBindSource srcName ty
  InternalName _ _ -> error "Unexpected internal name during parsing"

parsePrimitive :: String -> A.Value -> A.Parser Primitive
parsePrimitive name params = case name of
  "add" -> return Add
  "sin" -> return Sin
  "scan" -> Scan <$> parseJSON params
  "convert_element_type" -> ConvertElementType <$> parseJSON params
  _ -> fail $ "Unknown primitive " ++ name

instance ToJSON (JAtom n) where
  toJSON (JVariable var) = object ["var" .= var]
  toJSON (JLiteral  lit) = object ["lit" .= lit]

instance FromJSON (JAtom VoidS) where
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
        A.typeMismatch "Object with a var or lit key" invalid

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

instance ToJSON (Jaxpr n) where
  toJSON (Jaxpr invars constvars eqns outvars) = object
    [ "invars" .= nestToList' jBinderVar invars
    , "constvars" .= nestToList' jBinderVar constvars
    , "eqns" .= nestToList' voidify eqns
    , "outvars" .= outvars
    ] where
    voidify :: forall n' l. JEqn n' l -> JEqn VoidS VoidS
    voidify = unsafeCoerceB

instance FromJSON (Jaxpr VoidS) where
  parseJSON = \case
    (A.Object obj) -> do
      invars <- obj .: "invars"
      constvars <- obj .: "constvars"
      eqns <- obj .: "eqns"
      outvars <- obj .: "outvars"
      return $ Jaxpr (varsAsBinders invars) (varsAsBinders constvars)
        (voidNest eqns) outvars
    invalid -> A.prependFailure "parsing jaxpr failed, " $
      A.typeMismatch "Object" invalid

instance ToJSON JLit
instance ToJSON JVarType
instance ToJSON JEffects
instance ToJSON DimSizeName
instance ToJSON JFuncType
instance ToJSON Primitive
instance ToJSON DimSizeDeBrujin
instance ToJSON JArgType
instance ToJSON (ClosedJaxpr n)
instance ToJSON ScanParams
instance ToJSON ConvertElementTypeParams

instance FromJSON JLit
instance FromJSON JVarType
instance FromJSON JEffects
instance FromJSON DimSizeName
instance FromJSON JFuncType
instance FromJSON Primitive
instance FromJSON DimSizeDeBrujin
instance FromJSON JArgType
instance FromJSON (ClosedJaxpr VoidS)
instance FromJSON ScanParams
instance FromJSON ConvertElementTypeParams
