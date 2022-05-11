-- Copyright 2022 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module TraverseContexts (HasContexts, gatherContexts, addContextIds) where

import qualified Data.ByteString as BS
import qualified Data.List.NonEmpty as NE
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Control.Monad.State
import Control.Monad.Writer
import Foreign.Ptr
import GHC.Generics
import GHC.Int
import GHC.Word

import LabeledItems
import Name
import Occurrence
import SourceInfo
import Types.Primitives
import Types.Source

-- Naming: replace "Contexts" with "SourceInfo"

class HasContexts a where
  traverseContexts :: Applicative m => (SrcPosCtx -> m SrcPosCtx) -> a -> m a

  default traverseContexts :: (Applicative m, Generic a, HasContexts (Rep a Any)) => (SrcPosCtx -> m SrcPosCtx) -> a -> m a
  traverseContexts f x = to <$> traverseContexts f (from x :: Rep a Any)

tc :: HasContexts a => Applicative m => (SrcPosCtx -> m SrcPosCtx) -> a -> m a
tc = traverseContexts

instance HasContexts (V1 p) where
  traverseContexts _ x = pure x

instance HasContexts (U1 p) where
  traverseContexts _ x = pure x

instance (HasContexts c) => HasContexts (K1 i c p) where
  traverseContexts f (K1 x) = K1 <$> traverseContexts f x

instance HasContexts (f p) => HasContexts (M1 i c f p) where
  traverseContexts f (M1 x) = M1 <$> traverseContexts f x

instance (HasContexts (a p), HasContexts (b p)) => HasContexts ((a :+: b) p) where
  traverseContexts f (L1 x) = L1 <$> traverseContexts f x
  traverseContexts f (R1 x) = R1 <$> traverseContexts f x

instance (HasContexts (a p), HasContexts (b p)) => HasContexts ((a :*: b) p) where
  traverseContexts f (a :*: b) = (:*:) <$> traverseContexts f a <*> traverseContexts f b

instance HasContexts (UExpr n)
instance HasContexts (UExpr' n)

instance HasContexts (UFieldRowElem n)

instance HasContexts (ULamExpr n) where
  traverseContexts f (ULamExpr arr pat body) =
    ULamExpr arr <$> tc f pat <*> tc f body

instance HasContexts (UPiExpr n) where
  traverseContexts f (UPiExpr arr pat eff ty) =
    UPiExpr arr <$> tc f pat <*> tc f eff <*> tc f ty

instance HasContexts (UTabLamExpr n) where
  traverseContexts f (UTabLamExpr pat body) =
    UTabLamExpr <$> tc f pat <*> tc f body

instance HasContexts (UTabPiExpr n) where
  traverseContexts f (UTabPiExpr pat body) =
    UTabPiExpr <$> tc f pat <*> tc f body

instance HasContexts (UDeclExpr n) where
  traverseContexts f (UDeclExpr decl body) =
    UDeclExpr <$> tc f decl <*> tc f body

instance HasContexts (UDecl n l) where
  traverseContexts f udecl = case udecl of
    ULet letann upatann uexpr -> ULet letann <$> tc f upatann <*> tc f uexpr
    UDataDefDecl udatadef ubinder nest -> UDataDefDecl <$> tc f udatadef <*> tc f ubinder <*> tc f nest
    UStructDecl ustructdef ubinder -> UStructDecl <$> tc f ustructdef <*> tc f ubinder
    UInterface params superclasses methodTys interfaceName methodNames ->
      UInterface <$> tc f params <*> tc f superclasses <*> tc f methodTys <*> tc f interfaceName <*> tc f methodNames
    UInstance className bs params methods name ->
      UInstance <$> tc f className <*> tc f bs <*> tc f params <*> tc f methods <*> tc f name
    UEffectDecl opTypes effName opNames ->
      UEffectDecl <$> tc f opTypes <*> tc f effName <*> tc f opNames
    UHandlerDecl effName bodyTyArg tyArgs retEff retTy opDefs handlerName ->
      UHandlerDecl <$> tc f effName <*> tc f bodyTyArg <*> tc f tyArgs <*> tc f retEff <*> tc f retTy <*> tc f opDefs <*> tc f handlerName

instance HasContexts (UDataDef n) where
  traverseContexts f (UDataDef name binders datacons) =
    UDataDef <$> tc f name <*> tc f binders <*> tc f datacons

instance HasContexts (UDataDefTrail l) where
  traverseContexts f (UDataDefTrail nest) = UDataDefTrail <$> tc f nest

instance HasContexts (UStructDef n) where
  traverseContexts f (UStructDef name binders fields) =
    UStructDef <$> tc f name <*> tc f binders <*> tc f fields

instance HasContexts Arrow
instance HasContexts (UAnnBinderArrow c n l)
instance HasContexts (UAnnBinder c n l)

instance HasContexts (UPatAnn n l)
instance HasContexts (UPatAnnArrow n l)

instance HasContexts (UMethodType n)
instance HasContexts (UMethodDef l)

instance HasContexts (UEffectOpDef n)
instance HasContexts (UEffectOpType n)
instance HasContexts UResumePolicy

instance HasContexts (UForExpr n) where
  traverseContexts f (UForExpr binder body) =
    UForExpr <$> tc f binder <*> tc f body

instance HasContexts (UAlt n) where
  traverseContexts :: Applicative m => (SrcPosCtx -> m SrcPosCtx) -> UAlt n -> m (UAlt n)
  traverseContexts f (UAlt pat body) =
    UAlt <$> tc f pat <*> tc f body

instance HasContexts PrimName
instance HasContexts e => HasContexts (PrimCon r e)
instance HasContexts Direction
instance HasContexts e => HasContexts (AlwaysEqual e)
instance HasContexts e => HasContexts (PrimOp e)
instance HasContexts UnOp
instance HasContexts BinOp
instance HasContexts CmpOp
instance HasContexts e => HasContexts (MemOp e)
instance HasContexts e => HasContexts (VectorOp e)
instance HasContexts e => HasContexts (RecordOp e)
instance HasContexts e => HasContexts (MiscOp e)
instance HasContexts e => HasContexts (PrimTC r e)
instance HasContexts LitVal
instance HasContexts PtrLitVal
instance HasContexts PtrSnapshot
instance HasContexts a => HasContexts (Ptr a) where
  traverseContexts _ ptr = pure ptr

instance HasContexts BaseType
instance HasContexts ScalarBaseType
instance HasContexts AddressSpace

instance (HasContexts a, HasContexts b) => HasContexts (a, b)
instance (HasContexts a, HasContexts b, HasContexts c) => HasContexts (a, b, c)
instance (HasContexts a, HasContexts b) => HasContexts (Either a b)

instance HasContexts (UDepPairType n) where
  traverseContexts f (UDepPairType ann ty) =
    UDepPairType <$> tc f ann <*> tc f ty

instance HasContexts (UEffectRow l) where
  traverseContexts f (UEffectRow effs t) = UEffectRow <$> tc f effs <*> tc f t

instance (Ord a, HasContexts a) => HasContexts (S.Set a) where
  traverseContexts f s = S.fromList <$> tc f (S.toList s)

instance HasContexts RWS
instance HasContexts (UEffect n)

instance HasContexts (UPat' n l)
instance HasContexts (WithSrcB UPat' n l)

instance (
  forall l'. HasContexts (b1 n l'), forall l'. HasContexts (b2 l' l)
  ) => HasContexts (EitherB b1 b2 n l) where
  traverseContexts f x = case x of
    LeftB b1 -> LeftB <$> tc f b1
    RightB b1 -> RightB <$> tc f b1

instance (
  forall l'. HasContexts (b1 n l'), forall l'. HasContexts (b2 l' l)
  ) => HasContexts (PairB b1 b2 n l) where
  traverseContexts f (PairB b1 b2) =
    PairB <$> tc f b1 <*> tc f b2
instance HasContexts (NameBinder c n l)
instance HasContexts (UBinder c n l) where
  traverseContexts f binder = case binder of
    UBindSource pos name -> UBindSource <$> f pos <*> tc f name
    UIgnore -> pure binder
    UBind pos name binder' -> UBind <$> f pos <*> tc f name <*> tc f binder'

instance (forall n' l'. HasContexts (b n' l')) => HasContexts (Nest b n l) where
  traverseContexts f nest = case nest of
    Empty -> pure Empty
    Nest bnh ne -> Nest <$> tc f bnh <*> tc f ne

instance HasContexts (ExtLabeledItems (UExpr n) (UExpr n))
instance HasContexts (SourceOrInternalName c n)
instance HasContexts a => HasContexts (Maybe a)
instance HasContexts a => HasContexts (LabeledItems a)
instance HasContexts a => HasContexts (NE.NonEmpty a)

instance HasContexts a => HasContexts (M.Map Label a) where
  -- TODO(danielzheng): Find a more efficient implementation?
  traverseContexts f x = M.fromList <$> tc f (M.toList x)

instance HasContexts (UnitB n l) where
  traverseContexts _ x = pure x

instance HasContexts (UFieldRowPat n l) where
  traverseContexts _ x = pure x

instance HasContexts (Group')
--   traverseContexts f group' = case group' of
--     -- Trivial cases: syntax nodes with no SrcPosCtx.
--     CEmpty -> pure group'
--     CIdentifier _ -> pure group'
--     CNat _ -> pure group'
--     CInt _ -> pure group'
--     CString _ -> pure group'
--     CChar _ -> pure group'
--     CFloat _ -> pure group'
--     CHole -> pure group'
--     CLabel _ _ -> pure group'
--     -- Significant cases.
--     CPrim name group -> CPrim name <$> pure group
--     CParens block -> CParens <$> tc f block
--     CBracket _ group -> pure group'
--     CBin bin lhs rhs -> pure group'
--     CPrefix name group -> pure group'
--     CPostfix name group -> pure group'
--     CLambda groups body -> pure group'
--     CFor kind groups body -> pure group'
--     CCase scrutinee pattners -> pure group'
--     CIf cond thenBlock maybeElseBlock -> pure group'
--     CDo body -> pure group'

instance HasContexts Bin'
instance HasContexts LabelPrefix
instance HasContexts Bracket
instance HasContexts ForKind
instance HasContexts CSBlock
instance HasContexts CSDecl'
instance HasContexts CTopDecl'

instance HasContexts LetAnn
instance HasContexts UsageInfo
instance HasContexts Count

instance HasContexts a => HasContexts (WithSrc a) where
  traverseContexts f (WithSrc pos x) = WithSrc <$> f pos <*> tc f x

instance HasContexts Any
instance HasContexts Bool
instance HasContexts a => HasContexts [a]
instance HasContexts (SourceNameOr e n) where
  traverseContexts f x = case x of
    SourceName pos s -> SourceName <$> f pos <*> pure s
    InternalName pos s n -> InternalName <$> f pos <*> pure s <*> pure n
instance HasContexts (UVar n)
instance HasContexts (Name a n)
instance HasContexts RawName
instance HasContexts () where
  traverseContexts _ x = pure x
instance HasContexts Char where
  traverseContexts _ x = pure x
instance HasContexts Int where
  traverseContexts _ x = pure x
instance HasContexts Int32 where
  traverseContexts _ x = pure x
instance HasContexts Int64 where
  traverseContexts _ x = pure x
instance HasContexts Word8 where
  traverseContexts _ x = pure x
instance HasContexts Word16 where
  traverseContexts _ x = pure x
instance HasContexts Word32 where
  traverseContexts _ x = pure x
instance HasContexts Word64 where
  traverseContexts _ x = pure x
instance HasContexts Float where
  traverseContexts _ x = pure x
instance HasContexts Double where
  traverseContexts _ x = pure x
instance HasContexts BS.ByteString where
  traverseContexts _ x = pure x

-- The real base case.
instance HasContexts SrcPosCtx where
  traverseContexts f x = f x

gatherContexts :: (HasContexts a) => a -> [SrcPosCtx]
gatherContexts x = execWriter (tc (\(ctx :: SrcPosCtx) -> tell [ctx] >> return ctx) x)

addContextIds :: (HasContexts a) => a -> a
addContextIds x = evalState (tc f x) 0
  where f (SrcPosCtx maybeSrcPos _) = do
          currentId <- get
          put (currentId + 1)
          return (SrcPosCtx maybeSrcPos (Just currentId))
