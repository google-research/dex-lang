-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module Serialize (pprintVal, getDexString,
                  HasPtrs (..), takePtrSnapshot, restorePtrSnapshot) where

import Prelude hiding (pi, abs)
import Control.Monad
import Control.Monad.IO.Class
import qualified Data.ByteString as BS
import Data.List.NonEmpty qualified as NE
import Data.ByteString.Internal (memcpy)
import Data.ByteString.Unsafe (unsafeUseAsCString)
import Data.Foldable
import qualified Data.Map.Strict as M
import Data.Int
import Data.List.NonEmpty (NonEmpty (..))
import Data.Store hiding (size)
import Data.Text.Prettyprint.Doc  hiding (brackets)
import Foreign.Ptr
import Foreign.C.String
import Foreign.Marshal.Array
import GHC.Generics (Generic)
import Numeric (showHex)

import Core
import Err
import IRVariants
import Interpreter
import LabeledItems
import Name
import PPrint ()
import PPrint (PrettyPrec (..), PrecedenceLevel (..))
import QueryType
import Types.Core
import Types.Imp
import Types.Primitives
import Util (Tree (..), restructure)

foreign import ccall "malloc_dex"           dexMalloc    :: Int64  -> IO (Ptr ())
foreign import ccall "dex_allocation_size"  dexAllocSize :: Ptr () -> IO Int64

pprintVal :: (MonadIO1 m, EnvReader m, Fallible1 m) => Val CoreIR n -> m n String
pprintVal val = docAsStr <$> prettyVal val
{-# SCC pprintVal #-}

getDexString :: (MonadIO1 m, EnvReader m, Fallible1 m) => Val CoreIR n -> m n String
getDexString val = do
  -- TODO: use a `ByteString` instead of `String`
  Var v <- return val
  TopDataBound (RepVal _ tree) <- lookupAtomName v
  Branch [Leaf (IIdxRepVal n), Leaf (IPtrVar ptrName _)] <- return tree
  PtrBinding (CPU, Scalar Word8Type) (PtrLitVal ptr) <- lookupEnv ptrName
  liftIO $ peekCStringLen (castPtr ptr, fromIntegral n)

getTableElements :: (MonadIO1 m, EnvReader m, Fallible1 m) => Val CoreIR n -> m n [CAtom n]
getTableElements tab = do
  TabTy b _ <- getType tab
  idxs <- indices $ binderAnn b
  forM idxs \i -> liftInterpM $ evalExpr $ TabApp tab (i:|[])

-- Pretty-print values, e.g. for displaying in the REPL.
-- This doesn't handle parentheses well. TODO: treat it more like PrettyPrec
prettyVal
  :: (MonadIO1 m, EnvReader m, Fallible1 m)
  => Val CoreIR n -> m n (Doc ann)
prettyVal val = case val of
  Var v -> lookupAtomName v >>= \case
    TopDataBound repVal -> repValToCoreAtom repVal >>= prettyVal
    _ -> return $ prettyPrec val LowestPrec
  -- Pretty-print tables.
  TabVal _ _ -> do
    atoms <- getTableElements val
    elems <- forM atoms \atom -> do
      case atom of
        Con (Lit (Word8Lit  c)) -> return $ "'" ++ showChar (toEnum @Char $ fromIntegral c) "" ++ "'"
        Con (Lit (Word32Lit c)) -> return $ "0x" ++ showHex c ""
        Con (Lit (Word64Lit c)) -> return $ "0x" ++ showHex c ""
        _ -> pprintVal atom
    TabTy b _ <- getType val
    idxSetDoc <- return case binderType b of
      TC (Fin _)  -> mempty               -- (Fin n) is not shown
      idxSet -> "@" <> pretty idxSet -- Otherwise, show explicit index set
    return $ pretty elems <> idxSetDoc
  Record tys vals -> do
    let LabeledItems row = restructure vals tys
    let separator = line' <> ","
    let bindwith = " ="
    let elems = concatMap (\(k, vs) -> map (k,) (toList vs)) (M.toAscList row)
    let fmElem = \(label, v) -> ((pretty label <> bindwith) <+>) <$> prettyVal v
    docs <- mapM fmElem elems
    let innerDoc = "{" <> flatAlt " " ""
          <> concatWith (surround (separator <> " ")) docs
          <> "}"
    return $ align $ group innerDoc
  Con con -> case con of
    ProdCon [] -> return $ pretty ()
    ProdCon [x, y] -> do
      xStr <- pprintVal x
      yStr <- pprintVal y
      return $ pretty (xStr, yStr)
    ProdCon _ -> error "Unexpected product type: only binary products available in surface language."
    Newtype NatTy (IdxRepVal n) -> return $ pretty n
    Newtype vty@(VariantTy (NoExt types)) (Con (SumAsProd _ (TagRepVal trep) payload)) ->
      return $ pretty $ Newtype vty $ SumVal (toList types) t value
      where t = fromIntegral trep; value = payload !! t
    -- Pretty-print strings
    Newtype (TypeCon "List" _ (DataDefParams [(PlainArrow, Word8Ty)])) payload -> do
      DepPair _ xs _ <- return payload
      xs' <- getTableElements xs
      s <- forM xs' \case
        Con (Lit (Word8Lit c)) -> return $ toEnum $ fromIntegral c
        x -> error $ "bad" ++ pprint x
      return $ pretty $ "\"" ++ s ++ "\""
    Newtype (TypeCon _ dataDefName _) (Con (SumCon _ t e)) -> prettyData dataDefName t e
    Newtype (TypeCon _ dataDefName _) (Con (SumAsProd _ (TagRepVal trep) payload)) -> prettyData dataDefName t e
      where t = fromIntegral trep; e = payload !! t
    Newtype (TypeCon _ dataDefName _) e -> prettyData dataDefName 0 e
    SumAsProd _ _ _ -> error "SumAsProd with an unsupported type"
    _ -> return $ pretty con
  DepPair lhs rhs ty -> do
    lhs' <- prettyVal lhs
    rhs' <- prettyVal rhs
    ty' <- prettyVal $ DepPairTy ty
    return $ "(" <> lhs' <+> ",>" <+> rhs' <> ")" <+> "::" <+> ty'
  ProjectElt projections v -> lookupAtomName v >>= \case
    TopDataBound repVal -> do
      x <- repValToCoreAtom repVal
      prettyVal $ getProjection (NE.toList projections) x
    _ -> error "Only projectable vars left should be data vars"
  atom -> return $ prettyPrec atom LowestPrec
  where
    prettyData
      :: (MonadIO1 m, EnvReader m, Fallible1 m)
      => DataDefName n -> Int -> CAtom n -> m n (Doc ann)
    prettyData dataDefName t rep = do
      DataDef _ _ dataCons <- lookupDataDef dataDefName
      DataConDef conName _ idxs <- return $ dataCons !! t
      prettyArgs <- forM idxs \ix -> prettyVal $ getProjection (init ix) rep
      return $ case prettyArgs of
        []   -> pretty conName
        args -> parens $ pretty conName <+> hsep args

-- === taking memory snapshots for serializing heap-backed dex values ===

data WithSnapshot a = WithSnapshot a [PtrSnapshot]  deriving Generic
type RawPtr = Ptr ()

class HasPtrs a where
  traversePtrs :: Applicative f => (PtrType -> RawPtr -> f RawPtr) -> a -> f a

takePtrSnapshot :: PtrType -> PtrLitVal -> IO PtrLitVal
takePtrSnapshot _ NullPtr = return NullPtr
takePtrSnapshot (CPU, ptrTy) (PtrLitVal ptrVal) = case ptrTy of
  PtrType eltTy -> do
    childPtrs <- loadPtrPtrs ptrVal
    PtrSnapshot <$> PtrArray <$> mapM (takePtrSnapshot eltTy) childPtrs
  _ -> PtrSnapshot . ByteArray <$> loadPtrBytes ptrVal
takePtrSnapshot (GPU, _) _ = error "Snapshots of GPU memory not implemented"
takePtrSnapshot _ (PtrSnapshot _) = error "Already a snapshot"
{-# SCC takePtrSnapshot #-}

loadPtrBytes :: RawPtr -> IO BS.ByteString
loadPtrBytes ptr = do
  numBytes <- fromIntegral <$> dexAllocSize ptr
  liftM BS.pack $ peekArray numBytes $ castPtr ptr

loadPtrPtrs :: RawPtr -> IO [PtrLitVal]
loadPtrPtrs ptr = do
  numBytes <- fromIntegral <$> dexAllocSize ptr
  childPtrs <- peekArray (numBytes `div` ptrSize) $ castPtr ptr
  forM childPtrs \childPtr ->
    if childPtr == nullPtr
      then return NullPtr
      else return $ PtrLitVal childPtr

restorePtrSnapshot :: PtrLitVal -> IO PtrLitVal
restorePtrSnapshot NullPtr = return NullPtr
restorePtrSnapshot (PtrSnapshot snapshot) = case snapshot of
  PtrArray  children -> do
    childrenPtrs <- forM children \child ->
      restorePtrSnapshot child >>= \case
        NullPtr -> return nullPtr
        PtrLitVal p -> return p
        PtrSnapshot _ -> error "expected a pointer literal"
    PtrLitVal <$> storePtrPtrs childrenPtrs
  ByteArray bytes -> PtrLitVal <$> storePtrBytes bytes
restorePtrSnapshot (PtrLitVal _) = error "not a snapshot"
{-# SCC restorePtrSnapshot #-}

storePtrBytes :: BS.ByteString -> IO RawPtr
storePtrBytes xs = do
  let numBytes = BS.length xs
  destPtr <- dexMalloc $ fromIntegral numBytes
  -- this is safe because we don't modify srcPtr's memory or let it escape
  unsafeUseAsCString xs \srcPtr ->
    memcpy (castPtr destPtr) (castPtr srcPtr) numBytes
  return destPtr

storePtrPtrs :: [RawPtr] -> IO RawPtr
storePtrPtrs ptrs = do
  ptr <- dexMalloc $ fromIntegral $ length ptrs * ptrSize
  pokeArray (castPtr ptr) ptrs
  return ptr

-- === instances ===

instance Store a => Store (WithSnapshot a)
