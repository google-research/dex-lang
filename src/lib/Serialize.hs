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
import Data.Store hiding (size)
import Data.Text.Prettyprint.Doc  hiding (brackets)
import Data.Word
import System.IO (stderr, hPutStrLn)
import Foreign.Ptr
import Foreign.C.String
import Foreign.Marshal.Array
import GHC.Generics (Generic)
import Numeric (showHex)

import LabeledItems

import Interpreter
import Err
import PPrint (PrettyPrec (..), PrecedenceLevel (..))

import Syntax
import Types.Core
import QueryType
import Name
import PPrint ()
import Util (restructure)

foreign import ccall "malloc_dex"           dexMalloc    :: Int64  -> IO (Ptr ())
foreign import ccall "dex_allocation_size"  dexAllocSize :: Ptr () -> IO Int64

pprintVal :: (MonadIO1 m, EnvReader m, Fallible1 m) => Val CoreIR n -> m n String
pprintVal val = docAsStr <$> prettyVal val
{-# SCC pprintVal #-}

getDexString :: (MonadIO1 m, EnvReader m, Fallible1 m) => Val CoreIR n -> m n String
getDexString (Con (Newtype _ (DepPair _ xs _))) = undefined
-- getDexString (Con (Newtype _ (DepPair _ xs _))) = case tryParseStringContent xs of
--   Just (ptrAtom, n) -> do
--     lookupAtomName ptrAtom >>= \case
--       PtrLitBound _ ptrName -> lookupEnv ptrName >>= \case
--         PtrBinding (PtrLitVal (Heap CPU, Scalar Word8Type) ptr) -> do
--           liftIO $ peekCStringLen (castPtr ptr, fromIntegral n)
--         _ -> error "Expected a CPU pointer binding!"
--       _ -> error "Expected a pointer binding!"
--   Nothing -> do
--     liftIO $ hPutStrLn stderr $ "Falling back to a slow path in Dex string retrieval!"
--     xs' <- getTableElements xs
--     forM xs' \(Con (Lit (Word8Lit c))) -> return $ toEnum $ fromIntegral c
--   where
--     tryParseStringContent :: CAtom n -> Maybe (CAtomName n, Word32)
--     tryParseStringContent tabAtom  = do
--       TabLam (TabLamExpr i body) <- return tabAtom
--       FinConst n <- return $ binderType i
--       Block _ (Nest offDecl (Nest loadDecl Empty)) (Var result) <- return body
--       Let v1 (DeclBinding _ _ (Op (PtrOffset (Var ptrName) (ProjectElt (UnwrapBaseNewtype NE.:| [UnwrapBaseNewtype]) i')))) <- return offDecl
--       guard $ binderName i == i'
--       Let r (DeclBinding _ _ loadExpr) <- return loadDecl
--       guard $ binderName r == result
--       Hof (RunIO (Lam (LamExpr iob iobody))) <- return loadExpr
--       HoistSuccess (Block _ (Nest ioDecl Empty) (Var ioResult)) <- return $ hoist iob iobody
--       Let ioR (DeclBinding _ _ (Op (PtrLoad (Var v1')))) <- return ioDecl
--       guard $ binderName ioR == ioResult
--       guard $ binderName v1 == v1'
--       HoistSuccess ptrAtomTop <- return $ hoist i ptrName
--       return (ptrAtomTop, n)
-- getDexString x = error $ "Not a string: " ++ pprint x
-- {-# SCC getDexString #-}

getTableElements :: (MonadIO1 m, EnvReader m, Fallible1 m) => Val CoreIR n -> m n [CAtom n]
getTableElements tab = do
  TabTy b _ <- getType tab
  idxs <- indices $ binderAnn b
  forM idxs \i -> liftInterpM $ evalExpr $ TabApp tab (i:|[])

-- Pretty-print values, e.g. for displaying in the REPL.
-- This doesn't handle parentheses well. TODO: treat it more like PrettyPrec
prettyVal :: (MonadIO1 m, EnvReader m, Fallible1 m) => Val CoreIR n -> m n (Doc ann)
prettyVal val = case val of
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
    Newtype (TypeCon "List" _ (DataDefParams [(PlainArrow, Word8Ty)])) _ -> do
      s <- getDexString val
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
  atom -> return $ prettyPrec atom LowestPrec
  where
    prettyData :: (MonadIO1 m, EnvReader m, Fallible1 m) => DataDefName n -> Int -> CAtom n -> m n (Doc ann)
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

takePtrSnapshot :: PtrType -> RawPtr -> IO PtrSnapshot
takePtrSnapshot _ ptrVal | ptrVal == nullPtr = return NullPtr
takePtrSnapshot (Heap CPU, ptrTy) ptrVal = case ptrTy of
  PtrType eltTy -> do
    childPtrs <- loadPtrPtrs ptrVal
    PtrArray <$> mapM (takePtrSnapshot eltTy) childPtrs
  _ -> ByteArray <$> loadPtrBytes ptrVal
takePtrSnapshot (Heap GPU, _) _ = error "Snapshots of GPU memory not implemented"
takePtrSnapshot (Stack   , _) _ = error "Can't take snapshots of stack memory"
{-# SCC takePtrSnapshot #-}

loadPtrBytes :: RawPtr -> IO BS.ByteString
loadPtrBytes ptr = do
  numBytes <- fromIntegral <$> dexAllocSize ptr
  liftM BS.pack $ peekArray numBytes $ castPtr ptr

loadPtrPtrs :: RawPtr -> IO [RawPtr]
loadPtrPtrs ptr = do
  numBytes <- fromIntegral <$> dexAllocSize ptr
  peekArray (numBytes `div` ptrSize) $ castPtr ptr

restorePtrSnapshot :: PtrSnapshot -> IO RawPtr
restorePtrSnapshot snapshot = case snapshot of
  PtrArray  children -> storePtrPtrs =<< mapM restorePtrSnapshot children
  ByteArray bytes    -> storePtrBytes bytes
  NullPtr            -> return nullPtr
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
