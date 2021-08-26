-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE CPP #-}

module Serialize (pprintVal, cached, getDexString, cachedWithSnapshot,
                 HasPtrs (..)) where

import Prelude hiding (pi, abs)
import Control.Monad
import qualified Data.ByteString as BS
import Data.ByteString.Internal (memcpy)
import Data.ByteString.Unsafe (unsafeUseAsCString)
import System.Directory
import System.FilePath
import Control.Monad.Writer
import Control.Monad.State.Strict
import Data.Foldable
import qualified Data.Map.Strict as M
import Data.Int
import Data.Store hiding (size)
import Data.Text.Prettyprint.Doc  hiding (brackets)
import Foreign.Ptr
import Foreign.Marshal.Array
import GHC.Generics (Generic)
import Numeric (showHex)

import Interpreter
import LabeledItems
import Syntax
import Type
import PPrint
import Env

foreign import ccall "malloc_dex"           dexMalloc    :: Int64  -> IO (Ptr ())
foreign import ccall "dex_allocation_size"  dexAllocSize :: Ptr () -> IO Int64

pprintVal :: Val -> IO String
pprintVal val = docAsStr <$> prettyVal val

-- TODO: get the pointer rather than reading char by char
getDexString :: Val -> IO String
getDexString (DataCon _ _ 0 [_, xs]) = do
  let (TabTy b _) = getType xs
  idxs <- indices $ getType b
  forM idxs \i -> do
    ~(Con (Lit (Word8Lit c))) <- evalBlock mempty (Block Empty (App xs i))
    return $ toEnum $ fromIntegral c
getDexString x = error $ "Not a string: " ++ pprint x

-- Pretty-print values, e.g. for displaying in the REPL.
-- This doesn't handle parentheses well. TODO: treat it more like PrettyPrec
prettyVal :: Val -> IO (Doc ann)
prettyVal val = case val of
  -- Pretty-print tables.
  Lam abs@(Abs b (TabArrow, body)) -> do
    -- Pretty-print index set.
    let idxSet = binderType b
    let idxSetDoc = case idxSet of
          Fin _ -> mempty               -- (Fin n) is not shown
          _     -> "@" <> pretty idxSet -- Otherwise, show explicit index set
    -- Pretty-print elements.
    idxs <- indices idxSet
    elems <- forM idxs \idx -> do
      atom <- evalBlock mempty $ snd $ applyAbs abs idx
      case atom of
        Con (Lit (Word8Lit c)) ->
          return $ showChar (toEnum @Char $ fromIntegral c) ""
        Con (Lit (Word32Lit c)) -> return $ "0x" ++ showHex c ""
        Con (Lit (Word64Lit c)) -> return $ "0x" ++ showHex c ""
        _ -> pprintVal atom
    let bodyType = getType body
    let elemsDoc = case bodyType of
          -- Print table of characters as a string literal.
          TC (BaseType (Scalar Word8Type)) -> pretty ('"': concat elems ++ "\"")
          _      -> pretty elems
    return $ elemsDoc <> idxSetDoc
  DataCon (_, DataDef _ _ dataCons) _ con args ->
    case args of
      [] -> return $ pretty conName
      _  -> do
        ans <- mapM prettyVal args
        return $ parens $ pretty conName <+> hsep ans
    where DataConDef conName _ = dataCons !! con
  Con con -> case con of
    ProdCon [] -> return $ pretty ()
    ProdCon [x, y] -> do
      xStr <- pprintVal x
      yStr <- pprintVal y
      return $ pretty (xStr, yStr)
    ProdCon _ -> error "Unexpected product type: only binary products available in surface language."
    SumAsProd ty (TagRepVal trep) payload -> do
      let t = fromIntegral trep
      case ty of
        TypeCon (_, DataDef _ _ dataCons) _ ->
          case args of
            [] -> return $ pretty conName
            _  -> do
              ans <- mapM prettyVal args
              return $ parens $ pretty conName <+> hsep ans
          where
            DataConDef conName _ = dataCons !! t
            args = payload !! t
        VariantTy (NoExt types) -> return $ pretty variant
          where
            [value] = payload !! t
            (theLabel, repeatNum) = toList (reflectLabels types) !! t
            variant = Variant (NoExt types) theLabel repeatNum value
        _ -> error "SumAsProd with an unsupported type"
    _ -> return $ pretty con
  Record (LabeledItems row) -> do
    let separator = line' <> ","
    let bindwith = " ="
    let elems = concatMap (\(k, vs) -> map (k,) (toList vs)) (M.toAscList row)
    let fmElem = \(label, v) -> ((pretty label <> bindwith) <+>) <$> prettyVal v
    docs <- mapM fmElem elems
    let innerDoc = "{" <> flatAlt " " ""
          <> concatWith (surround (separator <> " ")) docs
          <> "}"
    return $ align $ group innerDoc
  atom -> return $ prettyPrec atom LowestPrec

-- === taking memory snapshots for serializing heap-backed dex values ===

data WithSnapshot a = WithSnapshot a [PtrSnapshot]  deriving Generic
type RawPtr = Ptr ()
-- TODO: we could consider using some mmap-able instead of ByteString
data PtrSnapshot = ByteArray BS.ByteString
                 | PtrArray [PtrSnapshot]
                 | NullPtr  deriving Generic

class HasPtrs a where
  traversePtrs :: Applicative f => (PtrType -> RawPtr -> f RawPtr) -> a -> f a

takeSnapshot :: HasPtrs a => a -> IO (WithSnapshot a)
takeSnapshot x =
  -- TODO: we're using `Writer []` (as we do elsewhere) which has bad
  -- asymptotics. We should switch all of these uses to use snoc lists instead.
  liftM (WithSnapshot x) $ execWriterT $ flip traversePtrs x \ptrTy ptrVal -> do
    snapshot <- lift $ takePtrSnapshot ptrTy ptrVal
    tell [snapshot]
    return ptrVal

takePtrSnapshot :: PtrType -> RawPtr -> IO PtrSnapshot
takePtrSnapshot _ ptrVal | ptrVal == nullPtr = return NullPtr
takePtrSnapshot (Heap CPU, ptrTy) ptrVal = case ptrTy of
  PtrType eltTy -> do
    childPtrs <- loadPtrPtrs ptrVal
    PtrArray <$> mapM (takePtrSnapshot eltTy) childPtrs
  _ -> ByteArray <$> loadPtrBytes ptrVal
takePtrSnapshot (Heap GPU, _) _ = error "Snapshots of GPU memory not implemented"
takePtrSnapshot (Stack   , _) _ = error "Can't take snapshots of stack memory"

loadPtrBytes :: RawPtr -> IO BS.ByteString
loadPtrBytes ptr = do
  numBytes <- fromIntegral <$> dexAllocSize ptr
  liftM BS.pack $ peekArray numBytes $ castPtr ptr

loadPtrPtrs :: RawPtr -> IO [RawPtr]
loadPtrPtrs ptr = do
  numBytes <- fromIntegral <$> dexAllocSize ptr
  peekArray (numBytes `div` ptrSize) $ castPtr ptr

restoreSnapshot :: HasPtrs a => WithSnapshot a -> IO a
restoreSnapshot (WithSnapshot x snapshots) =
  flip evalStateT snapshots $ flip traversePtrs x \_ _ -> do
    (s:ss) <- get
    put ss
    lift $ restorePtrSnapshot s

restorePtrSnapshot :: PtrSnapshot -> IO RawPtr
restorePtrSnapshot snapshot = case snapshot of
  PtrArray  children -> storePtrPtrs =<< mapM restorePtrSnapshot children
  ByteArray bytes    -> storePtrBytes bytes
  NullPtr            -> return nullPtr

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

-- === persistent cache ===

-- TODO: this isn't enough, since this module's compilation might be cached
curCompilerVersion :: String
curCompilerVersion = __TIME__

cachedWithSnapshot :: (Eq k, Store k, Store a, HasPtrs a)
                   => String -> k -> IO a -> IO a
cachedWithSnapshot cacheName key create = do
  result <- cached cacheName key $ create >>= takeSnapshot
  restoreSnapshot result

cached :: (Eq k, Store k, Store a) => String -> k -> IO a -> IO a
cached cacheName key create = do
  cacheDir <- getXdgDirectory XdgCache "dex"
  createDirectoryIfMissing True cacheDir
  let cacheKeyPath = cacheDir </> (cacheName ++ ".key")
  let cachePath    = cacheDir </> (cacheName ++ ".cache")
  cacheExists <- (&&) <$> doesFileExist cacheKeyPath <*> doesFileExist cachePath
  cacheUpToDate <- case cacheExists of
                     False -> return False
                     True -> do
                       maybeCacheKey <- decode <$> BS.readFile cacheKeyPath
                       case maybeCacheKey of
                         Right cacheKey -> return $ cacheKey == (curCompilerVersion, key)
                         Left  _        -> return False
  if cacheUpToDate
    then do
      decoded <- decode <$> BS.readFile cachePath
      case decoded of
        Right result -> return result
        _            -> removeFile cachePath >> cached cacheName key create
    else do
      result <- create
      BS.writeFile cacheKeyPath $ encode (curCompilerVersion, key)
      BS.writeFile cachePath    $ encode result
      return result

-- === instances ===

tp :: (HasPtrs a, Applicative f) => (PtrType -> RawPtr -> f RawPtr) -> a -> f a
tp = traversePtrs

instance HasPtrs Expr where
  traversePtrs f expr = case expr of
    App e1 e2 -> App  <$> tp f e1 <*> tp f e2
    Atom x    -> Atom <$> tp f x
    Op  e     -> Op   <$> traverse (tp f) e
    Hof e     -> Hof  <$> traverse (tp f) e
    Case e alts resultTy ->
      Case <$> tp f e <*> traverse (tp f) alts <*> tp f resultTy

instance (HasPtrs a, HasPtrs b) => HasPtrs (Abs a b) where
  traversePtrs f (Abs b body) = Abs <$> tp f b <*> tp f body

instance HasPtrs Block where
  traversePtrs f (Block decls result) =
    Block <$> traverse (tp f) decls <*> tp f result

instance HasPtrs Decl where
  traversePtrs f (Let ann b body) = Let ann <$> tp f b <*> tp f body

instance (HasPtrs a, HasPtrs b) => HasPtrs (a, b) where
  traversePtrs f (x, y) = (,) <$> tp f x <*> tp f y

instance HasPtrs eff => HasPtrs (ArrowP eff) where
  traversePtrs f arrow = case arrow of
    PlainArrow eff -> PlainArrow <$> tp f eff
    _ -> pure arrow

instance (HasPtrs a, HasPtrs b) => HasPtrs (ExtLabeledItems a b) where
  traversePtrs f (Ext items t) =
    Ext <$> traverse (tp f) items <*> traverse (tp f) t

instance HasPtrs DataConRefBinding where
  traversePtrs f (DataConRefBinding b ref) =
    DataConRefBinding <$> tp f b <*> tp f ref

instance HasPtrs Atom where
  traversePtrs f atom = case atom of
    Var v   -> Var <$> traverse (tp f) v
    Lam lam -> Lam <$> tp f lam
    Pi  ty  -> Pi  <$> tp f ty
    DepPairTy     ta -> DepPairTy <$> tp f ta
    DepPair   x y ta -> DepPair <$> tp f x <*> tp f y <*> tp f ta
    TC  tc  -> TC  <$> traverse (tp f) tc
    Con (Lit (PtrLit ptrTy ptr)) -> (Con . Lit . PtrLit ptrTy) <$> f ptrTy ptr
    Con con -> Con <$> traverse (tp f) con
    Eff eff -> Eff <$> tp f eff
    DataCon def ps con args -> DataCon def <$> tp f ps <*> pure con <*> tp f args
    TypeCon def ps          -> TypeCon def <$> tp f ps
    LabeledRow row -> LabeledRow <$> tp f row
    Record la -> Record <$> traverse (tp f) la
    Variant row label i val ->
      Variant <$> tp f row <*> pure label <*> pure i <*> tp f val
    RecordTy  row -> RecordTy  <$> tp f row
    VariantTy row -> VariantTy <$> tp f row
    ACase v alts rty -> ACase <$> tp f v <*>  tp f alts <*> tp f rty
    DataConRef def params args -> DataConRef def <$> tp f params <*> tp f args
    DepPairRef _ _ _ -> undefined  -- This is only used in Imp
    BoxedRef b ptr size body ->
      BoxedRef <$> tp f b <*> tp f ptr <*> tp f size <*> tp f body
    ProjectElt idxs v -> pure $ ProjectElt idxs v

instance HasPtrs Name      where traversePtrs _ x = pure x
instance HasPtrs EffectRow where traversePtrs _ x = pure x

instance HasPtrs a => HasPtrs [a]         where traversePtrs f xs = traverse (tp f) xs
instance HasPtrs a => HasPtrs (Nest a)    where traversePtrs f xs = traverse (tp f) xs
instance HasPtrs a => HasPtrs (BinderP a) where traversePtrs f xs = traverse (tp f) xs

instance HasPtrs AnyBinderInfo where
  traversePtrs f (AtomBinderInfo ty info) =
    AtomBinderInfo <$> traversePtrs f ty <*> traversePtrs f info
  traversePtrs _ info = pure info

instance HasPtrs BinderInfo where
  traversePtrs f binfo = case binfo of
   LetBound ann expr -> LetBound ann <$> tp f expr
   _ -> pure binfo

instance Store a => Store (WithSnapshot a)
instance Store PtrSnapshot
