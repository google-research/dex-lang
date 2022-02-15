-- Copyright 2020 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module Dex.Foreign.Serialize (
  CAtom,
  dexPrint, dexToCAtom, dexFromCAtom
  ) where

import Control.Monad.IO.Class
import Data.Word
import Data.Functor

import Foreign.C
import Foreign.Ptr
import Foreign.Storable

import Name
import Syntax
import Serialize (pprintVal)
import TopLevel

import Dex.Foreign.Context
import Dex.Foreign.Util

-- TODO: Free!
dexPrint :: Ptr Context -> Ptr AtomEx -> IO CString
dexPrint contextPtr atomPtr = do
  Context evalConfig env <- fromStablePtr contextPtr
  AtomEx atom <- fromStablePtr atomPtr
  fst <$> runTopperM evalConfig env do
    -- TODO: Check consistency of atom and context
    liftIO . newCString =<< pprintVal (unsafeCoerceE atom)

data CAtom = CLit LitVal | CRectArray (Ptr ()) [Int] [Int]

instance Storable CAtom where
  sizeOf _ = tag + val + val + val
    where tag = 8; val = 8
  alignment _ = 8
  peek addr = do
    tag <- val @Word64 0
    case tag of
      0 -> do
        litTag <- val @Word64 1
        CLit <$> case litTag of
                   0 -> Int64Lit   <$> val 2
                   1 -> Int32Lit   <$> val 2
                   2 -> Word8Lit   <$> val 2
                   3 -> Float64Lit <$> val 2
                   4 -> Float32Lit <$> val 2
                   5 -> Word32Lit  <$> val 2
                   6 -> Word64Lit  <$> val 2
                   _ -> error "Invalid tag"
      _ -> error "Invalid tag"
    where
      val :: forall a. Storable a => Int -> IO a
      val i = peekByteOff (castPtr addr) (i * 8)
  poke addr catom = case catom of
    CLit lit -> do
      val @Word64 0 0
      case lit of
        Int64Lit   v -> val @Word64 1 0 >> val 2 v
        Int32Lit   v -> val @Word64 1 1 >> val 2 v
        Word8Lit   v -> val @Word64 1 2 >> val 2 v
        Float64Lit v -> val @Word64 1 3 >> val 2 v
        Float32Lit v -> val @Word64 1 4 >> val 2 v
        Word32Lit  v -> val @Word64 1 5 >> val 2 v
        Word64Lit  v -> val @Word64 1 6 >> val 2 v
        VecLit     _ -> error "Unsupported"
        PtrLit     _ -> error "Unsupported"
    CRectArray _ _ _ -> error "Unsupported"
    where
      val :: forall a. Storable a => Int -> a -> IO ()
      val i v = pokeByteOff (castPtr addr) (i * 8) v

dexToCAtom :: Ptr AtomEx -> Ptr CAtom -> IO CInt
dexToCAtom atomPtr resultPtr = do
  AtomEx atom <- fromStablePtr atomPtr
  case atom of
    Con con -> case con of
      Lit (VecLit _) -> notSerializable
      Lit l          -> poke resultPtr (CLit l) $> 1
      _ -> notSerializable
    _ -> notSerializable
  where
    notSerializable = setError "Unserializable atom" $> 0

dexFromCAtom :: Ptr CAtom -> IO (Ptr AtomEx)
dexFromCAtom catomPtr = do
  catom <- peek catomPtr
  case catom of
    CLit lit         -> toStablePtr $ AtomEx $ Con $ Lit lit
    CRectArray _ _ _ -> unsupported
  where
    unsupported = setError "Unsupported CAtom" $> nullPtr
