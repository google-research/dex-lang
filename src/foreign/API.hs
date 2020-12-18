-- Copyright 2020 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module API where

import Control.Monad.State.Strict

import Foreign.Ptr
import Foreign.StablePtr
import Foreign.Storable
import Foreign.Marshal.Alloc
import Foreign.C.String
import Foreign.C.Types

import Data.String
import Data.Word
import Data.Int
import Data.Functor
import Data.Foldable

import Resources
import Syntax  hiding (sizeOf)
import Type
import TopLevel
import Parser (parseExpr, exprAsModule)
import Serialize (pprintVal)
import Env hiding (Tag)
import PPrint

-- Public API (commented out exports are defined in rts.c)
-- foreign export ccall "dexInit"     _ :: IO ()
-- foreign export ccall "dexFini"     _ :: IO ()
-- foreign export ccall "dexGetError" _ :: CString
foreign export ccall "dexCreateContext"  dexCreateContext  :: IO (Ptr Context)
foreign export ccall "dexDestroyContext" dexDestroyContext :: Ptr Context -> IO ()
foreign export ccall "dexPrint"    dexPrint    :: Ptr Atom                 -> IO CString
foreign export ccall "dexInsert"   dexInsert   :: Ptr Context -> CString   -> Ptr Atom -> IO (Ptr Context)
foreign export ccall "dexEval"     dexEval     :: Ptr Context -> CString   -> IO (Ptr Context)
foreign export ccall "dexEvalExpr" dexEvalExpr :: Ptr Context -> CString   -> IO (Ptr Atom)
foreign export ccall "dexLookup"   dexLookup   :: Ptr Context -> CString   -> IO (Ptr Atom)
foreign export ccall "dexToCAtom"  dexToCAtom  :: Ptr Atom    -> Ptr CAtom -> IO CInt

data Context = Context EvalConfig TopEnv

foreign import ccall "_internal_dexSetError" internalSetErrorPtr :: CString -> Int64 -> IO ()
setError :: String -> IO ()
setError msg = withCStringLen msg $ \(ptr, len) ->
  internalSetErrorPtr ptr (fromIntegral len)

dexCreateContext :: IO (Ptr Context)
dexCreateContext = do
  let evalConfig = EvalConfig LLVM Nothing
  maybePreludeEnv <- evalPrelude evalConfig preludeSource
  case maybePreludeEnv of
    Right preludeEnv -> toStablePtr $ Context evalConfig preludeEnv
    Left  _          -> setError "Failed to initialize standard library" $> nullPtr
  where
    evalPrelude :: EvalConfig -> String -> IO (Either Err TopEnv)
    evalPrelude opts contents = flip evalStateT mempty $ do
      results <- fmap snd <$> evalSource opts contents
      env <- get
      return $ env `unlessError` results
      where
        unlessError :: TopEnv -> [Result] -> Except TopEnv
        result `unlessError` []                        = Right result
        _      `unlessError` ((Result _ (Left err)):_) = Left err
        result `unlessError` (_:t                    ) = result `unlessError` t

dexDestroyContext :: Ptr Context -> IO ()
dexDestroyContext = freeStablePtr . castPtrToStablePtr . castPtr

dexPrint :: Ptr Atom -> IO CString
dexPrint atomPtr = newCString =<< pprintVal =<< fromStablePtr atomPtr

dexEval :: Ptr Context -> CString -> IO (Ptr Context)
dexEval ctxPtr sourcePtr = do
  Context evalConfig env <- fromStablePtr ctxPtr
  source <- peekCString sourcePtr
  (results, finalEnv) <- runStateT (evalSource evalConfig source) env
  let anyError = asum $ fmap (\case (_, Result _ (Left err)) -> Just err; _ -> Nothing) results
  case anyError of
    Nothing  -> toStablePtr $ Context evalConfig finalEnv
    Just err -> setError (pprint err) $> nullPtr

dexInsert :: Ptr Context -> CString -> Ptr Atom -> IO (Ptr Context)
dexInsert ctxPtr namePtr atomPtr = do
  Context evalConfig env <- fromStablePtr ctxPtr
  name <- GlobalName . fromString <$> peekCString namePtr
  atom <- fromStablePtr atomPtr
  let env' = env <> name @> (getType atom, LetBound PlainLet (Atom atom))
  toStablePtr $ Context evalConfig env'

dexEvalExpr :: Ptr Context -> CString -> IO (Ptr Atom)
dexEvalExpr ctxPtr sourcePtr = do
  Context evalConfig env <- fromStablePtr ctxPtr
  maybeExpr <- parseExpr <$> peekCString sourcePtr
  case maybeExpr of
    Right expr -> do
      let (v, m) = exprAsModule expr
      let block = SourceBlock 0 0 LogNothing "" (RunModule m) Nothing
      (resultEnv, Result [] maybeErr) <- evalSourceBlock evalConfig env block
      case maybeErr of
        Right () -> do
          let (_, LetBound _ (Atom atom)) = resultEnv ! v
          toStablePtr atom
        Left err -> setError (pprint err) $> nullPtr
    Left err -> setError (pprint err) $> nullPtr

dexLookup :: Ptr Context -> CString -> IO (Ptr Atom)
dexLookup ctxPtr namePtr = do
  Context _ env <- fromStablePtr ctxPtr
  name <- peekCString namePtr
  case envLookup env (GlobalName $ fromString name) of
    Just (_, LetBound _ (Atom atom)) -> toStablePtr atom
    Just _                           -> setError "Looking up an expression" $> nullPtr
    Nothing                          -> setError "Unbound name" $> nullPtr

dexToCAtom :: Ptr Atom -> Ptr CAtom -> IO CInt
dexToCAtom atomPtr resultPtr = do
  atom <- fromStablePtr atomPtr
  case atom of
    Con con -> case con of
      Lit (VecLit _) -> notSerializable
      Lit l          -> poke resultPtr (CLit l) $> 1
      _ -> notSerializable
    _ -> notSerializable
  where
    notSerializable = setError "Unserializable atom" $> 0

dexFreeCAtom :: Ptr CAtom -> IO ()
dexFreeCAtom = free

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
        VecLit     _ -> error "Unsupported"
        PtrLit _ _   -> error "Unsupported"
    CRectArray _ _ _ -> error "Unsupported"
    where
      val :: forall a. Storable a => Int -> a -> IO ()
      val i v = pokeByteOff (castPtr addr) (i * 8) v

fromStablePtr :: Ptr a -> IO a
fromStablePtr = deRefStablePtr . castPtrToStablePtr . castPtr

toStablePtr :: a -> IO (Ptr a)
toStablePtr x = castPtr . castStablePtrToPtr <$> newStablePtr x
