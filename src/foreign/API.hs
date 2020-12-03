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

import Data.String
import Data.Word

import Resources
import Syntax  hiding (sizeOf)
import Type
import TopLevel
import Parser (parseExpr, exprAsModule)
import Serialize (pprintVal)
import Env hiding (Tag)

foreign export ccall "dexCreateContext"  dexCreateContext  :: IO (Ptr ())
foreign export ccall "dexDestroyContext" dexDestroyContext :: Ptr () -> IO ()
foreign export ccall "dexPrint"    dexPrint    :: Ptr Atom    -> IO CString
foreign export ccall "dexInsert"   dexInsert   :: Ptr Context -> CString -> Ptr Atom -> IO (Ptr Context)
foreign export ccall "dexEval"     dexEval     :: Ptr Context -> CString -> IO (Ptr Context)
foreign export ccall "dexEvalExpr" dexEvalExpr :: Ptr Context -> CString -> IO (Ptr (WithErr APIErr (Ptr Atom)))
foreign export ccall "dexLookup"   dexLookup   :: Ptr Context -> CString -> IO (Ptr (WithErr APIErr (Ptr Atom)))
foreign export ccall "dexToCAtom"  dexToCAtom  :: Ptr Atom               -> IO (Ptr (WithErr APIErr CAtom))

data Context = Context EvalConfig TopEnv

dexCreateContext :: IO (Ptr ())
dexCreateContext = do
    let evalConfig = EvalConfig LLVM Nothing
    maybePreludeEnv <- evalPrelude evalConfig preludeSource
    case maybePreludeEnv of
      Right preludeEnv -> castStablePtrToPtr <$> newStablePtr (Context evalConfig preludeEnv)
      Left  _          -> return nullPtr
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

dexDestroyContext :: Ptr () -> IO ()
dexDestroyContext = freeStablePtr . castPtrToStablePtr @Context

dexPrint :: Ptr Atom -> IO CString
dexPrint atomPtr = do
  newCString =<< pprintVal =<< fromStablePtr atomPtr

dexEval :: Ptr Context -> CString -> IO (Ptr Context)
dexEval ctxPtr sourcePtr = do
  Context evalConfig env <- fromStablePtr ctxPtr
  source <- peekCString sourcePtr
  finalEnv <- execStateT (evalSource evalConfig source) env
  -- TODO: This ignores errors!
  toStablePtr $ Context evalConfig finalEnv

dexInsert :: Ptr Context -> CString -> Ptr Atom -> IO (Ptr Context)
dexInsert ctxPtr namePtr atomPtr = do
  Context evalConfig env <- fromStablePtr ctxPtr
  name <- GlobalName . fromString <$> peekCString namePtr
  atom <- fromStablePtr atomPtr
  let env' = env <> name @> (getType atom, LetBound PlainLet (Atom atom))
  toStablePtr $ Context evalConfig env'

dexEvalExpr :: Ptr Context -> CString -> IO (Ptr (WithErr APIErr (Ptr Atom)))
dexEvalExpr ctxPtr sourcePtr = do
  Context evalConfig env <- fromStablePtr ctxPtr
  maybeExpr <- parseExpr <$> peekCString sourcePtr
  case maybeExpr of
    Just expr -> do
      let (v, m) = exprAsModule expr
      (resultEnv, _) <- evalSourceBlock evalConfig env $ SourceBlock 0 0 LogNothing "" (RunModule m) Nothing
      let (_, LetBound _ (Atom atom)) = resultEnv ! v
      atomPtr <- castPtr . castStablePtrToPtr <$> newStablePtr atom
      packSuccess atomPtr
    _ -> packErr EInvalidExpr

dexLookup :: Ptr Context -> CString -> IO (Ptr (WithErr APIErr (Ptr Atom)))
dexLookup ctxPtr namePtr = do
  Context _ env <- deRefStablePtr $ castPtrToStablePtr $ castPtr ctxPtr
  name <- peekCString namePtr
  case envLookup env (GlobalName $ fromString name) of
    Just (_, LetBound _ (Atom atom)) -> do
      atomPtr <- castPtr . castStablePtrToPtr <$> newStablePtr atom
      packSuccess atomPtr
    Just _                          -> packErr EUnsupported
    Nothing                         -> packErr ENotFound

dexToCAtom :: Ptr Atom -> IO (Ptr (WithErr APIErr CAtom))
dexToCAtom atomPtr = packAtom =<< fromStablePtr atomPtr

packAtom :: Atom -> IO (Ptr (WithErr APIErr CAtom))
packAtom atom = case atom of
  Con con -> case con of
    Lit (VecLit _) -> notSerializable
    Lit l          -> packSuccess $ CLit l
    _ -> notSerializable
  _ -> notSerializable
  where
    notSerializable = packErr EUnsupported

unpackAtom :: CAtom -> Atom
unpackAtom catom = case catom of
  CLit l           -> Con $ Lit l
  CRectArray _ _ _ -> error "Unsupported"

data CAtom = CLit LitVal | CRectArray (Ptr ()) [Int] [Int]

data WithErr err val = Fail err | Success val
data APIErr = ENotFound | EUnsupported | EInvalidExpr deriving (Enum)

packErr :: (Storable err, Storable val) => err -> IO (Ptr (WithErr err val))
packErr = putOnHeap . Fail

packSuccess :: (Storable err, Storable val) => val -> IO (Ptr (WithErr err val))
packSuccess = putOnHeap . Success

bitcastWord :: Storable a => a -> IO Word64
bitcastWord x = do
  unless (sizeOf    x <= sizeOf    (undefined :: Word64)) $ error "Payload too large"
  unless (alignment x >= alignment (undefined :: Word64)) $ error "Payload requires stricter alignment"
  alloca $ \ref -> do
    poke ref 0
    poke (castPtr ref) x
    peek ref

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
                   2 -> Int8Lit    <$> val 2
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
        Int8Lit    v -> val @Word64 1 2 >> val 2 v
        Float64Lit v -> val @Word64 1 3 >> val 2 v
        Float32Lit v -> val @Word64 1 4 >> val 2 v
        VecLit     _ -> error "Unsupported"
        PtrLit _ _   -> error "Unsupported"
    CRectArray _ _ _ -> error "Unsupported"
    where
      val :: forall a. Storable a => Int -> a -> IO ()
      val i v = pokeByteOff (castPtr addr) (i * 8) v

instance Storable APIErr where
  sizeOf    _ = sizeOf    (undefined :: Word64)
  alignment _ = alignment (undefined :: Word64)
  peek addr   = toEnum @APIErr . fromIntegral <$> peek (castPtr @_ @Word64 addr)
  poke addr x = poke (castPtr @_ @Word64 addr) $ fromIntegral $ fromEnum x

instance (Storable err, Storable val) => Storable (WithErr err val) where
  -- TODO: Assert that alignment of err and val is not more than 8
  sizeOf    _ = 8 + max (sizeOf (undefined :: err)) (sizeOf (undefined :: val))
  alignment _ = 8
  peek ptr    = do
    tag <- peek (castPtr @_ @Word64 ptr)
    let payloadPtr = plusPtr ptr 8
    case tag of
      0 -> Fail    <$> peek (castPtr payloadPtr)
      1 -> Success <$> peek (castPtr payloadPtr)
      _ -> error    $  "Unexpected tag value: " ++ show tag
  poke ptr x  = do
    let tagPtr = castPtr @_ @Word64 ptr
    let payloadPtr = plusPtr ptr 8
    case x of
      Fail err    -> poke tagPtr 0 >> poke payloadPtr err
      Success val -> poke tagPtr 1 >> poke payloadPtr val

putOnHeap :: Storable a => a -> IO (Ptr a)
putOnHeap x = do
  addr <- calloc
  poke addr x
  return addr

fromStablePtr :: Ptr a -> IO a
fromStablePtr = deRefStablePtr . castPtrToStablePtr . castPtr

toStablePtr :: a -> IO (Ptr a)
toStablePtr x = castPtr . castStablePtrToPtr <$> newStablePtr x
