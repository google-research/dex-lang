-- Copyright 2023 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module RuntimePrint (showAny) where

import Control.Monad.Reader
import Data.Foldable (fold, toList)
import Data.Functor
import qualified Data.Map.Strict as M

import Builder
import Core
import Err
import IRVariants
import MTL1
import LabeledItems
import Name
import CheapReduction
import Types.Core
import Types.Source
import Types.Primitives
import QueryType
import Util (restructure)

newtype Printer (n::S) (a :: *) = Printer { runPrinter' :: ReaderT1 (Atom CoreIR) (BuilderM CoreIR) n a }
        deriving ( Functor, Applicative, Monad, EnvReader, MonadReader (Atom CoreIR n)
                 , Fallible, ScopeReader, MonadFail, EnvExtender, CBuilder, ScopableBuilder CoreIR)
type Print n = Printer n ()

showAny :: EnvReader m => Atom CoreIR n -> m n (Block CoreIR n)
showAny x = liftPrinter $ showAnyRec (sink x)

liftPrinter
  :: EnvReader m
  => (forall l. (DExt n l, Emits l) => Print l)
  -> m n (CBlock n)
liftPrinter cont = liftBuilder $ buildBlock $ withBuffer \buf ->
  runReaderT1 buf (runPrinter' cont)

getBuffer :: Printer n (CAtom n)
getBuffer = ask

emitCharTab :: Emits n => CAtom n -> Print n
emitCharTab tab = do
  buf <- getBuffer
  extendBuffer buf tab

emitChar :: Emits n => CAtom n -> Print n
emitChar tab = do
  buf <- getBuffer
  pushBuffer buf tab

emitLit :: Emits n => String -> Print n
emitLit s = stringLitAsCharTab s >>= emitCharTab

emitCharLit :: Emits n => Char -> Print n
emitCharLit c = emitChar $ charRepVal c

showAnyRec :: forall n. Emits n => CAtom n -> Print n
showAnyRec atom = getType atom >>= \atomTy -> case atomTy of
  -- hack to print chars nicely. TODO: make `Char` a newtype
  TC t -> case t of
    BaseType bt -> case bt of
      Vector _ _ -> error "not implemented"
      PtrType _  -> printTypeOnly "pointer"
      Scalar _ -> do
        (n, tab) <- fromPair =<< emitExpr (PrimOp $ MiscOp $ ShowScalar atom)
        logicalTabTy <- finTabTy (NewtypeCon NatCon n) CharRepTy
        tab' <- emitExpr $ PrimOp $ MiscOp $ UnsafeCoerce logicalTabTy tab
        emitCharTab tab'
    -- TODO: we could do better than this but it's not urgent because raw sum types
    -- aren't user-facing.
    SumType _ -> printAsConstant
    RefType _ _ -> printTypeOnly "reference"
    HeapType    -> printAsConstant
    ProdType _ -> do
      xs <- getUnpacked atom
      parens $ sepBy ", " $ map rec xs
    -- TODO: traverse the type and print out data components
    TypeKind -> printAsConstant
  Pi _ -> printTypeOnly "function"
  TabPi _ -> brackets $ forEachTabElt atom \iOrd x -> do
    isFirst <- ieq iOrd (NatVal 0)
    void $ emitIf isFirst UnitTy (return UnitVal) (emitLit ", " >> return UnitVal)
    rec x
  NewtypeTyCon tc -> case tc of
    Fin _ -> rec $ unwrapNewtype atom
    Nat -> do
      let n = unwrapNewtype atom
      -- Cast to Int so that it prints in decimal instead of hex
      let intTy = TC (BaseType (Scalar Int64Type))
      emitExpr (PrimOp $ MiscOp $ CastOp intTy n) >>= rec
    StaticRecordTyCon tys -> do
      xs <- getUnpacked $ unwrapNewtype atom
      let LabeledItems row = restructure xs tys
      braces $ sepBy ", " $ fold $ M.toAscList row <&> \(k, vs) ->
        toList vs <&> \v -> do
          emitLit (pprint k <> " = ")
          rec v
    RecordTyCon _   -> unexpectedPolymorphism
    LabelCon _       -> notAType
    LabelType        -> printAsConstant
    LabeledRowKindTC -> printAsConstant
    LabeledRowCon _  -> notAType
    EffectRowKind    -> printAsConstant
    -- hack to print strings nicely. TODO: make `Char` a newtype
    UserADTType "List" _ (DataDefParams [(PlainArrow, Word8Ty)]) -> do
      charTab <- normalizeNaryProj [ProjectProduct 1, UnwrapNewtype] atom
      emitCharLit '"'
      emitCharTab charTab
      emitCharLit '"'
    UserADTType _ defName params -> do
      def <- lookupDataDef defName
      cons <- instantiateDataDef def params
      case cons of
        [con] -> showDataCon con $ unwrapNewtype atom
        _ -> void $ buildCase atom UnitTy \i arg -> do
          showDataCon (sink $ cons !! i) arg
          return UnitVal
      where
        showDataCon :: Emits n' => DataConDef n' -> CAtom n' -> Print n'
        showDataCon (DataConDef sn _ _ projss) arg = do
          case projss of
            [] -> emitLit sn
            _ -> parens do
              emitLit (sn ++ " ")
              sepBy " " $ projss <&> \projs ->
                -- we use `init` to strip off the `UnwrapCompoundNewtype` since
                -- we're already under the case alternative
                rec =<< normalizeNaryProj (init projs) arg
  DictHole _ _ -> error "shouldn't have DictHole past inference"
  DepPairTy _ -> parens do
    (x, y) <- fromPair atom
    rec x >> emitLit " ,> " >> rec y
  -- Done well, this could let you inspect the results of dictionary synthesis
  -- and maybe even debug synthesis failures.
  DictTy _ -> printAsConstant
  ProjectElt _ _ -> notAType
  Lam _ _ _    -> notAType
  DictCon _    -> notAType
  Con _        -> notAType
  Eff _        -> notAType
  PtrVar _     -> notAType
  DepPair _ _  _ -> notAType
  NewtypeCon _ _ -> notAType
  Var _ -> error $ "unexpected type variable: " ++ pprint atomTy
  SimpInCore _ -> error "Don't expect to print SimpInCore"
  where
    rec :: Emits n' => CAtom n' -> Print n'
    rec = showAnyRec

    printTypeOnly :: String -> Print n
    printTypeOnly thingName = do
      ty <- getType atom
      emitLit $ "<" <> thingName <> " of type " <> pprint ty <> ">"

    printAsConstant :: Print n
    printAsConstant = emitLit $ pprint atom

    notAType :: Print n
    notAType = error $ "Error querying type of: " ++ pprint atom

    unexpectedPolymorphism :: Print n
    unexpectedPolymorphism = do
      emitLit ("Warning: unexpected polymorphism in evaluated term"
              ++ pprint atom)

parens :: Emits n => Print n -> Print n
parens x = emitCharLit '(' >> x >> emitCharLit ')'

brackets :: Emits n => Print n -> Print n
brackets x = emitCharLit '[' >> x >> emitCharLit ']'

braces :: Emits n => Print n -> Print n
braces x = emitCharLit '{' >> x >> emitCharLit '}'

sepBy :: forall n. Emits n => String -> [Print n] -> Print n
sepBy s xsTop = rec xsTop where
  rec :: [Print n] -> Print n
  rec = \case
    []   -> return ()
    [x]  -> x
    x:xs -> x >> emitLit s >> rec xs

-- === Builder helpers (consider moving these to Builder.hs) ===

withBuffer
  :: Emits n
  => (forall l . (Emits l, DExt n l) => CAtom l -> BuilderM CoreIR l ())
  -> BuilderM CoreIR n (CAtom n)
withBuffer cont = do
  lam <- withFreshBinder "h" (TC HeapType) \h -> do
    bufTy <- bufferTy (Var $ binderName h)
    withFreshBinder "buf" bufTy \b -> do
      let eff = OneEffect (RWSEffect State (Var $ sink $ binderName h))
      body <- buildBlock do
        cont $ sink $ Var $ binderName b
        return UnitVal
      let eff1 = Abs h Pure
      let eff2 = Abs b eff
      return $
        Lam (UnaryLamExpr h
              (AtomicBlock (Lam (UnaryLamExpr b body) PlainArrow eff2)))
            ImplicitArrow eff1
  applyPreludeFunction "with_stack_internal" [lam]

bufferTy :: EnvReader m => CAtom n -> m n (CType n)
bufferTy h = do
  t <- strType
  return $ RefTy h (PairTy NatTy t)

-- argument has type `Fin n => Word8`
extendBuffer :: (Emits n, CBuilder m) => CAtom n -> CAtom n -> m n ()
extendBuffer buf tab = do
  RefTy h _ <- getType buf
  TabTy (_:>ixTy) _ <- getType tab
  n <- indexSetSizeCore ixTy
  void $ applyPreludeFunction "stack_extend_internal" [n, h, buf, tab]

-- argument has type `Word8`
pushBuffer :: (Emits n, CBuilder m) => CAtom n -> CAtom n -> m n ()
pushBuffer buf x = do
  RefTy h _ <- getType buf
  void $ applyPreludeFunction "stack_push_internal" [h, buf, x]

stringLitAsCharTab :: (Emits n, CBuilder m) => String -> m n (CAtom n)
stringLitAsCharTab s = do
  t <- finTabTy (NatVal $ fromIntegral $ length s) CharRepTy
  emitExpr $ TabCon Nothing t (map charRepVal s)

getPreludeFunction :: EnvReader m => String -> m n (CAtom n)
getPreludeFunction sourceName = do
  lookupSourceMap sourceName >>= \case
    Just uvar -> case uvar of
      UAtomVar v -> return $ Var v
      _ -> notfound
    Nothing -> notfound
 where notfound = error $ "Function not defined: " ++ sourceName

applyPreludeFunction :: (Emits n, CBuilder m) => String -> [CAtom n] -> m n (CAtom n)
applyPreludeFunction name args = do
  f <- getPreludeFunction name
  naryApp f args

strType :: EnvReader m => m n (CType n)
strType = constructPreludeType "List" $ DataDefParams [(PlainArrow, CharRepTy)]

finTabTy :: EnvReader m => CAtom n -> CType n -> m n (CType n)
finTabTy n eltTy = IxType (FinTy n) (IxDictAtom (DictCon (IxFin n))) ==> eltTy

constructPreludeType :: EnvReader m => String -> DataDefParams n -> m n (CType n)
constructPreludeType sourceName params = do
  lookupSourceMap sourceName >>= \case
    Just uvar -> case uvar of
      UTyConVar v -> lookupEnv v >>= \case
        TyConBinding def _ -> return $ TypeCon sourceName def params
      _ -> notfound
    Nothing -> notfound
 where notfound = error $ "Type constructor not defined: " ++ sourceName

forEachTabElt
  :: (Emits n, ScopableBuilder CoreIR m)
  => CAtom n
  -> (forall l. (Emits l, DExt n l) => CAtom l -> CAtom l -> m l ())
  -> m n ()
forEachTabElt tab cont = do
  TabTy (_:>ixTy) _ <- getType tab
  void $ buildFor "i" Fwd ixTy \i -> do
    x <- tabApp (sink tab) (Var i)
    i' <- ordinalCore (sink ixTy) (Var i)
    cont i' x
    return $ UnitVal
