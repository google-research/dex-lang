-- Copyright 2023 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module RuntimePrint (showAny) where

import Control.Monad.Reader
import Data.Functor

import Builder
import Core
import Err
import IRVariants
import MTL1
import Name
import CheapReduction
import PPrint
import Types.Core
import Types.Source
import Types.Primitives
import QueryType
import Util (enumerate)

newtype Printer (n::S) (a :: *) = Printer { runPrinter' :: ReaderT1 (Atom CoreIR) (BuilderM CoreIR) n a }
        deriving ( Functor, Applicative, Monad, EnvReader, MonadReader (Atom CoreIR n)
                 , Fallible, ScopeReader, MonadFail, EnvExtender, CBuilder, ScopableBuilder CoreIR)
type Print n = Printer n ()

showAny :: EnvReader m => Atom CoreIR n -> m n (CExpr n)
showAny x = liftPrinter $ showAnyRec (sink x)

liftPrinter
  :: EnvReader m
  => (forall l. (DExt n l, Emits l) => Print l)
  -> m n (CExpr n)
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
showAnyRec atom = case getType atom of
  TyCon con -> showAnyTyCon con atom
  StuckTy _ e -> error $ "unexpected stuck type expression: " ++ pprint e

showAnyTyCon :: forall n. Emits n => TyCon CoreIR n -> CAtom n -> Print n
showAnyTyCon tyCon atom = case tyCon of
  BaseType bt -> case bt of
    Vector _ _ -> error "not implemented"
    PtrType _  -> printTypeOnly "pointer"
    Scalar _ -> do
      (n, tab) <- fromPair =<< emit (ShowScalar atom)
      logicalTabTy <- finTabTyCore (Con $ NewtypeCon NatCon n) CharRepTy
      tab' <- emit $ UnsafeCoerce logicalTabTy tab
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
    isFirst <- emit $ BinOp (ICmp Equal) iOrd (NatVal 0)
    void $ emitIf isFirst UnitTy (return UnitVal) (emitLit ", " >> return UnitVal)
    rec x
  NewtypeTyCon tc -> case tc of
    Fin _ -> rec =<< unwrapNewtype atom
    Nat -> do
      n <- unwrapNewtype atom
      -- Cast to Int so that it prints in decimal instead of hex
      let intTy = toType $ BaseType (Scalar Int64Type)
      emit (CastOp intTy n) >>= rec
    EffectRowKind    -> printAsConstant
    -- hack to print strings nicely. TODO: make `Char` a newtype
    UserADTType "List" _ (TyConParams [Explicit] [Con (TyConAtom (BaseType (Scalar (Word8Type))))]) -> do
      charTab <- applyProjections [ProjectProduct 1, UnwrapNewtype] atom
      emitCharLit '"'
      emitCharTab charTab
      emitCharLit '"'
    UserADTType tySourceName defName params -> do
      def <- lookupTyCon defName
      conDefs <- instantiateTyConDef def params
      case conDefs of
        ADTCons [con] -> showDataCon con =<< unwrapNewtype atom
        ADTCons cons -> void $ buildCase atom UnitTy \i arg -> do
          showDataCon (sink $ cons !! i) arg
          return UnitVal
        StructFields fields -> do
          emitLit $ pprint tySourceName
          parens do
            sepBy ", " $ (enumerate fields) <&> \(i, _) ->
              rec =<< projectStruct i atom
      where
        showDataCon :: Emits n' => DataConDef n' -> CAtom n' -> Print n'
        showDataCon (DataConDef sn _ _ projss) arg = do
          case projss of
            [] -> emitLit $ pprint sn
            _ -> parens do
              emitLit (pprint sn ++ " ")
              sepBy " " $ projss <&> \projs ->
                -- we use `init` to strip off the `UnwrapCompoundNewtype` since
                -- we're already under the case alternative
                rec =<< applyProjections (init projs) arg
  DepPairTy _ -> parens do
    (x, y) <- fromPair atom
    rec x >> emitLit " ,> " >> rec y
  -- Done well, this could let you inspect the results of dictionary synthesis
  -- and maybe even debug synthesis failures.
  DictTy _ -> printAsConstant
  where
    rec :: Emits n' => CAtom n' -> Print n'
    rec = showAnyRec

    printTypeOnly :: String -> Print n
    printTypeOnly thingName = do
      ty <- return $ getType atom
      emitLit $ "<" <> thingName <> " of type " <> pprint ty <> ">"

    printAsConstant :: Print n
    printAsConstant = emitLit $ pprint atom

parens :: Emits n => Print n -> Print n
parens x = emitCharLit '(' >> x >> emitCharLit ')'

brackets :: Emits n => Print n -> Print n
brackets x = emitCharLit '[' >> x >> emitCharLit ']'

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
  lam <- withFreshBinder "h" (TyCon HeapType) \h -> do
    bufTy <- bufferTy (toAtom $ binderVar h)
    withFreshBinder "buf" bufTy \b -> do
      let eff = OneEffect (RWSEffect State (toAtom $ sink $ binderVar h))
      body <- buildBlock do
        cont $ sink $ toAtom $ binderVar b
        return UnitVal
      let binders = BinaryNest h b
      let expls = [Inferred Nothing Unify, Explicit]
      let piTy = CorePiType ExplicitApp expls binders $ EffTy eff UnitTy
      let lam = LamExpr (BinaryNest h b) body
      return $ toAtom $ CoreLamExpr piTy lam
  applyPreludeFunction "with_stack_internal" [lam]

bufferTy :: EnvReader m => CAtom n -> m n (CType n)
bufferTy h = do
  t <- strType
  return $ RefTy h (PairTy NatTy t)

-- argument has type `Fin n => Word8`
extendBuffer :: (Emits n, CBuilder m) => CAtom n -> CAtom n -> m n ()
extendBuffer buf tab = do
  RefTy h _ <- return $ getType buf
  TyCon (TabPi t) <- return $ getType tab
  n <- applyIxMethodCore Size (tabIxType t) []
  void $ applyPreludeFunction "stack_extend_internal" [n, h, buf, tab]

-- argument has type `Word8`
pushBuffer :: (Emits n, CBuilder m) => CAtom n -> CAtom n -> m n ()
pushBuffer buf x = do
  RefTy h _ <- return $ getType buf
  void $ applyPreludeFunction "stack_push_internal" [h, buf, x]

stringLitAsCharTab :: (Emits n, CBuilder m) => String -> m n (CAtom n)
stringLitAsCharTab s = do
  t <- finTabTyCore (NatVal $ fromIntegral $ length s) CharRepTy
  emit $ TabCon Nothing t (map charRepVal s)

finTabTyCore :: (Fallible1 m, EnvReader m) => CAtom n -> CType n -> m n (CType n)
finTabTyCore n eltTy = return $ IxType (FinTy n) (DictCon $ IxFin n) ==> eltTy

getPreludeFunction :: EnvReader m => SourceName -> m n (CAtom n)
getPreludeFunction sourceName = do
  lookupSourceMap sourceName >>= \case
    Just uvar -> case uvar of
      UAtomVar v -> toAtom <$> toAtomVar v
      _ -> notfound
    Nothing -> notfound
 where notfound = error $ "Function not defined: " ++ pprint sourceName

applyPreludeFunction :: (Emits n, CBuilder m) => SourceName -> [CAtom n] -> m n (CAtom n)
applyPreludeFunction name args = do
  f <- getPreludeFunction name
  naryApp f args

strType :: forall n m. EnvReader m => m n (CType n)
strType = constructPreludeType "List" $ TyConParams [Explicit] [toAtom (CharRepTy :: CType n)]

constructPreludeType :: EnvReader m => SourceName -> TyConParams n -> m n (CType n)
constructPreludeType sourceName params = do
  lookupSourceMap sourceName >>= \case
    Just uvar -> case uvar of
      UTyConVar v -> return $ toType $ UserADTType sourceName v params
      _ -> notfound
    Nothing -> notfound
 where notfound = error $ "Type constructor not defined: " ++ pprint sourceName

forEachTabElt
  :: (Emits n, ScopableBuilder CoreIR m)
  => CAtom n
  -> (forall l. (Emits l, DExt n l) => CAtom l -> CAtom l -> m l ())
  -> m n ()
forEachTabElt tab cont = do
  TyCon (TabPi t) <- return $ getType tab
  let ixTy = tabIxType t
  void $ buildFor "i" Fwd ixTy \i -> do
    x <- tabApp (sink tab) (toAtom i)
    i' <- applyIxMethodCore Ordinal (sink ixTy) [toAtom i]
    cont i' x
    return $ UnitVal
