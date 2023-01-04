-- Copyright 2023 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module RuntimePrint (showAny) where

import Control.Monad.Reader
import Builder
import Core
import Err
import IRVariants
import MTL1
import Name
import Types.Core
import Types.Source
import Types.Primitives
import QueryType

newtype Printer (n::S) (a :: *) = Printer { runPrinter' :: ReaderT1 (Atom CoreIR) (BuilderM CoreIR) n a }
        deriving ( Functor, Applicative, Monad, EnvReader, MonadReader (Atom CoreIR n)
                 , Fallible, ScopeReader, MonadFail, EnvExtender, Builder CoreIR)

showAny :: EnvReader m => Type CoreIR n -> Atom CoreIR n -> m n (Block CoreIR n)
showAny ty x = liftPrinter $ showAnyRec (sink x) (sink ty)

liftPrinter
  :: EnvReader m
  => (forall l. (DExt n l, Emits l) => Printer l ())
  -> m n (CBlock n)
liftPrinter cont = liftBuilder $ buildBlock $ withBuffer \buf ->
  runReaderT1 buf (runPrinter' cont)

getBuffer :: Printer n (CAtom n)
getBuffer = ask

emitCharTab :: Emits n => CAtom n -> Printer n ()
emitCharTab tab = do
  buf <- getBuffer
  extendBuffer buf tab

emitLit :: Emits n => String -> Printer n ()
emitLit s = stringLitAsCharTab s >>= emitCharTab

showAnyRec :: Emits n => CAtom n -> CType n -> Printer n ()
showAnyRec _ = \case
  _ -> emitLit "TESTING"

-- === Builder helpers (consider moving these to Builder.hs) ===

withBuffer
  :: (Emits n, IsCore r)
  => (forall l . (Emits l, DExt n l) => Atom r l -> BuilderM r l ())
  -> BuilderM r n (Atom r n)
withBuffer cont = do
  lam <- withFreshBinder "h" (TC HeapType) \h -> do
    bufTy <- bufferTy (Var $ binderName h)
    withFreshBinder "buf" bufTy \b -> do
      let eff = OneEffect (RWSEffect State (Just $ sink $ binderName h))
      body <- withAllowedEffects eff $ buildBlock do
        cont $ sink $ Var $ binderName b
        return UnitVal
      let hB   = h :> TC HeapType
      let bufB = b :> bufTy
      let eff1 = Abs hB   Pure
      let eff2 = Abs bufB eff
      return $
        Lam (UnaryLamExpr hB
              (AtomicBlock (Lam (UnaryLamExpr bufB body) PlainArrow eff2)))
            ImplicitArrow eff1
  applyPreludeFunction "with_stack_internal" [lam]

bufferTy :: EnvReader m => Atom r n -> m n (Type r n)
bufferTy h = do
  t <- strType
  return $ RefTy h (PairTy NatTy t)

-- argument has type `Fin n => Char`
extendBuffer :: (Emits n, Builder r m) => Atom r n -> Atom r n -> m n ()
extendBuffer buf tab = do
  TC (RefType (Just h) _) <- getType buf
  TabTy (_:>IxType (FinTy n) _) _ <- getType tab
  void $ applyPreludeFunction "stack_extend_internal" [n, h, buf, tab]

stringLitAsCharTab :: (Emits n, Builder r m) => String -> m n (Atom r n)
stringLitAsCharTab s = do
  t <- finTabType (NatVal (fromIntegral $ length s)) CharRepTy
  emitExpr $ TabCon t (map charRepVal s)

getPreludeFunction :: EnvReader m => String -> m n (Atom r n)
getPreludeFunction sourceName = do
  lookupSourceMap sourceName >>= \case
    Just uvar -> case uvar of
      UAtomVar v -> return $ Var v
      _ -> notfound
    Nothing -> notfound
 where notfound = error $ "Function not defined: " ++ sourceName

applyPreludeFunction :: (Emits n, Builder r m) => String -> [Atom r n] -> m n (Atom r n)
applyPreludeFunction name args = do
  f <- getPreludeFunction name
  naryApp f args
