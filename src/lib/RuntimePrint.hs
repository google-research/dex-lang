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
import Types.Core
import Types.Source
import Types.Primitives
import QueryType

newtype Printer (n::S) (a :: *) = Printer { runPrinter' :: ReaderT1 (Atom CoreIR) (BuilderM CoreIR) n a }
        deriving ( Functor, Applicative, Monad, EnvReader, MonadReader (Atom CoreIR n)
                 , Fallible, ScopeReader, MonadFail, EnvExtender, Builder CoreIR, ScopableBuilder CoreIR)
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

emitLit :: Emits n => String -> Print n
emitLit s = stringLitAsCharTab s >>= emitCharTab

showAnyRec :: Emits n => CAtom n -> Print n
showAnyRec atom = getType atom >>= \case
  TC (BaseType (Scalar _)) -> do
    (n, tab) <- fromPair =<< emitExpr (PrimOp $ MiscOp $ ShowScalar atom)
    let n' = Con (Newtype NatTy n)
    logicalTabTy <- finTabType n' CharRepTy
    tab' <- emitExpr $ PrimOp $ MiscOp $ UnsafeCoerce logicalTabTy tab
    emitCharTab tab'
  TC (ProdType _) -> do
    xs <- getUnpacked atom
    parens $ sepBy ", " $ map rec xs
  TabTy _ _ -> brackets $ forEachTabElt atom \x -> do
    rec x
    emitLit ", " -- TODO: don't emit the ", " after the final element
  TypeCon _ defName params -> do
    def <- lookupDataDef defName
    cons <- instantiateDataDef def params
    void $ buildCase atom UnitTy \i arg -> do
      let DataConDef sn _ projss = cons !! i
      case projss of
        [] -> emitLit sn
        _ -> parens do
          emitLit (sn ++ " ")
          sepBy " " $ projss <&> \projs ->
            -- we use `init` to strip off the `UnwrapCompoundNewtype` since
            -- we're already under the case alternative
            rec =<< normalizeNaryProj (init projs) arg
      return UnitVal
  ty -> emitLit $ "<value of type: " <> pprint ty <> ">"
  where
    rec :: Emits n => CAtom n -> Print n
    rec = showAnyRec

parens :: Emits n => Print n -> Print n
parens x = emitLit "(" >> x >> emitLit ")"

brackets :: Emits n => Print n -> Print n
brackets x = emitLit "[" >> x >> emitLit "]"

sepBy :: forall n. Emits n => String -> [Print n] -> Print n
sepBy s xsTop = rec xsTop where
  rec :: [Print n] -> Print n
  rec = \case
    []   -> return ()
    [x]  -> x
    x:xs -> x >> emitLit s >> rec xs

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

forEachTabElt
  :: (Emits n, ScopableBuilder r m)
  => Atom r n
  -> (forall l. (Emits l, DExt n l) => Atom r l -> m l ())
  -> m n ()
forEachTabElt tab cont = do
  TabTy (_:>ixTy) _ <- getType tab
  void $ buildFor "i" Fwd ixTy \i -> do
    cont =<< tabApp (sink tab) (Var i)
    return $ UnitVal
