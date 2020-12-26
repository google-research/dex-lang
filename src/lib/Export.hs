-- Copyright 2020 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RecordWildCards #-}

module Export (
    exportFunctions, prepareFunctionForExport, exportedSignatureDesc,
    ExportedSignature (..), ExportArrayType (..), ExportArg (..), ExportResult (..),
  ) where

import Control.Monad.State.Strict
import Control.Monad.Writer hiding (pass)
import qualified Data.Text as T
import Data.String
import Data.Foldable
import Data.List (nub, intercalate)

import Algebra
import Syntax
import Embed
import Cat
import Env
import Type
import Simplify
import Imp
import JIT
import Logging
import LLVMExec
import PPrint
import Optimize

exportFunctions :: FilePath -> [(String, Atom)] -> TopEnv -> IO ()
exportFunctions objPath funcs env = do
  let names = fmap fst funcs
  unless (length (nub names) == length names) $ liftEitherIO $
    throw CompilerErr "Duplicate export names"
  modules <- forM funcs $ \(name, funcAtom) -> do
    let (impModule, _) = prepareFunctionForExport env name funcAtom
    (,[name]) <$> execLogger Nothing (flip impToLLVM impModule)
  exportObjectFile objPath modules


type CArgList = [IBinder] -- ^ List of arguments to the C call
data CArgEnv = CArgEnv { -- | Maps scalar atom binders to their CArgs. All atoms are Vars.
                         cargScalarScope :: Env Atom
                         -- | Tracks the CArg names used so far (globally scoped, unlike Embed)
                       , cargScope :: Env () }
type CArgM = WriterT CArgList (CatT CArgEnv Embed)

instance Semigroup CArgEnv where
  (CArgEnv a1 a2) <> (CArgEnv b1 b2) = CArgEnv (a1 <> b1) (a2 <> b2)

instance Monoid CArgEnv where
  mempty = CArgEnv mempty mempty

runCArg :: CArgEnv -> CArgM a -> Embed (a, [IBinder], CArgEnv)
runCArg initEnv m = repack <$> runCatT (runWriterT m) initEnv
  where repack ((ans, cargs), env) = (ans, cargs, env)

prepareFunctionForExport :: TopEnv -> String -> Atom -> (ImpModule, ExportedSignature)
prepareFunctionForExport env nameStr func = do
  -- Create a module that simulates an application of arguments to the function
  -- TODO: Assert that the type of func is closed?
  let ((dest, cargs, apiDesc), (_, decls)) = flip runEmbed (freeVars func) $ do
        (args, cargArgs, cargEnv) <- runCArg mempty $ createArgs $ getType func
        let (atomArgs, exportedArgSig) = unzip args
        resultAtom <- naryApp func atomArgs
        void $ emitTo outputName PlainLet $ Atom resultAtom
        ((resultDest, exportedResSig), cdestArgs, _) <- runCArg cargEnv $ createDest mempty $ getType resultAtom
        let cargs' = cargArgs <> cdestArgs
        let exportedCCallSig = fmap (\(Bind (v:>_)) -> v) cargs'
        return (resultDest, cargs', ExportedSignature{..})

  let coreModule = Module Core decls mempty
  let defunctionalized = simplifyModule env coreModule
  let Module _ optDecls optBindings = optimizeModule defunctionalized
  let (_, LetBound PlainLet outputExpr) = optBindings ! outputName
  let block = Block optDecls outputExpr

  let name = Name TopFunctionName (fromString nameStr) 0
  let (_, impModule, _) = toImpModule env LLVM CEntryFun name cargs (Just dest) block
  (impModule, apiDesc)
  where
    outputName = GlobalName "_ans_"

    createArgs :: Type -> CArgM [(Atom, ExportArg)]
    createArgs ty = case ty of
      PiTy b arrow result | arrow /= TabArrow -> do
        argSubst <- looks cargScalarScope
        let visibility = case arrow of
              PlainArrow Pure -> ExplicitArg
              PlainArrow _    -> error $ "Effectful functions cannot be exported"
              ImplicitArrow   -> ImplicitArg
              _               -> error $ "Unexpected type for an exported function: " ++ pprint ty
        (:) <$> createArg visibility (subst (argSubst, mempty) b) <*> createArgs result
      _ -> return []

    createArg :: ArgVisibility -> Binder -> CArgM (Atom, ExportArg)
    createArg vis b = case ty of
      BaseTy bt@(Scalar sbt) -> do
        ~v@(Var (name:>_)) <- newCVar bt
        extend $ mempty { cargScalarScope = b @> (Var $ name :> BaseTy bt) }
        return (v, ExportScalarArg vis name sbt)
      TabTy _ _ -> createTabArg vis mempty ty
      _ -> error $ "Unsupported arg type: " ++ pprint ty
      where ty = binderType b

    createTabArg :: ArgVisibility -> IndexStructure -> Type -> CArgM (Atom, ExportArg)
    createTabArg vis idx ty = case ty of
      BaseTy bt@(Scalar sbt) -> do
        ~v@(Var (name:>_)) <- newCVar (ptrTy bt)
        destAtom <- ptrLoad =<< applyIdxs v idx
        funcArgScope <- looks cargScope
        let exportArg = ExportArrayArg vis name $ case getRectShape funcArgScope idx of
              Just rectShape -> RectContArrayPtr sbt rectShape
              Nothing        -> GeneralArrayPtr  sbt
        return (destAtom, exportArg)
      TabTy b elemTy -> do
        buildLamAux b (const $ return TabArrow) $ \(Var i) -> do
          elemTy' <- substEmbed (b@>Var i) elemTy
          createTabArg vis (idx <> Nest (Bind i) Empty) elemTy'
      _ -> unsupported
      where unsupported = error $ "Unsupported table type suffix: " ++ pprint ty

    createDest :: IndexStructure -> Type -> CArgM (Atom, ExportResult)
    createDest idx ty = case ty of
      BaseTy bt@(Scalar sbt) -> do
        ~v@(Var (name:>_)) <- newCVar (ptrTy bt)
        dest <- Con . BaseTypeRef <$> applyIdxs v idx
        funcArgScope <- looks cargScope
        let exportResult = case idx of
              Empty -> ExportScalarResultPtr name sbt
              _     -> ExportArrayResult name $ case getRectShape funcArgScope idx of
                Just rectShape -> RectContArrayPtr sbt rectShape
                Nothing        -> GeneralArrayPtr  sbt
        return (dest, exportResult)
      TabTy b elemTy -> do
        (destTab, exportResult) <- buildLamAux b (const $ return TabArrow) $ \(Var i) -> do
          elemTy' <- substEmbed (b@>Var i) elemTy
          createDest (idx <> Nest (Bind i) Empty) elemTy'
        return (Con $ TabRef destTab, exportResult)
      _ -> unsupported
      where unsupported = error $ "Unsupported result type: " ++ pprint ty

    -- TODO: I guess that the address space depends on the backend?
    -- TODO: Have an ExternalPtr tag?
    ptrTy ty = PtrType (Heap CPU, ty)

    getRectShape :: Env () -> IndexStructure -> Maybe [Either Name Int]
    getRectShape scope idx = traverse (dimShape . binderType) $ toList idx
      where
        dimShape dimTy = case dimTy of
          Fin (IdxRepVal n)                  -> Just $ Right $ fromIntegral n
          Fin (Var v)       | v `isin` scope -> Just $ Left  $ varName v
          _                                  -> Nothing

    newCVar :: BaseType -> CArgM Atom
    newCVar bt = do
      name <- genFresh (Name CArgName "arg" 0) <$> looks cargScope
      extend $ mempty { cargScope = name @> () }
      tell [Bind $ name :> bt]
      return $ Var $ name :> BaseTy bt

-- === Exported function signature ===

data ExportArrayType = GeneralArrayPtr  ScalarBaseType
                     | RectContArrayPtr ScalarBaseType [Either Name Int]
data ArgVisibility = ImplicitArg | ExplicitArg
data ExportArg = ExportArrayArg  ArgVisibility Name ExportArrayType
               | ExportScalarArg ArgVisibility Name ScalarBaseType
data ExportResult = ExportArrayResult     Name ExportArrayType
                  | ExportScalarResultPtr Name ScalarBaseType
data ExportedSignature =
  ExportedSignature { exportedArgSig   :: [ExportArg]
                    , exportedResSig   :: ExportResult
                    , exportedCCallSig :: [Name]
                    }

-- Serialization

exportedSignatureDesc :: ExportedSignature -> (String, String, String)
exportedSignatureDesc ExportedSignature{..} =
  ( intercalate "," $ fmap show exportedArgSig
  , show exportedResSig
  , intercalate "," $ fmap showCArgName exportedCCallSig
  )

showExportSBT :: ScalarBaseType -> String
showExportSBT sbt = case sbt of
  Int64Type   -> "i64"
  Int32Type   -> "i32"
  Word8Type   -> "u8"
  Float64Type -> "f64"
  Float32Type -> "f32"

showCArgName :: Name -> String
showCArgName ~name@(Name namespace tag idx) = case namespace of
  CArgName -> T.unpack tag <> show idx
  _        -> error $ "Expected a CArgName namespace: " ++ show name

instance Show ExportArrayType where
  show arr = case arr of
    GeneralArrayPtr  sbt       -> showExportSBT sbt <> "[?]"
    RectContArrayPtr sbt shape -> showExportSBT sbt <> showShape shape
    where
      showShape shape = "[" <> (intercalate "," $ fmap showDim shape) <> "]"
      showDim size = case size of
        Left  name -> showCArgName name
        Right lit  -> show lit

instance Show ExportArg where
  show arg = case arg of
    ExportArrayArg  vis name ty  -> showVis vis <> showCArgName name <> ":" <> show ty
    ExportScalarArg vis name sbt -> showVis vis <> showCArgName name <> ":" <> showExportSBT sbt
    where
      showVis ImplicitArg = "?"
      showVis ExplicitArg = ""

instance Show ExportResult where
  show res = case res of
    ExportArrayResult     name ty  -> showCArgName name <> ":" <> show ty
    ExportScalarResultPtr name sbt -> showCArgName name <> ":" <> showExportSBT sbt
