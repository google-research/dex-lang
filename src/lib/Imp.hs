-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DerivingVia #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Imp (toImpFunction, toMDImpFunction, impExprType) where

import Prelude hiding (pi, abs)
import Control.Monad.Reader
import Control.Monad.Except hiding (Except)
import Control.Monad.State
import Control.Monad.Writer hiding (Alt)
import Data.Text.Prettyprint.Doc
import Data.Foldable (toList)
import Data.Coerce
import qualified Data.List.NonEmpty as NE
import qualified Data.Map.Strict as M

import Embed
import Array
import Syntax
import Env
import Type
import PPrint
import Cat
import qualified Algebra as A
import Util

-- Note [Valid Imp atoms]
--
-- The Imp translation functions as an interpreter for the core IR, which has a side effect
-- of emitting a low-level Imp program that would do the actual math. As an interpreter, each
-- expression has to produce a valid result Atom, that can be used as an input to all later
-- equations. However, because the Imp IR only supports a very limited selection of types
-- (really only base types and pointers to scalar tables), it is safe to assume that only
-- a subset of atoms can be returned by the impSubst. In particular, the atoms might contain
-- only:
--   * Variables of base type or array type
--   * Table lambdas
--   * Constructors for: pairs, sum types, AnyValue, Unit and Coerce
--
-- TODO: Use an ImpAtom type alias to better document the code

-- TODO: use `Env ()` instead of `Scope`. The problem is that we're mixing up
-- Imp and Core types in there.
type EmbedEnv prog = ((Env Dest, [IVar]), (Scope, prog))
type ImpMP prog = Cat (EmbedEnv prog)
type ImpM = ImpMP ImpProgram

toImpFunction :: ([ScalarTableBinder], Block) -> (ImpFunction, Atom)
toImpFunction (vsIn, block) = runImpMPBinders @ImpProgram vsIn $ do
  ((vsOut, atomOut), prog) <- scopedBlock $ materializeResult
  return $ (ImpFunction (fmap toBinder vsOut) vsIn prog, atomOut)
  where
    toBinder = Bind . (\(Var x) -> x) . toArrayAtom . IVar
    materializeResult = do
      outDest <- allocKind Unmanaged $ getType block
      void $ translateBlock mempty (Just outDest, block)
      atomOut <- destToAtomScalarAction (return . toArrayAtom . IVar) outDest
      return (destArrays outDest, atomOut)

toMDImpFunction :: ([ScalarTableBinder], Block) -> (MDImpFunction ImpKernel, Atom)
toMDImpFunction (vsIn, block) = runImpMPBinders @(MDImpProgram ImpKernel) vsIn $ do
  ((vsOut, atomOut), prog) <- scopedBlock $ materializeResult
  return $ (MDImpFunction (fmap toBinder vsOut) vsIn prog, atomOut)
  where
    toBinder = Bind . (\(Var x) -> x) . toArrayAtom . IVar
    materializeResult = do
      outDest <- allocKind Unmanaged $ getType block
      void $ translateBlock mempty (Just outDest, block)
      atomOut <- destToAtomScalarAction (return . toArrayAtom . IVar) outDest
      return (destArrays outDest, atomOut)

runImpMPBinders :: Monoid prog => [ScalarTableBinder] -> ImpMP prog a -> a
runImpMPBinders inBinders m = runImpMP inVarScope m
  where
    inVarScope :: Scope  -- TODO: fix (shouldn't use UnitTy)
    inVarScope = foldMap binderAsEnv $ fmap (fmap $ const (UnitTy, UnknownBinder)) inBinders

runImpMP :: Monoid prog => Scope -> ImpMP prog a -> a
runImpMP inVarScope m = fst $ runCat m (mempty, (inVarScope, mempty))

translateBlock :: MonadImp m instr => SubstEnv -> WithDest Block -> m Atom
translateBlock env destBlock = do
  let (decls, result, copies) = splitDest destBlock
  env' <- (env<>) <$> catFoldM translateDecl env decls
  forM_ copies $ \(dest, atom) -> copyAtom dest =<< impSubst env' atom
  translateExpr env' result

translateDecl :: MonadImp m instr => SubstEnv -> WithDest Decl -> m SubstEnv
translateDecl env (maybeDest, (Let _ b bound)) = do
  b' <- traverse (impSubst env) b
  ans <- translateExpr env (maybeDest, bound)
  return $ b' @> ans
translateDecl env (maybeDest, (Unpack bs bound)) = do
  bs' <- mapM (traverse (impSubst env)) bs
  expr <- translateExpr env (maybeDest, bound)
  case expr of
    DataCon _ _ _ ans -> return $ newEnv bs' ans
    Record items -> return $ newEnv bs $ toList items
    _ -> error "Unsupported type in an Unpack binding"

defaultTranslateExpr :: MonadImp m instr => SubstEnv -> WithDest Expr -> m Atom
defaultTranslateExpr env (maybeDest, expr) = case expr of
  App x' idx' -> case getType x' of
    TabTy _ _ -> do
      x <- impSubst env x'
      idx <- impSubst env idx'
      case x of
        Lam a@(Abs _ (TabArrow, _)) ->
          translateBlock mempty (maybeDest, snd $ applyAbs a idx)
        _ -> error $ "Invalid Imp atom: " ++ pprint x
    _ -> error $ "shouldn't have non-table app left"
  Atom x   -> copyDest maybeDest =<< impSubst env x
  Op   op  -> toImpOp . (maybeDest,) =<< traverse (impSubst env) op
  Hof  hof -> toImpHof env (maybeDest, hof)
  Case e alts _ -> do
    e' <- impSubst env e
    case e' of
      DataCon _ _ con args -> do
        let Abs bs body = alts !! con
        translateBlock (env <> newEnv bs args) (maybeDest, body)
      Variant (NoExt types) label i x -> do
        let LabeledItems ixtypes = enumerate types
        let index = fst $ ixtypes M.! label NE.!! i
        let Abs bs body = alts !! index
        translateBlock (env <> newEnv bs [x]) (maybeDest, body)
      Con (SumAsProd _ tag xss) -> do
        let tag' = fromScalarAtom tag
        dest <- allocDest maybeDest $ getType expr
        emitSwitch tag' $ flip map (zip xss alts) $
          \(xs, Abs bs body) ->
             void $ translateBlock (env <> newEnv bs xs) (Just dest, body)
        destToAtom dest
      _ -> error $ "Unexpected scrutinee: " ++ pprint e'

impSubst :: MonadImp m instr => Subst a => SubstEnv -> a -> m a
impSubst env x = do
  scope <- variableScope
  return $ subst (env, scope) x

toImpOp :: MonadImp m instr => WithDest (PrimOp Atom) -> m Atom
toImpOp (maybeDest, op) = case op of
  TabCon (TabTy b _) rows -> do
    dest <- allocDest maybeDest resultTy
    forM_ (zip [0..] rows) $ \(i, row) -> do
      ithDest <- destGet dest =<< intToIndex (binderType b) (fromScalarAtom $ IdxRepVal i)
      copyAtom ithDest row
    destToAtom dest
  Fst ~(PairVal x _) -> returnVal x
  Snd ~(PairVal _ y) -> returnVal y
  PrimEffect ~(Var refVar) m -> do
    refDest <- getRef refVar
    case m of
      MAsk    -> returnVal =<< destToAtom refDest
      MTell x -> addToAtom  refDest x >> returnVal UnitVal
      MPut x  -> copyAtom   refDest x >> returnVal UnitVal
      MGet -> do
        dest <- allocDest maybeDest resultTy
        -- It might be more efficient to implement a specialized copy for dests
        -- than to go through a general purpose atom.
        copyAtom dest =<< destToAtom refDest
        destToAtom dest
  IntAsIndex n i -> do
    let i' = fromScalarAtom i
    n' <- indexSetSize n
    cond <- emitInstr $ liftInstr $ IPrimOp $ ScalarBinOp (ICmp Less) i' n'
    cond' <- cast cond tagBT
    emitSwitch cond' [emitStatement $ IInstr (IDo, liftInstr $ IThrowError), return ()]
    returnVal =<< intToIndex resultTy i'
    where (BaseTy tagBT) = TagRepTy
  IdxSetSize n -> returnVal . toScalarAtom IdxRepTy =<< indexSetSize n
  IndexAsInt idx -> asInt $ case idx of
      Con (AnyValue t) -> anyValue t
      _                -> idx
    where
      asInt a = case a of
        Con (Coerce (TC (IntRange   _ _  )) i) -> returnVal $ i
        Con (Coerce (TC (IndexRange _ _ _)) i) -> returnVal $ i
        _ -> returnVal . toScalarAtom IdxRepTy =<< indexToInt (getType idx) idx
  Inject e -> do
    let rt@(TC (IndexRange t low _)) = getType e
    offset <- case low of
      InclusiveLim a -> indexToInt t a
      ExclusiveLim a -> indexToInt t a >>= iaddI (fromScalarAtom $ IdxRepVal 1)
      Unlimited      -> return (fromScalarAtom $ IdxRepVal 0)
    restrictIdx <- indexToInt rt e
    idx <- iaddI restrictIdx offset
    returnVal =<< intToIndex t idx
  IndexRef ~(Var refVar@(_:>(RefTy h (Pi a)))) i -> do
    refDest    <- getRef refVar
    subrefDest <- destGet refDest i
    subrefVar  <- freshVar (varName refVar :> RefTy h (snd $ applyAbs a i))
    putRef subrefVar subrefDest
    returnVal $ Var subrefVar
  FstRef ~(Var refVar@(_:>(RefTy h (PairTy a _)))) -> do
    ~(Dest (PairVal ref _)) <- getRef refVar
    subrefVar <- freshVar (varName refVar :> RefTy h a)
    putRef subrefVar $ Dest ref
    returnVal $ Var subrefVar
  SndRef ~(Var refVar@(_:>(RefTy h (PairTy _ b)))) -> do
    ~(Dest (PairVal _ ref)) <- getRef refVar
    subrefVar <- freshVar (varName refVar :> RefTy h b)
    putRef subrefVar $ Dest ref
    returnVal $ Var subrefVar
  ArrayOffset arr idx off -> do
    i <- indexToInt (getType idx) idx
    let (TC (ArrayType t)) = getType arr
    let resTy = tabTypeGet t i
    arrSlice <- impOffset (fromArrayAtom arr) (fromScalarAtom off) resTy
    returnVal $ toArrayAtom arrSlice
  ArrayLoad arr -> returnVal . toScalarAtom resultTy =<< load (fromArrayAtom arr)
  SliceOffset ~(Con (Coerce (TC (IndexSlice n l)) tileOffset)) idx -> do
    i' <- indexToInt l idx
    i <- iaddI (fromScalarAtom tileOffset) i'
    returnVal =<< intToIndex n i
  SliceCurry ~(Con (Coerce (TC (IndexSlice _ (PairTy u v))) tileOffset)) idx -> do
    vz <- intToIndex v $ fromScalarAtom $ IdxRepVal 0
    extraOffset <- indexToInt (PairTy u v) (PairVal idx vz)
    tileOffset' <- iaddI (fromScalarAtom tileOffset) extraOffset
    returnVal $ toScalarAtom resultTy tileOffset'
  ThrowError ty -> do
    emitStatement $ IInstr (IDo, liftInstr $ IThrowError)
    return $ Con $ AnyValue ty
  CastOp destTy x -> case (getType x, destTy) of
    (BaseTy _, BaseTy bt) -> returnVal =<< toScalarAtom destTy <$> cast (fromScalarAtom x) bt
    _ -> error $ "Invalid cast: " ++ pprint (getType x) ++ " -> " ++ pprint destTy
  Select p x y -> do
    dest <- allocDest maybeDest resultTy
    p' <- cast (fromScalarAtom p) tagBT
    emitSwitch p' [copyAtom dest y, copyAtom dest x]
    destToAtom dest
    where (BaseTy tagBT) = TagRepTy
  RecordCons   _ _ -> error "Unreachable: should have simplified away"
  RecordSplit  _ _ -> error "Unreachable: should have simplified away"
  VariantLift  _ _ -> error "Unreachable: should have simplified away"
  VariantSplit _ _ -> error "Unreachable: should have simplified away"
  _ -> do
    returnVal . toScalarAtom resultTy =<< emitInstr (liftInstr $ IPrimOp $ fmap fromScalarAtom op)
  where
    resultTy = getType $ Op op
    returnVal atom = case maybeDest of
      Nothing   -> return atom
      Just dest -> copyAtom dest atom >> return atom

toImpHof :: MonadImp m isntr => SubstEnv -> WithDest Hof -> m Atom
toImpHof env (maybeDest, hof) = do
  resultTy <- impSubst env $ getType $ Hof hof
  case hof of
    For d (LamVal b body) -> do
      idxTy <- impSubst env $ binderType b
      n' <- indexSetSize idxTy
      dest <- allocDest maybeDest resultTy
      emitLoop (binderNameHint b) d n' $ \i -> do
        idx <- intToIndex idxTy i
        ithDest <- destGet dest idx
        void $ translateBlock (env <> b @> idx) (Just ithDest, body)
      destToAtom dest
    Tile d (LamVal tb tBody) (LamVal sb sBody) -> do
      ~tileTy@(TC (IndexSlice idxTy tileIdxTy)) <- impSubst env $ binderType tb
      n <- indexSetSize idxTy
      dest <- allocDest maybeDest resultTy
      tileLen <- indexSetSize tileIdxTy
      nTiles      <- n `idivI` tileLen
      epilogueOff <- nTiles `imulI` tileLen
      nEpilogue   <- n `isubI` epilogueOff
      emitLoop (binderNameHint tb) Fwd nTiles $ \iTile -> do
        tileOffset <- toScalarAtom IdxRepTy <$> iTile `imulI` tileLen
        let tileAtom = Con $ Coerce tileTy tileOffset
        tileDest <- destSliceDim dest d tileOffset tileIdxTy
        void $ translateBlock (env <> tb @> tileAtom) (Just tileDest, tBody)
      emitLoop (binderNameHint sb) Fwd nEpilogue $ \iEpi -> do
        i <- iEpi `iaddI` epilogueOff
        idx <- intToIndex idxTy i
        sDest <- destGetDim dest d idx
        void $ translateBlock (env <> sb @> idx) (Just sDest, sBody)
      destToAtom dest
    While (Lam (Abs _ (_, cond))) (Lam (Abs _ (_, body))) -> do
      (condAtom, cond') <- scopedBlock $ translateBlock env (Nothing, cond)
      (_, body') <- scopedBlock $ void $ translateBlock env (Nothing, body)
      emitStatement $ IWhile (cond', Just $ fromScalarAtom condAtom) body'
      return UnitVal
    RunReader r (BinaryFunVal _ ref _ body) -> do
      rDest <- alloc $ getType r
      rVar  <- freshVar $ fromBind "ref" ref
      copyAtom rDest =<< impSubst env r
      localRef rVar rDest $
        translateBlock (env <> ref @> Var rVar) (maybeDest, body)
    RunWriter (BinaryFunVal _ ref _ body) -> do
      (aDest, wDest) <- destPairUnpack <$> allocDest maybeDest resultTy
      zeroDest $ wDest
      wVar <- freshVar $ fromBind "ref" ref
      void $ localRef wVar wDest $
        translateBlock (env <> ref @> Var wVar) (Just aDest, body)
      PairVal <$> destToAtom aDest <*> destToAtom wDest
    RunState s (BinaryFunVal _ ref _ body) -> do
      (aDest, sDest) <- destPairUnpack <$> allocDest maybeDest resultTy
      copyAtom sDest =<< impSubst env s
      sVar <- freshVar $ fromBind "ref" ref
      void $ localRef sVar sDest $
        translateBlock (env <> ref @> Var sVar) (Just aDest, body)
      PairVal <$> destToAtom aDest <*> destToAtom sDest
    _ -> error $ "Invalid higher order function primitive: " ++ pprint hof
  where
    localRef refVar refDest m = withRefScope $ putRef refVar refDest >> m

-- === Destination type ===
--
-- How is a destination different from a regular table? The fundamental distinction is
-- that destinations can be _written to_, and so just like tables yield scalars when
-- fully indexed, destinations simply yield _memory addresses_!
--
-- Based on that observation, we represent destinations using regular Imp atoms, with the
-- restriction that all atoms that terminate blocks appearing in the dest have to represent
-- dests or arrays. This allows us to nicely separate the logical layout, which is
-- encoded in table lambdas, from the physical layout of the data, which is encoded in the
-- array offset calculations that are based on the logical indices (i.e. lambda binders).
--
-- Note that we use a newtype to help distinguish between regular atoms and dests, since
-- it should only be allowed to convert from a dest to a regular atom (by simply issuing a
-- load instruction for each fully offset array), but not in the other direction.
-- Also, Dests should also always be fully simplified (i.e. no beta-redexes are allowed,
-- even under lambdas).

newtype Dest = Dest Atom deriving (Show)
type WithDest a = (Maybe Dest, a)

deriving via Atom instance HasVars Dest

pattern TabValAbs :: LamExpr -> Atom
pattern TabValAbs a <- Lam a@(Abs _ (TabArrow, _))

destPairUnpack :: Dest -> (Dest, Dest)
destPairUnpack (Dest (PairVal l r)) = (Dest l, Dest r)
destPairUnpack (Dest a) = error $ "Not a pair destination: " ++ pprint a

destArrays :: Dest -> [IVar]
destArrays dest = [fromIVar (fromArrayAtom (Var v)) | v@(_ :> ArrayTy _) <- free]
  where free = envAsVars $ fmap fst $ freeVars dest

-- TODO: Maybe just make fromArrayAtom return an IVar?
fromIVar :: IExpr -> IVar
fromIVar ~(IVar v) = v

destGet :: MonadImp m instr => Dest -> Atom -> m Dest
destGet dest idx = destGetDim dest 0 idx

destGetDim :: MonadImp m instr => Dest -> Int -> Atom -> m Dest
destGetDim dest dim idx = indexDest dest dim $ \(Dest d) -> Dest <$> appReduce d idx

destSliceDim :: MonadImp m instr => Dest -> Int -> Atom -> Type -> m Dest
destSliceDim dest dim fromOrdinal idxTy = indexDest dest dim $ \(Dest d) -> case d of
  TabVal b _ -> do
    lam <- buildLam (Bind (binderNameHint b :> idxTy)) TabArrow $ \idx -> do
      i <- indexToIntE idxTy idx
      ioff <- iadd i fromOrdinal
      vidx <- intToIndexE (binderType b) ioff
      appReduce d vidx
    return $ Dest $ lam
  _ -> error "Slicing a non-array dest"

indexDest :: MonadImp m instr => Dest -> Int -> (Dest -> EmbedT m Dest) -> m Dest
indexDest (Dest destAtom) dim f = do
  scope <- variableScope
  (block, _) <- runEmbedT (buildScoped $ go dim destAtom) scope
  Dest <$> translateBlock mempty (Nothing, block)
  where
    go 0 dest = coerce <$> f (Dest dest)
    go d da@(TabVal v _) = buildLam v TabArrow $ \v' -> go (d-1) =<< appReduce da v'
    go _ _ = error $ "Indexing a non-array dest"

-- XXX: This should only be called when it is known that the dest will _never_
--      be modified again, because it doesn't copy the state!
destToAtom :: MonadImp m instr => Dest -> m Atom
destToAtom dest = destToAtomScalarAction loadScalarRef dest
  where
    loadScalarRef ref = toScalarAtom (BaseTy b) <$> (load $ IVar ref)
      where ~(_ :> IRefType (BaseTy b)) = ref

destToAtomScalarAction :: MonadImp m instr => (IVar -> m Atom) -> Dest -> m Atom
destToAtomScalarAction fScalar dest = do
  scope <- variableScope
  (atom, (_, decls)) <- runEmbedT (destToAtom' fScalar True dest) scope
  unless (null decls) $ error $ "Unexpected decls: " ++ pprint decls
  return atom

destToAtom' :: MonadImp m instr => (IVar -> m Atom) -> Bool -> Dest -> EmbedT m Atom
destToAtom' fScalar scalar (Dest destAtom) = case destAtom of
  TabVal v _ ->
    buildLam v TabArrow $ \v' -> do
      -- XXX: We need a guarantee that appReduce will not unnecessarily cause the result
      --      be bound to a temporary value, because that will make it impossible to
      --      maintain the fully-reduced invariant.
      elemDestAtom <- appReduce destAtom v'
      destToAtom' fScalar False (Dest elemDestAtom)
  Var _ -> if scalar
    then lift $ fScalar $ fromIVar $ fromArrayAtom destAtom
    else arrLoad $ assertIsArray $ destAtom
    where assertIsArray = toArrayAtom . fromArrayAtom
  DataCon  def params con args -> DataCon def params con <$> mapM rec args
  Record items -> Record <$> mapM rec items
  Variant types label i item   -> Variant types label i <$> rec item
  Con destCon -> Con <$> case destCon of
    PairCon dl dr              -> PairCon <$> rec dl <*> rec dr
    UnitCon                    -> return $ UnitCon
    Coerce (ArrayTy CharTy) d  -> CharCon  <$> rec d
    Coerce (ArrayTy t     ) d  -> Coerce t <$> rec d
    SumAsProd ty tag xs        -> SumAsProd ty <$> rec tag <*> mapM (mapM rec) xs
    _ -> unreachable
  _ -> unreachable
  where
    rec = destToAtom' fScalar scalar . Dest
    unreachable :: forall a. a
    unreachable = error $ "Not a valid destination: " ++ pprint destAtom

splitDest :: WithDest Block -> ([WithDest Decl], WithDest Expr, [(Dest, Atom)])
splitDest (maybeDest, (Block decls ans)) = do
  case (maybeDest, ans) of
    (Just dest, Atom atom) ->
      let (gatherCopies, varDests) = runState (execWriterT $ gatherVarDests dest atom) mempty
          -- If any variable appearing in the ans atom is not defined in the
          -- current block (e.g. it comes from the surrounding block), then we need
          -- to do the copy explicitly, as there is no let binding that will use it
          -- as the destination.
          blockVars = foldMap (\(Let _ b _) -> b @> ()) decls
          closureCopies = fmap (\(n, (d, t)) -> (d, Var $ n :> t))
                               (envPairs $ varDests `envDiff` blockVars) in
        ( fmap (\d@(Let _ b _) -> (fst <$> varDests `envLookup` b, d)) $ toList decls
        , (Nothing, ans)
        , gatherCopies ++ closureCopies)
    _ -> (fmap (Nothing,) $ toList decls, (maybeDest, ans), [])
  where
    -- Maps all variables used in the result atom to their respective destinations.
    gatherVarDests :: Dest -> Atom -> WriterT [(Dest, Atom)] (State (Env (Dest, Type))) ()
    gatherVarDests dest result = case (dest, result) of
      (_, Var v) -> do
        dests <- get
        case dests `envLookup` v of
          Nothing -> modify $ (<> (v @> (dest, varType v)))
          Just _  -> tell [(dest, result)]
      -- If the result is a table lambda then there is nothing we can do, except for a copy.
      (_, TabVal _ _)  -> tell [(dest, result)]
      (_, Con (Lit _)) -> tell [(dest, result)]
      (Dest (DataCon _ _ con args), DataCon _ _ con' args')
        | con == con' && length args == length args' -> do
            zipWithM_ gatherVarDests (map Dest args) args'
      (Dest (Record items), Record items')
        | fmap (const ()) items == fmap (const ()) items' -> do
            zipWithM_ gatherVarDests (map Dest (toList items)) (toList items')
      (Dest (Con (SumAsProd _ _ _)), _) -> tell [(dest, result)]  -- TODO
      (Dest (Con dCon), Con rCon) -> case (dCon, rCon) of
        (PairCon ld rd , PairCon lr rr ) -> gatherVarDests (Dest ld) lr >>
                                            gatherVarDests (Dest rd) rr
        (UnitCon       , UnitCon       ) -> return ()
        (Coerce (ArrayTy CharTy) d, CharCon a) -> gatherVarDests (Dest d) a
        (Coerce _ db   , Coerce _ rb   ) -> gatherVarDests (Dest db) rb
        _ -> unreachable
      _ -> unreachable
      where
        unreachable = error $ "Invalid dest-result pair:\n"
                        ++ pprint dest ++ "\n  and:\n" ++ pprint result

copyDest :: MonadImp m instr => Maybe Dest -> Atom -> m Atom
copyDest maybeDest atom = case maybeDest of
  Nothing   -> return atom
  Just dest -> copyAtom dest atom >> return atom

allocDest :: MonadImp m instr => Maybe Dest -> Type -> m Dest
allocDest maybeDest t = case maybeDest of
  Nothing   -> alloc t
  Just dest -> return dest

-- Create a destination for a given type. Note that this doesn't actually allocate anything,
-- so make sure to call alloc for any variables in the dest.
makeDest :: MonadImp m instr => Name -> Type -> m Dest
makeDest nameHint destType = do
  scope <- variableScope
  (destAtom, (_, decls)) <- runEmbedT (go id [] destType) scope
  unless (null decls) $ error $ "Unexpected decls: " ++ pprint decls
  return $ Dest destAtom
  where
    go :: MonadImp m instr => (ScalarTableType -> ScalarTableType) -> [Atom] -> Type -> EmbedT m Atom
    go mkTy idxVars ty = case ty of
        TypeCon def params -> do
          let dcs = applyDataDefParams def params
          case dcs of
            [] -> error "Void type not allowed"
            [DataConDef _ bs] -> do
              dests <- mapM (rec . binderType) $ toList bs
              return $ DataCon def params 0 dests
            _ -> do
              tag <- rec TagRepTy
              let dcs' = applyDataDefParams def params
              contents <- forM dcs' $ \(DataConDef _ bs) -> forM (toList bs) (rec . binderType)
              return $ Con $ SumAsProd ty tag contents
        RecordTy (NoExt types) -> Record <$> forM types rec
        VariantTy (NoExt types) -> do
          tag <- rec TagRepTy
          contents <- forM (toList types) rec
          return $ Con $ SumAsProd ty tag $ map (\x->[x]) contents
        TabTy v bt ->
          buildLam v TabArrow $ \v' -> go (\t -> mkTy $ TabTy v t) (v':idxVars) bt
        TC con    -> case con of
          BaseType b -> do
            iv <- lift $ freshVar (nameHint :> (IRefType $ mkTy $ BaseTy b))
            foldM arrIndex (toArrayAtom $ IVar iv) $ reverse idxVars
            where
              arrIndex arr idx = do
                ordinal <- indexToIntE (getType idx) idx
                let (ArrayTy tabTy) = getType arr
                offset <- tabTy `offsetToE` ordinal
                arrOffset arr idx offset
          CharType         -> scalarCoerce Int8Type
          PairType a b     -> PairVal <$> rec a <*> rec b
          UnitType         -> return UnitVal
          IntRange   _ _   -> recCoerce IdxRepTy
          IndexRange _ _ _ -> recCoerce IdxRepTy
          _ -> unreachable
        _ -> unreachable
      where
        scalarCoerce rep = recCoerce (BaseTy $ Scalar rep)
        recCoerce rep = Con . Coerce (ArrayTy ty) <$> rec rep
        rec = go mkTy idxVars
        unreachable = error $ "Can't lower type to imp: " ++ pprint destType

-- === Atom <-> IExpr conversions ===

fromScalarAtom :: Atom -> IExpr
fromScalarAtom atom = case atom of
  Var (v:>BaseTy b) -> IVar (v :> IValType b)
  Con (Lit x)       -> ILit x
  Con (Coerce _ x)  -> fromScalarAtom x
  Con (AnyValue ty) -> fromScalarAtom $ anyValue ty
  -- TODO: Handle AnyValue inside the constructor?
  Con (CharCon (Con (Lit l)))                           -> ILit $ Int8Lit    $ fromIntegral $ getIntLit l
  Con (CharCon (Var (v :> (BaseTy (Scalar Int8Type))))) -> IVar (v :> IValType (Scalar Int8Type))
  _ -> error $ "Expected scalar, got: " ++ pprint atom

toScalarAtom :: Type -> IExpr -> Atom
toScalarAtom ty ie = case ty of
  BaseTy b -> case ie of
    ILit l                            -> Con $ Lit l
    IVar (v :> IValType b') | b == b' -> Var (v :> ty)
    _ -> unreachable
  CharTy -> Con $ CharCon  $ toScalarAtom (BaseTy $ Scalar Int8Type) ie
  TC (IntRange _ _)     -> Con $ Coerce ty $ toScalarAtom IdxRepTy ie
  TC (IndexRange _ _ _) -> Con $ Coerce ty $ toScalarAtom IdxRepTy ie
  TC (IndexSlice _ _)   -> Con $ Coerce ty $ toScalarAtom IdxRepTy ie
  _ -> unreachable
  where
    unreachable = error $ "Cannot convert " ++ show ie ++ " to " ++ show ty

fromArrayAtom :: Atom -> IExpr
fromArrayAtom atom = case atom of
  Var (n :> ArrayTy t) -> IVar (n :> IRefType t)
  _ -> error $ "Expected array, got: " ++ pprint atom

toArrayAtom :: IExpr -> Atom
toArrayAtom ie = case ie of
  IVar (v :> IRefType t) -> Var $ v :> ArrayTy t
  _                      -> error $ "Not an array atom: " ++ show ie

-- === Type classes ===

fromEmbed :: MonadImp m instr => Embed Atom -> m Atom
fromEmbed m = do
  scope <- variableScope
  translateBlock mempty (Nothing, fst $ runEmbed (buildScoped m) scope)

intToIndex :: MonadImp m instr => Type -> IExpr -> m Atom
intToIndex ty i   = fromEmbed (intToIndexE ty (toScalarAtom IdxRepTy i))

indexToInt :: MonadImp m instr => Type -> Atom -> m IExpr
indexToInt ty idx = fromScalarAtom <$> fromEmbed (indexToIntE ty idx)

indexSetSize :: MonadImp m instr => Type -> m IExpr
indexSetSize ty   = fromScalarAtom <$> fromEmbed (indexSetSizeE ty)

elemCount :: MonadImp m instr => ScalarTableType -> m IExpr
elemCount ty      = fromScalarAtom <$> fromEmbed (elemCountE ty)

offsetTo :: MonadImp m instr => ScalarTableType -> IExpr -> m IExpr
offsetTo ty i     = fromScalarAtom <$> fromEmbed (offsetToE ty (toScalarAtom IdxRepTy i))

elemCountE :: MonadEmbed m => ScalarTableType -> m Atom
elemCountE ty = case ty of
  BaseTy _  -> return $ IdxRepVal 1
  TabTy b _ -> offsetToE ty =<< indexSetSizeE (binderType b)
  _ -> error $ "Not a scalar table type: " ++ pprint ty

-- TODO: Accept an index instead of an ordinal?
offsetToE :: MonadEmbed m => ScalarTableType -> Atom -> m Atom
offsetToE ty i = case ty of
  BaseTy _  -> error "Indexing into a scalar!"
  TabTy _ _ -> A.evalSumClampPolynomial (A.offsets ty) i
  _ -> error $ "Not a scalar table type: " ++ pprint ty

zipWithDest :: MonadImp m instr => Dest -> Atom -> (IExpr -> IExpr -> m ()) -> m ()
zipWithDest dest@(Dest destAtom) atom f = case (destAtom, atom) of
  (TabValAbs da, TabValAbs aa) -> do
    -- This check is quite important, because Imp type checking has no way to
    -- figure out if the loop length we've generated here makes sense or not.
    unless (absArgType da == absArgType aa) $ error "Mismatched dimensions in zipWithDest!"
    let idxTy = absArgType da
    n <- indexSetSize idxTy
    emitLoop "i" Fwd n $ \i -> do
      idx <- intToIndex idxTy i
      ai  <- translateExpr mempty (Nothing, App atom idx)
      di  <- destGet dest idx
      rec di ai
  (DataCon _ _ con args, DataCon _ _ con' args')
    | con == con' && length args == length args' -> do
       zipWithM_ rec (map Dest args) args'
  (Record items, Record items')
    | fmap (const ()) items == fmap (const ()) items' -> do
        zipWithM_ rec (map Dest (toList items)) (toList items')
  -- TODO: Check array type?
  (Var d, Var a)           | varType d == ArrayTy (varType a)    -> f (fromArrayAtom destAtom) (fromScalarAtom atom)
  (Var d, Con (Lit _))     | varType d == ArrayTy (getType atom) -> f (fromArrayAtom destAtom) (fromScalarAtom atom)
  (Con (SumAsProd _ tag payload), DataCon _ _ con x) -> do
    recDest tag (TagRepVal $ fromIntegral con)
    zipWithM_ recDest (payload !! con) x
  (Con (SumAsProd _ tag payload), Variant (NoExt types) label i x) -> do
    let LabeledItems ixtypes = enumerate types
    let index = fst $ (ixtypes M.! label) NE.!! i
    recDest tag (TagRepVal $ fromIntegral index)
    zipWithM_ recDest (payload !! index) [x]
  (Con dcon, Con acon) -> case (dcon, acon) of
    (PairCon ld rd, PairCon la ra) -> rec (Dest ld) la >> rec (Dest rd) ra
    (UnitCon      , UnitCon      ) -> return ()
    (Coerce (ArrayTy CharTy) d, CharCon _) -> f (fromArrayAtom d) (fromScalarAtom atom)
    (Coerce _ d   , Coerce _ a   ) -> rec (Dest d) a
    (SumAsProd _ tag xs, SumAsProd _ tag' xs') -> do
      recDest tag tag'
      zipWithM_ (zipWithM_ recDest) xs xs'
    _ -> unreachable
  _ -> unreachable
  where
    rec x y = zipWithDest x y f
    recDest x y = zipWithDest (Dest x) y f
    unreachable = error $ "Not an imp atom, or mismatched dest: "
                             ++ pprint dest ++ ", and " ++ pprint atom

copyAtom :: MonadImp m instr => Dest -> Atom -> m ()
copyAtom dest src = zipWithDest dest src store

zeroDest :: MonadImp m instr => Dest -> m ()
zeroDest dest = mapM_ (initializeZero . IVar) (destArrays dest)
  where
    initializeZero ref = case impExprType ref of
      IRefType (BaseTy (Scalar Float64Type)) -> store ref (ILit $ Float64Lit 0.0)
      IRefType (BaseTy (Vector Float64Type)) -> store ref (ILit $ VecLit $ replicate vectorWidth $ Float64Lit 0.0)
      IRefType (TabTy b _) -> do
        n <- indexSetSize $ binderType b
        emitLoop "i" Fwd n $ \i -> impGet ref i >>= initializeZero
      ty -> error $ "Zeros not implemented for type: " ++ pprint ty

addToAtom :: MonadImp m instr => Dest -> Atom -> m ()
addToAtom topDest topSrc = zipWithDest topDest topSrc addToDestScalar
  where
    addToDestScalar dest src = do
      cur     <- load dest
      let op = case impExprType cur of
                 IValType (Scalar _) -> ScalarBinOp
                 IValType (Vector _) -> VectorBinOp
                 _ -> error $ "The result of load cannot be a reference"
      updated <- emitInstr $ liftInstr $ IPrimOp $ op FAdd cur src
      store dest updated

-- === Imp embedding ===

embedBinOp :: MonadImp m instr => (Atom -> Atom -> Embed Atom) -> (IExpr -> IExpr -> m IExpr)
embedBinOp f x y =
  fromScalarAtom <$> fromEmbed (f (toScalarAtom (BaseTy bt) x) (toScalarAtom (BaseTy bt) y))
  where (IValType bt) = impExprType x

iaddI :: MonadImp m instr => IExpr -> IExpr -> m IExpr
iaddI = embedBinOp iadd

isubI :: MonadImp m instr => IExpr -> IExpr -> m IExpr
isubI = embedBinOp isub

imulI :: MonadImp m instr => IExpr -> IExpr -> m IExpr
imulI = embedBinOp imul

idivI :: MonadImp m instr => IExpr -> IExpr -> m IExpr
idivI = embedBinOp idiv

impGet :: MonadImp m instr => IExpr -> IExpr -> m IExpr
impGet ref i = case ref of
  (IVar (_ :> IRefType t)) -> do
    off <- t `offsetTo` i
    let resTy = tabTypeGet t i
    emitInstr $ liftInstr $ IOffset ref off resTy
  _ -> error $ "impGet called with non-ref: " ++ show ref

tabTypeGet :: ScalarTableType -> IExpr -> ScalarTableType
tabTypeGet (TabTyAbs a) i = snd $ applyAbs a (toScalarAtom (absArgType a) i)
tabTypeGet t _ = error $ "Not a non-scalar scalar table: " ++ pprint t

impOffset :: MonadImp m instr => IExpr -> IExpr -> ScalarTableType -> m IExpr
impOffset ref off ty = case ref of
  (IVar (_ :> IRefType _)) -> emitInstr $ liftInstr $ IOffset ref off ty
  _ -> error $ "impOffset called with non-ref: " ++ show ref

cast :: MonadImp m instr => IExpr -> BaseType -> m IExpr
cast x bt = emitInstr $ liftInstr $ ICastOp (IValType bt) x

load :: MonadImp m instr => IExpr -> m IExpr
load x = emitInstr $ liftInstr $ Load x

store :: MonadImp m instr => IExpr -> IExpr -> m ()
store dest src = emitStatement $ IInstr (IDo, liftInstr $ Store dest src)

alloc :: MonadImp m instr => Type -> m Dest
alloc ty = allocKind Managed ty

-- TODO: Consider targeting LLVM's `switch` instead of chained conditionals.
emitSwitch :: MonadImp m instr => IExpr -> [m ()] -> m ()
emitSwitch testIdx = rec 0
  where
    rec :: MonadImp m instr => Int -> [m ()] -> m ()
    rec _ [] = error "Shouldn't have an empty list of alternatives"
    rec _ [body] = body
    rec curIdx (body:rest) = do
      let curTag = fromScalarAtom $ TagRepVal $ fromIntegral curIdx
      cond       <- emitInstr $ liftInstr $ IPrimOp $ ScalarBinOp (ICmp Equal) testIdx curTag
      thisCase   <- liftM snd $ scopedBlock $ body
      otherCases <- liftM snd $ scopedBlock $ rec (curIdx + 1) rest
      emitStatement $ ICond cond thisCase otherCases

emitLoop :: MonadImp m instr => Name -> Direction -> IExpr -> (IExpr -> m ()) -> m ()
emitLoop hint d n body = do
  (i, loopBody) <- scopedBlock $ do
    i <- freshVar (hint:>impExprType n)
    body $ IVar i
    return i
  emitStatement $ IFor d (Bind i) n loopBody

emitInstr :: MonadImp m instr => instr -> m IExpr
emitInstr instr = do
  case getIType instr of
    IVoidType -> error "Expected non-void result"
    ty -> do
      v <- freshVar ("v":>ty)
      emitStatement $ IInstr (Bind v, instr)
      return $ IVar v

data AllocType = Managed | Unmanaged

class ImpSuperset instr where
  liftInstr :: ImpInstr -> instr

instance ImpSuperset ImpInstr where
  liftInstr = id

class (Monad m, HasIType instr, ImpSuperset instr) => MonadImp m instr | m -> instr where
  allocKind :: AllocType -> Type -> m Dest
  scopedBlock :: m a -> m (a, IProg instr)
  emitStatement :: IStmt instr -> m ()
  variableScope :: m Scope
  freshVar :: VarP a -> m (VarP a)
  translateExpr :: SubstEnv -> WithDest Expr -> m Atom
  withRefScope :: m a -> m a
  getRef :: Var -> m Dest
  putRef :: Var -> Dest -> m ()

instance MonadImp ImpM ImpInstr where
  allocKind allocTy ty = do
    dest <- makeDest "v" ty
    let vs = destArrays dest
    flip mapM_ vs $ \v@(_:>IRefType refTy) -> do
      numel <- elemCount refTy
      emitStatement $ IInstr (Bind v, Alloc refTy numel)
    case allocTy of
      Managed   -> extend $ asFst $ asSnd vs
      Unmanaged -> return ()
    return dest

  scopedBlock body = do
    (ans, ((_, allocs), (scope', prog))) <- scoped body
    extend (mempty, (scope', mempty))  -- Keep the scope extension to avoid reusing variable names
    let frees = toNest [IInstr (IDo, Free v) | v <- allocs]
    return (ans, prog <> frees)

  emitStatement statement = extend $ asSnd $ asSnd $ toNest [statement]

  variableScope = looks $ fst . snd

  freshVar (hint:>t) = do
    scope <- looks (fst . snd)
    let v = genFresh (rawName GenName $ nameTag hint) scope
    extend $ asSnd $ asFst (v @> (UnitTy, UnknownBinder)) -- TODO: fix!
    return $ v:>t

  translateExpr = defaultTranslateExpr

  withRefScope m = do
    (a, ((_, x), (y, z))) <- scoped $ m
    extend ((mempty, x), (y, z))
    return a
  getRef v = looks $ (! v) . fst . fst
  putRef v d = extend ((v @> d, mempty), mempty)

instance ImpSuperset (MDImpInstr k) where
  liftInstr instr = case instr of
    Load  ref     -> MDLoadScalar  (fromIVar ref)
    Store ref val -> MDStoreScalar (fromIVar ref) val
    Alloc ty num  -> MDAlloc ty num
    Free  ref     -> MDFree ref
    _             -> MDHostInstr instr

type MDImpM = ImpMP (MDImpProgram ImpKernel)

instance HasIType (MDImpInstr k) where
  getIType instr = case instr of
    MDLaunch _ _ _    -> IVoidType
    MDAlloc ty _      -> IRefType ty
    MDFree _          -> IVoidType
    MDLoadScalar  ref -> ignoreExcept $ IValType <$> fromScalarRefType (impExprType $ IVar ref)
    MDStoreScalar _ _ -> IVoidType
    MDHostInstr i     -> getIType i

instance MonadImp MDImpM (MDImpInstr ImpKernel) where
  allocKind allocTy ty = do
    dest <- makeDest "v" ty
    let vs = destArrays dest
    flip mapM_ vs $ \v@(_:>IRefType refTy) -> do
      numel <- elemCount refTy
      emitStatement $ IInstr (Bind v, MDAlloc refTy numel)
    case allocTy of
      Managed   -> extend $ asFst $ asSnd vs
      Unmanaged -> return ()
    return dest

  scopedBlock body = do
    (ans, ((_, allocs), (scope', prog))) <- scoped body
    extend (mempty, (scope', mempty))  -- Keep the scope extension to avoid reusing variable names
    let frees = toNest [IInstr (IDo, MDFree v) | v <- allocs]
    return (ans, prog <> frees)

  emitStatement statement = extend $ asSnd $ asSnd $ toNest [statement]

  variableScope = looks $ fst . snd

  freshVar (hint:>t) = do
    scope <- looks (fst . snd)
    let v = genFresh (rawName GenName $ nameTag hint) scope
    extend $ asSnd $ asFst (v @> (UnitTy, UnknownBinder)) -- TODO: fix!
    return $ v:>t

  translateExpr env (maybeDest, expr) = case expr of
      -- TODO: Add support for reductions
      -- TODO: Not every parallel for can be made a kernel, since we don't
      --       lift large allocations just yet.
      Hof (For _ (LamVal b body)) | isPure expr -> do
        idxTy <- impSubst env $ binderType b
        n     <- indexSetSize idxTy
        dest  <- allocDest maybeDest $ getType expr
        scope <- variableScope
        i <- freshVar (binderNameHint b:>impExprType n)
        let ((), kernel) = runImpMP @ImpProgram scope $ scopedBlock $ do
                              idx <- intToIndex idxTy $ IVar i
                              ithDest <- destGet dest idx
                              void $ translateBlock (env <> b @> idx) (Just ithDest, body)
        let args = envAsVars $ freeIVars kernel `envDiff` (i @> ())
        emitStatement $ IInstr (IDo, MDLaunch n args $ ImpKernel (Bind <$> args) (Bind i) kernel)
        destToAtom dest
      _ -> defaultTranslateExpr env (maybeDest, expr)

  withRefScope m = do
    (a, ((_, x), (y, z))) <- scoped $ m
    extend ((mempty, x), (y, z))
    return a
  getRef v = looks $ (! v) . fst . fst
  putRef v d = extend ((v @> d, mempty), mempty)


-- === type checking imp programs ===

-- State keeps track of _all_ names used in the program, Reader keeps the type env.
type ImpCheckM a = StateT (Env ()) (ReaderT (Env IType) (Either Err)) a

instance Checkable ImpFunction where
  checkValid (ImpFunction _ vsIn prog) = do
    let scope = foldMap (binderAsEnv . fmap (const ())) vsIn
    let env   = foldMap (binderAsEnv . fmap (IRefType . dropArray)) vsIn
    void $ runReaderT (runStateT (checkProg prog) scope) env
    where dropArray ~(ArrayTy t) = t

checkProg :: IProg ImpInstr -> ImpCheckM ()
checkProg prog = () <$ checkProgVal (prog, Nothing)

checkProgVal :: IProgVal ImpInstr -> ImpCheckM (Maybe IType)
checkProgVal (Empty, val) = traverse checkIExpr val
checkProgVal ((Nest stmt prog), val) = do
  env <- case stmt of
    IInstr (binder, instr) -> do
      ty <- instrTypeChecked instr
      case (binder, ty) of
        (IDo    , IVoidType) -> return mempty
        (Bind _ , IVoidType) -> throw CompilerErr $ "Can't assign result of void instruction"
        (b, _) -> do
          checkBinder b
          checkValidType $ binderAnn b
          assertEq (binderAnn b) ty "Type mismatch in instruction"
          return (b@>ty)
    IFor _ i size block -> do
      checkInt size
      checkBinder i
      assertEq (binderAnn i) (impExprType size) $ "Mismatch between the loop iterator and upper bound type"
      extendR (i @> impExprType size) $ checkProg block
      return mempty
    IWhile cond body -> do
      Just condTy <- checkProgVal cond
      assertEq (IValType $ Scalar Int8Type) condTy $ "Not a bool: " ++ pprint cond
      checkProg body
      return mempty
    ICond predicate consequent alternative -> do
      predTy <- checkIExpr predicate
      assertEq (IValType $ Scalar Int8Type) predTy "Type mismatch in predicate"
      checkProg consequent
      checkProg alternative
      return mempty
  extendR env $ checkProgVal (prog, val)

instrTypeChecked :: ImpInstr -> ImpCheckM IType
instrTypeChecked instr = case instr of
  IPrimOp op -> checkImpOp op
  ICastOp dt x -> do
    case impExprType x of
      IValType (Scalar _) -> return ()
      _ -> throw CompilerErr $ "Invalid cast source type: " ++ pprint dt
    case dt of
      IValType (Scalar _) -> return ()
      _ -> throw CompilerErr $ "Invalid cast destination type: " ++ pprint dt
    return dt
  Load ref -> do
    b <- (checkIExpr >=> fromScalarRefType) ref
    return $ IValType b
  Store dest val -> do
    b <- (checkIExpr >=> fromScalarRefType) dest
    valTy <- checkIExpr val
    assertEq (IValType b) valTy "Type mismatch in store"
    return IVoidType
  Alloc ty _ -> return $ IRefType ty
  Free _   -> return IVoidType  -- TODO: check matched alloc/free
  IOffset e i t -> do
    IRefType (TabTy _ _) <- checkIExpr e
    checkInt i
    return $ IRefType $ t
  IThrowError -> return IVoidType

checkBinder :: IBinder -> ImpCheckM ()
checkBinder v = do
  scope <- get
  when (v `isin` scope) $ error $ "shadows: " ++ pprint v
  modify (<>(v@>()))

checkValidType :: IType -> ImpCheckM ()
checkValidType (IValType _)           = return ()
checkValidType (IRefType (TabTy _ b)) = checkValidType $ IRefType b
checkValidType (IRefType (BaseTy _))  = return ()
checkValidType t = throw CompilerErr $ "Invalid Imp type: " ++ show t

checkIExpr :: IExpr -> ImpCheckM IType
checkIExpr expr = case expr of
  ILit val -> return $ IValType $ litType val
  -- TODO: check shape matches vector length
  IVar v -> asks $ (! v)

checkInt :: IExpr -> ImpCheckM ()
checkInt expr = do
  (IValType bt) <- checkIExpr expr
  checkIntBaseType False (BaseTy bt)

checkImpOp :: IPrimOp -> ImpCheckM IType
checkImpOp op = do
  op' <- traverse checkIExpr op
  case op' of
    ScalarBinOp bop x y -> checkImpBinOp bop x y
    VectorBinOp bop x y -> checkImpBinOp bop x y
    ScalarUnOp  uop x   -> checkImpUnOp  uop x
    Select _ x y -> checkEq x y >> return x
    FFICall _ ty _ -> return $ IValType ty
    VectorPack xs -> do
      IValType (Scalar ty) <- return $ head xs
      mapM_ (checkEq (IValType $ Scalar ty)) xs
      return $ IValType $ Vector ty
    VectorIndex x i -> do
      IValType (Vector ty) <- return x
      IValType ibt         <- return i
      checkIntBaseType False $ BaseTy ibt
      return $ IValType $ Scalar ty
    _ -> error $ "Not allowed in Imp IR: " ++ pprint op
  where
    checkEq :: (Pretty a, Show a, Eq a) => a -> a -> ImpCheckM ()
    checkEq t t' = assertEq t t' (pprint op)

fromScalarRefType :: MonadError Err m => IType -> m BaseType
fromScalarRefType (IRefType (BaseTy b)) = return b
fromScalarRefType ty = throw CompilerErr $ "Not a scalar reference type: " ++ pprint ty

impExprType :: IExpr -> IType
impExprType expr = case expr of
  ILit v    -> IValType $ litType v
  IVar (_:>ty) -> ty

class HasIType a where
  getIType :: a -> IType

instance HasIType ImpInstr where
  getIType = impInstrType

impInstrType :: ImpInstr -> IType
impInstrType instr = case instr of
  IPrimOp op      -> impOpType op
  ICastOp t _     -> t
  Load ref        -> ignoreExcept $ IValType <$> fromScalarRefType (impExprType ref)
  Store _ _       -> IVoidType
  Alloc ty _      -> IRefType ty
  Free _          -> IVoidType
  IOffset _ _ ty  -> IRefType ty
  IThrowError     -> IVoidType

checkImpBinOp :: MonadError Err m => BinOp -> IType -> IType -> m IType
checkImpBinOp op (IValType x) (IValType y) = do
  retTy <- checkBinOp op (BaseTy x) (BaseTy y)
  case retTy of
    BaseTy bt -> return $ IValType bt
    _         -> throw CompilerErr $ "Unexpected BinOp return type: " ++ pprint retTy
checkImpBinOp _ _ _ = throw CompilerErr "BinOp with reference arguments"

checkImpUnOp :: MonadError Err m => UnOp -> IType -> m IType
checkImpUnOp op (IValType x) = do
  retTy <- checkUnOp op (BaseTy x)
  case retTy of
    BaseTy bt -> return $ IValType bt
    _         -> throw CompilerErr $ "Unexpected UnOp return type: " ++ pprint retTy
checkImpUnOp _ _ = throw CompilerErr "UnOp with reference arguments"

impOpType :: IPrimOp -> IType
impOpType pop = case pop of
  ScalarBinOp op x y -> ignoreExcept $ checkImpBinOp op (impExprType x) (impExprType y)
  ScalarUnOp  op x   -> ignoreExcept $ checkImpUnOp  op (impExprType x)
  VectorBinOp op x y -> ignoreExcept $ checkImpBinOp op (impExprType x) (impExprType y)
  FFICall _ ty _     -> IValType ty
  Select  _ x  _     -> impExprType x
  VectorPack xs      -> IValType $ Vector ty
    where (IValType (Scalar ty)) = impExprType $ head xs
  VectorIndex x _    -> IValType $ Scalar ty
    where (IValType (Vector ty)) = impExprType x
  _ -> unreachable
  where unreachable = error $ "Not allowed in Imp IR: " ++ pprint pop

instance Pretty Dest where
  pretty (Dest atom) = "Dest" <+> pretty atom
