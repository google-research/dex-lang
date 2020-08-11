-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DerivingVia #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Imp (toImpFunction, impExprType) where

import Prelude hiding (pi, abs)
import Control.Monad.Reader
import Control.Monad.Except hiding (Except)
import Control.Monad.State
import Control.Monad.Writer hiding (Alt)
import Data.Text.Prettyprint.Doc
import Data.Foldable (toList)
import Data.Coerce
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
type EmbedEnv = ((Env Dest, [IVar]), (Scope, ImpProg))
type ImpM = ReaderT Bindings (Cat EmbedEnv)

toImpFunction :: Bindings -> ([ScalarTableBinder], Block) -> (ImpFunction, Atom)
toImpFunction bindings (vsIn, block) = runImpM bindings vsIn $ do
  ((vsOut, atomOut), prog) <- scopedBlock $ materializeResult
  return $ (ImpFunction (fmap toBinder vsOut) vsIn prog, atomOut)
  where
    toBinder = Bind . (\(Var x) -> x) . toArrayAtom . IVar
    materializeResult = do
      outDest <- allocKind Unmanaged $ getType block
      void $ toImpBlock mempty (Just outDest, block)
      atomOut <- destToAtomScalarAction (return . toArrayAtom . IVar) outDest
      return (destArrays outDest, atomOut)

runImpM :: Bindings -> [ScalarTableBinder] -> ImpM a -> a
runImpM bindings inBinders m =
  fst $ runCat (runReaderT m bindings) (mempty, (bindings <> inVarScope, mempty))
  where
    inVarScope :: Scope  -- TODO: fix (shouldn't use UnitTy)
    inVarScope = foldMap binderAsEnv $ fmap (fmap $ const (UnitTy, UnknownBinder)) inBinders

toImpBlock :: SubstEnv -> WithDest Block -> ImpM Atom
toImpBlock env destBlock = do
  (decls, result, copies) <- splitDest destBlock
  env' <- (env<>) <$> catFoldM toImpDecl env decls
  forM_ copies $ \(dest, atom) -> copyAtom dest =<< impSubst env' atom
  toImpExpr env' result

toImpDecl :: SubstEnv -> WithDest Decl -> ImpM SubstEnv
toImpDecl env (maybeDest, (Let _ b bound)) = do
  b' <- traverse (impSubst env) b
  ans <- toImpExpr env (maybeDest, bound)
  return $ b' @> ans
toImpDecl env (maybeDest, (Unpack bs bound)) = do
  bs' <- mapM (traverse (impSubst env)) bs
  expr <- toImpExpr env (maybeDest, bound)
  case expr of
    DataCon _ _ _ ans -> return $ newEnv bs' ans
    Record items -> return $ newEnv bs $ toList items
    _ -> error "Unsupported type in an Unpack binding"

toImpExpr :: SubstEnv -> WithDest Expr -> ImpM Atom
toImpExpr env (maybeDest, expr) = case expr of
  App x' idx' -> case getType x' of
    TabTy _ _ -> do
      x <- impSubst env x'
      idx <- impSubst env idx'
      case x of
        Lam a@(Abs _ (TabArrow, _)) ->
          toImpBlock mempty (maybeDest, snd $ applyAbs a idx)
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
        toImpBlock (env <> newEnv bs args) (maybeDest, body)
      Variant types label i x -> do
        let LabeledItems ixtypes = enumerate types
        let index = fst $ ixtypes M.! label !! i
        let Abs bs body = alts !! index
        toImpBlock (env <> newEnv bs [x]) (maybeDest, body)
      Con (SumAsProd _ tag xss) -> do
        let tag' = fromScalarAtom tag
        dest <- allocDest maybeDest $ getType expr
        emitSwitch tag' $ flip map (zip xss alts) $
          \(xs, Abs bs body) ->
             void $ toImpBlock (env <> newEnv bs xs) (Just dest, body)
        destToAtom dest
      _ -> error $ "Unexpected scrutinee: " ++ pprint e'

impSubst :: Subst a => SubstEnv -> a -> ImpM a
impSubst env x = do
  scope <- looks $ fst . snd
  return $ subst (env, scope) x

toImpOp :: WithDest (PrimOp Atom) -> ImpM Atom
toImpOp (maybeDest, op) = case op of
  TabCon (TabTy b _) rows -> do
    dest <- allocDest maybeDest resultTy
    forM_ (zip [0..] rows) $ \(i, row) -> do
      ithDest <- destGet dest =<< intToIndex (binderType b) (asImpInt i)
      copyAtom ithDest row
    destToAtom dest
  Fst ~(PairVal x _) -> returnVal x
  Snd ~(PairVal _ y) -> returnVal y
  PrimEffect ~(Var refVar) m -> do
    refDest <- looks $ (! refVar) . fst . fst
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
    ans <- emitInstr $ IPrimOp $
             FFICall "int_to_index_set" (Scalar Int64Type) [i', n']
    returnVal =<< intToIndex resultTy ans
  IdxSetSize n -> returnVal . toScalarAtom resultTy =<< indexSetSize n
  IndexAsInt idx -> asInt $ case idx of
      Con (AnyValue t) -> anyValue t
      _                -> idx
    where
      asInt a = case a of
        Con (Coerce (TC (IntRange   _ _  )) i) -> returnVal $ i
        Con (Coerce (TC (IndexRange _ _ _)) i) -> returnVal $ i
        _ -> returnVal . toScalarAtom IntTy =<< indexToInt (getType idx) idx
  Inject e -> do
    let rt@(TC (IndexRange t low _)) = getType e
    offset <- case low of
      InclusiveLim a -> indexToInt t a
      ExclusiveLim a -> indexToInt t a >>= iaddI (asImpInt 1)
      Unlimited      -> return (asImpInt 0)
    restrictIdx <- indexToInt rt e
    idx <- iaddI restrictIdx offset
    returnVal =<< intToIndex t idx
  IndexRef ~(Var refVar@(_:>(RefTy h (Pi a)))) i -> do
    refDest    <- looks $ (! refVar) . fst . fst
    subrefDest <- destGet refDest i
    subrefVar  <- freshVar (varName refVar :> RefTy h (snd $ applyAbs a i))
    extend ((subrefVar @> subrefDest, mempty), mempty)
    returnVal $ Var subrefVar
  FstRef ~(Var refVar@(_:>(RefTy h (PairTy a _)))) -> do
    ~(Dest (PairVal ref _))  <- looks $ (! refVar) . fst . fst
    subrefVar <- freshVar (varName refVar :> RefTy h a)
    extend ((subrefVar @> Dest ref, mempty), mempty)
    returnVal $ Var subrefVar
  SndRef ~(Var refVar@(_:>(RefTy h (PairTy _ b)))) -> do
    ~(Dest (PairVal _ ref))  <- looks $ (! refVar) . fst . fst
    subrefVar <- freshVar (varName refVar :> RefTy h b)
    extend ((subrefVar @> Dest ref, mempty), mempty)
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
    vz <- intToIndex v $ asImpInt 0
    extraOffset <- indexToInt (PairTy u v) (PairVal idx vz)
    tileOffset' <- iaddI (fromScalarAtom tileOffset) extraOffset
    returnVal $ toScalarAtom resultTy tileOffset'
  ThrowError ty -> do
    emitStatement (IDo, IThrowError)
    return $ Con $ AnyValue ty
  CastOp destTy x -> case (getType x, destTy) of
    (_, BaseTy bt) -> castTo bt
    (_, IntTy    ) -> castTo $ Scalar Int64Type
    (_, FloatTy  ) -> castTo $ Scalar Float64Type
    _ -> error $ "Invalid cast: " ++ pprint (getType x) ++ " -> " ++ pprint destTy
    where
      castTo bt = do
        result <- cast (fromScalarAtom x) bt
        returnVal $ toScalarAtom destTy result
  Select p x y -> do
    dest <- allocDest maybeDest resultTy
    p' <- cast (fromScalarAtom p) $ Scalar Int64Type
    emitSwitch p' [copyAtom dest y, copyAtom dest x]
    destToAtom dest
  _ -> do
    returnVal . toScalarAtom resultTy =<< emitInstr (IPrimOp $ fmap fromScalarAtom op)
  where
    resultTy :: Type
    resultTy = getType $ Op op

    returnVal :: Atom -> ImpM Atom
    returnVal atom = case maybeDest of
      Nothing   -> return atom
      Just dest -> copyAtom dest atom >> return atom

toImpHof :: SubstEnv -> WithDest Hof -> ImpM Atom
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
        void $ toImpBlock (env <> b @> idx) (Just ithDest, body)
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
        tileOffset <- toScalarAtom IntTy <$> iTile `imulI` tileLen
        let tileAtom = Con $ Coerce tileTy tileOffset
        tileDest <- destSliceDim dest d tileOffset tileIdxTy
        void $ toImpBlock (env <> tb @> tileAtom) (Just tileDest, tBody)
      emitLoop (binderNameHint sb) Fwd nEpilogue $ \iEpi -> do
        i <- iEpi `iaddI` epilogueOff
        idx <- intToIndex idxTy i
        sDest <- destGetDim dest d idx
        void $ toImpBlock (env <> sb @> idx) (Just sDest, sBody)
      destToAtom dest
    While (Lam (Abs _ (_, cond))) (Lam (Abs _ (_, body))) -> do
      ~condVarDest@(Dest condVar) <- allocDest Nothing (BaseTy $ Scalar Int8Type)
      void $ toImpBlock env (Just condVarDest, cond)
      (_, body') <- scopedBlock $do
        void $ toImpBlock env (Nothing, body)
        toImpBlock env (Just condVarDest, cond)
      emitStatement (IDo, IWhile (fromArrayAtom condVar) body')
      return UnitVal
    RunReader r (BinaryFunVal _ ref _ body) -> do
      rDest <- alloc $ getType r
      rVar  <- freshVar $ fromBind "ref" ref
      copyAtom rDest =<< impSubst env r
      withRefScope rVar rDest $
        toImpBlock (env <> ref @> Var rVar) (maybeDest, body)
    RunWriter (BinaryFunVal _ ref _ body) -> do
      (aDest, wDest) <- destPairUnpack <$> allocDest maybeDest resultTy
      zeroDest $ wDest
      wVar <- freshVar $ fromBind "ref" ref
      void $ withRefScope wVar wDest $
        toImpBlock (env <> ref @> Var wVar) (Just aDest, body)
      PairVal <$> destToAtom aDest <*> destToAtom wDest
    RunState s (BinaryFunVal _ ref _ body) -> do
      (aDest, sDest) <- destPairUnpack <$> allocDest maybeDest resultTy
      copyAtom sDest =<< impSubst env s
      sVar <- freshVar $ fromBind "ref" ref
      void $ withRefScope sVar sDest $
        toImpBlock (env <> ref @> Var sVar) (Just aDest, body)
      PairVal <$> destToAtom aDest <*> destToAtom sDest
    _ -> error $ "Invalid higher order function primitive: " ++ pprint hof
  where
    withRefScope :: Var -> Dest -> ImpM a -> ImpM a
    withRefScope refVar refDest m = do
      (a, ((_, x), (y, z))) <- scoped $ extend (asFst $ asFst $ refVar @> refDest) >> m
      extend ((mempty, x), (y, z))
      return a

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

destGet :: Dest -> Atom -> ImpM Dest
destGet dest idx = destGetDim dest 0 idx

destGetDim :: Dest -> Int -> Atom -> ImpM Dest
destGetDim dest dim idx = indexDest dest dim $ \(Dest d) -> Dest <$> appReduce d idx

destSliceDim :: Dest -> Int -> Atom -> Type -> ImpM Dest
destSliceDim dest dim fromOrdinal idxTy = indexDest dest dim $ \(Dest d) -> case d of
  TabVal b _ -> do
    lam <- buildLam (Bind (binderNameHint b :> idxTy)) TabArrow $ \idx -> do
      i <- indexToIntE idxTy idx
      ioff <- iadd i fromOrdinal
      vidx <- intToIndexE (binderType b) ioff
      appReduce d vidx
    return $ Dest $ lam
  _ -> error "Slicing a non-array dest"

indexDest :: Dest -> Int -> (Dest -> EmbedT ImpM Dest) -> ImpM Dest
indexDest (Dest destAtom) dim f = do
  scope <- looks $ fst . snd
  (block, _) <- runEmbedT (buildScoped $ go dim destAtom) scope
  Dest <$> toImpBlock mempty (Nothing, block)
  where
    go :: Int -> Atom -> EmbedT ImpM Atom
    go 0 dest = coerce <$> f (Dest dest)
    go d da@(TabVal v _) = buildLam v TabArrow $ \v' ->
      go (d-1) =<< appReduce da v'
    go _ _ = error $ "Indexing a non-array dest"

-- XXX: This should only be called when it is known that the dest will _never_
--      be modified again, because it doesn't copy the state!
destToAtom :: Dest -> ImpM Atom
destToAtom dest = destToAtomScalarAction loadScalarRef dest
  where
    loadScalarRef ref = toScalarAtom (BaseTy b) <$> (load $ IVar ref)
      where ~(_ :> IRefType (BaseTy b)) = ref

destToAtomScalarAction :: (IVar -> ImpM Atom) -> Dest -> ImpM Atom
destToAtomScalarAction fScalar dest = do
  scope <- looks $ fst . snd
  (atom, (_, decls)) <- runEmbedT (destToAtom' fScalar True dest) scope
  unless (null decls) $ error $ "Unexpected decls: " ++ pprint decls
  return atom

destToAtom' :: (IVar -> ImpM Atom) -> Bool -> Dest -> EmbedT ImpM Atom
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
    Coerce (ArrayTy IntTy ) d  -> IntCon   <$> rec d
    Coerce (ArrayTy FloatTy) d -> FloatCon  <$> rec d
    Coerce (ArrayTy CharTy) d  -> CharCon  <$> rec d
    Coerce (ArrayTy t     ) d  -> Coerce t <$> rec d
    SumAsProd ty tag xs -> SumAsProd ty <$> rec tag <*> mapM (mapM rec) xs
    _ -> unreachable
  _ -> unreachable
  where
    rec = destToAtom' fScalar scalar . Dest
    unreachable = error $ "Not a valid destination: " ++ pprint destAtom

splitDest :: WithDest Block -> ImpM ([WithDest Decl], WithDest Expr, [(Dest, Atom)])
splitDest (maybeDest, (Block decls ans)) = do
  case (maybeDest, ans) of
    (Just dest, Atom atom) -> do
      let (gatherCopies, varDests) = runState (execWriterT $ gatherVarDests dest atom) mempty
      -- If any variable appearing in the ans atom is not defined in the
      -- current block (e.g. it comes from the surrounding block), then we need
      -- to do the copy explicitly, as there is no let binding that will use it
      -- as the destination.
      let blockVars = foldMap (\(Let _ b _) -> b @> ()) decls
      let closureCopies = fmap (\(n, (d, t)) -> (d, Var $ n :> t))
                               (envPairs $ varDests `envDiff` blockVars)
      return $ ( fmap (\d@(Let _ b _) -> (fst <$> varDests `envLookup` b, d)) $ toList decls
               , (Nothing, ans)
               , gatherCopies ++ closureCopies)
    _ -> return $ (fmap (Nothing,) $ toList decls, (maybeDest, ans), [])
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
        (Coerce (ArrayTy IntTy ) d, IntCon a ) -> case getType a of
          BaseTy (Scalar Int64Type)   -> gatherVarDests (Dest d) a
          _                           -> tell [(dest, result)]
        (Coerce (ArrayTy FloatTy) d, FloatCon a) -> case getType a of
          BaseTy (Scalar Float64Type) -> gatherVarDests (Dest d) a
          _                           -> tell [(dest, result)]
        (Coerce (ArrayTy CharTy) d, CharCon a) -> case getType a of
          BaseTy (Scalar Int8Type)    -> gatherVarDests (Dest d) a
          _                           -> tell [(dest, result)]
        (Coerce _ db   , Coerce _ rb   ) -> gatherVarDests (Dest db) rb
        _ -> unreachable
      _ -> unreachable
      where
        unreachable = error $ "Invalid dest-result pair:\n"
                        ++ pprint dest ++ "\n  and:\n" ++ pprint result

copyDest :: Maybe Dest -> Atom -> ImpM Atom
copyDest maybeDest atom = case maybeDest of
  Nothing   -> return atom
  Just dest -> copyAtom dest atom >> return atom

allocDest :: Maybe Dest -> Type -> ImpM Dest
allocDest maybeDest t = case maybeDest of
  Nothing   -> alloc t
  Just dest -> return dest

-- Create a destination for a given type. Note that this doesn't actually allocate anything,
-- so make sure to call alloc for any variables in the dest.
makeDest :: Name -> Type -> ImpM Dest
makeDest nameHint destType = do
  bindings <- ask
  scope <- looks $ fst . snd
  (destAtom, (_, decls)) <- runEmbedT (go bindings id [] destType) scope
  unless (null decls) $ error $ "Unexpected decls: " ++ pprint decls
  return $ Dest destAtom
  where
    go :: Bindings -> (ScalarTableType -> ScalarTableType) -> [Atom] -> Type
       -> EmbedT ImpM Atom
    go bindings mkTy idxVars ty = case ty of
        TypeCon def params -> do
          let dcs = applyDataDefParams def params
          case dcs of
            [] -> error "Void type not allowed"
            [DataConDef _ bs] -> do
              dests <- mapM (rec . binderType) $ toList bs
              return $ DataCon def params 0 dests
            _ -> do
              tag <- rec IntTy
              let dcs' = applyDataDefParams def params
              contents <- forM dcs' $ \(DataConDef _ bs) -> forM (toList bs) (rec . binderType)
              return $ Con $ SumAsProd ty tag contents
        RecordTy types -> Record <$> forM types rec
        VariantTy types -> do
          tag <- rec IntTy
          contents <- forM (toList types) rec
          return $ Con $ SumAsProd ty tag $ map (\x->[x]) contents
        TabTy v bt ->
          buildLam v TabArrow $ \v' -> go bindings (\t -> mkTy $ TabTy v t) (v':idxVars) bt
        TC con    -> case con of
          BaseType b -> do
            iv <- lift $ freshVar (nameHint :> (IRefType $ mkTy $ BaseTy b))
            foldM arrIndex (toArrayAtom $ IVar iv) $ reverse idxVars
            where
              arrIndex :: Atom -> Atom -> EmbedT ImpM Atom
              arrIndex arr idx = do
                ordinal <- indexToIntE (getType idx) idx
                let (ArrayTy tabTy) = getType arr
                offset <- tabTy `offsetToE` ordinal
                arrOffset arr idx offset
          IntType          -> scalarCoerce Int64Type
          FloatType        -> scalarCoerce Float64Type
          CharType         -> scalarCoerce Int8Type
          PairType a b     -> PairVal <$> rec a <*> rec b
          UnitType         -> return UnitVal
          IntRange   _ _   -> recCoerce IntTy
          IndexRange _ _ _ -> recCoerce IntTy
          _ -> unreachable
        _ -> unreachable
      where
        scalarCoerce rep = recCoerce (BaseTy $ Scalar rep)
        recCoerce rep = Con . Coerce (ArrayTy ty) <$> rec rep
        rec = go bindings mkTy idxVars
        unreachable = error $ "Can't lower type to imp: " ++ pprint destType

-- === Atom <-> IExpr conversions ===

fromScalarAtom :: Atom -> IExpr
fromScalarAtom atom = case atom of
  Var (v:>BaseTy b) -> IVar (v :> IValType b)
  Con (Lit x)       -> ILit x
  Con (Coerce _ x)  -> fromScalarAtom x
  Con (AnyValue ty) -> fromScalarAtom $ anyValue ty
  -- TODO: Handle AnyValue inside the constructors?
  Con (IntCon  (Con (Lit l)))  -> ILit $ Int64Lit   $ fromIntegral $ getIntLit l
  Con (FloatCon (Con (Lit l)))  -> ILit $ Float64Lit $ getFloatLit l
  Con (CharCon (Con (Lit l)))  -> ILit $ Int8Lit    $ fromIntegral $ getIntLit l
  Con (IntCon  (Var (v :> (BaseTy (Scalar Int64Type)))))   -> IVar (v :> IValType (Scalar Int64Type))
  Con (FloatCon (Var (v :> (BaseTy (Scalar Float64Type))))) -> IVar (v :> IValType (Scalar Float64Type))
  Con (CharCon (Var (v :> (BaseTy (Scalar Int8Type)))))    -> IVar (v :> IValType (Scalar Int8Type))
  _ -> error $ "Expected scalar, got: " ++ pprint atom

toScalarAtom :: Type -> IExpr -> Atom
toScalarAtom ty ie = case ty of
  BaseTy b -> case ie of
    ILit l                            -> Con $ Lit l
    IVar (v :> IValType b') | b == b' -> Var (v :> ty)
    _ -> unreachable
  IntTy   -> Con $ IntCon   $ toScalarAtom (BaseTy $ Scalar Int64Type  ) ie
  FloatTy -> Con $ FloatCon $ toScalarAtom (BaseTy $ Scalar Float64Type) ie
  CharTy  -> Con $ CharCon  $ toScalarAtom (BaseTy $ Scalar Int8Type   ) ie
  TC (IntRange _ _)     -> Con $ Coerce ty $ toScalarAtom IntTy ie
  TC (IndexRange _ _ _) -> Con $ Coerce ty $ toScalarAtom IntTy ie
  TC (IndexSlice _ _)   -> Con $ Coerce ty $ toScalarAtom IntTy ie
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

fromEmbed :: Embed Atom -> ImpM Atom
fromEmbed m = do
  scope <- looks $ fst . snd
  toImpBlock mempty (Nothing, fst $ runEmbed (buildScoped m) scope)

intToIndex :: Type -> IExpr -> ImpM Atom
intToIndex ty i   = fromEmbed (intToIndexE ty (toScalarAtom IntTy i))

indexToInt :: Type -> Atom -> ImpM IExpr
indexToInt ty idx = fromScalarAtom <$> fromEmbed (indexToIntE ty idx)

indexSetSize :: Type -> ImpM IExpr
indexSetSize ty   = fromScalarAtom <$> fromEmbed (indexSetSizeE ty)

elemCount :: ScalarTableType -> ImpM IExpr
elemCount ty      = fromScalarAtom <$> fromEmbed (elemCountE ty)

offsetTo :: ScalarTableType -> IExpr -> ImpM IExpr
offsetTo ty i     = fromScalarAtom <$> fromEmbed (offsetToE ty (toScalarAtom IntTy i))

elemCountE :: MonadEmbed m => ScalarTableType -> m Atom
elemCountE ty = case ty of
  BaseTy _  -> return $ IntLit $ Int64Lit 1
  TabTy b _ -> offsetToE ty =<< indexSetSizeE (binderType b)
  _ -> error $ "Not a scalar table type: " ++ pprint ty

-- TODO: Accept an index instead of an ordinal?
offsetToE :: MonadEmbed m => ScalarTableType -> Atom -> m Atom
offsetToE ty i = case ty of
  BaseTy _  -> error "Indexing into a scalar!"
  TabTy _ _ -> A.evalSumClampPolynomial (A.offsets ty) i
  _ -> error $ "Not a scalar table type: " ++ pprint ty

zipWithDest :: Dest -> Atom -> (IExpr -> IExpr -> ImpM ()) -> ImpM ()
zipWithDest dest@(Dest destAtom) atom f = case (destAtom, atom) of
  (TabValAbs da, TabValAbs aa) -> do
    -- This check is quite important, because Imp type checking has no way to
    -- figure out if the loop length we've generated here makes sense or not.
    unless (absArgType da == absArgType aa) $ error "Mismatched dimensions in zipWithDest!"
    let idxTy = absArgType da
    n <- indexSetSize idxTy
    emitLoop "i" Fwd n $ \i -> do
      idx <- intToIndex idxTy i
      ai  <- toImpExpr mempty (Nothing, App atom idx)
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
    recDest tag (IntLit $ Int64Lit $ fromIntegral con)
    zipWithM_ recDest (payload !! con) x
  (Con (SumAsProd _ tag payload), Variant types label i x) -> do
    let LabeledItems ixtypes = enumerate types
    let index = fst $ (ixtypes M.! label) !! i
    recDest tag (IntLit $ Int64Lit $ fromIntegral index)
    zipWithM_ recDest (payload !! index) [x]
  (Con dcon, Con acon) -> case (dcon, acon) of
    (PairCon ld rd, PairCon la ra) -> rec (Dest ld) la >> rec (Dest rd) ra
    (UnitCon      , UnitCon      ) -> return ()
    (Coerce (ArrayTy IntTy ) d, IntCon _ )   -> f (fromArrayAtom d) (fromScalarAtom atom)
    (Coerce (ArrayTy FloatTy) d, FloatCon _) -> f (fromArrayAtom d) (fromScalarAtom atom)
    (Coerce (ArrayTy CharTy) d, CharCon _)   -> f (fromArrayAtom d) (fromScalarAtom atom)
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

copyAtom :: Dest -> Atom -> ImpM ()
copyAtom dest src = zipWithDest dest src store

zeroDest :: Dest -> ImpM ()
zeroDest dest = mapM_ (initializeZero . IVar) (destArrays dest)
  where
    initializeZero :: IExpr -> ImpM ()
    initializeZero ref = case impExprType ref of
      IRefType (BaseTy (Scalar Float64Type)) -> store ref (ILit $ Float64Lit 0.0)
      IRefType (BaseTy (Vector Float64Type)) -> store ref (ILit $ VecLit $ replicate vectorWidth $ Float64Lit 0.0)
      IRefType (TabTy b _) -> do
        n <- indexSetSize $ binderType b
        emitLoop "i" Fwd n $ \i -> impGet ref i >>= initializeZero
      ty -> error $ "Zeros not implemented for type: " ++ pprint ty

addToAtom :: Dest -> Atom -> ImpM ()
addToAtom topDest topSrc = zipWithDest topDest topSrc addToDestScalar
  where
    addToDestScalar :: IExpr -> IExpr -> ImpM ()
    addToDestScalar dest src = do
      cur     <- load dest
      let op = case impExprType cur of
                 IValType (Scalar _) -> ScalarBinOp
                 IValType (Vector _) -> VectorBinOp
                 _ -> error $ "The result of load cannot be a reference"
      updated <- emitInstr $ IPrimOp $ op FAdd cur src
      store dest updated

-- === Imp embedding ===

embedBinOp :: (Atom -> Atom -> Embed Atom) -> Type -> Type -> (IExpr -> IExpr -> ImpM IExpr)
embedBinOp f xt yt x y = fromScalarAtom <$> fromEmbed (f (toScalarAtom xt x) (toScalarAtom yt y))

iaddI :: IExpr -> IExpr -> ImpM IExpr
iaddI = embedBinOp iadd IntTy IntTy

isubI :: IExpr -> IExpr -> ImpM IExpr
isubI = embedBinOp isub IntTy IntTy

imulI :: IExpr -> IExpr -> ImpM IExpr
imulI = embedBinOp imul IntTy IntTy

idivI :: IExpr -> IExpr -> ImpM IExpr
idivI = embedBinOp idiv IntTy IntTy

impGet :: IExpr -> IExpr -> ImpM IExpr
impGet ref i = case ref of
  (IVar (_ :> IRefType t)) -> do
    off <- t `offsetTo` i
    let resTy = tabTypeGet t i
    emitInstr $ IOffset ref off resTy
  _ -> error $ "impGet called with non-ref: " ++ show ref

tabTypeGet :: ScalarTableType -> IExpr -> ScalarTableType
tabTypeGet (TabTyAbs a) i = snd $ applyAbs a (toScalarAtom (absArgType a) i)
tabTypeGet t _ = error $ "Not a non-scalar scalar table: " ++ pprint t

impOffset :: IExpr -> IExpr -> ScalarTableType -> ImpM IExpr
impOffset ref off ty = case ref of
  (IVar (_ :> IRefType _)) -> emitInstr $ IOffset ref off ty
  _ -> error $ "impOffset called with non-ref: " ++ show ref

cast :: IExpr -> BaseType -> ImpM IExpr
cast x bt = emitInstr $ ICastOp (IValType bt) x

load :: IExpr -> ImpM IExpr
load x = emitInstr $ Load x

store :: IExpr -> IExpr -> ImpM ()
store dest src = emitStatement (IDo, Store dest src)

data AllocType = Managed | Unmanaged

alloc :: Type -> ImpM Dest
alloc ty = allocKind Managed ty

allocKind :: AllocType -> Type -> ImpM Dest
allocKind allocTy ty = do
  dest <- makeDest "v" ty
  let vs = destArrays dest
  flip mapM_ vs $ \v@(_:>IRefType refTy) -> do
    numel <- elemCount refTy
    emitStatement (Bind v, Alloc refTy numel)
  case allocTy of
    Managed   -> extend $ asFst $ asSnd vs
    Unmanaged -> return ()
  return dest

freshVar :: VarP a -> ImpM (VarP a)
freshVar (hint:>t) = do
  scope <- looks (fst . snd)
  let v = genFresh (rawName GenName $ nameTag hint) scope
  extend $ asSnd $ asFst (v @> (UnitTy, UnknownBinder)) -- TODO: fix!
  return $ v:>t

-- TODO: Consider targeting LLVM's `switch` instead of chained conditionals.
emitSwitch :: IExpr -> [ImpM ()] -> ImpM ()
emitSwitch testIdx = rec 0
  where
    rec :: Int -> [ImpM ()] -> ImpM ()
    rec _ [] = error "Shouldn't have an empty list of alternatives"
    rec _ [body] = body
    rec curIdx (body:rest) = do
      cond <- emitInstr $ IPrimOp $ ScalarBinOp (ICmp Equal) testIdx (asImpInt curIdx)
      thisCase   <- liftM snd $ scopedBlock $ body
      otherCases <- liftM snd $ scopedBlock $ rec (curIdx + 1) rest
      emitStatement (IDo, If cond thisCase otherCases)

emitLoop :: Name -> Direction -> IExpr -> (IExpr -> ImpM ()) -> ImpM ()
emitLoop hint d n body = do
  (i, loopBody) <- scopedBlock $ do
    i <- freshVar (hint:>IIntTy)
    body $ IVar i
    return i
  emitStatement (IDo, Loop d (Bind i) n loopBody)

scopedBlock :: ImpM a -> ImpM (a, ImpProg)
scopedBlock body = do
  (ans, ((_, allocs), (scope', prog))) <- scoped body
  extend (mempty, (scope', mempty))  -- Keep the scope extension to avoid reusing variable names
  let frees = ImpProg [(IDo, Free v) | v <- allocs]
  return (ans, prog <> frees)

emitStatement :: ImpStatement -> ImpM ()
emitStatement statement = extend $ asSnd $ asSnd $ ImpProg [statement]

emitInstr :: ImpInstr -> ImpM IExpr
emitInstr instr = do
  case ignoreExcept (instrType instr) of
    IVoidType -> error "Expected non-void result"
    ty -> do
      v <- freshVar ("v":>ty)
      emitStatement (Bind v, instr)
      return $ IVar v

-- === type checking imp programs ===

-- State keeps track of _all_ names used in the program, Reader keeps the type env.
type ImpCheckM a = StateT (Env ()) (ReaderT (Env IType) (Either Err)) a

instance Checkable ImpFunction where
  checkValid (ImpFunction _ vsIn (ImpProg prog)) = do
    let scope = foldMap (binderAsEnv . fmap (const ())) vsIn
    let env   = foldMap (binderAsEnv . fmap (IRefType . dropArray)) vsIn
    void $ runReaderT (runStateT (checkProg prog) scope) env
    where dropArray ~(ArrayTy t) = t

checkProg :: [ImpStatement] -> ImpCheckM ()
checkProg [] = return ()
checkProg ((binder, instr):prog) = do
  ty <- instrTypeChecked instr
  case (binder, ty) of
    (IDo    , IVoidType) -> checkProg prog
    (Bind _ , IVoidType) -> throw CompilerErr $ "Can't assign result of void instruction"
    (b, _) -> do
      checkBinder b
      checkValidType $ binderAnn b
      assertEq (binderAnn b) ty "Type mismatch in instruction"
      extendR (b@>ty) $ checkProg prog

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
  Loop _ i size (ImpProg block) -> do
    checkInt size
    checkBinder i
    assertEq (binderAnn i) (impExprType size) $ "Mismatch between the loop iterator and upper bound type"
    extendR (i @> IIntTy) $ checkProg block
    return IVoidType
  IWhile cond (ImpProg body) -> do
    condRefTy <- checkIExpr cond
    assertEq (IRefType $ BaseTy $ Scalar Int8Type) condRefTy $ "Not a bool ref: " ++ pprint cond
    checkProg body
    return IVoidType
  If predicate (ImpProg consequent) (ImpProg alternative) -> do
    predTy <- checkIExpr predicate
    assertEq IBoolTy predTy "Type mismatch in predicate"
    checkProg consequent
    checkProg alternative
    return IVoidType
  IOffset e i t -> do
    IRefType (TabTy _ _) <- checkIExpr e
    checkInt i
    return $ IRefType $ t
  IThrowError -> return IVoidType

checkBinder :: IBinder -> ImpCheckM ()
checkBinder v = do
  scope <- get
  when (v `isin` scope) $ throw CompilerErr $ "shadows: " ++ pprint v
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

instrType :: MonadError Err m => ImpInstr -> m IType
instrType instr = case instr of
  IPrimOp op      -> return $ impOpType op
  ICastOp t _     -> return t
  Load ref        -> IValType <$> fromScalarRefType (impExprType ref)
  Store _ _       -> return IVoidType
  Alloc ty _      -> return $ IRefType ty
  Free _          -> return IVoidType
  Loop _ _ _ _    -> return IVoidType
  IWhile _ _      -> return IVoidType
  IOffset _ _ ty  -> return $ IRefType ty
  If _ _ _        -> return IVoidType
  IThrowError     -> return IVoidType

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

pattern IIntTy :: IType
pattern IIntTy = IValType (Scalar Int64Type)

pattern IBoolTy :: IType
pattern IBoolTy = IValType (Scalar Int8Type)

asImpInt :: Int -> IExpr
asImpInt x = ILit (Int64Lit (fromIntegral x))

instance Pretty Dest where
  pretty (Dest atom) = "Dest" <+> pretty atom
