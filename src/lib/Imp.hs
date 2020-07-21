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
import Data.Foldable (fold)
import Data.Coerce

import Embed
import Array
import Syntax
import Env
import Type
import PPrint
import Cat
import Util (lookupWithIdx)
import qualified Algebra as A
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

toImpFunction :: Bindings -> ([ScalarTableVar], Block) -> (ImpFunction, Atom)
toImpFunction bindings (vsIn, block) = runImpM bindings vsIn $ do
  ((vsOut, atomOut), prog) <- scopedBlock $ materializeResult
  return $ (ImpFunction (fmap toVar vsOut) vsIn prog, atomOut)
  where
    toVar = (\(Var x) -> x) . toArrayAtom . IVar
    materializeResult = do
      outDest <- allocKind Unmanaged $ getType block
      void $ toImpBlock mempty (Just outDest, block)
      atomOut <- destToAtomScalarAction (return . toArrayAtom . IVar) outDest
      return (destArrays outDest, atomOut)

runImpM :: Bindings -> [ScalarTableVar] -> ImpM a -> a
runImpM bindings inVars m =
  fst $ runCat (runReaderT m bindings) (mempty, (bindings <> inVarScope, mempty))
  where
    inVarScope :: Scope  -- TODO: fix (shouldn't use UnitTy)
    inVarScope = foldMap varAsEnv $ fmap (fmap $ const (UnitTy, UnknownBinder)) inVars

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
  ~(DataCon _ _ _ ans) <- toImpExpr env (maybeDest, bound)
  return $ fold $ zipWith (@>) bs' ans

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
        let NAbs bs body = alts !! con
        toImpBlock (env <> newEnv bs args) (maybeDest, body)
      Con (SumAsProd _ tag xss) -> do
        let tag' = fromScalarAtom tag
        dest <- allocDest maybeDest $ getType expr
        emitSwitch tag' $ flip map (zip xss alts) $
          \(xs, NAbs bs body) ->
             void $ toImpBlock (env <> newEnv bs xs) (Just dest, body)
        destToAtom dest

impSubst :: HasVars a => SubstEnv -> a -> ImpM a
impSubst env x = do
  scope <- looks $ fst . snd
  return $ subst (env, scope) x

toImpOp :: WithDest (PrimOp Atom) -> ImpM Atom
toImpOp (maybeDest, op) = case op of
  TabCon (TabTy v _) rows -> do
    dest <- allocDest maybeDest resultTy
    forM_ (zip [0..] rows) $ \(i, row) -> do
      ithDest <- destGet dest =<< intToIndex (varType v) (IIntVal i)
      copyAtom ithDest row
    destToAtom dest
  SumGet ~(SumVal  _ l r) left -> returnVal $ if left then l else r
  SumTag ~(SumVal  t _ _)      -> returnVal t
  Fst    ~(PairVal x _)        -> returnVal x
  Snd    ~(PairVal _ y)        -> returnVal y
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
             FFICall "int_to_index_set" (Scalar IntType) [i', n']
    returnVal =<< intToIndex resultTy ans
  IdxSetSize n -> returnVal . toScalarAtom resultTy =<< indexSetSize n
  IndexAsInt idx -> case idx of
    Con (Coerce (TC (IntRange   _ _  )) i) -> returnVal $ i
    Con (Coerce (TC (IndexRange _ _ _)) i) -> returnVal $ i
    Con (AnyValue t)                       -> returnVal $ anyValue t
    _ -> returnVal . toScalarAtom IntTy =<< indexToInt (getType idx) idx
  Inject e -> do
    let rt@(TC (IndexRange t low _)) = getType e
    offset <- case low of
      InclusiveLim a -> indexToInt t a
      ExclusiveLim a -> indexToInt t a >>= iaddI IOne
      Unlimited      -> return IZero
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
    vz <- intToIndex v $ IIntVal 0
    extraOffset <- indexToInt (PairTy u v) (PairVal idx vz)
    tileOffset' <- iaddI (fromScalarAtom tileOffset) extraOffset
    returnVal $ toScalarAtom resultTy tileOffset'
  ThrowError ty -> do
    emitStatement (Nothing, IThrowError)
    return $ Con $ AnyValue ty
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
    For d (LamVal b@(hint:>idxTy') body) -> do
      idxTy <- impSubst env idxTy'
      n' <- indexSetSize idxTy
      dest <- allocDest maybeDest resultTy
      emitLoop hint d n' $ \i -> do
        idx <- intToIndex idxTy i
        ithDest <- destGet dest idx
        void $ toImpBlock (env <> b @> idx) (Just ithDest, body)
      destToAtom dest
    Tile d (LamVal tb@(tHint:>tileTy') tBody) (LamVal sb@(sHint:>_) sBody) -> do
      ~tileTy@(TC (IndexSlice idxTy tileIdxTy)) <- impSubst env tileTy'
      n <- indexSetSize idxTy
      dest <- allocDest maybeDest resultTy
      tileLen <- indexSetSize tileIdxTy
      nTiles      <- n `idivI` tileLen
      epilogueOff <- nTiles `imulI` tileLen
      nEpilogue   <- n `isubI` epilogueOff
      emitLoop tHint Fwd nTiles $ \iTile -> do
        tileOffset <- toScalarAtom IntTy <$> iTile `imulI` tileLen
        let tileAtom = Con $ Coerce tileTy tileOffset
        tileDest <- destSliceDim dest d tileOffset tileIdxTy
        void $ toImpBlock (env <> tb @> tileAtom) (Just tileDest, tBody)
      emitLoop sHint Fwd nEpilogue $ \iEpi -> do
        i <- iEpi `iaddI` epilogueOff
        idx <- intToIndex idxTy i
        sDest <- destGetDim dest d idx
        void $ toImpBlock (env <> sb @> idx) (Just sDest, sBody)
      destToAtom dest
    While (Lam (Abs _ (_, cond))) (Lam (Abs _ (_, body))) -> do
      ~condVarDest@(Dest condVar) <- allocDest Nothing BoolTy
      void $ toImpBlock env (Just condVarDest, cond)
      (_, body') <- scopedBlock $do
        void $ toImpBlock env (Nothing, body)
        toImpBlock env (Just condVarDest, cond)
      emitStatement (Nothing, IWhile (fromArrayAtom condVar) body')
      return UnitVal
    RunReader r (BinaryFunVal _ ref _ body) -> do
      rDest <- alloc $ getType r
      rVar  <- freshVar ref
      copyAtom rDest =<< impSubst env r
      withRefScope rVar rDest $
        toImpBlock (env <> ref @> Var rVar) (maybeDest, body)
    RunWriter (BinaryFunVal _ ref _ body) -> do
      (aDest, wDest) <- destPairUnpack <$> allocDest maybeDest resultTy
      zeroDest $ wDest
      wVar <- freshVar ref
      void $ withRefScope wVar wDest $
        toImpBlock (env <> ref @> Var wVar) (Just aDest, body)
      PairVal <$> destToAtom aDest <*> destToAtom wDest
    RunState s (BinaryFunVal _ ref _ body) -> do
      (aDest, sDest) <- destPairUnpack <$> allocDest maybeDest resultTy
      copyAtom sDest =<< impSubst env s
      sVar <- freshVar ref
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
  TabVal v _ -> do
    lam <- buildLam (varName v :> idxTy) TabArrow $ \idx -> do
      i <- indexToIntE idxTy idx
      ioff <- iadd i fromOrdinal
      vidx <- intToIndexE (varType v) ioff
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
  Con destCon -> Con <$> case destCon of
    PairCon dl dr        -> PairCon <$> rec dl <*> rec dr
    UnitCon              -> return $ UnitCon
    Coerce (ArrayTy t) d -> Coerce t <$> rec d
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
      let blockVars = foldMap (\(Let _ v _) -> v @> ()) decls
      let closureCopies = fmap (\(n, (d, t)) -> (d, Var $ n :> t))
                               (envPairs $ varDests `envDiff` blockVars)
      return $ ( fmap (\d@(Let _ v _) -> (fst <$> varDests `envLookup` v, d)) decls
               , (Nothing, ans)
               , gatherCopies ++ closureCopies)
    _ -> return $ (fmap (Nothing,) decls, (maybeDest, ans), [])
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
      (Dest (Con dCon), Con rCon) -> case (dCon, rCon) of
        (PairCon ld rd , PairCon lr rr ) -> gatherVarDests (Dest ld) lr >>
                                            gatherVarDests (Dest rd) rr
        (UnitCon       , UnitCon       ) -> return ()
        (Coerce _ db   , Coerce _ rb   ) -> gatherVarDests (Dest db) rb
        (_             , SumCon _ _ _  ) -> error "Not implemented"
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
              dests <- mapM (rec . varType) bs
              return $ DataCon def params 0 dests
            _ -> do
              tag <- rec IntTy
              let dcs' = applyDataDefParams def params
              contents <- forM dcs' $ \(DataConDef _ bs) -> forM bs  (rec . varType)
              return $ Con $ SumAsProd ty tag contents
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
          PairType a b     -> PairVal <$> rec a <*> rec b
          UnitType         -> return UnitVal
          IntRange   _ _   -> scalarIndexSet ty
          IndexRange _ _ _ -> scalarIndexSet ty
          _ -> unreachable
        _ -> unreachable
      where
        scalarIndexSet t = Con . Coerce (ArrayTy t) <$> rec IntTy
        rec = go bindings mkTy idxVars
        unreachable = error $ "Can't lower type to imp: " ++ pprint destType

-- === Atom <-> IExpr conversions ===

fromScalarAtom :: Atom -> IExpr
fromScalarAtom atom = case atom of
  Var (v:>BaseTy b) -> IVar (v :> IValType b)
  Con (Lit x)       -> ILit x
  Con (Coerce _ x)  -> fromScalarAtom x
  Con (AnyValue ty) -> fromScalarAtom $ anyValue ty
  _ -> error $ "Expected scalar, got: " ++ pprint atom

toScalarAtom :: Type -> IExpr -> Atom
toScalarAtom ty ie = case ie of
  ILit l -> Con $ Lit l
  IVar (v :> IValType b) -> case ty of
    BaseTy b' | b == b'     -> Var (v :> ty)
    TC (IntRange _ _)       -> Con $ Coerce ty $ toScalarAtom IntTy ie
    TC (IndexRange ty' _ _) -> Con $ Coerce ty $ toScalarAtom ty' ie
    TC (IndexSlice _ _)     -> Con $ Coerce ty $ toScalarAtom IntTy ie
    _ -> unreachable
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
  BaseTy _  -> return $ IntVal 1
  TabTy v _ -> offsetToE ty =<< indexSetSizeE (varType v)
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
    emitLoop NoName Fwd n $ \i -> do
      idx <- intToIndex idxTy i
      ai  <- toImpExpr mempty (Nothing, App atom idx)
      di  <- destGet dest idx
      rec di ai
  (DataCon _ _ con args, DataCon _ _ con' args')
    | con == con' && length args == length args' -> do
       zipWithM_ rec (map Dest args) args'
  -- TODO: Check array type?
  (Var _, Var _)       -> f (fromArrayAtom destAtom) (fromScalarAtom atom)
  (Var _, Con (Lit _)) -> f (fromArrayAtom destAtom) (fromScalarAtom atom)
  (Con (SumAsProd _ tag payload), DataCon _ _ con x) -> do
    recDest tag (IntVal con)
    zipWithM_ recDest (payload !! con) x
  (Con dcon, Con acon) -> case (dcon, acon) of
    (PairCon ld rd, PairCon la ra) -> rec (Dest ld) la >> rec (Dest rd) ra
    (UnitCon      , UnitCon      ) -> return ()
    (Coerce _ d   , Coerce _ a   ) -> rec (Dest d) a
    (SumCon _ _ _ , SumCon _ _ _ ) -> error "Not implemented"
    (SumAsProd _ tag xs, SumAsProd _ tag' xs') -> do
      recDest tag tag'
      zipWithM_ (zipWithM_ recDest) xs xs'
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
      IRefType (BaseTy (Scalar RealType)) -> store ref (ILit $ RealLit 0.0)
      IRefType (BaseTy (Vector RealType)) -> store ref (ILit $ VecLit $ replicate vectorWidth $ RealLit 0.0)
      IRefType (TabTy v _) -> do
        n <- indexSetSize $ varType v
        emitLoop NoName Fwd n $ \i -> impGet ref i >>= initializeZero
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

load :: IExpr -> ImpM IExpr
load x = emitInstr $ Load x

store :: IExpr -> IExpr -> ImpM ()
store dest src = emitStatement (Nothing, Store dest src)

data AllocType = Managed | Unmanaged

alloc :: Type -> ImpM Dest
alloc ty = allocKind Managed ty

allocKind :: AllocType -> Type -> ImpM Dest
allocKind allocTy ty = do
  dest <- makeDest "v" ty
  let vs = destArrays dest
  flip mapM_ vs $ \v@(_:>IRefType refTy) -> do
    numel <- elemCount refTy
    emitStatement (Just v, Alloc refTy numel)
  case allocTy of
    Managed   -> extend $ asFst $ asSnd vs
    Unmanaged -> return ()
  return dest

freshVar :: VarP a -> ImpM (VarP a)
freshVar (hint:>t) = do
  scope <- looks (fst . snd)
  let v' = rename (name:>t) scope
  extend $ asSnd $ asFst (v' @> (UnitTy, UnknownBinder)) -- TODO: fix!
  return v'
  where name = rawName GenName $ nameTag hint

-- TODO: Consider targeting LLVM's `switch` instead of chained conditionals.
emitSwitch :: IExpr -> [ImpM ()] -> ImpM ()
emitSwitch testIdx = rec 0
  where
    rec :: Int -> [ImpM ()] -> ImpM ()
    rec _ [] = error "Shouldn't have an empty list of alternatives"
    rec _ [body] = body
    rec curIdx (body:rest) = do
      pred <- emitInstr $ IPrimOp $ ScalarBinOp (ICmp Equal) testIdx (IIntVal curIdx)
      thisCase   <- liftM snd $ scopedBlock $ body
      otherCases <- liftM snd $ scopedBlock $ rec (curIdx + 1) rest
      emitStatement (Nothing, If pred thisCase otherCases)

emitLoop :: Name -> Direction -> IExpr -> (IExpr -> ImpM ()) -> ImpM ()
emitLoop maybeHint d n body = do
  (i, loopBody) <- scopedBlock $ do
    i <- freshVar (hint:>IIntTy)
    body $ IVar i
    return i
  emitStatement (Nothing, Loop d i n loopBody)
  where hint = case maybeHint of NoName -> "q"; _ -> maybeHint

scopedBlock :: ImpM a -> ImpM (a, ImpProg)
scopedBlock body = do
  (ans, ((_, allocs), (scope', prog))) <- scoped body
  extend (mempty, (scope', mempty))  -- Keep the scope extension to avoid reusing variable names
  let frees = ImpProg [(Nothing, Free v) | v <- allocs]
  return (ans, prog <> frees)

emitStatement :: ImpStatement -> ImpM ()
emitStatement statement = extend $ asSnd $ asSnd $ ImpProg [statement]

emitInstr :: ImpInstr -> ImpM IExpr
emitInstr instr = do
  case ignoreExcept (instrType instr) of
    Just ty -> do
      v <- freshVar ("v":>ty)
      emitStatement (Just v, instr)
      return $ IVar v
    Nothing -> error "Expected non-void result"

-- === type checking imp programs ===

-- State keeps track of _all_ names used in the program, Reader keeps the type env.
type ImpCheckM a = StateT (Env ()) (ReaderT (Env IType) (Either Err)) a

instance Checkable ImpFunction where
  checkValid (ImpFunction _ vsIn (ImpProg prog)) = do
    let scope = foldMap (varAsEnv . fmap (const ())) vsIn
    let env   = foldMap (varAsEnv . fmap (IRefType . dropArray)) vsIn
    void $ runReaderT (runStateT (checkProg prog) scope) env
    where dropArray ~(ArrayTy t) = t

checkProg :: [ImpStatement] -> ImpCheckM ()
checkProg [] = return ()
checkProg ((maybeBinder, instr):prog) = do
  maybeTy <- instrTypeChecked instr
  case (maybeBinder, maybeTy) of
    (Nothing, Nothing) -> checkProg prog
    (Nothing, Just _ ) -> throw CompilerErr $ "Result of non-void instruction must be assigned"
    (Just _ , Nothing) -> throw CompilerErr $ "Can't assign result of void instruction"
    (Just v@(_:>ty), Just ty') -> do
      checkBinder v
      checkValidType ty
      assertEq ty ty' "Type mismatch in instruction"
      extendR (v@>ty) $ checkProg prog

instrTypeChecked :: ImpInstr -> ImpCheckM (Maybe IType)
instrTypeChecked instr = case instr of
  IPrimOp op -> liftM Just $ checkImpOp op
  Load ref -> do
    b <- (checkIExpr >=> fromScalarRefType) ref
    return $ Just $ IValType b
  Store dest val -> do
    b <- (checkIExpr >=> fromScalarRefType) dest
    valTy <- checkIExpr val
    assertEq (IValType b) valTy "Type mismatch in store"
    return Nothing
  Alloc ty _ -> return $ Just $ IRefType ty
  Free _   -> return Nothing  -- TODO: check matched alloc/free
  Loop _ i size (ImpProg block) -> do
    checkInt size
    checkBinder i
    extendR (i @> IIntTy) $ checkProg block
    return Nothing
  IWhile cond (ImpProg body) -> do
    condRefTy <- checkIExpr cond
    assertEq (IRefType BoolTy) condRefTy $ "Not a bool ref: " ++ pprint cond
    checkProg body
    return Nothing
  If predicate (ImpProg consequent) (ImpProg alternative) -> do
    predTy <- checkIExpr predicate
    assertEq (IValType $ Scalar BoolType) predTy "Type mismatch in predicate"
    checkProg consequent
    checkProg alternative
    return Nothing
  IOffset e i t -> do
    IRefType (TabTy _ _) <- checkIExpr e
    checkInt i
    return $ Just $ IRefType $ t
  IThrowError -> return Nothing

checkBinder :: IVar -> ImpCheckM ()
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
  ty <- checkIExpr expr
  assertEq (IValType $ Scalar IntType) ty $ "Not an int: " ++ pprint expr

checkImpOp :: IPrimOp -> ImpCheckM IType
checkImpOp op = do
  op' <- traverse checkIExpr op
  case op' of
    ScalarBinOp binOp x y -> checkBinOp Scalar binOp x y
    VectorBinOp binOp x y -> checkBinOp Vector binOp x y
    ScalarUnOp scalarOp x -> do
      checkEq x (IValType $ Scalar x')
      return $ IValType $ Scalar ty
      where (x', ty) = unOpType scalarOp
    Select _ x y -> checkEq x y >> return x
    FFICall _ ty _ -> return $ IValType ty
    VectorPack xs -> do
      IValType (Scalar ty) <- return $ head xs
      mapM_ (checkEq (IValType $ Scalar ty)) xs
      return $ IValType $ Vector ty
    VectorIndex x i -> do
      IValType (Vector ty) <- return x
      assertEq (IValType $ Scalar IntType) i $ "Not an int: " ++ pprint i
      return $ IValType $ Scalar ty
    _ -> error $ "Not allowed in Imp IR: " ++ pprint op
  where
    checkEq :: (Pretty a, Show a, Eq a) => a -> a -> ImpCheckM ()
    checkEq t t' = assertEq t t' (pprint op)

    checkBinOp :: (ScalarBaseType -> BaseType) -> BinOp -> IType -> IType -> ImpCheckM IType
    checkBinOp toBase binOp x y = do
      checkEq x (IValType $ toBase x')
      checkEq y (IValType $ toBase y')
      return $ IValType $ toBase ty
      where (x', y', ty) = binOpType binOp

fromScalarRefType :: MonadError Err m => IType -> m BaseType
fromScalarRefType (IRefType (BaseTy b)) = return b
fromScalarRefType ty = throw CompilerErr $ "Not a scalar reference type: " ++ pprint ty

impExprType :: IExpr -> IType
impExprType expr = case expr of
  ILit v    -> IValType $ litType v
  IVar (_:>ty) -> ty

instrType :: MonadError Err m => ImpInstr -> m (Maybe IType)
instrType instr = case instr of
  IPrimOp op      -> return $ Just $ impOpType op
  Load ref        -> Just . IValType <$> fromScalarRefType (impExprType ref)
  Store _ _       -> return Nothing
  Alloc ty _      -> return $ Just $ IRefType ty
  Free _          -> return Nothing
  Loop _ _ _ _    -> return Nothing
  IWhile _ _      -> return Nothing
  IOffset _ _ ty  -> return $ Just $ IRefType ty

impOpType :: IPrimOp -> IType
impOpType (ScalarBinOp op _ _) = IValType $ Scalar ty  where (_, _, ty) = binOpType op
impOpType (ScalarUnOp  op _  ) = IValType $ Scalar ty  where (_,    ty) = unOpType  op
impOpType (VectorBinOp op _ _) = IValType $ Vector ty  where (_, _, ty) = binOpType op
impOpType (FFICall _ ty _ )    = IValType ty
impOpType (Select _ x _    )   = impExprType x
impOpType (VectorPack xs)      = IValType $ Vector ty
  where (IValType (Scalar ty)) = impExprType $ head xs
impOpType (VectorIndex x _)    = IValType $ Scalar ty
  where (IValType (Vector ty)) = impExprType x
impOpType op = error $ "Not allowed in Imp IR: " ++ pprint op

pattern IIntTy :: IType
pattern IIntTy = IValType (Scalar IntType)

pattern IIntVal :: Int -> IExpr
pattern IIntVal x = ILit (IntLit x)

pattern IZero :: IExpr
pattern IZero = IIntVal 0

pattern IOne :: IExpr
pattern IOne = IIntVal 1

instance Pretty Dest where
  pretty (Dest atom) = "Dest" <+> pretty atom
