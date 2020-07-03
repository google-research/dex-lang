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
{-# OPTIONS_GHC -Wno-orphans #-}

module Imp (toImpFunction, impExprType) where

import Prelude hiding (pi, abs)
import Control.Monad.Reader
import Control.Monad.Except hiding (Except)
import Control.Monad.State
import Control.Monad.Writer
import Data.Text.Prettyprint.Doc
import Data.Foldable

import Embed
import Array
import Syntax
import Env
import Type
import PPrint
import Cat
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
type ImpM = Cat EmbedEnv

toImpFunction :: ([ScalarTableVar], Block) -> (ImpFunction, Atom)
toImpFunction (vsIn, block) = runImpM vsIn $ do
  ((vsOut, atomOut), prog) <- scopedBlock $ materializeResult
  return $ (ImpFunction (fmap toVar vsOut) vsIn prog, atomOut)
  where
    toVar = (\(Var x) -> x) . toArrayAtom . IVar
    materializeResult = do
      outDest <- allocKind Unmanaged $ getType block
      void $ toImpBlock mempty (Just outDest, block)
      atomOut <- destToAtomScalarAction (return . toArrayAtom . IVar) outDest
      return (toList outDest, atomOut)

runImpM :: [ScalarTableVar] -> ImpM a -> a
runImpM inVars m = fst $ runCat m (mempty, (inVarScope, mempty))
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

impSubst :: HasVars a => SubstEnv -> a -> ImpM a
impSubst env x = do
  scope <- looks $ fst . snd
  return $ subst (env, scope) x

toImpOp :: WithDest (PrimOp Atom) -> ImpM Atom
toImpOp (maybeDest, op) = case op of
  TabCon (TabTy _ _) rows -> do
    dest <- allocDest maybeDest resultTy
    forM_ (zip [0..] rows) $ \(i, row) -> do
      ithDest <- destGet dest $ IIntVal i
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
    subrefDest <- destGet refDest =<< indexToInt (getType i) i
    subrefVar  <- freshVar (varName refVar :> RefTy h (snd $ applyAbs a i))
    extend ((subrefVar @> subrefDest, mempty), mempty)
    returnVal $ Var subrefVar
  ArrayOffset arr idx off -> do
    i <- indexToInt (getType idx) idx
    let (TC (ArrayType t)) = getType arr
    let resTy = tabTypeGet t i
    arrSlice <- impOffset (fromArrayAtom arr) (fromScalarAtom off) resTy
    returnVal $ toArrayAtom arrSlice
  ArrayLoad arr -> returnVal . toScalarAtom resultTy =<< load (fromArrayAtom arr)
  SliceOffset ~(Con (Coerce (TC (IndexSlice n l)) tileOffset)) idx -> do
    i' <- indexToInt (TC (IntRange (IntVal 0) l)) idx
    i <- iaddI (fromScalarAtom tileOffset) i'
    returnVal =<< intToIndex n i
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
        ithDest <- destGet dest i
        void $ toImpBlock (env <> b @> idx) (Just ithDest, body)
      destToAtom dest
    Tile (LamVal tb@(tHint:>tileTy') tBody) (LamVal sb@(sHint:>_) sBody) -> do
      ~tileTy@(TC (IndexSlice idxTy tileLenAtom)) <- impSubst env tileTy'
      n <- indexSetSize idxTy
      dest <- allocDest maybeDest resultTy
      let tileLen = fromScalarAtom tileLenAtom
      nTiles      <- n `idivI` tileLen
      epilogueOff <- nTiles `imulI` tileLen
      nEpilogue   <- n `isubI` epilogueOff
      let tileDimType = TC $ IntRange (IntVal 0) tileLenAtom
      emitLoop tHint Fwd nTiles $ \iTile -> do
        tileOffset <- iTile `imulI` tileLen
        let tileAtom = Con $ Coerce tileTy (toScalarAtom IntTy tileOffset)
        tileDest <- destSlice dest tileOffset tileDimType
        void $ toImpBlock (env <> tb @> tileAtom) (Just tileDest, tBody)
      emitLoop sHint Fwd nEpilogue $ \iEpi -> do
        i <- iEpi `iaddI` epilogueOff
        idx <- intToIndex idxTy i
        ithDest <- destGet dest i
        void $ toImpBlock (env <> sb @> idx) (Just ithDest, sBody)
      destToAtom dest
    While (Lam (Abs _ (_, cond))) (Lam (Abs _ (_, body))) -> do
      ~condVarDest@(DRef condVar) <- allocDest Nothing BoolTy
      void $ toImpBlock env (Just condVarDest, cond)
      (_, body') <- scopedBlock $do
        void $ toImpBlock env (Nothing, body)
        toImpBlock env (Just condVarDest, cond)
      emitStatement (Nothing, IWhile (IVar condVar) body')
      return UnitVal
    RunReader r (BinaryFunVal _ ref _ body) -> do
      rDest <- alloc $ getType r
      rVar  <- freshVar ref
      copyAtom rDest =<< impSubst env r
      withRefScope rVar rDest $
        toImpBlock (env <> ref @> Var rVar) (maybeDest, body)
    RunWriter (BinaryFunVal _ ref _ body) -> do
      ~(DPair aDest wDest) <- allocDest maybeDest resultTy
      zeroDest wDest
      wVar <- freshVar ref
      void $ withRefScope wVar wDest $
        toImpBlock (env <> ref @> Var wVar) (Just aDest, body)
      PairVal <$> destToAtom aDest <*> destToAtom wDest
    RunState s (BinaryFunVal _ ref _ body) -> do
      ~(DPair aDest sDest) <- allocDest maybeDest resultTy
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
-- Desinations are an analog to regular Atoms, except they guarantee that the "leaf"
-- elements are scalar tables with non-aliasing memory. The Dest data structure is a
-- view that reverses the structure-of-arrays transformation we apply. When we go to
-- the atom world, we use table lambdas for the same purpose, but destinations are
-- a little easier to work with, since they can't contain arbitrary code.

-- This takes a type parameter only so that we can derive Traversalbe. Use Dest instead.
data DestP ref = DFor   (Abs (DestP ref))
               | DPair  (DestP ref) (DestP ref)
               | DUnit
               | DRef   ref
               | DCoerce Type (DestP ref)
                 deriving (Show, Functor, Foldable, Traversable)
type Dest = DestP IVar
type WithDest a = (Maybe Dest, a)

instance HasVars Dest where
  freeVars dest = case dest of
    DFor abs               -> freeVars abs
    DPair l r              -> freeVars l <> freeVars r
    DUnit                  -> mempty
    DRef (_ :> IValType _) -> mempty
    DRef (_ :> IRefType t) -> freeVars t
    DCoerce t d            -> freeVars t <> freeVars d

  subst env dest = case dest of
    DFor abs               -> DFor (subst env abs)
    DPair l r              -> DPair (subst env l) (subst env r)
    DUnit                  -> dest
    DRef (_ :> IValType _) -> dest
    DRef (v :> IRefType t) -> DRef (v :> IRefType (subst env t))
    DCoerce t d            -> DCoerce (subst env t) (subst env d)

destGet :: Dest -> IExpr -> ImpM Dest
destGet dest i = case dest of
  DFor a@(Abs v _) -> do
    idx <- intToIndex (varType v) i
    traverse (\ref -> fromIVar <$> (IVar ref) `impGet` i) $ applyAbs a idx
  _ -> error "Indexing into a non-array dest"
  where fromIVar ~(IVar v) = v

destSlice :: Dest -> IExpr -> Type -> ImpM Dest
destSlice dest from idxTy = case dest of
  DFor (Abs v d) -> do
    when (v `isin` freeVars d) $ error "destSlice doesn't support dependent dimensions!"
    DFor . Abs (NoName:>idxTy) <$> traverse sliceRef d
  _ -> error "Slicing a non-array dest"
  where
    fromIVar ~(IVar v) = v
    sliceRef ~ref@(_:>IRefType t@(TabTy dv b)) = do
      when (dv `isin` freeVars b) $ error "destSlice doesn't support dependent dimension!"
      off <- t `offsetTo` from
      fromIVar <$> impOffset (IVar ref) off (TabTy (NoName:>idxTy) b)

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
  (atom, (_, decls)) <- runEmbedT (destToAtom' fScalar [] dest) scope
  case decls of
    [] -> return $ atom
    _  -> error "Unexpected decls"

destToAtom' :: (IVar -> ImpM Atom) -> [Atom] -> Dest -> EmbedT ImpM Atom
destToAtom' fScalar forVars dest = case dest of
  DFor a@(Abs v _) -> do
    -- FIXME: buildLam does not maintain the NoName convention, so we have to
    --        fix it up locally
    ~(Lam (Abs v'' b)) <- buildLam ("idx" :> varType v) TabArrow $ \v' ->
      destToAtom' fScalar (v' : forVars) (applyAbs a v')
    return $ Lam $ makeAbs v'' b
  DRef ref       -> case forVars of
    [] -> lift $ fScalar ref
    _  -> do
      scalarArray <- foldM arrIndex (toArrayAtom $ IVar ref) $ reverse forVars
      arrLoad scalarArray
      where
        arrIndex :: Atom -> Atom -> EmbedT ImpM Atom
        arrIndex arr idx = do
          ordinal <- indexToIntE (getType idx) idx
          let (ArrayTy tabTy) = getType arr
          offset <- tabTy `offsetToE` ordinal
          arrOffset arr idx offset
  DPair dl dr    -> PairVal <$> rec dl <*> rec dr
  DUnit          -> return $ UnitVal
  DCoerce t d    -> Con . Coerce t <$> rec d
  where rec = destToAtom' fScalar forVars

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
      (DFor _, TabVal _ _) -> tell [(dest, result)]
      (_, Con rCon) -> case (dest, rCon) of
        (DRef _      , Lit _         ) -> tell [(dest, result)]
        (DPair ld rd , PairCon lr rr ) -> gatherVarDests ld lr >> gatherVarDests rd rr
        (DUnit       , UnitCon       ) -> return ()
        (DCoerce _ db, Coerce _ rb   ) -> gatherVarDests db rb
        (_           , SumCon _ _ _  ) -> error "Not implemented"
        _ -> unreachable
      _ -> unreachable
      where
        unreachable = error $ "Invalid dest-result pair:\n" ++ show dest ++ "\n  and:\n" ++ show result

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
makeDest nameHint destType = go id destType
  where
    go :: (ScalarTableType -> ScalarTableType) -> Type -> ImpM Dest
    go mkTy ty = case ty of
        -- TODO: Is it ok to reuse the variables here?
        --       Once might be ok, but the type will have aliasing binders!
        TabTy v b -> DFor . Abs v <$> go (\t -> mkTy $ TabTy v t) b
        TC con    -> case con of
          BaseType b       -> DRef  <$> freshVar (nameHint :> (IRefType $ mkTy $ BaseTy b))
          PairType a b     -> DPair <$> go mkTy a <*> go mkTy b
          UnitType         -> return DUnit
          IntRange   _ _   -> scalarIndexSet ty
          IndexRange _ _ _ -> scalarIndexSet ty
          _ -> unreachable
        _ -> unreachable
      where
        scalarIndexSet t = DCoerce t <$> go mkTy IntTy
        unreachable = error $ "Can't lower type to imp: " ++ pprint ty

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
zipWithDest dest atom f = case (dest, atom) of
  (DFor (Abs v _), Lam (Abs lv (TabArrow, _))) -> do
    -- This check is quite important, because Imp type checking has no way to
    -- figure out if the loop length we've generated here makes sense or not.
    unless (varType v == varType lv) $ error "Mismatched dimensions in zipWithDest!"
    let idxTy = varType v
    n <- indexSetSize idxTy
    emitLoop NoName Fwd n $ \i -> do
      idx <- intToIndex idxTy i
      ai  <- toImpExpr mempty (Nothing, App atom idx)
      di  <- destGet dest i
      rec di ai
  (DRef r, Var v) -> case varType v of
    BaseTy _  -> f (IVar r) (fromScalarAtom atom)
    _         -> error $ "Type error"
  (_, Con con) -> case (dest, con) of
    (DRef r     , Lit _        ) -> f (IVar r) (fromScalarAtom atom)
    (DPair ld rd, PairCon la ra) -> rec ld la >> rec rd ra
    (DUnit      , UnitCon      ) -> return () -- We could call f in here as well I guess...
    (DCoerce _ d, Coerce _ a   ) -> rec d a
    (_          , SumCon _ _ _ ) -> error "Not implemented"
    _                            -> unreachable
  _ -> unreachable
  where
    rec x y = zipWithDest x y f
    unreachable = error $ "Not an imp atom, or mismatched dest: " ++ show dest ++ ", and " ++ show atom

copyAtom :: Dest -> Atom -> ImpM ()
copyAtom dest src = zipWithDest dest src store

zeroDest :: Dest -> ImpM ()
zeroDest dest = traverse_ (initializeZero . IVar) dest
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
  let vs = toList dest
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
  IOffset e i t -> do
    IRefType (TabTy _ _) <- checkIExpr e
    checkInt i
    return $ Just $ IRefType $ t

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

    checkBinOp :: (ScalarBaseType -> BaseType) -> ScalarBinOp -> IType -> IType -> ImpCheckM IType
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
