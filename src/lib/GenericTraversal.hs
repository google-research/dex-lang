
-- Copyright 2021 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module GenericTraversal
  ( GenericTraverser (..), GenericallyTraversableE (..)
  , GenericTraverserM (..), liftGenericTraverserM
  , traverseExprDefault, traverseAtomDefault
  , traverseDeclNest, traverseBlock, traverseLamBinder ) where

import Control.Monad
import Control.Monad.State.Class

import Name
import Err
import Builder
import Syntax
import MTL1
import LabeledItems
import Util (onSndM)

liftGenericTraverserM :: EnvReader m => s n -> GenericTraverserM s n n a -> m n (a, s n)
liftGenericTraverserM s m =
  liftBuilder $ runStateT1 (runSubstReaderT idSubst $ runGenericTraverserM' m) s
{-# INLINE liftGenericTraverserM #-}

newtype GenericTraverserM s i o a =
  GenericTraverserM
    { runGenericTraverserM' :: SubstReaderT AtomSubstVal (StateT1 s BuilderM) i o a }
    deriving ( Functor, Applicative, Monad, SubstReader AtomSubstVal, Builder, ScopableBuilder
             , EnvReader, ScopeReader, EnvExtender, MonadFail, Fallible, MonadState (s o))

class (SinkableE s, HoistableState s) => GenericTraverser s where
  traverseExpr :: Emits o => Expr i -> GenericTraverserM s i o (Expr o)
  traverseExpr = traverseExprDefault

  traverseInlineExpr :: Emits o => Expr i -> GenericTraverserM s i o (Either (Atom o) (Expr o))
  traverseInlineExpr e = Right <$> traverseExpr e

  traverseAtom :: Atom i -> GenericTraverserM s i o (Atom o)
  traverseAtom = traverseAtomDefault

traverseExprDefault :: Emits o => GenericTraverser s => Expr i -> GenericTraverserM s i o (Expr o)
traverseExprDefault expr = confuseGHC >>= \_ -> case expr of
  App g xs -> App <$> tge g <*> mapM tge xs
  TabApp g xs -> TabApp <$> tge g <*> mapM tge xs
  Atom x  -> Atom <$> tge x
  Op  op  -> Op   <$> mapM tge op
  Hof hof -> Hof  <$> mapM tge hof
  Case scrut alts resultTy effs ->
    Case <$> tge scrut <*> mapM traverseAlt alts <*> tge resultTy <*> substM effs
  Handle hndName args body ->
    Handle <$> substM hndName <*> mapM tge args <*> tge body

traverseAtomDefault :: GenericTraverser s => Atom i -> GenericTraverserM s i o (Atom o)
traverseAtomDefault atom = confuseGHC >>= \_ -> case atom of
  Var _ -> substM atom
  Lam (LamExpr b body) -> traverseLamBinder b \b' -> Lam . LamExpr b' <$> tge body
  Pi (PiType (PiBinder b ty arr) eff resultTy) -> do
    ty' <- tge ty
    withFreshPiBinder (getNameHint b) (PiBinding arr ty') \b' -> do
      extendRenamer (b@>binderName b') $
        Pi <$> (PiType b' <$> substM eff <*> tge resultTy)
  TabLam (TabLamExpr (b:>ty) body) -> do
    ty' <- tge ty
    let hint = getNameHint b
    withFreshBinder hint ty' \b' -> do
      extendRenamer (b@>binderName b') do
        body' <- tge body
        return $ TabLam $ TabLamExpr (b':>ty') body'
  TabPi (TabPiType (b:>ty) resultTy) -> do
    ty' <- tge ty
    withFreshBinder (getNameHint b) ty' \b' -> do
      extendRenamer (b@>binderName b') $
        TabPi <$> (TabPiType (b':>ty') <$> tge resultTy)
  Con con -> Con <$> mapM tge con
  TC  tc  -> TC  <$> mapM tge tc
  Eff _   -> substM atom
  TypeCon sn dataDefName params ->
    TypeCon sn <$> substM dataDefName <*> tge params
  DictCon dictExpr -> DictCon <$> tge dictExpr
  DictTy (DictType sn cn params) ->
    DictTy <$> (DictType sn <$> substM cn <*> mapM tge params)
  LabeledRow elems -> LabeledRow <$> traverseGenericE elems
  RecordTy elems -> RecordTy <$> traverseGenericE elems
  VariantTy ext -> VariantTy <$> traverseExtLabeledItems ext
  ProjectElt _ _ -> substM atom
  DepPairTy dty -> DepPairTy <$> tge dty
  DepPair l r dty -> DepPair <$> tge l <*> tge r <*> tge dty
  ACase _ _ _ -> nyi
  DepPairRef _ _ _ -> nyi
  BoxedRef _ -> nyi
  where nyi = error $ "not implemented: " ++ pprint atom

traverseExtLabeledItems :: GenericTraverser s => ExtLabeledItems (Atom i) (AtomName i)
                        -> GenericTraverserM s i o (ExtLabeledItems (Atom o) (AtomName o))
traverseExtLabeledItems (Ext items rest) = do
  items' <- mapM tge items
  rest' <- flip traverse rest \r -> substM (Var r) >>= \case
    Var r' -> return r'
    _ -> error "Not implemented"
  return $ Ext items' rest'

tge :: (GenericallyTraversableE e, GenericTraverser s)
    => e i -> GenericTraverserM s i o (e o)
tge = traverseGenericE

class GenericallyTraversableE (e::E) where
  traverseGenericE :: GenericTraverser s => e i -> GenericTraverserM s i o (e o)

instance GenericallyTraversableE Atom where
  traverseGenericE = traverseAtom

instance GenericallyTraversableE Block where
  traverseGenericE (Block _ decls result) = do
    buildBlock $ traverseDeclNest decls $ traverseAtom result

instance GenericallyTraversableE FieldRowElems where
  traverseGenericE elems = do
    els' <- fromFieldRowElems <$> substM elems
    dropSubst $ fieldRowElemsFromList <$> forM els' \case
      StaticFields items  -> StaticFields <$> mapM tge items
      DynField  labVar ty -> DynField labVar <$> tge ty
      DynFields rowVar    -> return $ DynFields rowVar

instance GenericallyTraversableE DataDefParams where
  traverseGenericE (DataDefParams params) =
    DataDefParams <$> mapM (onSndM tge) params

instance GenericallyTraversableE DepPairType where
  traverseGenericE (DepPairType (b:>lty) rty) = do
    lty' <- tge lty
    withFreshBinder (getNameHint b) lty' \b' -> do
      extendRenamer (b@>binderName b') $ DepPairType (b':>lty') <$> tge rty

instance GenericallyTraversableE IxType where
  traverseGenericE (IxType ty dict) = IxType <$> tge ty <*> tge dict

instance GenericallyTraversableE DictExpr where
  traverseGenericE e = confuseGHC >>= \_ -> case e of
    InstanceDict v args -> InstanceDict <$> substM v <*> mapM tge args
    InstantiatedGiven given args -> InstantiatedGiven <$> tge given <*> mapM tge args
    SuperclassProj subclass i -> SuperclassProj <$> tge subclass <*> pure i
    IxFin n ->  IxFin <$> tge n

instance (GenericallyTraversableE e1, GenericallyTraversableE e2) =>
  (GenericallyTraversableE (EitherE e1 e2)) where
  traverseGenericE ( LeftE e) =  LeftE <$> tge e
  traverseGenericE (RightE e) = RightE <$> tge e

traverseBlock
  :: (GenericTraverser s, Emits o)
  => Block i -> GenericTraverserM s i o (Atom o)
traverseBlock (Block _ decls result) = traverseDeclNest decls $ traverseAtom result

traverseDeclNest
  :: (GenericTraverser s, Emits o)
  => Nest Decl i i'
  -> (forall o'. (Emits o', Ext o o') => GenericTraverserM s i' o' (e o'))
  -> GenericTraverserM s i o (e o)
traverseDeclNest decls cont = do
  s <- getSubst
  s' <- traverseDeclNestS s decls
  withSubst s' cont
{-# INLINE traverseDeclNest #-}

traverseDeclNestS :: (GenericTraverser s, Emits o)
                  => Subst AtomSubstVal l o -> Nest Decl l i'
                  -> GenericTraverserM s i o (Subst AtomSubstVal i' o)
traverseDeclNestS !s = \case
  Empty -> return s
  Nest (Let b (DeclBinding ann _ expr)) rest -> do
    expr' <- withSubst s $ traverseInlineExpr expr
    sExt <- case expr' of
      Left a  -> return $ b @> SubstVal a
      Right e -> (b @>) . Rename <$> emitDecl (getNameHint b) ann e
    traverseDeclNestS (s <>> sExt) rest

traverseAlt
  :: GenericTraverser s
  => Alt i
  -> GenericTraverserM s i o (Alt o)
traverseAlt (Abs (b:>ty) body) = do
  ty' <- tge ty
  buildAbs (getNameHint b) ty' \v -> extendRenamer (b@>v) $ tge body

traverseLamBinder
  :: GenericTraverser s
  => LamBinder i i'
  -> (forall o'. DExt o o' => LamBinder o o' -> GenericTraverserM s i' o' a)
  -> GenericTraverserM s i o a
traverseLamBinder (LamBinder b ty arr eff) cont = do
  ty' <- tge ty
  let hint = getNameHint b
  effAbs <- withFreshBinder hint ty' \b' ->
    extendRenamer (b@>binderName b') do
      Abs (b':>ty') <$> substM eff
  withFreshLamBinder hint (LamBinding arr ty') effAbs \b' -> do
    extendRenamer (b@>binderName b') $ cont b'

-- See Note [Confuse GHC] from Simplify.hs
confuseGHC :: EnvReader m => m n (DistinctEvidence n)
confuseGHC = getDistinct
{-# INLINE confuseGHC #-}
