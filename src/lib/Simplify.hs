-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleContexts #-}

module Simplify (simplifyModule, evalSimplified) where

import Control.Monad
import Control.Monad.Identity
import Control.Monad.Reader
import Data.Foldable (toList)
import Data.Functor
import Data.List (partition)

import Autodiff
import Env
import Syntax
import Cat
import Embed
import Type
import PPrint

type SimplifyM = SubstEmbedT Identity

simplifyModule :: TopEnv -> Module -> Module
simplifyModule scope (Module Core decls bindings) = do
  let simpDecls = snd $ snd $ runSubstEmbed (simplifyDecls decls) scope
  let isAtomDecl decl = case decl of Let _ _ (Atom _) -> True; _ -> False
  let (declsDone, declsNotDone) = partition isAtomDecl $ toList simpDecls
  let bindings' = foldMap boundVars declsDone
  dceModule $ Module Simp (toNest declsNotDone) (bindings <> bindings')
simplifyModule _ (Module ir _ _) = error $ "Expected Core, got: " ++ show ir

evalSimplified :: Monad m => Module -> (Block -> m Atom) -> m Module
evalSimplified (Module Simp Empty bindings) _ =
  return $ Module Evaluated Empty bindings
evalSimplified (Module Simp decls bindings) evalBlock = do
  let localVars = filter (not . isGlobal) $ bindingsAsVars $ freeVars bindings
  let block = Block decls $ Atom $ mkConsList $ map Var localVars
  vals <- (ignoreExcept . fromConsList) <$> evalBlock block
  return $ Module Evaluated Empty $
    scopelessSubst (newEnv localVars vals) bindings
evalSimplified (Module _ _ _) _ =
  error "Not a simplified module"

simplifyDecls :: Nest Decl -> SimplifyM SubstEnv
simplifyDecls Empty = return mempty
simplifyDecls (Nest decl rest) = do
  substEnv <- simplifyDecl decl
  substEnv' <- extendR substEnv $ simplifyDecls rest
  return (substEnv <> substEnv')

simplifyDecl :: Decl -> SimplifyM SubstEnv
simplifyDecl (Let ann b expr) = do
  x <- simplifyExpr expr
  let name = binderNameHint b
  if isGlobal (name:>())
    then emitTo name ann (Atom x) $> mempty
    else return $ b @> x
simplifyDecl (Unpack bs expr) = do
  x <- simplifyExpr expr
  xs <- case x of
    DataCon _ _ _ xs -> return xs
    Record items -> return $ toList items
    _ -> emitUnpack $ Atom x
  return $ newEnv bs xs

simplifyBlock :: Block -> SimplifyM Atom
simplifyBlock (Block decls result) = do
  substEnv <- simplifyDecls decls
  extendR substEnv $ simplifyExpr result

simplifyAtom :: Atom -> SimplifyM Atom
simplifyAtom atom = case atom of
  Var v -> do
    substEnv <- ask
    scope <- getScope
    case envLookup substEnv v of
      Just x -> return $ deShadow x scope
      Nothing -> case envLookup scope v of
        Just (_, info) -> case info of
          LetBound _ (Atom x) -> dropSub $ simplifyAtom x
          _ -> substEmbedR atom
        _   -> substEmbedR atom
  -- We don't simplify body of lam because we'll beta-reduce it soon.
  Lam _ -> substEmbedR atom
  Pi  _ -> substEmbedR atom
  Con (AnyValue (TabTy v b)) -> TabValA v <$> mkAny b
  Con (AnyValue (PairTy a b))-> PairVal <$> mkAny a <*> mkAny b
  Con (AnyValue (SumTy l r)) -> do
    Con <$> (SumCon <$> mkAny (TC $ BaseType $ Scalar BoolType) <*> mkAny l <*> mkAny r)
  Con con -> Con <$> mapM simplifyAtom con
  TC tc -> TC <$> mapM substEmbedR tc
  Eff eff -> Eff <$> substEmbedR eff
  TypeCon def params          -> TypeCon def <$> substEmbedR params
  DataCon def params con args -> DataCon def <$> substEmbedR params
                                             <*> pure con <*> mapM simplifyAtom args
  Record items -> Record <$> mapM simplifyAtom items
  RecordTy items -> RecordTy <$> substEmbedR items
  Variant types label i value -> Variant <$>
    substEmbedR types <*> pure label <*> pure i <*> simplifyAtom value
  VariantTy items -> VariantTy <$> substEmbedR items
  where mkAny t = Con . AnyValue <$> substEmbedR t >>= simplifyAtom

-- `Nothing` is equivalent to `Just return` but we can pattern-match on it
type Reconstruct m a = Maybe (a -> m a)

simplifyLam :: Atom -> SimplifyM (Atom, Reconstruct SimplifyM Atom)
simplifyLam = simplifyLams 1

simplifyBinaryLam :: Atom -> SimplifyM (Atom, Reconstruct SimplifyM Atom)
simplifyBinaryLam = simplifyLams 2

-- Unlike `substEmbedR`, this simplifies under the binder too.
simplifyLams :: Int -> Atom -> SimplifyM (Atom, Reconstruct SimplifyM Atom)
simplifyLams numArgs lam = do
  lam' <- substEmbedR lam
  dropSub $ simplifyLams' numArgs mempty $ Block Empty $ Atom lam'

simplifyLams' :: Int -> Scope -> Block
              -> SimplifyM (Atom, Reconstruct SimplifyM Atom)
simplifyLams' 0 scope block = do
  topScope <- getScope
  if isData topScope (getType block)
    then liftM (,Nothing) $ simplifyBlock block
    else do
      (block', (scope', decls)) <- embedScoped $ simplifyBlock block
      mapM_ emitDecl decls
      let (dataVals, recon) = separateDataComponent (scope <> scope') block'
      return (dataVals, Just recon)
simplifyLams' n scope (Block Empty (Atom (Lam (Abs b (arr, body))))) = do
  b' <- mapM substEmbedR b
  buildLamAux b' (\x -> extendR (b@>x) $ substEmbedR arr) $ \x@(Var v) -> do
    let scope' = scope <> v @> (varType v, LamBound (void arr))
    extendR (b@>x) $ simplifyLams' (n-1) scope' body
simplifyLams' _ _ _ = error "Expected n lambdas"

separateDataComponent :: MonadEmbed m => Scope -> Atom -> (Atom, Atom -> m Atom)
separateDataComponent localVars atom = (mkConsList $ map Var vs, recon)
  where
    vs = bindingsAsVars $ localVars `envIntersect` freeVars atom
    recon :: MonadEmbed m => Atom -> m Atom
    recon xs = do
      xs' <- unpackConsList xs
      scope <- getScope
      return $ subst (newEnv vs xs', scope) atom

applyRecon :: MonadEmbed m => Maybe (Atom -> m Atom) -> Atom -> m Atom
applyRecon Nothing x = return x
applyRecon (Just f) x = f x

simplifyExpr :: Expr -> SimplifyM Atom
simplifyExpr expr = case expr of
  App f x -> do
    x' <- simplifyAtom x
    f' <- simplifyAtom f
    case f' of
      Lam (Abs b (_, body)) ->
        dropSub $ extendR (b@>x') $ simplifyBlock body
      DataCon def params con xs -> return $ DataCon def params' con xs'
         where DataDef _ paramBs _ = def
               (params', xs') = splitAt (length paramBs) $ params ++ xs ++ [x']
      _ -> emit $ App f' x'
  Op  op  -> mapM simplifyAtom op >>= simplifyOp
  Hof hof -> simplifyHof hof
  Atom x  -> simplifyAtom x
  Case e alts resultTy -> do
    e' <- simplifyAtom e
    resultTy' <- substEmbedR resultTy
    case e' of
      DataCon _ _ con args -> do
        let Abs bs body = alts !! con
        extendR (newEnv bs args) $ simplifyBlock body
      _ -> do
        alts' <- forM alts $ \(Abs bs body) -> do
          bs' <-  mapM (mapM substEmbedR) bs
          buildNAbs bs' $ \xs -> extendR (newEnv bs' xs) $ simplifyBlock body
        emit $ Case e' alts' resultTy'

-- TODO: come up with a coherent strategy for ordering these various reductions
simplifyOp :: Op -> SimplifyM Atom
simplifyOp op = case op of
  Fst (PairVal x _) -> return x
  Snd (PairVal _ y) -> return y
  SumGet (SumVal _ l r) left -> return $ if left then l else r
  SumTag (SumVal s _ _) -> return $ s
  _ -> emitOp op

simplifyHof :: Hof -> SimplifyM Atom
simplifyHof hof = case hof of
  For d lam -> do
    ~(lam'@(Lam (Abs i _)), recon) <- simplifyLam lam
    ans <- emit $ Hof $ For d lam'
    case recon of
      Nothing -> return ans
      Just f  -> buildLam i TabArrow $ \i' -> app ans i' >>= f
  Tile d fT fS -> do
    ~(fT', Nothing) <- simplifyLam fT
    ~(fS', Nothing) <- simplifyLam fS
    emit $ Hof $ Tile d fT' fS'
  While cond body -> do
    ~(cond', Nothing) <- simplifyLam cond
    ~(body', Nothing) <- simplifyLam body
    emit $ Hof $ While cond' body'
  Linearize lam -> do
    ~(lam', Nothing) <- simplifyLam lam
    scope <- getScope
    -- TODO: simplify the result to remove functions introduced by linearization
    return $ linearize scope lam'
  Transpose lam -> do
    ~(lam', Nothing) <- simplifyLam lam
    scope <- getScope
    return $ transposeMap scope lam'
  RunReader r lam -> do
    r' <- simplifyAtom r
    ~(lam', recon) <- simplifyBinaryLam lam
    applyRecon recon =<< (emit $ Hof $ RunReader r' lam')
  RunWriter lam -> do
    ~(lam', recon) <- simplifyBinaryLam lam
    (ans, w) <- fromPair =<< (emit $ Hof $ RunWriter lam')
    ans' <- applyRecon recon ans
    return $ PairVal ans' w
  RunState s lam -> do
    s' <- simplifyAtom s
    ~(lam', recon) <- simplifyBinaryLam lam
    (ans, sOut) <- fromPair =<< (emit $ Hof $ RunState s' lam')
    ans' <- applyRecon recon ans
    return $ PairVal ans' sOut
  SumCase c lBody rBody -> do
    ~(lBody', Nothing) <- simplifyLam lBody
    ~(rBody', Nothing) <- simplifyLam rBody
    l <- projApp lBody' True
    r <- projApp rBody' False
    isLeft <- simplRec $ Op $ SumTag c
    emitOp $ Select isLeft l r
    where
      simplRec :: Expr -> SimplifyM Atom
      simplRec = dropSub . simplifyExpr
      projApp f isLeft = do
        cComp <- simplRec $ Op $ SumGet c isLeft
        simplRec $ App f cComp

dropSub :: SimplifyM a -> SimplifyM a
dropSub m = local mempty m
