module DeShadow (deShadowPass) where

import Control.Monad.Reader
import Control.Monad.Except hiding (Except)

import Env
import Syntax
import Pass
import Fresh
import PPrint
import Util (repeated)

type DeShadowM a = ReaderT DeShadowEnv (FreshRT (Either Err)) a
type DeShadowEnv = FullEnv Var Var

deShadowPass :: UDecl -> TopPass FreshScope UDecl
deShadowPass decl = case decl of
  UTopLet b expr -> do
    mapM checkTopShadow (binderVars b)
    putEnv (foldMap newScope (binderVars b))
    liftM (UTopLet b) $ deShadowTop expr
  UTopUnpack b tv expr -> do
    mapM checkTopShadow (binderVars b)
    checkTopShadow tv
    putEnv (foldMap newScope (binderVars b))
    liftM (UTopUnpack b tv) $ deShadowTop expr
  UEvalCmd NoOp -> return (UEvalCmd NoOp)
  UEvalCmd (Command cmd expr) -> do
    expr' <- deShadowTop expr
    case cmd of Passes -> writeOut $ "\n\nDeshadowed\n" ++ show expr'
                _ -> return ()
    return $ UEvalCmd (Command cmd expr')
  where
    deShadowTop :: UExpr -> TopPass FreshScope UExpr
    deShadowTop expr = do
      scope <- getEnv
      liftEither $ runFreshRT (runReaderT (deShadowExpr expr) mempty) scope

checkTopShadow :: Var -> TopPass FreshScope ()
checkTopShadow v = do
  scope <- getEnv
  if isFresh v scope then return ()
                     else throw RepeatedVarErr (pprint v)

deShadowExpr :: UExpr -> DeShadowM UExpr
deShadowExpr expr = case expr of
  ULit x -> return (ULit x)
  UVar v -> liftM UVar (getLVar v)
  UBuiltin b -> return (UBuiltin b)
  ULet p bound body -> do
    bound' <- recur bound
    deShadowPat p $ \p' -> do
      body' <- recur body
      return $ ULet p' bound' body'
  ULam p body -> do
    deShadowPat p $ \p' -> do
      body' <- recur body
      return $ ULam p' body'
  UApp fexpr arg -> liftM2 UApp (recur fexpr) (recur arg)
  UFor b body -> do
    deShadowPat [b] $ \[b'] -> do
      body' <- recur body
      return $ UFor b' body'
  UGet e v -> liftM2 UGet (recur e) (getLVar v)
  UUnpack b tv bound body -> do
    bound' <- recur bound
    freshName tv $ \tv' ->
      extendWith (asTEnv (tv @> tv')) $
        deShadowPat [b] $ \[b'] -> do
          body' <- recur body
          return $ UUnpack b' tv' bound' body'
  URecCon r -> liftM URecCon $ traverse recur r
  UAnnot body ty -> liftM2 UAnnot (recur body) (deShadowType ty)
  where recur = deShadowExpr
        getLVar :: Var -> DeShadowM Var
        getLVar v = asks $ lookupSubst v . lEnv
        deShadowAnnot b = fmap (fmap deShadowType) b

deShadowPat :: Traversable f =>
               f UBinder -> (f UBinder -> DeShadowM a) -> DeShadowM a
deShadowPat pat cont = do
  checkRepeats pat
  pat' <- traverse (traverse (traverse deShadowType)) pat
  freshenBinders pat' $ \subst pat'' ->
    extendWith (asLEnv subst) $
      cont pat''

deShadowType :: Type -> DeShadowM Type
deShadowType ty = do
  subst <- asks $ tEnv
  let sub v = Just (TypeVar (lookupSubst v subst))
  return $ maybeSub sub ty

checkRepeats :: Foldable f => f UBinder -> DeShadowM ()
checkRepeats bs = case repeated (foldMap binderVars bs) of
                    [] -> return ()
                    xs -> throw RepeatedVarErr (pprint xs)
