module DeShadow (deShadowPass) where

import Control.Monad.Reader
import Control.Monad.Except hiding (Except)

import Env
import Record
import Syntax
import Pass
import Fresh
import PPrint
import Util (repeated)

type DeShadowM a = ReaderT DeShadowEnv (FreshRT (Either Err)) a
type DeShadowEnv = FullEnv Var Var
type Ann = Maybe Type

deShadowPass :: UDecl -> TopPass FreshScope (PDecl Ann)
deShadowPass decl = case decl of
  UTopLet b expr -> do
    mapM checkTopShadow (binderVars b)
    putEnv (foldMap newScope (binderVars b))
    liftM (TopLet b) $ deShadowTop expr
  UTopUnpack b tv expr -> do
    mapM checkTopShadow (binderVars b)
    checkTopShadow tv
    putEnv (foldMap newScope (binderVars b))
    liftM (TopUnpack b tv) $ deShadowTop expr
  UEvalCmd NoOp -> return (EvalCmd NoOp)
  UEvalCmd (Command cmd expr) -> do
    expr' <- deShadowTop expr
    case cmd of Passes -> writeOut $ "\n\nDeshadowed\n" ++ show expr'
                _ -> return ()
    return $ EvalCmd (Command cmd expr')
  where
    deShadowTop :: UExpr -> TopPass FreshScope (PExpr Ann)
    deShadowTop expr = do
      scope <- getEnv
      liftEither $ runFreshRT (runReaderT (deShadowExpr expr) mempty) scope

checkTopShadow :: Var -> TopPass FreshScope ()
checkTopShadow v = do
  scope <- getEnv
  if isFresh v scope then return ()
                     else throw RepeatedVarErr (pprint v)

deShadowExpr :: UExpr -> DeShadowM (PExpr Ann)
deShadowExpr expr = case expr of
  ULit x -> return (Lit x)
  UVar v -> liftM Var (getLVar v)
  UBuiltin b -> return (Builtin b)
  ULet p bound body -> do
    bound' <- recur bound
    (body', b) <- deShadowPat p (recur body)
    return $ Let b bound' body'
  ULam p body -> do
    (body', b) <- deShadowPat p (recur body)
    return $ Lam b body'
  UApp fexpr arg -> liftM2 App (recur fexpr) (recur arg)
  UFor b body -> do
    (body', b') <- deShadowPat (RecLeaf b) (recur body)
    return $ For b' body'
  UGet e v -> liftM2 Get (recur e) (getLVar v)
  UUnpack b tv bound body -> do
    bound' <- recur bound
    freshName tv $ \tv' ->
      extendWith (asTEnv (tv @> tv')) $ do
        (body', b') <- deShadowPat (RecLeaf b) (recur body)
        return $ Unpack b' tv' bound' body'
  URecCon r -> liftM RecCon $ traverse recur r
  UAnnot body ty -> liftM2 Annot (recur body) (deShadowType ty)
  where recur = deShadowExpr
        getLVar :: Var -> DeShadowM Var
        getLVar v = asks $ lookupSubst v . lEnv
        deShadowAnnot b = fmap (fmap deShadowType) b

deShadowPat :: RecTree (PBinder Ann) -> DeShadowM (PExpr Ann)
            -> DeShadowM (PExpr Ann, PBinder Ann)
deShadowPat pat cont = do
  checkRepeats pat
  pat' <- traverse (traverse (traverse deShadowType)) pat
  freshenBinders pat' $ \subst pat'' ->
    extendWith (asLEnv subst) $
      case pat'' of
        RecLeaf b -> do expr <- cont
                        return (expr, b)
        p -> freshName (rawName "pat") $ \v -> do
               expr <- cont
               let b = v %> Nothing
                   recGet fields = foldr (flip RecGet) (Var v) fields
                   addLet (fields, b') expr' = Let b' (recGet fields) expr'
               return (foldr addLet expr (recTreeNamed p), b)

deShadowType :: Type -> DeShadowM Type
deShadowType ty = do
  subst <- asks $ tEnv
  let sub v = Just (TypeVar (lookupSubst v subst))
  return $ maybeSub sub ty

checkRepeats :: Foldable f => f UBinder -> DeShadowM ()
checkRepeats bs = case repeated (foldMap binderVars bs) of
                    [] -> return ()
                    xs -> throw RepeatedVarErr (pprint xs)
