module DeShadow (deShadowPass) where

import Control.Monad.Reader

import Env
import Syntax
import Pass
import Fresh
import PPrint
import Util (repeated)

type DeShadowM a = Pass FreshSubst () a

-- TODO: deshadow lexically scoped type variables

deShadowPass :: UDecl -> TopPass FreshSubst UDecl
deShadowPass decl = case decl of
  UTopLet b expr -> do checkTopShadow b
                       putEnv (newSubst (binderVars b))
                       liftM (UTopLet b) $ deShadowTop expr
  UTopUnpack b tv expr -> do checkTopShadow b
                             putEnv (newSubst (binderVars b))
                             liftM (UTopUnpack b tv) $ deShadowTop expr
  UEvalCmd NoOp -> return (UEvalCmd NoOp)
  UEvalCmd (Command cmd expr) -> do
    expr' <- deShadowTop expr
    case cmd of Passes -> writeOut $ "\n\nDeshadowed\n" ++ show expr'
                _ -> return ()
    return $ UEvalCmd (Command cmd expr')
  where
    deShadowTop :: UExpr -> TopPass FreshSubst UExpr
    deShadowTop expr = liftTopPass () mempty (deShadowExpr expr)

checkTopShadow :: UBinder -> TopPass FreshSubst ()
checkTopShadow b = do
  subst <- getEnv
  case binderVars b of
    [] -> return ()
    [v] | isFresh v subst -> return ()
        | otherwise -> throw RepeatedVarErr (pprint v)

deShadowExpr :: UExpr -> DeShadowM UExpr
deShadowExpr expr = case expr of
  ULit x -> return (ULit x)
  UVar v -> liftM UVar $ asks (getRenamed v)
  UBuiltin b -> return (UBuiltin b)
  ULet p bound body -> do
    bound' <- recur bound
    (p', scope) <- freshen p
    body' <- extendWith scope (recur body)
    return $ ULet p' bound' body'
  ULam p body -> do
    (p', scope) <- freshen p
    body' <- extendWith scope (recur body)
    return $ ULam p' body'
  UApp fexpr arg -> liftM2 UApp (recur fexpr) (recur arg)
  UFor b body -> do
    ([b'], scope) <- freshen [b]
    body' <- extendWith scope (recur body)
    return $ UFor b' body'
  UGet e v -> liftM2 UGet (recur e) (asks (getRenamed v))
  UUnpack b tv bound body -> do
    bound' <- recur bound
    ([b'], scope) <- freshen [b]
    body' <- extendWith scope (recur body)
    return $ UUnpack b' tv bound' body'
  URecCon r -> liftM URecCon $ traverse recur r
  -- TODO: deshadow type as well when we add scoped type vars
  UAnnot body ty -> liftM (flip UAnnot ty) (recur body)
  where recur = deShadowExpr

freshen :: Traversable f => f UBinder -> DeShadowM (f UBinder, FreshSubst)
freshen p = do checkRepeats p
               scope <- ask
               return $ freshenBinders scope p

checkRepeats :: Foldable f => f UBinder -> DeShadowM ()
checkRepeats bs = case repeated (foldMap binderVars bs) of
                    [] -> return ()
                    xs -> throw RepeatedVarErr (pprint xs)

