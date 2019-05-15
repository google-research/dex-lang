module DeShadow (deShadowPass) where

import Syntax
import Pass
import Fresh
import PPrint
import Util (repeated)

import Data.Foldable
import Control.Monad.Reader

type DeShadowM a = Pass FreshSubst () a

deShadowPass :: UDecl -> TopPass FreshSubst UDecl
deShadowPass decl = case decl of
  UTopLet b expr -> do checkTopShadow b
                       putEnv (newSubst (fst b))
                       liftM (UTopLet b) $ deShadowTop expr
  UTopUnpack b expr -> do checkTopShadow b
                          putEnv (newSubst (fst b))
                          liftM (UTopUnpack b) $ deShadowTop expr
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
checkTopShadow (v,_) = do
  subst <- getEnv
  if isFresh v subst then return ()
                     else throw RepeatedVarErr (pprint v)

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
  UUnpack v bound body -> do
    bound' <- recur bound
    ([(v',_)], scope) <- freshen [(v,Nothing)]
    body' <- extendWith scope (recur body)
    return $ UUnpack v' bound' body'
  URecCon r -> liftM URecCon $ traverse recur r
  -- TODO: deshadow type as well when we add scoped type vars
  UAnnot body ty -> liftM (flip UAnnot ty) (recur body)
  where recur = deShadowExpr

freshen :: Traversable f => f UBinder -> DeShadowM (f UBinder, FreshSubst)
freshen p = do checkRepeats p
               scope <- ask
               let f (v, ann) = let (v', scope') = rename v scope
                                in ((v', ann), scope')
               let zipped = fmap f p
               return (fmap fst zipped, fold (fmap snd zipped))

checkRepeats :: Foldable f => f UBinder -> DeShadowM ()
checkRepeats bs = case repeated (map fst (toList bs)) of
                    [] -> return ()
                    xs -> throw RepeatedVarErr (pprint xs)
