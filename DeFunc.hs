module DeFunc (deFuncPass) where

import Syntax
import Env
import Record
import Util
import Type
import Fresh
import Pass
import PPrint

import Data.Foldable (toList)
import Control.Monad
import Control.Monad.State (put, gets)
import Control.Monad.Writer (tell)
import Control.Monad.Reader (Reader, runReader, local, ask, asks)

type DFEnv = FullEnv TypedDFVal (Maybe Type)

-- type is post-defunctionalization (TODO: change that. tracking pre-types
-- is simpler and we can get easily derive the post-type)
type TypedDFVal = (DFVal, Type)

data DFVal = DFNil
           | LamVal Pat DFEnv Expr
           | TLamVal [TBinder] DFEnv Expr
           | RecVal (Record DFVal)

type DeFuncM a = MonadPass DFEnv () a

deFuncPass :: Decl -> TopMonadPass DFEnv Decl
deFuncPass decl = case decl of
  TopLet (v,ty) expr -> do
    (val, expr') <- deFuncTop expr
    let ty' = deFuncType val ty
    put $ newFullEnv [(v, (val,ty'))] []
    return $ TopLet (v, ty') expr'
  TopUnpack (v,ty) iv expr -> do
    (val, expr') <- deFuncTop expr
    let ty' = deFuncType val ty
    put $ newFullEnv [(v, (val,ty'))] [(iv,Nothing)]
    return $ TopUnpack (v, ty') iv expr'
  EvalCmd NoOp -> put mempty >> return (EvalCmd NoOp)
  EvalCmd (Command cmd expr) -> do
    (val, expr') <- deFuncTop expr
    put mempty
    case cmd of Passes  -> do tell ["\n\nDefunctionalized\n" ++ pprint expr']
                _ -> return ()
    return $ EvalCmd (Command cmd expr')

  where
    deFuncTop :: Expr -> TopMonadPass DFEnv (DFVal, Expr)
    deFuncTop expr = liftTopPass () (deFuncExpr expr)

deFuncExpr :: Expr -> DeFuncM (DFVal, Expr)
deFuncExpr expr = case expr of
  Var v     -> do val <- asks $ fst . (! v) . lEnv
                  return (val, Var v)
  Lit l     -> return (DFNil, Lit l)
  Let p bound body -> do (x,  bound') <- recur bound
                         (p', xs) <- bindPat p x
                         (ans, body') <- recurWith xs body
                         return (ans, Let p' bound' body')
  Lam p body -> do env <- asks $ capturedEnv body
                   return (LamVal p env body,  envTupCon env)
  App (Builtin b) arg -> do (_, arg') <- recur arg
                            return (DFNil, App (Builtin b) arg')
  App (TApp (Builtin Fold) ts) arg -> deFuncFold ts arg
  App fexpr arg -> do fexpr' <- recur fexpr
                      arg'   <- recur arg
                      deFuncApp fexpr' arg'
  For (v,ty) body -> do ty' <- subTy ty
                        (ans, body') <- recurWith [(v, (DFNil, ty'))] body
                        return (ans, For (v,ty') body')
  Get e ie -> do (ans, e') <- recur e
                 return (ans, Get e' ie)
  RecCon r -> do r' <- traverse recur r
                 return (RecVal (fmap fst r'), RecCon (fmap snd r'))
  TLam b body -> do env <- asks $ capturedEnv body
                    return (TLamVal b env body, envTupCon env)
  TApp fexpr ts -> do
    (TLamVal bs env body, fexpr') <- recur fexpr
    ts' <- traverse subTy ts
    let env' = setTEnv (addVs (zip (map fst bs) (map Just ts'))) env
    (ans, body') <- local (const env') (deFuncExpr body)
    let expr'= case envPat env of
                 Nothing -> body'
                 Just p -> Let p fexpr' body'
    return (ans, expr')
  Unpack b tv bound body -> do
    (val, bound') <- recur bound
    let updateT = setTEnv (addV (tv, Nothing))
    (b', valTy) <- local updateT (deFuncBinder (b,val))
    let updateL = setLEnv (addV valTy)
    (ans, body') <- local (updateL . updateT) (deFuncExpr body)
    return (ans, Unpack b' tv bound' body')

  where recur = deFuncExpr
        recurWith  xs = local (setLEnv $ addVs xs) . deFuncExpr

capturedEnv :: Expr -> FullEnv a b -> FullEnv a b
capturedEnv expr env = setLEnv (envSubset (freeLVars expr)) env

subTy :: Type -> DeFuncM Type
subTy ty = do { tenv <- asks tEnv; return $ maybeSub (tenv !) ty }

bindPat :: Pat -> DFVal -> DeFuncM (Pat, RecTree (Var, TypedDFVal))
bindPat pat val = do
  zipped <- traverse deFuncBinder (recTreeZip pat val)
  return (fmap fst zipped, fmap snd zipped)

deFuncBinder :: (Binder, DFVal) -> DeFuncM (Binder, (Var, TypedDFVal))
deFuncBinder ((v, ty), val) = do ty' <- liftM (deFuncType val) (subTy ty)
                                 return ((v, ty'), (v, (val, ty')))

deFuncType :: DFVal -> Type -> Type
deFuncType (RecVal r) (RecType r') = RecType $ recZipWith deFuncType r r'
deFuncType DFNil t = t
deFuncType (LamVal p env _) _   = RecType $ Tup (envTypes env)
deFuncType (TLamVal _ env _)  _ = RecType $ Tup (envTypes env)

posPat = RecTree . Tup
lhsPair x y = posPat [x, y]
rhsPair x y = RecCon (Tup [x, y])

envTypes :: DFEnv -> [Type]
envTypes env = map snd $ toList (lEnv env)

envPat :: DFEnv -> Maybe Pat
envPat env = case envPairs (lEnv env) of
  [] -> Nothing
  pairs -> Just $ RecTree $ Tup [RecLeaf (v,ty) | (v,(_,ty)) <- pairs]

envTupCon :: DFEnv -> Expr
envTupCon env = RecCon $ Tup (map Var $ envVars (lEnv env))

deFuncApp :: (DFVal, Expr) -> (DFVal, Expr) -> DeFuncM (DFVal, Expr)
deFuncApp (LamVal p env body, fexpr) (argVal, arg') = do
  (p', argVals) <- local (const env) (bindPat p argVal)
  let env' = setLEnv (addVs argVals) env
  (ans, body') <- local (const env') (deFuncExpr body)
  let expr' = case envPat env of
                Nothing -> Let p' arg' body'
                Just ep -> Let (lhsPair ep p') (rhsPair fexpr arg') body'
  return (ans, expr')

-- TODO: check/fail higher order case
deFuncFold :: [Type] -> Expr -> DeFuncM (DFVal, Expr)
deFuncFold ts (RecCon (Tup [Lam p body, x0, xs])) = do
  ts' <- traverse subTy ts
  (x0Val, x0') <- deFuncExpr x0
  (xsVal, xs') <- deFuncExpr xs
  (p', bindings) <- bindPat p (RecVal (Tup [x0Val, xsVal]))
  (ans, body') <- local (setLEnv $ addVs bindings) (deFuncExpr body)
  return (ans, App (TApp (Builtin Fold) ts') (RecCon (Tup [Lam p' body', x0', xs'])))

instance RecTreeZip DFVal where
  recTreeZip (RecTree r) (RecVal r') = RecTree (recZipWith recTreeZip r r')
  recTreeZip (RecLeaf x) x' = RecLeaf (x, x')
