{-# LANGUAGE FlexibleContexts #-}

module DeShadow (deShadowPass) where

import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.Except hiding (Except)

import Env
import Record
import Syntax
import Pass
import Fresh
import PPrint
import Cat

type DeShadowM a = ReaderT DeShadowEnv (FreshRT (Either Err)) a
type DeShadowCat a = WriterT [DeclP Ann]
                       (CatT (DeShadowEnv, FreshScope)
                          (Either Err)) a
type DeShadowEnv = (Env Var, Env Type)
type Ann = Maybe Type

deShadowPass :: UTopDecl -> TopPass (DeShadowEnv, FreshScope) (TopDeclP Ann)
deShadowPass decl = case decl of
  UTopDecl decl -> do ((), decls) <- catToTop $ deShadowDecl decl
                      return $ case decls of
                        [decl'] ->  TopDecl decl'
                        [] -> EvalCmd NoOp
  UEvalCmd NoOp -> return (EvalCmd NoOp)
  UEvalCmd (Command cmd expr) -> do
    expr' <- deShadowTop expr
    case cmd of Passes -> writeOutText $ "\n\nDeshadowed\n" ++ show expr'
                _ -> return ()
    return $ EvalCmd (Command cmd expr')
  where
    deShadowTop :: UExpr -> TopPass (DeShadowEnv, FreshScope) (ExprP Ann)
    deShadowTop expr = do
      (env, scope) <- getEnv
      liftEither $ runFreshRT (runReaderT (deShadowExpr expr) env) scope

deShadowExpr :: UExpr -> DeShadowM (ExprP Ann)
deShadowExpr expr = case expr of
  ULit x -> return (Lit x)
  UVar v -> asks $ Var . lookupSubst v . fst
  UPrimOp b args -> liftM (PrimOp b []) (traverse recur args)
  UDecls decls body ->
    withCat (mapM_ deShadowDecl decls) $ \() decls' -> do
      body' <- recur body
      return $ Decls decls' body'
  ULam p body ->
    withCat (deShadowPat p) $ \b decls -> do
      body' <- recur body
      return $ Lam b $ wrapDecls decls body'
  UApp fexpr arg -> liftM2 App (recur fexpr) (recur arg)
  UFor b body ->
    withCat (deShadowPat (RecLeaf b)) $ \b' decls -> do
      body' <- recur body
      return $ For b' $ wrapDecls decls body'
  UGet e v -> liftM2 Get (recur e) (recur v)
  URecCon r -> liftM RecCon $ traverse recur r
  UTabCon xs -> liftM (TabCon 0 unitTy) (mapM recur xs)
  UAnnot body ty -> liftM2 Annot (recur body) (deShadowType ty)
  USrcAnnot e pos -> liftM (flip SrcAnnot pos) (recur e)
  where recur = deShadowExpr
        deShadowAnnot b = fmap (fmap deShadowType) b

deShadowDecl :: UDecl -> DeShadowCat ()
deShadowDecl (ULet p bound) = do
  bound' <- toCat $ deShadowExpr bound
  (b, decls) <- captureW $ deShadowPat p
  tell $ Let b bound' : decls
deShadowDecl (UUnpack b tv bound) = do
  bound' <- toCat $ deShadowExpr bound
  tv' <- looks $ rename tv . snd
  extend (asSnd (tv @> TypeVar tv'), tv'@>())
  (b', decls) <- captureW $ deShadowPat (RecLeaf b)
  tell $ Unpack b' tv' bound' : decls
deShadowDecl (UTAlias v ty) = do  -- TODO: deal with capture
  ty' <- toCat $ deShadowType ty
  extend (asSnd (v @> ty'), v@>())

deShadowPat :: RecTree UBinder -> DeShadowCat (BinderP Ann)
deShadowPat pat = do
  case pat of
    RecLeaf (UBind b) -> do
      b' <- freshBinder b
      return b'
    p -> do
      v <- looks $ genFresh "pat" . snd
      extend $ asSnd (v@>())
      traverse (getPatElt v) (recTreeNamed p)
      return (v:>Nothing)

getPatElt :: Var -> ([RecField], UBinder) -> DeShadowCat ()
getPatElt _ (_, IgnoreBind) = return ()
getPatElt v (fields, (UBind b)) = do
  b' <- freshBinder b
  tell $ [Let b' $ foldr (flip RecGet) (Var v) fields]

freshBinder :: BinderP Ann -> DeShadowCat (BinderP Ann)
freshBinder (v :> ty) = do
  shadowed <- looks $ (v `isin`) . snd
  if shadowed then throw RepeatedVarErr (pprint v)
              else return ()
  ty' <- toCat $ traverse deShadowType ty
  v' <- looks $ rename v . snd
  extend (asFst (v@>v'), v'@>())
  return (v' :> ty')

deShadowType :: Type -> DeShadowM Type
deShadowType ty = do
  subst <- asks $ snd
  return $ maybeSub (envLookup subst) ty

toCat :: DeShadowM a -> DeShadowCat a
toCat m = do
  (env, scope) <- look
  liftEither $ flip runFreshRT scope $ flip runReaderT env $ m

withCat :: DeShadowCat a -> (a -> [DeclP Ann] -> DeShadowM b) -> DeShadowM b
withCat m cont = do
  env <- ask
  scope <- askFresh
  ((ans, decls), (env', scope')) <- liftEither $
                                      flip runCatT (env, scope) $ runWriterT m
  extendR env' $ localFresh (<> scope') $ cont ans decls

catToTop :: DeShadowCat a -> TopPass (DeShadowEnv, FreshScope) (a, [DeclP Ann])
catToTop m = do
  env <- getEnv
  (ans, env') <- liftEither $ flip runCatT env $ runWriterT m
  putEnv env'
  return ans
