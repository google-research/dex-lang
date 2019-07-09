{-# LANGUAGE FlexibleContexts #-}

module Imp (impPass, checkImp) where

import Control.Monad.Reader
import Control.Monad.Except (liftEither)

import Syntax
import Env
import Type
import PPrint
import Pass
import Cat

data Dest = Buffer Var [Index]

impPass :: NTopDecl -> TopPass () ImpDecl
impPass decl = case decl of
  NTopDecl (NLet bs expr) -> return $ ImpTopLet bs' prog'
    where
      prog' = toImp (map asDest bs) expr
      bs' = map (fmap toImpType) bs
  NEvalCmd NoOp -> return noOpCmd
  -- seems to require type info. An alternative is to store an NDecl instead
  -- EvalCmd (Command cmd expr) ->
  where
    noOpCmd = ImpEvalCmd (const undefined) [] NoOp

toImp :: [Dest] -> NExpr -> ImpProg
toImp dests expr = case expr of
    NDecls [] body -> toImp dests body
    NDecls (decl:rest) final -> case decl of
       NLet bs bound -> wrapAllocs bs' $ bound' <> body'
         where
           bs' = map (fmap toImpType) bs
           bound' = toImp (map asDest bs) bound
           body'  = toImp dests (NDecls rest final)
    -- NFor b e -> refreshBindersR [b] $ \[b'] -> liftM (NFor b') (nSubst e)
    NPrimOp b _ xs -> ImpProg [writeBuiltin b dest (map toImpAtom xs)]
      where [dest] = dests
    NAtoms xs -> ImpProg $ zipWith copy dests (map toImpAtom xs)

toImpAtom :: NAtom -> IExpr
toImpAtom atom = case atom of
  NLit x -> ILit x
  NVar v -> IVar v
  NGet e i -> IGet (toImpAtom e) (toImpAtom i)

toImpType :: NType -> IType
toImpType ty = case ty of
  NBaseType b -> IType b []
  NTabType a b -> addIdx (typeToSize a) (toImpType b)

addIdx :: Size -> IType -> IType
addIdx n (IType ty shape) = IType ty (n : shape)

typeToSize :: NType -> IExpr
typeToSize (NTypeVar v) = IVar v
typeToSize (NIdxSetLit n) = ILit (IntLit n)

asDest :: NBinder -> Dest
asDest (v:>_) = Buffer v []

wrapAllocs :: [IBinder] -> ImpProg -> ImpProg
wrapAllocs [] prog = prog
wrapAllocs (b:bs) prog = ImpProg [Alloc b (wrapAllocs bs prog)]

copy :: Dest -> IExpr -> Statement
copy (Buffer v idxs) x = Update v idxs Copy [x]

writeBuiltin :: Builtin -> Dest -> [IExpr] -> Statement
writeBuiltin b (Buffer name destIdxs) exprs = Update name destIdxs b exprs

intTy :: IType
intTy = IType IntType []

-- === type checking imp programs ===

type ImpCheckM a = Pass (Env IType) () a

checkImp :: ImpDecl -> TopPass (Env IType) ImpDecl
checkImp decl = decl <$ case decl of
  ImpTopLet binders prog -> do
    check binders prog
    putEnv $ bindFold binders
  ImpEvalCmd _ _ NoOp -> return ()
  ImpEvalCmd _ bs (Command _ prog) -> check bs prog
  where
    check :: [IBinder] -> ImpProg -> TopPass (Env IType) ()
    check bs prog = do
      env <- getEnv
      liftEither $ addContext (pprint prog) $
          evalPass (env <> bindFold bs) () mempty (checkProg prog)

checkProg :: ImpProg -> ImpCheckM ()
checkProg (ImpProg statements) = mapM_ checkStatement statements

lookupVar :: Var -> ImpCheckM IType
lookupVar v = asks $ (! v)

checkStatement :: Statement -> ImpCheckM ()
checkStatement statement = case statement of
  Alloc b body -> do
    env <- ask
    if binderVar b `isin` env then throw CompilerErr "Shadows!"
                              else return ()
    extendR (bind b) (checkProg body)
  Update v idxs Copy [expr] -> do
    mapM_ checkInt idxs
    IType b  shape  <- asks $ (! v)
    IType b' shape' <- impExprType expr
    assertEq b b' "Base type mismatch in copy"
    assertEq (drop (length idxs) shape) shape' "Dimension mismatch"
  Update v idxs builtin args -> do -- scalar builtins only
    argTys <- mapM impExprType args
    let BuiltinType _ inTys (BaseType b) = builtinType builtin
    zipWithM_ checkScalarTy inTys argTys
    IType b' shape  <- asks $ (! v)
    case drop (length idxs) shape of
      [] -> assertEq b b' "Base type mismatch in builtin application"
      _  -> throw CompilerErr "Writing to non-scalar buffer"
  Loop i size block -> extendR (i @> intTy) $ do
                          checkInt size
                          checkProg block

impExprType :: IExpr -> ImpCheckM IType
impExprType expr = case expr of
  ILit val -> return $ IType (litType val) []
  IVar v   -> asks $ (! v)
  IGet e i -> do IType b (_:shape) <- impExprType e
                 checkInt i
                 return $ IType b shape

checkScalarTy :: Type -> IType -> ImpCheckM ()
checkScalarTy (BaseType b) (IType b' []) | b == b'= return ()
checkScalarTy ty ity = throw CompilerErr $ "Wrong types. Expected:" ++ pprint ty
                                                         ++ " Got " ++ pprint ity

checkInt :: IExpr -> ImpCheckM ()
checkInt (IVar v) = do ty <- lookupVar v
                       assertEq ty intTy "Not a valid int"
checkInt (ILit (IntLit _)) = return ()
checkInt expr = throw CompilerErr $ "Not an int: " ++ pprint expr
