module DeFunc (deFuncPass) where

import Syntax
import Env
import Record
import Util

import Data.Foldable (toList)

deFuncPass :: Pass Expr Expr DFVal Type
deFuncPass = undefined

type DFEnv = FullEnv (DFVal, Type) Type

data DFVal = DFNil
           | LamVal (Pat ()) DFEnv Expr
           | TLamVal DFEnv Expr
           | RecVal (Record DFVal)

unitLit :: Expr
unitLit = RecCon emptyRecord

deFuncExpr :: DFEnv -> Expr -> (Expr, DFVal)
deFuncExpr env expr = case expr of
  Var v -> (expr, fst ((lEnv env) ! v))
  Lit _ -> (expr, DFNil)
  Builtin _ -> (expr, DFNil)
  Let p bound body ->
    let (bound', x) = recur bound
        (body', ans) = recurWith p x body
        p' = deFuncPat p
    in (Let p' bound' body', ans)
  -- TODO: only capture vars needed instead of full env
  Lam p body -> (RecCon $ posRecord envBVars, LamVal (deFuncPat p) env body)
  App fexpr arg ->
      let (fexpr', fVal  ) = recur fexpr
          (arg'  , argVal) = recur arg
      in case fVal of
        DFNil -> (App fexpr' arg', DFNil)
        LamVal p env' body ->
          let env'' = setLEnv (addBVars $ bindPat p argVal) env'
              (body', ans) = deFuncExpr env'' body
              expr' = Let (lhsPair p (envPat env')) (rhsPair arg' fexpr') body'
          in (expr', ans)
  RecCon r -> let r' = fmap recur r
              in (RecCon (fmap fst r'), RecVal (fmap snd r'))
  TLam _ body -> (RecCon $ posRecord envBVars, TLamVal env body)
  TApp fexpr ts ->
    let (fexpr', tLamVal) = recur fexpr
        ts' = map (deFuncType env) ts
    in case tLamVal of
      DFNil -> (TApp fexpr' ts, DFNil)
      TLamVal env' body ->
          let (body', ans) = deFuncExpr (setTEnv (addBVars ts) env') expr
          in (Let (envPat env') fexpr' body', ans)
  -- Unpack bound body ->
  --   let (bound', val) = recur bound
  --       -- TODO: fix (maybe even change unpack to have a type annotation)
  --       ty = undefined :: Type
  --       env' = setLEnv (addBVar (val, ty)) $ setTEnv (addBVar ()) $ env
  --       (body', ans) = deFuncExpr env' body
  --   in (Unpack bound' body', ans)
  where recur = deFuncExpr env
        recurWith p x = deFuncExpr $ setLEnv (addBVars $ bindPat p x) env
        envBVars = map (Var . BV) [0..length (bVars (lEnv env)) - 1]
        lhsPair x y = RecTree (posRecord [x, y])
        rhsPair x y = RecCon  (posRecord [x, y])
        envPat env = RecTree $ posRecord $ map (RecLeaf . snd) (bVars (lEnv env))
        deFuncPat p = fmap (deFuncType env) p

bindPat :: Pat () -> DFVal -> [(DFVal, Type)]
bindPat (RecTree r) (RecVal r') = concat $ zipWith bindPat (toList r) (toList r')
bindPat (RecLeaf t) x = [(x, t)]

deFuncType :: DFEnv -> Type -> Type
deFuncType env ty = instantiateBodyFVs (fmap Just (tEnv env)) (noLeaves ty)
