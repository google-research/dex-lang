module Parser (parseProg, parseTopDecl, Prog) where

import Control.Monad
import Control.Monad.Combinators.Expr
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Parsec as P
import Data.List (isPrefixOf)
import Data.Either (isRight)
import qualified Data.Map.Strict as M

import Env
import Record
import ParseUtil
import Syntax
import Fresh
import Inference
import PPrint

type Prog = [(String, Except UTopDecl)]

parseProg :: String -> Prog
parseProg source = map (\s -> (s, parseTopDecl s)) (splitDecls source)

parseTopDecl :: String -> Except UTopDecl
parseTopDecl = parseit (emptyLines >> topDeclInstr <* emptyLines)

parseit :: Parser a -> String -> Except a
parseit p s = case parse (p <* eof) "" s of
                Left e -> throw ParseErr (errorBundlePretty e)
                Right x -> return x

topDeclInstr :: Parser UTopDecl
topDeclInstr =   explicitCommand
             <|> liftM UTopDecl typedTopLet
             <|> liftM UTopDecl topUnpack
             <|> liftM UTopDecl topLet
             <|> liftM (UEvalCmd . Command EvalExpr) expr
             <?> "top-level declaration"

explicitCommand :: Parser UTopDecl
explicitCommand = do
  symbol ":"
  cmdName <- identifier
  cmd <- case cmdName of
           "p"       -> return EvalExpr
           "t"       -> return GetType
           "passes"  -> return Passes
           "llvm"    -> return LLVM
           "asm"     -> return Asm
           "time"    -> return TimeIt
           "plot"    -> return Plot
           "plotmat" -> return PlotMat
           _   -> fail $ "unrecognized command: " ++ show cmdName
  e <- expr
  return $ UEvalCmd (Command cmd e)

typedTopLet :: Parser UDecl
typedTopLet = do
  v <- try (varName <* symbol "::")
  ty <- typeExpr <* eol
  ULet p e <- topLet
  case p of
    RecTree _ -> fail "Can't annotate top-level pattern-match"
    RecLeaf (UBind (v' :> b)) ->
     if v' /= v
       then fail "Type declaration variable must match assignment variable."
       else case b of
              Just _ -> fail "Conflicting type annotations"
              Nothing -> return $ ULet (RecLeaf (UBind (v :> Just ty))) e

topUnpack :: Parser UDecl
topUnpack = do
  (b, tv) <- try unpackBinder
  body <- expr
  return $ UUnpack b tv body

unpackBinder :: Parser (UBinder, Var)
unpackBinder = do
  b <- binder
  symbol ","
  tv <- varName
  symbol "=" >> symbol "unpack"
  return (b, tv)

topLet :: Parser UDecl
topLet = do
  (p, wrap) <- try $ do p <- pat
                        wrap <- idxLhsArgs <|> lamLhsArgs
                        symbol "="
                        return (p, wrap)
  body <- expr
  return $ ULet p (wrap body)

expr :: Parser UExpr
expr = makeExprParser (sc >> term >>= maybeAnnot) ops

term :: Parser UExpr
term =   parenRaw
     <|> varExpr
     <|> liftM ULit literal
     <|> declExpr
     <|> lamExpr
     <|> forExpr
     <|> builtinExpr
     <?> "term"

maybeAnnot :: UExpr -> Parser UExpr
maybeAnnot e = do
  t <- optional typeAnnot
  return $ case t of
             Nothing -> e
             Just t -> UAnnot e t

typeAnnot :: Parser Type
typeAnnot = symbol "::" >> typeExpr

parenRaw = do
  elts <- parens $ expr `sepBy` symbol ","
  return $ case elts of
    [expr] -> expr
    elts -> URecCon $ Tup elts

-- maybeNamed :: Parser a -> Parser (Maybe String, a)
-- maybeNamed p = do
--   v <- optional $ try $
--     do v <- identifier
--        symbol "="
--        return v
--   x <- p
--   return (v, x)

varExpr :: Parser UExpr
varExpr = liftM (UVar . rawName) identifier

builtinExpr :: Parser UExpr
builtinExpr = do
  symbol "%"
  s <- identifier
  case strToBuiltin s of
    Just b -> return $ UBuiltin b
    Nothing -> fail $ "Unexpected builtin: " ++ s

declExpr :: Parser UExpr
declExpr = do
  symbol "let"
  decls <- (unpackDecl <|> typedLocalLet <|> localLet) `sepBy` symbol ";"
  symbol "in"
  body <- expr
  return $ UDecls decls body

lamExpr :: Parser UExpr
lamExpr = do
  symbol "lam"
  ps <- pat `sepBy` sc
  symbol "."
  body <- expr
  return $ foldr ULam body ps

forExpr :: Parser UExpr
forExpr = do
  symbol "for"
  vs <- some idxPat -- `sepBy` sc
  symbol "."
  body <- expr
  return $ foldr UFor body vs

-- decl :: Parser (Pat, UExpr)
unpackDecl :: Parser UDecl
unpackDecl = do
  (b, tv) <- try unpackBinder
  body <- expr
  return $ UUnpack b tv body

typedLocalLet :: Parser UDecl
typedLocalLet = do
  v <- try (varName <* symbol "::")
  ty <- typeExpr <* symbol ";"
  v' <- varName
  if v' /= v
    then fail "Type declaration variable must match assignment variable."
    else return ()
  wrap <- idxLhsArgs <|> lamLhsArgs
  symbol "="
  body <- expr
  return $ ULet (RecLeaf (UBind (v :> Just ty))) (wrap body)

localLet :: Parser UDecl
localLet = do
  p <- pat
  wrap <- idxLhsArgs <|> lamLhsArgs
  symbol "="
  body <- expr
  return $ ULet p (wrap body)

idxLhsArgs = do
  symbol "."
  args <- idxPat `sepBy` symbol "."
  return $ \body -> foldr UFor body args

lamLhsArgs = do
  args <- pat `sepBy` sc
  return $ \body -> foldr ULam body args

literal :: Parser LitVal
literal = lexeme $  fmap IntLit  (try (int <* notFollowedBy (symbol ".")))
                <|> fmap RealLit real
                <|> fmap StrLit stringLiteral

opNames = ["+", "*", "/", "-", "^"]
resNames = ["for", "lam", "let", "in", "unpack"]

identifier = makeIdentifier resNames

appRule = InfixL (sc
                  *> notFollowedBy (choice . map symbol $ opNames)
                  >> return UApp)
binOpRule opchar builtin = InfixL (symbol opchar >> return binOpApp)
  where binOpApp e1 e2 = UApp (UBuiltin builtin) (URecCon (Tup [e1, e2]))

getRule = Postfix $ do
  vs  <- many $ symbol "." >> idxExpr
  return $ \body -> foldr (flip UGet) body (reverse vs)

ops = [ [getRule, appRule]
      , [binOpRule "^" Pow]
      , [binOpRule "*" FMul]  -- binOpRule "/" Div]
      , [binOpRule "+" FAdd, binOpRule "-" FSub]
      ]

-- idxExpr =   parenIdxExpr
--         <|> liftM (RecLeaf . FV) identifier

-- parenIdxExpr = do
--   elts <- parens $ maybeNamed idxExpr `sepBy` symbol ","
--   return $ case elts of
--     [(Nothing, expr)] -> expr
--     elts -> RecTree $ mixedRecord elts

varName = liftM rawName identifier
idxExpr = varName

binder :: Parser UBinder
binder =     (symbol "_" >> return IgnoreBind)
         <|> (liftM UBind $ liftM2 (:>) varName (optional typeAnnot))

idxPat = binder

pat :: Parser Pat
pat =   parenPat
    <|> liftM RecLeaf binder

parenPat :: Parser Pat
parenPat = do
  xs <- parens $ pat `sepBy` symbol ","
  return $ case xs of
    [x] -> x
    xs -> RecTree $ Tup xs

typeExpr :: Parser Type
typeExpr = makeExprParser (sc >> typeExpr') typeOps

-- var :: Parser Var
-- var = liftM rawName $ makeIdentifier
--             ["Int", "Real", "Bool", "Str", "A", "E"]

builtinNames = M.fromList [
  ("iadd", Add), ("isub", Sub), ("imul", Mul), ("fadd", FAdd), ("fsub", FSub),
  ("fmul", FMul), ("fdiv", FDiv), ("pow", Pow), ("exp", Exp),
  ("log", Log), ("sqrt", Sqrt), ("sin", Sin), ("cos", Cos), ("tan", Tan),
  ("fold", Fold), ("iota", Iota), ("range", Range), ("inttoreal", IntToReal),
  ("hash", Hash), ("rand", Rand), ("randint", Randint), ("deriv", Deriv),
  ("transpose", Transpose)]

strToBuiltin :: String -> Maybe Builtin
strToBuiltin name = M.lookup name builtinNames

forallType :: Parser Type
forallType = do
  try $ symbol "A"
  vs <- varName `sepBy` sc
  symbol "."
  body <- typeExpr
  case inferKinds vs body of
    Left e -> fail $ pprint e
    Right kinds -> return $ Forall kinds (abstractTVs vs body)

existsType :: Parser Type
existsType = do
  try $ symbol "E"
  v <- varName
  symbol "."
  body <- typeExpr
  return $ Exists (abstractTVs [v] body)

baseType :: Parser BaseType
baseType = (symbol "Int"  >> return IntType)
       <|> (symbol "Real" >> return RealType)
       <|> (symbol "Bool" >> return BoolType)
       <|> (symbol "Str"  >> return StrType)
       <?> "base type"

typeOps = [ [InfixR (symbol "=>" >> return TabType)]
          , [InfixR (symbol "->" >> return ArrType)]]

typeExpr' =   parenTy
          <|> liftM TypeVar varName
          <|> liftM BaseType baseType
          <|> forallType
          <|> existsType
          <?> "type"

parenTy :: Parser Type
parenTy = do
  elts <- parens $ typeExpr `sepBy` symbol ","
  return $ case elts of
    [ty] -> ty
    _ -> RecType $ Tup elts

type LineParser = P.Parsec [String] ()

splitDecls :: String -> [String]
splitDecls s = parsecParse (   blanks
                            >> P.many (P.try topDeclString)
                            <* commentsOrBlanks) $ lines s

parsecParse :: LineParser a -> [String] -> a
parsecParse p s = case P.parse (p <* P.eof) "" s of
                    Left e -> error (show e)
                    Right x -> x

lineMatch :: (String -> Bool) -> LineParser String
lineMatch test = P.tokenPrim show nextPos toMaybe
  where nextPos pos _ _ = P.incSourceColumn pos 1
        toMaybe x = if test x then Just x
                              else Nothing

topDeclString :: LineParser String
topDeclString = do comments <- P.many (commentLine <* blanks)
                   annLines <- P.many annotLine
                   fstLine  <- lineMatch (const True)
                   rest     <- P.many continuedLine <* blanks
                   return $ unlines $ comments ++ annLines ++ (fstLine : rest)
  where
    annotLine = lineMatch $ isRight . parse (identifier >> symbol "::") ""
    continuedLine = lineMatch (" "  `isPrefixOf`)

commentLine :: LineParser String
commentLine = lineMatch ("--" `isPrefixOf`)

commentsOrBlanks :: LineParser ()
commentsOrBlanks = void $ P.many (void commentLine <|> blankLine)

blankLine :: LineParser ()
blankLine = void $ lineMatch (\line -> null line || ">" `isPrefixOf` line)

blanks :: LineParser ()
blanks = void $ P.many blankLine

-- data BoundVars = BoundVars { lVars :: [Var]
--                            , tVars :: [Var] }

-- lowerInstr :: UDecl -> UDecl
-- lowerInstr = fmap (lower empty)
--   where empty = BoundVars [] []

-- lower :: BoundVars -> UExpr -> UExpr
-- lower env expr = case expr of
--   ULit c         -> ULit c
--   UVar v         -> UVar $ toDeBruijn (lVars env) v
--   UBuiltin b     -> UBuiltin b
--   ULet p e body  -> ULet p (recur e) $ lowerWithMany p body
--   ULam p body    -> ULam p           $ lowerWithMany p body
--   UApp fexpr arg -> UApp (recur fexpr) (recur arg)
--   UFor p body    -> UFor p           $ lowerWith p body
--   UGet e ie      -> UGet (recur e) $ toDeBruijn (lVars env) ie
--   URecCon r      -> URecCon $ fmap recur r
--   UAnnot e t     -> UAnnot (recur e) (lowerType env t)
--   UUnpack v e body -> UUnpack v (recur e) $
--                          lower (env {lVars = v : lVars env}) body
--   where recur = lower env
--         lowerWith p expr = lower (updateLVar p env) expr
--         lowerWithMany p expr = lower (updateLVars (toList p) env) expr

--         updateLVar :: Var -> BoundVars -> BoundVars
--         updateLVar v env = env {lVars = v : lVars env}

--         updateLVars :: [Var] -> BoundVars -> BoundVars
--         updateLVars vs env = env {lVars = vs ++ lVars env}

-- lowerType :: BoundVars -> Type -> Type
-- lowerType env ty = case ty of
--   BaseType b    -> BaseType b
--   TypeVar v     -> TypeVar $ toDeBruijn (tVars env) v
--   ArrType t1 t2 -> ArrType (recur t1) (recur t2)
--   TabType t1 t2 -> TabType (recur t1) (recur t2)
--   -- MetaTypeVar m -> MetaTypeVar m
--   where recur = lowerType env

-- updateTVars :: [Var] -> BoundVars -> BoundVars
-- updateTVars vs env = env {tVars = vs ++ tVars env}

-- -- boundVarPass :: Pass UExpr UExpr () ()
-- -- boundVarPass = Pass
-- --   { lowerExpr   = \expr env -> do liftErrIO $ checkBoundVarsExpr expr env
-- --                                   return ((), expr)
-- --   , lowerUnpack = \_ expr env -> do liftErrIO $ checkBoundVarsExpr expr env
-- --                                     return ((), (), expr)
-- --   , lowerCmd    = \cmd  env -> return $ checkBoundVarsCmd cmd env }

-- checkBoundVarsCmd :: Command UExpr -> Vars -> Command UExpr
-- checkBoundVarsCmd cmd@(Command cmdName expr) envVars =
--   case checkBoundVarsExpr expr envVars of
--     Left err -> CmdErr err
--     Right () -> cmd
-- checkBoundVarsCmd x _ = x

-- checkBoundVarsExpr :: UExpr -> Vars -> Except ()
-- checkBoundVarsExpr expr envVars = do
--   let freeVars = fvsUExpr expr
--   lEnv envVars `contains` lEnv freeVars
--   tEnv envVars `contains` tEnv freeVars
--   return ()
--   where contains :: Env i a -> Env i a -> Except ()
--         contains e1 e2 = case fVars (e2 `envDiff` e1) of
--                             v:_ -> Left $ UnboundVarErr v
--                             [] -> Right ()
