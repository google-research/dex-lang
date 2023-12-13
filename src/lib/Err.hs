-- Copyright 2021 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE UndecidableInstances #-}

module Err (
  Err (..), Except (..), ToErr (..), PrintableErr (..),
  ParseErr (..), SyntaxErr (..), NameErr (..), TypeErr (..), MiscErr (..),
  Fallible (..), Catchable (..), catchErrExcept,
  HardFailM (..), runHardFail, throw,
  catchIOExcept, liftExcept, liftExceptAlt,
  ignoreExcept, getCurrentCallStack, printCurrentCallStack,
  ExceptT (..), rootSrcId, SrcId (..), assertEq, throwInternal,
  InferenceArgDesc, InfVarDesc (..), HasSrcId (..), getErrSrcId) where

import Control.Exception hiding (throw)
import Control.Applicative
import Control.Monad
import Control.Monad.Identity
import Control.Monad.Writer.Strict
import Control.Monad.State.Strict
import Control.Monad.Reader
import Data.Aeson (ToJSON)
import Data.Coerce
import Data.Hashable
import Data.List (sort)
import Data.Foldable (fold)
import Data.Store (Store (..))
import GHC.Stack
import GHC.Generics

import PPrint

-- === source info ===

-- XXX: 0 is reserved for the root The IDs are generated from left to right in
-- parsing order, so IDs for lexemes are guaranteed to be sorted correctly.
newtype SrcId = SrcId Int  deriving (Show, Eq, Ord, Generic)

rootSrcId :: SrcId
rootSrcId = SrcId 0

class HasSrcId a where
  getSrcId :: a -> SrcId

getErrSrcId :: Err -> Maybe SrcId
getErrSrcId = \case
  SearchFailure _ -> Nothing
  InternalErr   _ -> Nothing
  ParseErr      _ -> Nothing
  SyntaxErr sid _ -> Just sid
  NameErr   sid _ -> Just sid
  TypeErr   sid _ -> Just sid
  RuntimeErr -> Nothing
  MiscErr _  -> Nothing

-- === core errro type ===

data Err =
   SearchFailure String      -- used as the identity for `Alternative` instances and for MonadFail.
 | InternalErr String
 | ParseErr  ParseErr
 | SyntaxErr SrcId SyntaxErr
 | NameErr   SrcId NameErr
 | TypeErr   SrcId TypeErr
 | RuntimeErr
 | MiscErr MiscErr
   deriving (Show, Eq)

type MsgStr  = String
type VarStr  = String
type TypeStr = String

data ParseErr =
  MiscParseErr MsgStr
  deriving (Show, Eq)

data SyntaxErr =
   MiscSyntaxErr MsgStr
 | TopLevelArrowBinder
 | CantConstrainAnonBinders
 | UnexpectedBinder
 | OnlyUnaryWithoutParens
 | IllegalPattern
 | UnexpectedConstraint
 | ExpectedIdentifier String
 | UnexpectedEffectForm
 | UnexpectedMethodDef
 | BlockWithoutFinalExpr
 | UnexpectedGivenClause
 | ArgsShouldHaveParens
 | BadEqualSign
 | BadColon
 | ExpectedAnnBinder
 | BadField
 | BadPrefix VarStr
   deriving (Show, Eq)

data NameErr =
   MiscNameErr MsgStr
 | UnboundVarErr VarStr    -- name of var
 | EscapedNameErr [VarStr] -- names
 | RepeatedPatVarErr VarStr
 | RepeatedVarErr VarStr
 | NotAnOrdinaryVar VarStr
 | NotADataCon VarStr
 | NotAClassName VarStr
 | NotAMethodName VarStr
 | AmbiguousVarErr VarStr [String]
 | VarDefErr VarStr
   deriving (Show, Eq)

data TypeErr =
   MiscTypeErr MsgStr
 | CantSynthDict     TypeStr
 | CantSynthInfVars  TypeStr
 | NotASynthType     TypeStr
 | CantUnifySkolem
 | OccursCheckFailure VarStr TypeStr
 | UnificationFailure TypeStr TypeStr [VarStr]  -- expected, actual, inference vars
 | DisallowedEffects  String String  -- allowed, actual
 | InferEmptyTable
 | ArityErr        Int Int  -- expected, actual
 | PatternArityErr Int Int  -- expected, actual
 | SumTypeCantFail
 | PatTypeErr String String  -- expected type constructor (from pattern), actual type (from rhs)
 | EliminationErr String String  -- expected type constructor, actual type
 | IllFormedCasePattern
 | NotAMethod VarStr VarStr
 | DuplicateMethod VarStr
 | MissingMethod   VarStr
 | WrongArrowErr String String
 | AnnotationRequired
 | NotAUnaryConstraint TypeStr
 | InterfacesNoImplicitParams
 | RepeatedOptionalArgs [VarStr]
 | UnrecognizedOptionalArgs [VarStr] [VarStr]
 | NoFields TypeStr
 | TypeMismatch TypeStr TypeStr  -- TODO: should we merege this with UnificationFailure
 | InferHoleErr
 | InferDepPairErr
 | InferEmptyCaseEff
 | UnexpectedTerm String TypeStr
 | CantFindField VarStr TypeStr [VarStr]  -- field name, field type, known fields
 | TupleLengthMismatch Int Int
 | CantReduceType TypeStr
 | CantReduceDict
 | CantReduceDependentArg
 | AmbiguousInferenceVar VarStr TypeStr InfVarDesc
 | FFIResultTyErr    TypeStr
 | FFIArgTyNotScalar TypeStr
   deriving (Show, Eq)

data MiscErr =
   MiscMiscErr MsgStr
 | ModuleImportErr VarStr
 | CantFindModuleSource VarStr
   deriving (Show, Eq)

-- name of function, name of arg
type InferenceArgDesc = (String, String)
data InfVarDesc =
   ImplicitArgInfVar InferenceArgDesc
 | AnnotationInfVar String -- name of binder
 | TypeInstantiationInfVar String -- name of type
 | MiscInfVar
   deriving (Show, Generic, Eq, Ord)

-- === ToErr class ===

class ToErr a where
  toErr :: SrcId -> a -> Err

instance ToErr SyntaxErr where toErr = SyntaxErr
instance ToErr NameErr   where toErr = NameErr
instance ToErr TypeErr   where toErr = TypeErr

-- === Error messages ===

class PrintableErr a where
  printErr :: a -> String

instance PrintableErr Err where
  printErr = \case
    SearchFailure s -> "Internal search failure: " ++ s
    InternalErr s -> "Internal compiler error: " ++ s ++ "\n" ++
      "Please report this at github.com/google-research/dex-lang/issues\n"
    ParseErr    e -> "Parse error: "  ++ printErr e
    SyntaxErr _ e -> "Syntax error: " ++ printErr e
    NameErr   _ e -> "Name error: "   ++ printErr e
    TypeErr   _ e -> "Type error: "   ++ printErr e
    MiscErr     e -> "Error: "        ++ printErr e
    RuntimeErr    -> "Runtime error"

instance PrintableErr ParseErr where
  printErr = \case
    MiscParseErr s -> s

instance PrintableErr SyntaxErr where
  printErr = \case
    MiscSyntaxErr s -> s
    TopLevelArrowBinder ->
      "Arrow binder syntax <- not permitted at the top level, because the binding would have unbounded scope."
    CantConstrainAnonBinders -> "can't constrain anonymous binders"
    UnexpectedBinder -> "binder must be an identifier or `_`"
    OnlyUnaryWithoutParens ->"only unary constructors can form patterns without parens"
    IllegalPattern -> "illegal pattern"
    UnexpectedConstraint -> "unexpected constraint"
    ExpectedIdentifier ctx -> "expected " ++ ctx ++ " to be an identifier"
    UnexpectedEffectForm ->
      "unexpected effect form; expected one of `Read h`, `Accum h`, `State h`, `Except`, `IO`, "
       ++ "or the name of a user-defined effect."
    UnexpectedMethodDef -> "unexpected method definition. Expected `def` or `x = ...`."
    BlockWithoutFinalExpr -> "block must end in expression"
    UnexpectedGivenClause -> "unexpected `given` clause"
    ArgsShouldHaveParens -> "argument types should be in parentheses"
    BadEqualSign -> "equal sign must be used as a separator for labels or binders, not a standalone operator"
    BadColon ->
      "colon separates binders from their type annotations, is not a standalone operator.\n"
      ++ " If you are trying to write a dependent type, use parens: (i:Fin 4) => (..i)"
    ExpectedAnnBinder -> "expected an annotated binder"
    BadField -> "field must be a name or an integer"
    BadPrefix name -> "prefix (" ++ name ++ ") not legal as a bare expression"

instance PrintableErr NameErr where
  printErr = \case
    MiscNameErr s -> s
    UnboundVarErr v     -> "variable not in scope: " ++ v
    EscapedNameErr vs   -> "leaked local variables: " ++ unwords vs
    RepeatedPatVarErr v -> "variable already defined within pattern: " ++ v
    RepeatedVarErr    v -> "variable already defined : " ++ v
    NotAnOrdinaryVar v -> "not an ordinary variable: " ++ v
    NotADataCon      v -> "not a data constructor: "   ++ v
    NotAClassName    v -> "not a class name: "         ++ v
    NotAMethodName   v -> "not a method name: "        ++ v
    -- we sort the lines to make the result a bit more deterministic for quine tests
    AmbiguousVarErr v defs ->
      "ambiguous occurrence: " ++ v ++ " is defined:\n"
      ++ unlines (sort defs)
    -- TODO: we see this message a lot. We should improve it by including more information.
    -- Ideally we'd provide a link to where the original error happened."
    VarDefErr v -> "error in (earlier) definition of variable: " ++ v

instance PrintableErr TypeErr where
  printErr = \case
    MiscTypeErr s -> s
    FFIResultTyErr t    -> "FFI result type should be scalar or pair. Got: " ++ t
    FFIArgTyNotScalar t -> "FFI function arguments should be scalar. Got: " ++ t
    CantSynthDict t     -> "can't synthesize a class dictionary for: " ++ t
    CantSynthInfVars t  -> "can't synthesize a class dictionary for a type with inference vars: " ++ t
    NotASynthType t     -> "can't synthesize terms of type: " ++ t
    CantUnifySkolem     -> "can't unify with skolem vars"
    OccursCheckFailure v t -> "occurs check failure: " ++ v ++ " occurs in " ++ t
    DisallowedEffects r1 r2 -> "\nAllowed:   " ++ pprint r1 ++
                               "\nRequested: " ++ pprint r2
    UnificationFailure t1 t2 vs -> "\nExpected: " ++ t1
                                ++ "\nActual: " ++ t2 ++ case vs of
                                                          [] -> ""
                                                          _  -> "\n(Solving for: " ++ unwords vs ++ ")"
    InferEmptyTable       -> "can't infer type of empty table"
    ArityErr n1 n2 -> "wrong number of positional arguments provided. Expected " ++ show n1 ++ " but got " ++ show n2
    PatternArityErr n1 n2 -> "unexpected number of pattern binders. Expected "   ++ show n1 ++ " but got " ++ show n2
    SumTypeCantFail               -> "sum type constructor in can't-fail pattern"
    PatTypeErr patTy rhsTy        -> "pattern is for a " ++ patTy ++ "but we're matching against a " ++ rhsTy
    EliminationErr expected ty    -> "expected a " ++ expected ++ ". Got: " ++ ty
    IllFormedCasePattern          -> "case patterns must start with a data constructor or variant pattern"
    NotAMethod method className   -> "unexpected method: " ++ method ++ " is not a method of " ++ className
    DuplicateMethod method        -> "duplicate method: " ++ method
    MissingMethod   method        -> "missing method: "   ++ method
    WrongArrowErr expected actual -> "wrong arrow. Expected " ++ expected ++ " got " ++ actual
    AnnotationRequired            -> "type annotation or constraint required"
    NotAUnaryConstraint ty        -> "constraint should be a unary function. Got: " ++ ty
    InterfacesNoImplicitParams    -> "interfaces can't have implicit parameters"
    RepeatedOptionalArgs vs       -> "repeated names offered:" ++ unwords vs
    UnrecognizedOptionalArgs vs accepted -> "unrecognized named arguments: " ++ unwords vs
                                       ++ ". Should be one of: " ++ pprint accepted
    NoFields ty -> "can't get fields for type " ++ pprint ty
    TypeMismatch expected actual -> "\nExpected: " ++ expected ++
                                    "\nActual:   " ++ actual
    InferHoleErr -> "can't infer value of hole"
    InferDepPairErr -> "can't infer the type of a dependent pair; please annotate its type"
    InferEmptyCaseEff -> "can't infer empty case expressions"
    UnexpectedTerm term ty -> "unexpected " ++ term ++ ". Expected: " ++ ty
    CantFindField field fieldTy knownFields ->
      "can't resolve field " ++ field ++ " of type " ++ fieldTy ++
      "\nKnown fields are: " ++ unwords knownFields
    TupleLengthMismatch req actual -> do
        "tuple length mismatch. Expected: " ++ show req ++ " but got " ++ show actual
    CantReduceType  ty -> "Can't reduce type expression: " ++ ty
    CantReduceDict -> "Can't reduce dict"
    CantReduceDependentArg ->
      "dependent functions can only be applied to fully evaluated expressions. " ++
      "Bind the argument to a name before you apply the function."
    AmbiguousInferenceVar infVar ty desc -> case desc of
       AnnotationInfVar v ->
         "couldn't infer type of unannotated binder " <> v
       ImplicitArgInfVar (f, argName) ->
         "couldn't infer implicit argument `" <> argName <> "` of " <> f
       TypeInstantiationInfVar t ->
         "couldn't infer instantiation of type " <> t
       MiscInfVar ->
         "ambiguous type variable: " ++ infVar ++ ": " ++ ty

instance PrintableErr MiscErr where
  printErr = \case
    MiscMiscErr s -> s
    ModuleImportErr v -> "couldn't import " ++ v
    CantFindModuleSource v ->
      "couldn't find a source file for module " ++ v ++
      "\nHint: Consider extending --lib-path"

-- === monads and helpers ===

class MonadFail m => Fallible m where
  throwErr :: Err -> m a

class Fallible m => Catchable m where
  catchErr :: m a -> (Err -> m a) -> m a

catchErrExcept :: Catchable m => m a -> m (Except a)
catchErrExcept m = catchErr (Success <$> m) (\e -> return $ Failure e)

catchSearchFailure :: Catchable m => m a -> m (Maybe a)
catchSearchFailure m = (Just <$> m) `catchErr` \case
  SearchFailure _ -> return Nothing
  err -> throwErr err

instance Fallible IO where
  throwErr errs = throwIO errs
  {-# INLINE throwErr #-}

instance Catchable IO where
  catchErr cont handler =
    catchIOExcept cont >>= \case
      Success result -> return result
      Failure errs -> handler errs

-- === ExceptT type ===

newtype ExceptT m a = ExceptT { runExceptT :: m (Except a) }

instance Monad m => Functor (ExceptT m) where
  fmap = liftM
  {-# INLINE fmap #-}

instance Monad m => Applicative (ExceptT m) where
  pure = return
  {-# INLINE pure #-}
  liftA2 = liftM2
  {-# INLINE liftA2 #-}

instance Monad m => Monad (ExceptT m) where
  return x = ExceptT $ return (Success x)
  {-# INLINE return #-}
  m >>= f = ExceptT $ runExceptT m >>= \case
    Failure errs -> return $ Failure errs
    Success x    -> runExceptT $ f x
  {-# INLINE (>>=) #-}

instance Monad m => MonadFail (ExceptT m) where
  fail s = ExceptT $ return $ Failure $ SearchFailure s
  {-# INLINE fail #-}

instance Monad m => Fallible (ExceptT m) where
  throwErr errs = ExceptT $ return $ Failure errs
  {-# INLINE throwErr #-}

instance Monad m => Alternative (ExceptT m) where
  empty = throwErr $ SearchFailure ""
  {-# INLINE empty #-}
  m1 <|> m2 = do
    catchSearchFailure m1 >>= \case
      Nothing -> m2
      Just x -> return x
  {-# INLINE (<|>) #-}

instance Monad m => Catchable (ExceptT m) where
  m `catchErr` f = ExceptT $ runExceptT m >>= \case
    Failure errs -> runExceptT $ f errs
    Success x    -> return $ Success x
  {-# INLINE catchErr #-}

instance MonadState s m => MonadState s (ExceptT m) where
  get = lift get
  {-# INLINE get #-}
  put x = lift $ put x
  {-# INLINE put #-}

instance MonadTrans ExceptT where
  lift m = ExceptT $ Success <$> m
  {-# INLINE lift #-}

-- === Except type ===

-- Except is isomorphic to `Either Err` but having a distinct type makes it
-- easier to debug type errors.

data Except a =
   Failure Err
 | Success a
   deriving (Show, Eq)

instance Functor Except where
  fmap = liftM
  {-# INLINE fmap #-}

instance Applicative Except where
  pure = return
  {-# INLINE pure #-}
  liftA2 = liftM2
  {-# INLINE liftA2 #-}

instance Monad Except where
  return = Success
  {-# INLINE return #-}
  Failure errs >>= _ = Failure errs
  Success x >>= f = f x
  {-# INLINE (>>=) #-}

instance Alternative Except where
  empty = throwErr $ SearchFailure ""
  {-# INLINE empty #-}
  m1 <|> m2 = do
    catchSearchFailure m1 >>= \case
      Nothing -> m2
      Just x -> return x
  {-# INLINE (<|>) #-}

instance Catchable Except where
  Success ans `catchErr` _ = Success ans
  Failure errs `catchErr` f = f errs
  {-# INLINE catchErr #-}

-- === HardFail ===

-- Implements Fallible by crashing. Used in type querying when we want to avoid
-- work by trusting decl annotations and skipping the checks.
newtype HardFailM a =
  HardFailM { runHardFail' :: Identity a }
  -- We don't derive Functor, Applicative and Monad, because Identity doesn't
  -- use INLINE pragmas in its own instances, which unnecessarily inhibits optimizations.

instance Functor HardFailM where
  fmap f (HardFailM (Identity x)) = HardFailM $ Identity $ f x
  {-# INLINE fmap #-}

instance Applicative HardFailM where
  pure = HardFailM . Identity
  {-# INLINE pure #-}
  (<*>) = coerce
  {-# INLINE (<*>) #-}
  liftA2 = coerce
  {-# INLINE liftA2 #-}

instance Monad HardFailM where
  (HardFailM (Identity x)) >>= k = k x
  {-# INLINE (>>=) #-}
  return = HardFailM . Identity
  {-# INLINE return #-}

runHardFail :: HardFailM a -> a
runHardFail m = runIdentity $ runHardFail' m
{-# INLINE runHardFail #-}

instance MonadFail HardFailM where
  fail s = error s
  {-# INLINE fail #-}

instance Fallible HardFailM where
  throwErr errs = error $ pprint errs
  {-# INLINE throwErr #-}

-- === convenience layer ===

throw :: (ToErr e, Fallible m) => SrcId -> e -> m a
throw sid e = throwErr $ toErr sid e
{-# INLINE throw #-}

getCurrentCallStack :: () -> Maybe [String]
getCurrentCallStack () =
#ifdef DEX_DEBUG
  case reverse (unsafePerformIO currentCallStack) of
    []    -> Nothing
    stack -> Just stack
#else
  Nothing
#endif
{-# NOINLINE getCurrentCallStack #-}

printCurrentCallStack :: Maybe [String] -> String
printCurrentCallStack Nothing = "<no call stack available>"
printCurrentCallStack (Just frames) = fold frames

catchIOExcept :: MonadIO m => IO a -> m (Except a)
catchIOExcept m = liftIO $ (liftM Success m) `catches`
  [ Handler \(e::Err)           -> return $ Failure e
  , Handler \(e::IOError)        -> return $ Failure $ MiscErr $ MiscMiscErr $ show e
  -- Propagate asynchronous exceptions like ThreadKilled; they are
  -- part of normal operation (of the live evaluation modes), not
  -- compiler bugs.
  , Handler \(e::AsyncException) -> liftIO $ throwIO e
  , Handler \(e::SomeException)  -> return $ Failure $ InternalErr $ show e
  ]

liftExcept :: Fallible m => Except a -> m a
liftExcept (Failure errs) = throwErr errs
liftExcept (Success ans) = return ans
{-# INLINE liftExcept #-}

liftExceptAlt :: Alternative m => Except a -> m a
liftExceptAlt = \case
  Success a -> pure a
  Failure _ -> empty
{-# INLINE liftExceptAlt #-}

ignoreExcept :: HasCallStack => Except a -> a
ignoreExcept (Failure e) = error $ pprint e
ignoreExcept (Success x) = x
{-# INLINE ignoreExcept #-}

assertEq :: (HasCallStack, Fallible m, Show a, Pretty a, Eq a) => a -> a -> String -> m ()
assertEq x y s = if x == y then return ()
                           else throwInternal msg
  where msg = "assertion failure (" ++ s ++ "):\n"
              ++ pprint x ++ " != " ++ pprint y

throwInternal :: (HasCallStack, Fallible m) => String -> m a
throwInternal s = throwErr $ InternalErr $ s ++ "\n" ++ prettyCallStack callStack ++ "\n"

instance (Monoid w, Fallible m) => Fallible (WriterT w m) where
  throwErr errs = lift $ throwErr errs
  {-# INLINE throwErr #-}

instance Fallible [] where
  throwErr _ = []
  {-# INLINE throwErr #-}

instance Fallible Maybe where
  throwErr _ = Nothing
  {-# INLINE throwErr #-}

-- === instances ===

instance Fallible Except where
  throwErr errs = Failure errs
  {-# INLINE throwErr #-}

instance MonadFail Except where
  fail s = Failure $ SearchFailure s
  {-# INLINE fail #-}

instance Exception Err

instance Fallible m => Fallible (ReaderT r m) where
  throwErr errs = lift $ throwErr errs
  {-# INLINE throwErr #-}

instance Catchable m => Catchable (ReaderT r m) where
  ReaderT f `catchErr` handler = ReaderT \r ->
    f r `catchErr` \e -> runReaderT (handler e) r

instance Fallible m => Fallible (StateT s m) where
  throwErr errs = lift $ throwErr errs
  {-# INLINE throwErr #-}

instance Catchable m => Catchable (StateT s m) where
  StateT f `catchErr` handler = StateT \s ->
    f s `catchErr` \e -> runStateT (handler e) s

instance Pretty Err where
  pretty e = pretty $ printErr e

instance ToJSON SrcId

instance Store InfVarDesc
instance Store SrcId

instance Hashable InfVarDesc
instance Hashable SrcId
