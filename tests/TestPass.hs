module TestPass (typeCheckPass, passInterp, fullPassJit, runTestPass) where

import Control.Monad.IO.Class

import Pass
import DeShadow
import Inference
import Imp
import Syntax
import Type
import JIT
import Flops
import Normalize
import Interpreter
import Cat

extractResult :: TopPass a b -> TopPass a Result'
extractResult (TopPass f) = TopPass $ \x -> do
    env1 <- look
    ~(Left res, env1') <- liftIO $ runTopPassM env1 (f x)
    extend env1'
    return res

typeCheckPass :: TopPass SourceBlock TopDecl
typeCheckPass = sourcePass >+> deShadowPass >+> typePass >+> checkTyped

passInterp :: TopPass TopDecl Result'
passInterp = extractResult interpPass

fullPassJit :: TopPass TopDecl Result'
fullPassJit = extractResult (normalizePass >+> checkNExpr
                                >+> simpPass      >+> checkNExpr
                                >+> impPass       >+> checkImp
                                >+> flopsPass
                                >+> jitPass)

runTestPass :: TopPass a b -> a -> IO (Either Result' b)
runTestPass (TopPass pass) source = do
    (res, _) <- runTopPassM mempty (pass source)
    return res