-- Copyright 2022 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module OccurrenceSpec (spec) where

import Prelude hiding ((.), seq)

import Control.Monad.Reader.Class
import Data.Map.Strict qualified as M
import Data.String
import Test.Hspec

import MTL1
import IRVariants
import Name hiding (NameMap)
import Occurrence

-- === Embedded DSL for spelling example Access objects ===

data UAccessOpen =
    ULoc [UIxExpr] Count
  | UAny [UAccessOpen]
  | UAll [UAccessOpen]
  | UForEach String UAccessOpen

data UAccess = Free [String] UAccessOpen

closed :: UAccessOpen -> UAccess
closed = Free []

data UIxExpr =
    UVar String
  | UProduct [UIxExpr]
  | UInject Int UIxExpr
  | UDeterministic [String]

instance IsString UIxExpr where
  fromString = UVar

resolveNames :: UAccess -> Abs (Nest (NameBinder ('AtomNameC SimpIR))) Access 'VoidS
resolveNames (Free names uaccess) = runResolverM
  $ withFreshNamesM (map getNameHint names) \bs ->
    local ((NameMap $ M.fromList
            $ zip names (nestToList (\b -> sink $ binderName b) bs)) <>) do
      access <- resolveNames' uaccess
      return $ Abs bs access

withFreshNamesM
  :: (Color c, ScopeExtender m, Distinct n)
  => [NameHint]
  -> (forall l. DExt n l => (Nest (NameBinder c)) n l -> m l a)
  -> m n a
withFreshNamesM [] cont = cont Empty
withFreshNamesM (hint:hints) cont = withFreshM hint \b ->
  withFreshNamesM hints \bs -> cont $ Nest b bs

newtype NameMap (n::S) = NameMap (M.Map String (Name ('AtomNameC SimpIR) n))
  deriving (Semigroup, Monoid)

instance SinkableE NameMap where
  sinkingProofE c (NameMap m) = NameMap $ fmap (sinkingProofE c) m

newtype ResolverM (n::S) a = ResolverM {
  runResolverM' :: ReaderT1 NameMap ScopeReaderM n a }
  deriving (Functor, Applicative, Monad,
            ScopeReader, ScopeExtender, MonadReader (NameMap n))

runResolverM :: ResolverM 'VoidS a -> a
runResolverM action = runScopeReaderM emptyOutMap
  $ runReaderT1 (NameMap M.empty)
  $ runResolverM' action

resolveNames' :: UAccessOpen -> ResolverM n (Access n)
resolveNames' (ULoc ixs ct) = flip Location ct <$> mapM resolveNames'' ixs
resolveNames' (UAny uaccesses) = Any <$> mapM resolveNames' uaccesses
resolveNames' (UAll uaccesses) = All <$> mapM resolveNames' uaccesses
resolveNames' (UForEach str uaccess) =
  withFreshM (getNameHint str) \b ->
    ForEach b <$> (local ((NameMap $ M.singleton str (binderName b)) <>)
      $ resolveNames' uaccess)

resolveNames'' :: UIxExpr -> ResolverM n (IxExpr n)
resolveNames'' (UVar str) = Var <$> lookupName str
resolveNames'' (UProduct elts) = Product <$> mapM resolveNames'' elts
resolveNames'' (UInject i elt) = Inject i <$> resolveNames'' elt
resolveNames'' (UDeterministic names) = Deterministic <$> mapM lookupName names

lookupName :: String -> ResolverM n (Name ('AtomNameC SimpIR) n)
lookupName str = do
  (NameMap names) <- ask
  case M.lookup str names of
    Just n -> return n
    Nothing -> error $ "Unknown name " ++ str

for :: String -> UAccessOpen -> UAccessOpen
for = UForEach

xs :: UAccessOpen
xs = ULoc [] One

(.) :: UAccessOpen -> UIxExpr -> UAccessOpen
(ULoc items ct) . item = ULoc (items ++ [item]) ct
_ . _ = error "Invalid indexing expression"

seq :: [UAccessOpen] -> UAccessOpen
seq = UAll

tup :: [UIxExpr] -> UIxExpr
tup = UProduct

alt :: [UAccessOpen] -> UAccessOpen
alt = UAny

inj :: Int -> UIxExpr -> UIxExpr
inj = UInject

left :: UIxExpr -> UIxExpr
left = inj 0

right :: UIxExpr -> UIxExpr
right = inj 1

det :: [String] -> UIxExpr
det = UDeterministic

free :: [String] -> UAccessOpen -> UAccess
free = Free

-- === The actual spec ===

answerC :: UAccessOpen -> DynUseInfo
answerC open = answer $ closed open

answer :: UAccess -> DynUseInfo
answer uaccess = case resolveNames uaccess of
  (Abs _ open) -> approxConst $ collapse $ interp $ open

spec :: Spec
spec = do
  describe "Occurrence computes the right answer on" do
    it "just an access" do
      answerC xs `shouldBe` (0, One)
    it "1-D identity array" do
      answerC (for "i" $ xs . "i") `shouldBe` (1, One)
    it "two sequential accesses" do
      answerC (seq [for "i" $ xs . "i", for "i" $ xs . "i"])
        `shouldBe` (1, Bounded 2)
    it "in-body sequential access" do
      answerC (for "i" $ seq [xs . "i", xs . "i"]) `shouldBe` (1, Bounded 2)
    it "two alternate accesses" do
      answerC (alt [for "i" $ xs . "i", for "i" $ xs . "i"])
        `shouldBe` (1, One)
    it "in-body access alternation" do
      answerC (for "i" $ alt [xs . "i", xs . "i"]) `shouldBe` (1, One)
    it "2-D identity array" do
      answerC (for "i" $ for "j" $ xs . "i" . "j") `shouldBe` (2, One)
    it "2-D transposition" do
      answerC (for "i" $ for "j" $ xs . "j" . "i") `shouldBe` (2, One)
    it "a known function of the index" do
      answerC (for "i" $ xs . left "i") `shouldBe` (1, One)
    it "separately accessing two variants of the index type" do
      answerC (seq [ for "i" $ xs . left  "i"
                   , for "i" $ xs . right "i"]) `shouldBe` (1, One)
    it "unknown indexing in a loop" do
      answerC (for "i" $ xs . det ["i"]) `shouldBe` (1, Unbounded)
    it "loop-invariant access" do
      answerC (for "i" $ xs) `shouldBe` (0, Unbounded)
    it "2-D loop-invariant access" do
      answerC (for "i" $ for "j" $ xs . "j") `shouldBe` (1, Unbounded)
    it "a simple access with a ternary sum index type" do
      answerC (for "i" $ seq [ xs . inj 1 "i"
                             , xs . inj 2 "i"
                             , xs . inj 3 "i"
                             ]) `shouldBe` (1, One)
    it "taking the trace" do
      -- TODO Actually, xs is safe to inline even if we can only see
      -- one dimension, because the first index proves unique access
      -- without requiring the second one.  So this answer should
      -- really be (1, One); but the analysis doesn't do that yet.
      answerC (for "i" $ xs . "i" . "i") `shouldBe` (2, One)
    it "sequencing distinct alternate accesses" do
      let access = for "i" $
            seq [ alt [xs . inj 1 "i", xs . inj 2 "i"]
                , alt [xs . inj 3 "i", xs . inj 4 "i"]
                ]
      answerC access `shouldBe` (1, One)
    it "sequencing colliding alternate accesses" do
      let access = for "i" $
            seq [ alt [xs . inj 1 "i", xs . inj 2 "i"]
                , alt [xs . inj 1 "i", xs . inj 4 "i"]
                ]
      answerC access `shouldBe` (1, Bounded 2)
    it "sequencing non-colliding alternate accesses" do
      let access = for "i" $
            seq [ alt [xs . inj 1 "i", xs . inj 1 "i"]
                , alt [xs . inj 3 "i", xs . inj 4 "i"]
                ]
      answerC access `shouldBe` (1, Bounded 1)
    it "taking a 'trace' with one unknown index" do
      answerC (for "i" $ xs . det ["i"] . "i") `shouldBe` (2, One)
    it "a tuple-typed index" do
      answerC (for "i" $ for "j" $ xs . tup ["i", "j"]) `shouldBe` (1, One)
    it "a tuple-typed index with an Either inside" do
      answerC (seq [ for "i" $ for "j" $ xs . tup ["i", left "j"]
                   , for "i" $ for "j" $ xs . tup ["i", right "j"]])
        `shouldBe` (1, One)
  describe "Occurrence computes the right answer on open terms" do
    it "accessing a free index" do
      answer (free ["i"] $ xs . "i") `shouldBe` (1, One)
    it "accessing a free index in a loop" do
      -- TODO Same conservativeness here: one dimension is enough
      -- to prove safety
      answer (free ["j"] $ for "i" $ xs . "i" . "j") `shouldBe` (2, One)
    it "accessing a free index in a loop transposed" do
      -- Here, on the other hand, we really need two dimensions to
      -- inline without duplicating work.
      answer (free ["j"] $ for "i" $ xs . "j" . "i") `shouldBe` (2, One)
    it "accessing potentially colliding free indices" do
      -- Here we can't be completely safe inlining, because j and k
      -- could collide and force us to duplicate work on that one
      -- element in that one circumstance.  However, a more
      -- sophisticated analysis could discover that it may be worth
      -- either (1) just eating the duplication, if the j and k spaces
      -- are large enough and the body of xs is uniform enough, and/or
      -- (2) adding a guard condition for `j == k` and inlining into
      -- the branch where this is false.
      answer (free ["j", "k"] $ seq
               [ for "i" $ xs . "i" . "j"
               , for "i" $ xs . "i" . "k"
               ]) `shouldBe` (2, Bounded 2)
    it "accessing unknown free index" do
      -- Again, the real answer is (0, One), but the analysis doesn't
      -- know that yet.
      answer (free ["i"] $ xs . (det ["i"])) `shouldBe` (1, One)

-- === TODO Property-based testing ===
--
-- The Occurrence data structures should obey some invariants:
-- - Each MaxPlus instance should obey the Semigroup laws (except
--   annihilation)
-- - max(answer(a), answer(b)) == answer(max(a, b))
-- - sum(answer(a), answer(b)) >= answer(sum(a, b))
--
-- These would be good targets for property-based testing.  The open
-- issue is generating well-typed synthetic Access, Use, or
-- CollapsedUse terms.
--
-- One way to do that would be to
-- - Generate a type for a binding -- an array, indexed by a product
--   or sum-typed index, with given elements or alternatives, etc.
-- - Generate an Access for a binding of that type
--   - Generate some free index names
--   - When generating a `for`, generate a new index name
--   - When generating a Location, generate expressions according
--     to the binding's type
--
-- Issue: What type to make the generated iteration-space binders?
-- Make something up and hope expressions become possible?  Reuse
-- (parts of) the type of the binding?  Make a type variable and infer
-- it based on leaf Location expressions?
