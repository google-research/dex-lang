-- Copyright 2022 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE StrictData #-}
{-# LANGUAGE UndecidableInstances #-}

module Occurrence where

import Prelude hiding (abs, iterate, max, sum)
import Prelude qualified

import Control.Monad.State.Strict
import Data.Hashable
import Data.IntMap.Strict qualified as M
import Data.List (foldl')
import Data.Store (Store (..))
import GHC.Generics (Generic (..))

import IRVariants
import Name

-- === Use Analysis ===

-- We want to know how a binding is used in a Dex program, so as to
-- know whether inlining it is guaranteed to conserve work and code
-- size.

-- Conservation of code size is easy.  Coservation of work, however,
-- is more subtle.  Inlining the computation of x into
--   for i. x
-- does not conserve work (unless the index set has size 0 or 1), but
-- inlining x into
--   for i. x.i
-- does conserve work -- provided we have access to the loop body
-- that constructs it so we can beta-reduce against the indexing
-- operation.

-- The main difficulty is that Dex allows indexing by expressions
-- other than referencing a loop binder, so to solve subtle cases we
-- need to translate iteration-space expressions into data-space.
-- For example, inlining x into
--   for i. x.(Left i)
--   for j. x.(Right j)
-- conserves work, because the two injections have disjoint ranges.

-- We proceed with a four-phase translation.
--
-- - Phase 1 translates Dex source into the Access structure.  An
--   Access mirrors the control pattern of the Dex source, abstracting
--   away most Dex syntax but still referring to iteration space.
--   Access retains nearly complete usage information.
--
-- - Phase 2 transposes Access into Use by turning iteration space
--   into data space.  (Use is like Access, except organized in data
--   space.)  Use retains about the same amount of usage information
--   as Access.
--
-- - Phase 3 collapses Use into CollapsedUse.  This process normalizes
--   the subsets of the data space that are actually accessed, such as
--   realizing that the subsets of all `Left` values and all `Right`
--   values cannot intersect.  This is where most of the
--   overapproximations are; CollapsedUse forgets much of the
--   detailed usage information Use retained.
--
-- - Phase 4 actually extracts the inlining-relevant information from
--   CollapsedUse.

-- === Algebra ===

-- The algebraic structure we want in order to represent uses is
-- max-plus: max corresponds to `if` or `case` in the Dex program, and
-- plus corresponds to multiple sequential statements.
--
-- This is almost a semiring, in that
-- - max and plus are both monoids
-- - max (and plus) are commutative
-- - plus distributes over max
-- - however, in our case, all actual uses that will occur are
--   "positive", which means we can use `zero` (the identity for plus)
--   as the identity for max as well, except that it then doesn't obey
--   the annihilation law.

class MaxPlus a where
  zero :: a
  max :: a -> a -> a
  plus :: a -> a -> a

instance (MaxPlus a) => MaxPlus (NameMap c a n) where
  zero = mempty
  max  = unionWithNameMap max
  plus = unionWithNameMap plus

deriving instance (MaxPlus (e n)) => MaxPlus (NameMapE c e n)

-- === Access ===

-- We represent an upper bound on the pattern by which (the object
-- bound to) a name is accessed.  The goal is to determine whether
-- inlining the name could duplicate work, so this is an upper bound
-- (as opposed to an estimate or a lower bound).

-- Each element (or subarray) of the object may be accessed a known or
-- unbounded number of times.  We also highlight "accessed once" and
-- "not accessed" as patterns, because that's what will mainly
-- determine inlining decisions.

-- We also use the Count type to count how many times a binding is
-- referenced statically.

data Count =
    Bounded Int
  | Unbounded
  deriving (Eq, Ord, Show, Generic)

instance Hashable Count
instance Store Count

pattern Zero :: Count
pattern Zero = Bounded 0

pattern One :: Count
pattern One = Bounded 1

pattern Two :: Count
pattern Two = Bounded 2

instance MaxPlus Count where
  zero = Zero
  max Unbounded _ = Unbounded
  max _ Unbounded = Unbounded
  max (Bounded i1) (Bounded i2) = Bounded $ i1 `Prelude.max` i2
  plus Unbounded _ = Unbounded
  plus _ Unbounded = Unbounded
  plus (Bounded i1) (Bounded i2) = Bounded $ i1 + i2

instance Bounded Count where
  maxBound = Unbounded
  minBound = zero

-- An access bound for a compound object determines some paths to some
-- leaves or subtrees of the object, and how many times that leaf or
-- subtree is accessed (at most).  Note that the access bound may
-- depend on names in the scope `n`, such as indices of enclosing
-- loops.

-- The Access represents accesses in "iteration space", i.e., the
-- binders in the `ForEach` constructors correspond to loops in the
-- user program.
data Access (n::S) where
  -- This chain of indices of this object is accessed this many times.
  -- Corresponds to indexing.
  Location :: [IxExpr n] -> Count -> Access n
  -- The object may be accessed in any one of these ways (as, e.g., in
  -- different arms of a downstream `case` expression).
  -- Corresponds to case expressions.
  Any :: [Access n] -> Access n
  -- The object may be accessed in some or all of these ways (e.g.,
  -- from multiple references).
  -- Corresponds to sequential statements (e.g., x.i; x.j)
  All :: [Access n] -> Access n
  -- The object may be accessed in any of the ways given by the second
  -- argument, as the name in the `Binder` argument varies over its
  -- type.
  -- Corresponds to `for`.
  ForEach :: forall n l. (NameBinder (AtomNameC SimpIR) n l) -> Access l -> Access n

deriving instance Show (Access n)

accessOnce :: Access n
accessOnce = Location [] One

accessMuch :: Access n -> Access n
accessMuch = \case
  Location ixs _ -> Location ixs Unbounded
  Any as -> Any $ map accessMuch as
  All as -> All $ map accessMuch as
  ForEach b a -> ForEach b $ accessMuch a

-- Prepend the given indexing expression onto an existing Access
location :: IxExpr n -> Access n -> Access n
location ix (Location ixs a) = Location (ix:ixs) a
location _ _ = error "Cannot nest general Access in Location"

-- These are the indexing expressions we model.  An IxExpr n is an abstraction
-- of a function from names in the n scope, to either a single index location or
-- to a set of index locations.  We only track the operations we have a hope of
-- being able to analyze usefully.
data IxExpr (n::S) =
  -- Indexing by an identifier in scope
    Var (Name (AtomNameC SimpIR) n)
  -- An index of product type
  | Product [IxExpr n]
  -- An index of sum type
  | Inject Int (IxExpr n)
  -- Unknown deterministic function of the given names
  | Deterministic [Name (AtomNameC SimpIR) n]
  -- All indices are accessed, or we are conservatively assuming they are
  -- because we don't know which are accessed.  See note "IxAll semantics" in
  -- "Notes".
  | IxAll
  -- TODO(precision) Could add more constructors to capture other indexing
  -- expressions, such as `from_ordinal _ $ ordinal i + 1`.  If that's
  -- the only indexing expression the binding is safe to inline, and
  -- inlining even preserves locality, not just work.
  deriving (Eq, Ord, Show)

-- We give Access semantics by a notional translation into a piece of
-- code that dynamically counts the number of times every index is
-- actually accessed.  Except, Access intentionally loses information,
-- so the semantics of Access is actually a program that has some
-- control path that accesses at least as much as the original.
--
-- - An Access becomes a function consuming a buffer reference
--   and returning unit.  The buffer has the same type as the
--   object whose accesses we are analyzing, except for integer
--   leaves.
--
-- - For every control path of the source program, there is a control
--   path of the Access program that accumulates at least as many
--   counts into each element of the buffer as the number of times the
--   source program read that element.
--
-- - `Location exprs ct` turns into accumulation
--     \ref. ref!<exprs> += ct
--     Note that this += must be understood as pointwise if
--     the source indexing expression is not fully saturated.
--
-- - `Any opts` turns into case
--     \ref. index = randint $ length opts
--       case index of
--         1 -> compile opt1 ref
--         2 -> compile opt2 ref
--         ...
--
-- - `All parts` turns into sequentialization
--     \ref.
--       compile part1 ref
--       compile part2 ref
--       ...
--
-- - `ForEach b sub` is iteration
--     \ref. for b in (type of b).
--       compile sub ref
--   The type that `b` iterates over can in principle be fetched from
--   the Dex program that led to this `ForEach` constructor.  It only
--   matters for the semantics, so we don't actually store it.

instance MaxPlus (Access n) where
  zero = Location [] Zero
  a1 `max` a2 = Any [a1, a2]
  a1 `plus` a2 = All [a1, a2]

-- === Use ===

-- The Use structure is a "data space" representation of accessing
-- arrays.
--
-- A Use implicitly iterates over as many dimensions of the accessed
-- object as there are nesting levels of At constructors in the Use.
-- We do not use explicit binders for this because they always appear
-- in the same nesting order, so it's simplest to leave them implicit.
-- For example, the case
--   xs = ...
--   for i. for j. xs.i.j
-- is represented by the Use
--   At IxAll (At IxAll One)
-- meaning "we access every element or subarray once, two dimensions
-- deep".
--
-- Note that a Use can still depend on iteration-space indices (from
-- the `iter` scope)---it just doesn't have internal binders that are
-- meant to be interpreted in iteration space.  For example, the Use
-- for `xs` in
--   for i.
--     xs = ...
--     xs.i
-- is
--   At (Var i) One
-- meaning that `xs` is accessed at the location `i`.

data Use (iter::S) =
  -- The object is accessed in its entirety
    Const Count
  -- The object is accessed at the positions given by the first
  -- argument.  The subarray at those positions is accessed according
  -- to the sub-Use.  Note that at this point we permit the `IxAll`
  -- constructor in `IxExpr`, so an `IxExpr` may represent a set of
  -- positions.
  | At (IxExpr iter) (Use iter)
  -- The object is accessed in at most one of the given Use patterns.
  | Max [Use iter]
  -- The object is accessed in all of the given Use patterns.
  | Sum [Use iter]
  deriving (Eq, Show)

-- The semantics of Use are similar to those for Access.  Here is the
-- compilation that turns a Use into a program that dynamically counts
-- how many times each index is used.
--
-- Note that IxExpr permits the `IxAll` constructor, so an `IxExpr`
-- represents a subset of indices rather than a single index.
--
-- - `Const ct` becomes accumulation
--     \ref. ref += ct
--     Also polymorphic in the ref type, applying elementwise
--
-- - `Max alts` becomes case
--     \ref. case randint (length alts) of
--       1 -> compile alt1 ref
--       2 -> compile alt2 ref
--       ...
--
-- - `Sum parts` becomes sequencing
--     \ref.
--       compile alt1 ref
--       compile alt2 ref
--       ...
--
-- - `At expr use` becomes testing and slicing
--     \ref. for b in <next object dim>.
--       if b in expr then (compile use ref!b)

-- This semantics implies a transformation that we perform eagerly:
-- - It's safe to distribute Sum into Max, so that Max ends up on the
--   outside.

-- All the At constructors created by `interp`, below, on any path
-- through a sound Access refer to the same dimensions of the object
-- being indexed, in the same order, with no gaps.  Why?  Because each
-- is introduced at the same point in the sequence of index
-- expressions applied to the object, regardless of the
-- iteration-space control path that got there.
--
-- Another way to see this is that the compilation of At is the only
-- thing that cares about and alters the type of the reference being
-- passed around.  Ergo, all the At constructors must occur in the
-- same order.

-- === Tropical semiring on Use ===

-- We lightly normalize Use data under these operations.  The main
-- invariants are
--
-- - Max constructors appear outside of adjacent Sum constructors
-- - If the `Use` represents no use, it's represented as `Const Zero`
--
-- We also take the opportunity to peephole-simplify the Use
-- structure.

instance MaxPlus (Use iter) where
  zero = Const zero

  max (Const Unbounded) _ = Const Unbounded
  max _ (Const Unbounded) = Const Unbounded
  max (Const b1) (Const b2) = Const $ b1 `max` b2
  max (Max uses1) (Max uses2) = Max $ uses1 ++ uses2
  -- This is trying to eliminate zero-valued elements, because they can cause
  -- (potentially severe) loss of precision downstream.  However, that relies on
  -- upstream construction canonicalizing all semantically-zero Uses to the
  -- `zero` use.
  -- TODO Prove or unit-test that upstream cannot construct semantically-zero
  -- Use objects that are not `== zero`.
  max (Max uses1) use2
    | use2 == zero = Max uses1
    | otherwise = Max $ uses1 ++ [use2]
  max use1 (Max uses2)
    | use1 == zero = Max uses2
    | otherwise = Max $ use1:uses2
  max use1 use2
    | use1 == zero = use2
    | use2 == zero = use1
    | otherwise = Max [use1, use2]

  plus (Const Unbounded) _ = Const Unbounded
  plus _ (Const Unbounded) = Const Unbounded
  plus (Const b1) (Const b2) = Const $ b1 `plus` b2
  plus (Max uses1) (Max uses2) = Max uses' where
    uses' = concat $ flip map uses1 (\use1 ->
      flip map uses2 \use2 -> plus use1 use2)
  plus u1@(Max _) use2
    | use2 == zero = u1
    | otherwise = plus u1 (Max [use2])
  plus use1 u2@(Max _)
    | use1 == zero = u2
    | otherwise = plus (Max [use1]) u2
  plus (Sum uses1) (Sum uses2) = Sum $ uses1 ++ uses2
  plus (Sum uses1) use2
    -- TODO(code cleanliness) Is there a way to deduplicate these zero checks?
    | use2 == zero = Sum uses1
    | otherwise = Sum $ uses1 ++ [use2]
  plus use1 (Sum uses2)
    | use1 == zero = Sum uses2
    | otherwise = Sum $ use1:uses2
  plus use1 use2
    | use1 == zero = use2
    | use2 == zero = use1
    | otherwise = Sum [use1, use2]

-- === Interpreting Access into Use ===

-- The main interpreter is pretty straightforward.  The main trick is
-- just semantics: an indexing expression becomes a (nested) `At`,
-- which represents a data-space loop that checks that the data-space
-- variable equals the indexing expression.
interp :: Access iter -> Use iter
interp = \case
  Location [] ct -> Const ct
  Location (expr:exprs) ct -> At expr $ interp $ Location exprs ct
  Any accesses -> foldl'  max zero $ map interp accesses
  All accesses -> foldl' plus zero $ map interp accesses
  ForEach b access -> iterate False b $ interp access

-- The interesting function is resolution of iteration-space loops.
-- We have to construct a Use that can refer to subsets of data space
-- (as opposed to single points, as in Access).
-- The `Bool` argument means "have we already observed that upstream
-- indexing touches different parts of the object?"  Even if the
-- answer is "yes", we do still have to recur, because we need to
-- translate the interation-space binder into data space.

iterate :: Bool -> (NameBinder (AtomNameC SimpIR) iter iter')
          -> Use iter' -> (Use iter)
iterate True _ (Const ct) = Const ct
iterate False _ (Const ct) =
  -- If we haven't proven upstream that indexing is injective,
  -- we have to assume here that it collides with itself.
  -- e.g., for i. xs
  -- Note: If we have a bound on the size of the index set traversed
  -- by `ib`, then we can compute a bound on the number of accesses,
  -- but there's no need to do that until we make inlining decisions
  -- on a more fine-grained basis than "was this used more than once?"
  if ct == zero then zero else Const Unbounded
iterate injective ib (At expr use) = At expr' use' where
  (expr', injective') =
    flip runState injective $ iterateIxExpr ib expr
  use' = iterate injective' ib use
iterate injective ib (Max uses) =
  -- TODO(correctness) This can be an underapproximation if the upstream
  -- structure becomes expressive enough, but it's OK for now.  For example,
  -- consider the access pattern
  --   for i.
  --     if ...
  --       then xs.i
  --       else xs.(i+1)
  -- Here inlining xs will in general duplicate work, because the `if`
  -- could go different ways in different iterations, thus accessing
  -- some elements of `xs` more than once (and others not at all).
  --
  -- However, if we were to distribute the `for` into the `if` as
  -- this code does, we would get
  --   if ...
  --     then for i. xs.i
  --     else for i. xs.(i+1)
  -- Now, `xs` _is_ work-preserving to inline here, because each
  -- branch accesses each element of `xs` only once.  So mistaking
  -- the former for the latter would be a mistake.
  --
  -- However, the current Access structure cannot actually _prove_
  -- that inlining `xs` into the latter expression is safe, because
  -- the addition will register as an unknown function of `i`.  The
  -- distribution bug is therefore masked.
  --
  -- In fact, that currently always happens.  All distinct functions
  -- that produce indices of type n that Access can currently
  -- represent are either `Deterministic` or have disjoint ranges, so this
  -- kind of underapproximation cannot yet lead to a mistaken
  -- assertion that some binding is safe to inline.
  foldl' max zero $ map (iterate injective ib) uses
iterate injective ib (Sum uses) =
  foldl' plus zero $ map (iterate injective ib) uses

iterateIxExpr :: NameBinder (AtomNameC SimpIR) iter iter'
              -> IxExpr iter' -> State Bool (IxExpr iter)
iterateIxExpr ib (Var i) =
  case hoist ib i of
    HoistSuccess i' -> return $ Var i'
    HoistFailure _ ->
      -- If we hit a reference to the iteration binder,
      -- that constitutes a proof that indexing is injective,
      -- because all constructors of `IxExpr` that this could
      -- be nested under represent invertible functions.
      -- If we were already injective, this case is an
      -- over-approximation: the object is actually accessed at just
      -- one value of the index, but since we don't know which one, we
      -- assume it was all of them.
      put True >> return IxAll
iterateIxExpr ib (Product elts) =
  -- Rectangular approximation to something like xs.(j, j)
  Product <$> mapM (iterateIxExpr ib) elts
iterateIxExpr ib (Inject i elt) =
  Inject i <$> iterateIxExpr ib elt
iterateIxExpr ib (Deterministic names) =
  case hoist ib (ListE names) of
    HoistSuccess (ListE names') -> return $ Deterministic names'
    -- If we hit a reference to an unknown function of the binder, we
    -- must assume it can hit any data index (which we
    -- over-approximate as it hitting all of them); and we also do not
    -- gain a proof that the indexing is injective, because different
    -- values of the iteration-space binder could lead to the same
    -- value of the data-space binder.
    HoistFailure _ -> return IxAll
iterateIxExpr _ IxAll = return IxAll

-- === CollapsedUse ===

-- CollapsedUse is like Use, but now it is also independent of binders
-- in scope outside the inlining decision under consideration.
-- Collapsing Use into CollapsedUse perforce over-approximates those
-- binders, potentially severely.

-- A CollapsedUse is either a count of the accesses to the whole
-- object, or a subset of the leading dimension of the object.  In the
-- latter case, the object is not accessed outside that subset.  The
-- Subset structure maintains a map of further subsets, and how later
-- dimensions are accessed in each of them.

-- Note that we care not just about which elements are used, but also
-- the indexing depth of the object.  That is `CConst One` and
-- `CSubset (SAll (CConst One))` both mean "used everywhere exactly
-- once", but the latter also means "do not inline unless you have an
-- explicit `for` to cancel against indexing".
data CollapsedUse =
    CConst Count
  | CSubset (Subset CollapsedUse)
  deriving (Eq, Show)

-- A subset of an index type.  The constructors correspond to possible
-- index types---each one gives known information about the structure
-- of the type, and relevant available subset information.
-- A trie on subtypes of an index type that supports subset
-- intersection as efficiently as is practicable.
data Subset a =
  -- The index could be any type, and all of it is accessed.
    SAll a
  -- The index is a sum.  We maintain a map from constructors to
  -- subsets of their respective types.  The Maybe is a performance
  -- optimization: a `(Just a)` is associated with the whole type,
  -- which we just store here instead of broadcasting it over all the
  -- cases.
  | Inj  (Maybe a) (M.IntMap (Subset a))
  -- The index is a product.  We maintain one rectangle as a subset.
  | Prod [Subset ()] a
  deriving (Eq, Show)

-- === Collapsing Use to CollapsedUse ===

collapse :: Use iter -> CollapsedUse
collapse (Const ct) = (CConst ct)
collapse (At expr use) =
  let use' = collapse use in
  if use' == zero then zero
  else CSubset $ exprToSubset expr use'
collapse (Sum uses) = foldl' plus zero $ map collapse uses
collapse (Max uses) = foldl' max zero $ map collapse uses

exprToSubset :: IxExpr n -> a -> Subset a
-- An iteration-space variable approximates to "all", because at this
-- point it can take any value.  This is a severe over-approximation,
-- but simplifies the structure.
--
-- - In particular, distinct iteration-space variables will collide
--   rarely, but we conservatively assume they always do.  Consider
--   inlining x into
--     for i. x.j.i
--     for i. x.k.i
--   where j and k are free outside the binding of x.  Whenever j and
--   k are distinct, inlining leads to savings; potentially large
--   savings if the j and k spaces are large.  But, they may
--   occasionally be equal, in which case inlining would duplicate
--   work (but on just those elements).  We conservatively miss this
--   inlining opportunity, but perhaps should revisit that.
exprToSubset (Var _) x = SAll x
exprToSubset (Product exprs) x = Prod (map (flip exprToSubset ()) exprs) x
exprToSubset (Inject i expr) x =
  Inj Nothing $ M.singleton i $ exprToSubset expr x
exprToSubset IxAll   x = SAll x
-- A Deterministic that survies to this point should only reference
-- iteration-space variables that are scoped over the entire inlining,
-- like the `Var` constructor.  We overapproximate with `SAll` for the
-- same reason.
exprToSubset (Deterministic _) x = SAll x

instance MaxPlus CollapsedUse where
  zero = CConst zero

  plus :: CollapsedUse -> CollapsedUse -> CollapsedUse
  plus (CConst ct1) (CConst ct2) = CConst $ ct1 `plus` ct2
  plus (CSubset s1) (CSubset s2) = CSubset $ s1 `plus` s2
  plus (CSubset s1) (CConst ct2)
    | ct2 == zero = CSubset s1
    | otherwise = CSubset $ s1 `plus` (SAll (CConst ct2))
  plus (CConst ct1) (CSubset s2)
    | ct1 == zero = CSubset s2
    | otherwise = CSubset $ (SAll (CConst ct1)) `plus` s2

  max :: CollapsedUse -> CollapsedUse -> CollapsedUse
  max (CConst ct1) (CConst ct2) = CConst $ ct1 `max` ct2
  max (CSubset s1) (CSubset s2) = CSubset $ s1 `max` s2
  max (CSubset s1) (CConst ct2)
    | ct2 == zero = CSubset s1
    | otherwise = CSubset $ s1 `max` (SAll (CConst ct2))
  max (CConst ct1) (CSubset s2)
    | ct1 == zero = CSubset s2
    | otherwise = CSubset $ (SAll (CConst ct1)) `max` s2

-- === Subset operations ===

instance MaxPlus () where
  zero = ()
  max _ _ = ()
  plus _ _ = ()

instance MaxPlus a => MaxPlus (Subset a) where
  zero = SAll zero
  max = smerge max
  plus = smerge plus

smerge :: MaxPlus a => (a -> a -> a) -> Subset a -> Subset a -> Subset a
smerge merge (SAll a1) (SAll a2) = SAll $ merge a1 a2
smerge merge (SAll a) i@(Inj _ _) = smerge merge (Inj (Just a) M.empty) i
smerge merge i@(Inj _ _) (SAll a) = smerge merge i (Inj (Just a) M.empty)
smerge merge (Inj a1 elts1) (Inj a2 elts2) = Inj a' elts' where
  a' = case (a1, a2) of
    (Nothing, Just a)  -> Just a
    (Just a, Nothing)  -> Just a
    (Just a1', Just a2') -> Just $ merge a1' a2'
    (Nothing, Nothing) -> Nothing
  elts' = M.unionWith (smerge merge) elts1 elts2
smerge merge (Prod elts1 a1) (Prod elts2 a2) = Prod elts' a' where
  -- We approximate the max or the sum of two rectangles as the
  -- smallest rectangle that contains them.
  -- TODO(precision) This needlessly loses precision if one of the aruments is
  -- actually a zero use; but we hope they are all normalized away upstream.
  elts' = zipWith max elts1 elts2
  -- The payload of that rectangle is the requested merge if the
  -- arguments intersect, but always the max if they do not.
  a' = if all id $ zipWith intersect elts1 elts2 then
         merge a1 a2
       else
         -- always max, regardless of the merge function
         a1 `max` a2
smerge merge (SAll a1) (Prod _ a2) = SAll $ merge a1 a2
smerge merge (Prod _ a1) (SAll a2) = SAll $ merge a1 a2
smerge _ (Inj _ _) (Prod _ _) = error "Impossible: index type both a sum and a product"
smerge _ (Prod _ _) (Inj _ _) = error "Impossible: index type both a sum and a product"

intersect :: Subset a -> Subset a -> Bool
intersect (SAll _) _ = True
intersect _ (SAll _) = True
intersect (Inj (Just _) _) _ = True
intersect _ (Inj (Just _) _) = True
intersect (Inj Nothing elts1) (Inj Nothing elts2) =
  not $ M.null $ M.intersection elts1 elts2
intersect (Prod elts1 _) (Prod elts2 _) =
  all id $ zipWith intersect elts1 elts2
intersect (Inj _ _) (Prod _ _) = error "Impossible: index type both a sum and a product"
intersect (Prod _ _) (Inj _ _) = error "Impossible: index type both a sum and a product"

-- === Overapproximating a CollapsedUse with a final Count ===

type DynUseInfo = (Int, Count)  -- The int is maximum number of indexed dimensions

instance MaxPlus Int where
  zero = 0
  max = Prelude.max
  plus = (+)

instance (MaxPlus a, MaxPlus b) => MaxPlus (a, b) where
  zero = (zero, zero)
  (a1, b1) `max` (a2, b2) = (a1 `max` a2, b1 `max` b2)
  (a1, b1) `plus` (a2, b2) = (a1 `plus` a2, b1 `plus` b2)

class ApproxConst a where
  approxConst :: a -> DynUseInfo

instance ApproxConst CollapsedUse where
  approxConst (CConst ct) = (0, ct)
  approxConst (CSubset subset) = (1, zero) `plus` approxConst subset

instance ApproxConst a => ApproxConst (Subset a) where
  approxConst (SAll use) = approxConst use
  approxConst (Inj (Just all_use) uses) =
    -- TODO(optimization) Short-circuit if the all_use is heavy enough
    approxConst all_use `plus` approxConst uses
  approxConst (Inj Nothing uses) = approxConst uses
  approxConst (Prod _ use) = approxConst use

instance ApproxConst v => ApproxConst (M.IntMap v) where
  approxConst uses = foldl' max zero $ map approxConst $ M.elems uses

-- === Usage info including static usage ===

-- The `Count` is the count of static occurrences, i.e., how many times
-- references to this binding occur in the source code.  We track this
-- separately from the (dynamic) Access so we can control code blow-up during
-- inlining.
data AccessInfo n = AccessInfo Count (Access n)
  deriving (Show)

instance MaxPlus (AccessInfo n) where
  zero = AccessInfo zero zero
  -- Note that, since `max` corresponds to `case`, the static count is
  -- still added
  (AccessInfo s1 d1) `max` (AccessInfo s2 d2) =
    AccessInfo (s1 `plus` s2) $ d1 `max` d2
  (AccessInfo s1 d1) `plus` (AccessInfo s2 d2) =
    AccessInfo (s1 `plus` s2) $ d1 `plus` d2

instance SinkableE AccessInfo where
  sinkingProofE rename (AccessInfo n a) = AccessInfo n $ sinkingProofE rename a

data UsageInfo = UsageInfo Count DynUseInfo  -- The `Count` is the static use count
  deriving (Eq, Generic, Show)

instance MaxPlus UsageInfo where
  zero = UsageInfo zero zero
  -- Note that, since `max` corresponds to `case`, the static count is
  -- still added
  (UsageInfo s1 d1) `max` (UsageInfo s2 d2) =
    UsageInfo (s1 `plus` s2) $ d1 `max` d2
  (UsageInfo s1 d1) `plus` (UsageInfo s2 d2) =
    UsageInfo (s1 `plus` s2) $ d1 `plus` d2

usageInfo :: AccessInfo n -> UsageInfo
usageInfo (AccessInfo s dyn) =
  UsageInfo s $ approxConst $ collapse $ interp dyn

-- === Notes ===

-- Projection (inlining tuple-typed bindings)
--
-- Adding Projection is pretty easy: projections slice the reference,
-- so have a defined order interleaved with At.
-- - If a body is parametrically polymorphic in the reference, it's safe
--   to wrap it with a sum of all the projections
-- - So does this mean that Projections will be places where formal Sums
--   and Maxes have to rest?  That seems annoying.
-- - I think it's the case that a Sum-Max tree over Projections, where
--   everything underneath is parametrically polymorphic in the
--   reference type (i.e., when we are computing the final answer),
--   can just become the relevant sums and maxes of the pieces.  (Sum
--   over projecting to distinct indices turns into max; sum over
--   colliding indices turns into sum; max turns into max whether the
--   indices collide or not.)
--   - max over Sum [Projection-with-distinct-indices] can be approximated as
--     Sum [indexwise max], but I only want to do that once I've accumulated
--     all the maxes I am going to?  Or does that not matter?
--   - So maybe Sum [Projection-with-distinct-indices] is a normal form
--     without needing formal Max nodes?
--   - Come to think of it, is the same thing true of At?

-- Sum and Max
--
-- In general:
-- - max over Sum unions the indices and does an indexwise max and emits Sum
-- - max over Max unions the indices and does an indexwise max and emits Max
-- - sum over Sum unions the indices and does an indexwise sum and emits Sum
-- - sum over Max unions the indices and does an indexwise sum and emits Max
-- - So if I'm never going to turn formal Sum or Max nodes back into sum or max
--   operations, there is no difference between them.
-- - At the end, when approximating with Const, I max over distinct indices
--   regardless of whether it's a formal Max or a formal Sum node.
-- - However, the distinction between Sum and Max matters if I'm trying to
--   compute whether a given object is accessed exactly once everywhere,
--   so as to try to inline an effectful operation.  (That said, inlining
--   effects also requires paying attention to the order of the accesses.)

-- IxAll semantics
--
-- IxAll can actually also mean "accessed at one unknown index".  Logically this
-- is fine because the Access is an overapproximation.  It can arise when, e.g.,
-- indexing by the content of a reference, since the analysis doesn't trace what
-- values might occupy that reference.
--
-- Some examples may help clarify.
--
-- Example 1
--   xs = for ...
--   with_state ... \ref.
--     xs.(get ref)
--
-- - The indexing is represented by `Location IxAll One`
-- - It doesn't change when it goes above the `ref` binder
-- - `xs` will look inlinable, which is fine because it's only accessed once.
--   In fact, it's probably very beneficial to inline `xs` because it's only
--   accessed at one location, but the analysis doesn't notice that.
--
-- Example 2
--   xs = for ...
--   with_state ... \ref.
--     for i.
--       xs.(get ref)
--
-- - The indexing is represented by `Location IxAll One`
-- - Going above the `i` binder turns this into `Location IxAll Unbounded`
--   because there is no proof that the accesses are distinct across loop
--   iterations (and indeed they are not if the reference is not modified)
-- - `xs` will not look inlinable, which is sound and not even too conservative
--   because the same element may be accessed many times.
--
-- Example 3
--   xs = for n. for ...
--   with_state ... \ref.
--     for i.
--       xs.i.(get ref)
--
-- - The outer indexing is represented by `Location IxAll One`
-- - The inner indexing is represented by `Location (Var i) (Location IxAll One)`
-- - Going above the `i` binder turns this into `Location IxAll (Location IxAll
--   One)`.  This is sound because there _is_ a proof that the accesses are
--   distinct across loop iterations -- each `xs.i` subarray is accessed in at
--   most one unknown location.
-- - `xs` will look inlinable.
--
-- TODO(precision) Could add a constructor to IxExpr to model "accessed at just
-- one unknown index", which might support trying harder to inline an array if
-- very few of its elements are actually read.  The case to imagine is a big
-- array whose elements have fairly uniform costs to compute, and which is
-- accessed at just a few (potentially colliding) indices.  Then inlining
-- duplicates work on some elements, but saves work overall.  The current
-- analysis would, however, conservatively avoid inlining such an array because
-- of the per-element work duplication.

-- === Boring instances ===

instance GenericE IxExpr where
  type RepE IxExpr = EitherE5
    (Name (AtomNameC SimpIR))
    (ListE IxExpr)
    (PairE (LiftE Int) IxExpr)
    (ListE (Name (AtomNameC SimpIR)))
    UnitE
  fromE = \case
    (Var n)            -> Case0   n
    (Product ixs)      -> Case1 $ ListE ixs
    (Inject i ix)      -> Case2 $ PairE (LiftE i) ix
    (Deterministic ns) -> Case3 $ ListE ns
    IxAll              -> Case4   UnitE
  {-# INLINE fromE #-}
  toE = \case
    (Case0 n) -> Var n
    (Case1 (ListE ixs)) -> Product ixs
    (Case2 (PairE (LiftE i) ix)) -> Inject i ix
    (Case3 (ListE ns)) -> Deterministic ns
    (Case4 UnitE) -> IxAll
    _ -> error "impossible"
  {-# INLINE toE #-}

instance HoistableE IxExpr
instance SinkableE IxExpr
instance RenameE IxExpr

instance GenericE Access where
  type RepE Access = EitherE4
    (PairE (ListE IxExpr) (LiftE Count))
    (ListE Access)
    (ListE Access)
    (Abs (NameBinder (AtomNameC SimpIR)) Access)
  fromE = \case
    (Location ixs ct) -> Case0 $ PairE (ListE ixs) (LiftE ct)
    (Any as) -> Case1 $ ListE as
    (All as) -> Case2 $ ListE as
    (ForEach b a) -> Case3 $ Abs b a
  {-# INLINE fromE #-}
  toE = \case
    (Case0 (PairE (ListE ixs) (LiftE ct))) -> Location ixs ct
    (Case1 (ListE as)) -> Any as
    (Case2 (ListE as)) -> All as
    (Case3 (Abs b a))  -> ForEach b a
    _ -> error "impossible"
  {-# INLINE toE #-}

instance HoistableE Access
instance SinkableE Access
instance RenameE Access

instance GenericE AccessInfo where
  type RepE AccessInfo = PairE (LiftE Count) Access
  fromE (AccessInfo s dyn) = PairE (LiftE s) dyn
  {-# INLINE fromE #-}
  toE (PairE (LiftE s) dyn) = AccessInfo s dyn
  {-# INLINE toE #-}

instance HoistableE AccessInfo
instance RenameE AccessInfo

instance Hashable UsageInfo
instance Store UsageInfo
