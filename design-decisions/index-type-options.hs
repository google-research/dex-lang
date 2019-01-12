

-- do type variables range over closed types with quantifiers?

data T = BaseT BaseT
       | Var V
       | Pair T T
       | Tab IdxT T
       | Forall V T
       | Exists V T

data IdxT = IdxTVar V
          | IdxT ElementT Set
          | IdxPair IdxT IdxT -- needed?

data ElementT = IBaseT BaseT
              | ElementVar V
              | ElementPair ElementT ElementT

data Set = ConcreteSet [IdxVal]
         | SetVar V
         | SetPair Set Set  -- needed?

type V = String
data BaseT = Int | String | Real


-- Questions
 -- do we need IdxPair and/or SetPair
 -- do we need ElementT at all or are sets enough?

-- examples
-- a[b]=>c
-- Int[a]=>b
-- (Int,String)[(a,b)]=>c
-- Int[(a,b)]=>c -- problem

-- quantifier at level of type, not index type, so no way for index variables to
-- range over quantifiers. That means these must be rectangular:
-- Int[i]=>Int[j]=>a
-- Int[i]=>Int[j]=>a -> b
-- (Int,Int)[(i,j)] => a   -- requires IdxSetPair constructor
-- (Int[i],Int[k]) => a    -- requires IPair constructor. Same thing as above?
-- (i, j)=>b               -- requires IPair constructor
-- (Int[i], a[j])=>b

-- But not these
-- (Int,Int)[i] => a -- uses IdxElementPair , natural friends with IdxSetPair
-- Int[i]=> E.i (Int[j]=>a)


-- Without IdxElementPair, we can't express non-rectangular tuple-index tables!
-- So that probably rules out IdxPair
-- Unclear if we want/need IdxSetPair
--   It's needed for faithfully uncurrying rectangular arrays. So maybe we want it.
-- need some bounded quantification to handle coupling of element type to set?
  -- e.g. `i` is limited to integer sets in `a[i]=>b`


-- version with no element types at all

data T = BaseT BaseT
       | Var V
       | Pair T T
       | Tab Set T
       | Forall V T
       | Exists V T

data Set = ConcreteSet BaseT [IdxVal]
         | ProductSet Set Set -- necessarily rectangular
         | SetVar V

-- examples
-- a=>c
-- i=>j=>b
-- (i,j)=>b
-- (Int[0,1,2],j)=>b

-- But can't express `Int[i]=>a` or `e[i]=>a`

-- Appealingly simple
-- No way to separately specify element type. How do we type `for i: i`?
    -- maybe we could get away with an `iota :: i=>a -> i=>Int` instead
    -- (only lifts integer indices into value space but maybe that's enough)
-- Seems silly to pretend we don't know element types ahead of time
-- Can't satisfyingly type things like data in a database, where we know the
-- element types but not the set
-- Can't handle intersection semantics

-- overall, this version, sadly, seems like a non-starter
