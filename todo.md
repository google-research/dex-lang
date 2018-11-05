# Todo ordered (easy things)
  * evaluation with patterns
  * get rid of error and add writer (for constraints) to constrain monad?
  * syntax for named records (and make it consistent with tuple syntax)
  * make record traversable


  * product types
    * record types?
      * could singleton records reduce the need for newtype?)
      * enough to be worth playing with, I think
    * anonymous tuples?
    * might be easier to do all of these at once
    * data/newtype

  * fix weird trailing stuff parse failure e.g. : lam x y: reduce add 0 for i: x.i * y.i

  * raster/ggplot/canvas output?

  * write up explanation and make some demos

# Want
  * parallel
  * performant
  * functional
  * linear algebra and relational together (all of data science)
  * statically typed
  * io statically determined
  * partially rank-polymorphic

# Todo
* example programs
  * prelude: matmul, standard deviation, promote, normalize-over
  * summary stats (R-style workflow)
  * neural net training (manual derivatives)
  * --------------------

* language features
  * syntax
    * backslash to escape multiline assignments
    * comments
  * builtins
    * group by
  * floats/strings
  * in/out: csv/sql input
  * non-invertible output: ggplot, pretty-print
  * anonymous sum, product and record types
  * repl: printing parses, types, etc, values, etc
  * type decls (type parsing will also make tests easier to write)
  * --------------------
  * type annotations?
  * autodiff?
  * rank polymorphism?
  * make named indices more central?
  * static checking of keys etc?

* implementation
  * type inference/checking with HM
    * good example here:
      https://github.com/sdiehl/write-you-a-haskell/tree/master/chapter7/poly)
  * typed ast
    * nice implementation of STLC here:
      http://www.cs.ox.ac.uk/projects/gip/school/tc.hs
  * --------------------
  * arrays instead of maps
* execution backends
  * SQL backend
  * Halide backend
  * LLVM backend

* interactive outputs
  * sql-like
  * array-like view (last two dims as rectangle)
  * ggplot and raster images (b/w and color) - via canvas?
    * simplest: navigate up and down in extra dimensions
    * on ggplot and raster images, maybe even use faceting for extra dimensions...
    * auto-advance gives an animation
    * maybe handles/sliders for exploring extra dimensions


* design decisions
  * (at least initially) limit higher functions?
  * restrictions on values types - functions?
  * restrictions on key types - maps?


What's minimal for a demo to Martin/Misard?
  * prelude of core functions, repl example
  * relational and linalg
  * io: sql? pretty-printed table? ggplot?
  * types?
  * rank polymorphism?
  * not fancy backends?
  * maybe not names either?

purpose:
  * argue that it's a compelling programming model
  * justify spending time working on compiler side

Here's a plan:
  * get vanilla index comprehension language working first
  * write up examples and show people
  * figure out which parts are painful and thus need names, rank polymorphism
    etc
  * get buy-in to build backend


# Story with names
Here's the classic case: we want to write a function that normalizes a vector.
Then we want to apply it along a particular axis. We want everything statically
knowable, so we need to pass things like axis arguments as type-level params.
APL/remora does a rank/frame decomposition based on array shape and the
function's expected rank. But we'd like things to work for arbitrary key types.
If we want to apply a function `f :: kin=>v -> kout=>v` to `x :: k1=>v`, we need
to specify two mappings: `k -> (kextra, kin)` and `(kextra, kout) -> k2`.
Since it's just going to be about unpacking tuples (inc named tuples) this
doesn't sound too bad... Add some sugar for the common cases and this might
actually work pretty nicely. Actually, it's not too far off from
pattern-matching in the index comprehensions, so maybe it just desugars to that.
This, again, suggests implementing the vanilla version first, looking at what's
hard, and creating some sugar accordingly.

# typed map for interpreter, with gadts

How to implement e.g. map? The hard part is that we need to give it an untyped
function that we know is `a -> b` but is encoded as `Val -> Val`. At the very
least, I need to know ahead of time what the actual output type is. So let's
maybe revisit this once we have type inference.
