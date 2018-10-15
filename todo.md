# Todo ordered (easy things)
  * implement reduce and check matmul
  * sugar
    * multi-let/lam/idxcomp
    * top-level lambda without '\'

  * repl with partial programs
    * including non-crashing parse errors and type errors (don't need to be helpful)

  * product and record types

  * sqlite i/o

  * type inference (and print types)
  * string/float/bool types




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
    * multi-let/lam/idxcomp
    * top-level lambda without '\'
  * builtins
    * reduce
    * group by
  * floats/strings
  * in/out: csv/sql input
  * non-invertible output: ggplot, pretty-print
  * anonymous sum, product and record types
  * repl: printing parses, types, etc, values, etc
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
  * SQL backend
  * Halide backend
  * LLVM backend


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
