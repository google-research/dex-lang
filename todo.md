# Todo ordered (easy things)
  * .cod file format parser and pretty-printer
  * json i/o
  * ffi for calling shell scripts


  * orchestrate jax benchmarking from coddle

  * play with some data set
    * download R's datasets
    * write csvToSqlite (includes metadata about primary keys etc)

  * literate programming output
  * raster/ggplot/canvas output?
  * write up explanation and make some demos

  * records polymorphic?
    * this is going to get tricky. Let's get a working demo with some compelling
      examples before tackling it

# Want
  * parallel
  * performant
  * functional
  * linear algebra and relational together (all of data science)
  * statically typed
  * io statically determined
  * partially rank-polymorphic

# bugfixes
  * weird trailing stuff parse failure e.g. : lam x y: reduce add 0 for i: x.i * y.i


# Todo
* parser for non-csv user-entered tables
  * could also be used for literal tables in programs
  * can we use a joint parser-printer library like Data.Syntax
  * emacs mode to re-align


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


# textual representation for tabular data

We need to pretty-print tables. We also need an easy way to make table literals,
either in the source program or as a separate file. We also want to read
existing textual quasi-formats like csv but that could be separate.

{tab,whitespace,comma}-separated values are close. But we need a few more
features:
  * Explicitly typed columns (avoid the "OCT4 problem"!)
  * Distinction between primary keys and the rest
  * Multiple named tables in one file

Some more desiderata:
  * pretty-printing that's also a valid serialization
  * small delta from existing formats - e.g. csv
  * easy to edit in emacs etc
  * easy to read, possibly edit, with unix tools

The existing pretty-printing representation, seems reasonable.

One bifurcation is whether to use possibly-aligned spaces or tabs.
Tabs seem like the better approach (the tab explicitly means 'table'!)
But the columns won't be aligned with terminal output or default text editor
settings. We could allow tabs and spaces. That removes some of the benefits of
tabs (e.g. allowing data containing spaces). And even if we accept either,
there's still the question of what to use by default.

pro spaces:
  * easy to align in a way that works in any fixed-width font
  * easy to edit without magic (or maybe just an "align everything" command)
  * probably need space output when writing to terminal anyway
pro tabs:
  * don't have to update whole file to maintain alignment
  * more space-efficient (but textual data isn't going to be space-efficient
    anyway)
  * don't have problems with occasional pathologically large cells

I think we should accept both. And pretty-printing output needs to be spaces
too, for now, for the sake of rendering.

Let's also make a csv2cod converter that "sniffs" the columns to guess col types.

Another q: should pretty-printing include col types?
 * We need it for deserialization. But we don't want it in data to share
 * Maybe it's a repr/str distinction? We just need an alternative pretty-printer
   that isn't invertible. (Maybe that one would also have things for controlling
   layout and precision. Even column names might be different - things with
   spaces and so on rather than valid identifiers. It's a distinct sink type,
   like plotting, that's explicitly only for human consumption. But the default
   can still be repr, which is both human-consumable and machine-consumable)

More questions
  * Should input be sorted? (Probably not - liberal in what we accept)
  * what about missing keys (with the "use the key above" convention)?
    * It does imply sorted
    * tricky with whitespace-separated - have to count number of fields in each
      row and right-align. But it could lead to hard-to-catch errors if there
      are fields missing for other reasons.
      * maybe a character like '.' or '_' meaning "as above" might be more explicit.
        * yes, I think that works

Representing things like empty tuples is tricky if we only handle the leaves
(since it's hard to distinguish (Int, Int) from (Int, (), Int) ).

Consider the following (flat) table types:

(Int,Int)=>(Int,Int)
(Int,)=>(Int,)
(Int)=>(Int)
()=>()
()

The simplest approach would be to keep the parens and maybe replace '=>' with
whitespace. But the commas are a bit ugly. If we drop them, we need to make the
parens significant, so that `(Int)` is a singleton tuple and `Int` is Int:

(Int Int) (Int Int)
Int Int
(Int) (Int)
() ()
()

Maybe if we realy wanted we could introduce special syntax '|' which means
"treat left and right as components of a record, so that the first example
(which is the most common in translation from csvs) would become:
Int Int | Int Int
But let's leave that for later, with feedback from others. The parens syntax
seems clean and uniform for now.


