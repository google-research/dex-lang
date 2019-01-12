# current todo
  * Create explicit type-lambda IR in type inference
  * Add type annotation syntax to let and lambda with scoped type variables
  * Existentials with explicit pack, unpack and typing rules
  * Simple compiler (strict index comprehensions only)
  * Write prelude, example programs in explicit style
  * Consider making some things implicit/automatic:
    * placement of pack and unpack
    * terser table type syntax, e.g. implicit element type

# main goals
  1. existentially typed index sets with some inference
  2. type-directed compilation with llvm and ffi
  3. plotting - ggplot-like grammar and backend
  4. end of feb: end-to-end demo with interactive setup

# language features to add
  * guard-like filter syntax (giving slice)
  * index variables allowed in normal expressions (giving iota)

# primitives to add
  * range (`Int -> Ei. i=>()`)
  * scalar math ops - sin, exp, erf etc
  * give
  * `==`, `>`, etc
  * hash, giving randn (also linear types?)
  * groupby
  * union, difference
  * cholesky, trisolve (giving solve)
  * blas matmul

# eventually
  * branching and sum types
  * type declarations
  * type, newtype, data etc
  * row polymorphism
  * differentiation
  * cached incremental evaluation
  * syntax
    * multiline layout syntax
    * comments
  * tab format - cosmetic
    * simple strings without quotes
    * avoid repeating keys
    * use fixed numeric precision
  * compiler optimizations
    * avoid materialization before reductions if no other consumers
    * predictably hoist loop constants (e.g. cholesky decomp within solve)
  * emacs syntax highlighting
