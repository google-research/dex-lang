We need a way to get data in and out of coddle. A binary format supporting
random access will be needed for large data sets. But it would be nice to also
have a simple text format that's human-readable and hand-editable.

# Some desiderata
  * Represent all coddle values except arrow types (and possibly only finite
    tables)
  * Close in edit-distance to existing formats like csv
  * Servable as the default pretty-printing format too
  * Very simple and intuitive for these common cases:
    1. Record-tree of scalars, `(Int, Int, (x=String, y=Read)`
    2. Single table, like `(Int, Int)=>(String, Real)`
       or `(x:Int, y:Int)=>(a:String, b:Real)`
    3. One top-level record of simple tables

# What's missing from csv and friends

Typed columns! The classic `Oct-4` problem. Or representing the empty table.
Type annotations on header is a lightweight way to solve this. Otherwise,
whitespace-delimited values aren't too bad. Need to do things like quoting the
empty string or strings containing whitespace, and escaping quote characters and
possibly newlines. But that's all manageable.

Multiple tables in a single file.

Distinguishing key and non-key columns.

# Tricky bits

1. "Dee" and "dum" - the two tables of type `()=>()` (i.e. with and without the
   only valid row) and generalizations, `()=>()=>()`. If we only represented
   the base-typed leaves as columns then these would all look like whitespace.

2. Higher-order tables with empty-table values, e.g. table of type
  `Int=>Int=>Int` formed from pairs
      [(0,[(1,2),
           (3,4)]),
       (1,[     ])]

3. Higher-order tables with a product on the rhs, like `Int=>(Int,Int=>Int)`.
   I think the only way to avoid a complicated parsing/printing problem is to
   flatten such a thing into two tables, `Int=>Int` and `Int=>Int=>Int`.


# Cosmetic stuff

1. Tabs, spaces or some other delimiter.

2. How to represent (possibly nested) index/value types in header. Some options:
   1. Direct                  (x:Int, y:Int) => (a:Real, (b:String, c:Int)) => Real
   2. more whitespace         (x:Int  y:Int)    (a:Real  (b:String  c:Int))    Real
   3. Even more whitespace     x:Int  y:Int | a:Real  (b:String  c:Int) | Real

  Of these, 3 is the most attractive. To have it be sensibly represented by
  some unix tool that accepts whitespace-separate values, we'd need to mash the
  pipe together. otoh you'd probably delete the header to handle it with unix
  tools other than pretty-printing, which it should be already.
  Problem: how to distinguish `(Int,)` from `Int`. We could have a special case
  for not-top-level-record types, like `[Int]`. But maybe it'd be cleaner to go
  with something more consistent like 2, and see how it goes.


