# Dex Syntax Overview

Dex has a lot of syntax.  It can be hard to keep track of, but to make it easier
Dex tries to be uniform about its grouping structure.  For instance, the colon
`:` means "I have a name (or pattern) on my left, whose type is on my right".
But sometimes that name is a variable binding, sometimes it's a function
argument, and sometimes it's a record field name.  However, in all of these
cases, the binding precedence of `:` is consistent (and quite loose), so you can
tell what other operators are part of the type vs part of the enclosing context
just by parsing the precedence and the grouping parens, without having to
remember the enclosing syntactic form.

In fact, Dex achieves this with a two-stage parser: Dex resolves keywords,
grouping, and operator precedence first, uniformly, and then constructs its
abstract syntax from that.  That's why you see two different kinds of errors.  A
"Parse error" comes from the first pass, effectively inserting parentheses in
the right places around all the infix operators.  At this stage, Dex detects
completely malformed stuff like `x + * y`.  On the other hand, a "Syntax error"
comes from the second pass, and detects well-grouped but nonsensical things like
`x : Int : Float`.

Here is the precedence table of all the punctuation in Dex, from
tightest-binding to loosest-binding.

| Symbol(s)             | Default Meaning                          | Associativity |
|-----------------------|------------------------------------------|---------------|
| . !                   | indexing, reference slicing              | Left          |
| juxtaposition (space) | function application                     | Left          |
| unary + -             | negation, integer literals               | Prefix        |
| backquoted functions  | infix application of binary functions    | Left          |
| other                 | user-defined operators                   | Left          |
| * /                   | scalar multiplication, division          | Left          |
| .* *.                 | scalar * vector and vector * scalar      | Left          |
| **. .**               | matrix * vector and vector * matrix      | Left          |
| **                    | matrix * matrix                          | Left          |
| binary + -            | addition, subtraction                    | Left          |
| -\|                   | clamping subtraction on Nat              | Left          |
| +>>                   | pointer offset                           | Left          |
| <>                    | monoid combine                           | Left          |
| ~~                    | floating-point "almost equal"            | None          |
| < <= > >=             | comparison                               | None          |
| == !=                 | equality, inequality                     | None          |
| &&                    | boolean "and"                            | Left          |
| \|\|                  | boolean "or"                             | Left          |
| unary .. ..<          | indices up to                            | Prefix        |
| unary .. >..          | indices from                             | Postfix       |
| =>                    | array type arrow                         | Right         |
| -> ?-> ?=> --o        | function type arrows                     | Right         |
| >>>                   | forward function composition             | Left          |
| <<<                   | reverse function composition             | Left          |
| &>>                   | forward isomorphism composition          | Left          |
| <<&                   | reverse isomorphism composition          | Left          |
| binary @              | infix from_ordinal                       | Left          |
| unary @               | computed field name                      | Prefix        |
| unary @...            | computed name for multiple fields        | Prefix        |
| ...                   | name for multiple fields                 | Prefix        |
| \|>                   | reverse function application             | Left          |
| $                     | loose-binding function application       | Right         |
| ::                    | infix "has type" on values               | None          |
| := +=                 | assignment, accumulation                 | None          |
| :                     | "has type" with a binder on the left     | Right         |
| =                     | let binding, field assignment            | Left          |
| ?                     | separator for labeled rows               | Left          |
| ,                     | separator for tuples, records, others    | Right         |
| ,>                    | separator for dependent pairs            | Right         |
| &                     | separator for record types               | Right         |
| &>                    | separator for dependent pair types       | Right         |
| \|                    | separator for variants and variant types | Left          |
|-----------------------|------------------------------------------|---------------|

Why this particular precedence table?  The general guiding principle is to
reduce surprise and grouping parentheses.  Reducing surprise means following
conventional precedence orders when they exist.  Reducing parentheses means that
operator A should bind tighter than operator B if it's more typical to pass the
result of A into B than vice versa (in particular, if A is ill-typed on the
result of B).  Those desiderata actually constrain the partial order on
operators quite a lot; the presented table is a consistent total order.

Specifially, we want the following things:

1. Numeric arithmetic has a strong conventional order:

  - Exponentiation is tightest (but Dex has no operator for it)

  - Then unary +, -

  - Then multiplication and division

  - We include .* and *. for scalar-vector multiplication, and make it looser than
    scalar-scalar multiplication so that 2 * 3 .* [1, 2, 3] needs no parens

  - We also include .** and **. for vector-matrix multiplication, and make it
    looser yet to continue the pattern of increasing rank (also, 3 .* [1, 2, 3]
    .** matrix will choose the more efficient order this way, folding the 3 into
    the vector instead of computing mat-vec and folding the 3 into the result)

  - Finally, we also include ** for matrix-matrix multiplication, and make it
    looser still, on the same logic

  - Then addition and subtraction

  - The dash-pipe `-|` is a subtraction operator, namely subtracting natural
    numbers clamping the result to 0

2. Comparison operators are looser than numeric operators because the former can
   consume the results of the latter, but not vice versa.

  - `~~` is tightest of these because it only makes sense on (structures of)
    floating-point numbers

  - The standard comparisons `>`, `<`, `>=`, `<=` are given the same precedence
    by convention

  - The equality operators `==` and `!=` get the next precedence, looser than
    comparison because `4 < 5 == True` is a reasonable thing to write (if a bit
    redundant)

3. Boolean arithmetic follows, because it can consume the results of comparisons

  - `&&` is tighter than `||` because the or-of-ands form for Boolean formulas
    is easier to understand; analogous to sum-of-products form for polynomials

4. Our next class is type-level operators

  - The unary operators prefix `..`, prefix `..<`, suffix `..`, and suffix `<..`
    are tighter than array arrow, so they can appear without parens in dependent
    (triangular) array types.  However, they are looser than arithmetic (at
    least for now) in case we want to allow computing on them.

  - The array arrow `=>` is tighter than the function arrows because we
    often want arrays in function types but not so much vice versa.

  - The function arrows (`->`, `--o`, `?->`, and `?=>`) follow.  They are all at
    the same precedence so they can chain to form functions with intermixed
    implicit, explicit, class, and linear arguments.

  - The colon is looser than the arrows, to make it easier to annotate binders
    with function types.

    - We could also make it tighter, to make it easier to write dependent types
      with simply-typed arguments, but we decided against that on the grounds
      that explicit dependent types are rarer than binders annotated with
      function or array types.
      
5. With that core, we move on to universal operators that interact almost everything

  - Juxtaposition as function application is tighter than all the above because
    functions can compute arguments to those operators

  - However, we make array indexing and reference slicing tighter than function
    composition because they make function arguments very often, and we like
    punning x.i as a name (in this case, for the array element)

  - Dollar `$` as function application is looser than all the above because the
    above can compute arguments to functions

  - Reverse function application `|>` is just one level tighter
    than dollar, because
      `value |> unary |> unary |> binary $ value`
    sort of makes sense, and the left pipe should compute the first,
    not second, argument to the binary function

  - The assignment `:=` and accumulation `+=` operators are statement-like in
    that they return unit, so cannot be usefully nested.  Thus, they are even
    looser than dollar, so that dollar can be used to compute the RHS.

  - Binary atsign `@` is sugar for `from_ordinal` taking the number on the left
    and the type on the right, and producing an index.
    
    - If we make it looser than indexing, then it will have to be
      parenthesized as a direct argument to indexing anyway, and we
      might as well make it very loose so it doesn't force parens
      on any type and arithmetic computations
    - However, it feels weird to have @ be looser than number
      arithmetic because it seems to want to change the
      interpretation of one thing, rather than a computation for
      things
    - On the other hand, maybe it is reasonable for it to be looser
      than type arithmetic, so we can write `4 @ Fin 2 & Fin 3`
    - An alternative would be to make `@` tighter than indexing, so
      that `xs.5@_` works.  However, because indexing is tighter than
      application, there's no way for `xs.5@Fin 7` to work without parens
      somewhere.
    - If we make `@` loose, we should probably write it with surrounding
      spaces.
    - Also, this decision doesn't matter very much, because binary `@` is not a
      very common operator anyway.

  - Atsign `@` is also used in the curly brace syntaxes as a prefix
    to a field label that makes that field name evaluated instead
    of taken literally.  In this capacity, the only requirement is
    that it bind tighter than the separator between the label and
    the value, namely, `:` or `=`.

  - At-ellipsis `@...` is used in such syntaxes as a prefix to
    denote that the field label refers to multiple fields.

  - Type arithmetic (`&`, `|`)

    - `&` should be tighter than `|` for the same reason as `&&` and `||`

    - One might argue that these should be tighter than function arrows because
      we want to return or consume tuples or pairs more than we want to form
      pairs of functions.

    - However, they are also used as separators for record and variant types,
      where they want to be looser than `:` because `:` is used as a
      sub-separator separating the field name from its type.  Also, records and
      variants are already grouped by curlies, so there is no pressure to make
      their separators tight.

    - We choose that the latter use dominates, with the down side that pairs and
      `Either` types must always be enclosed in parens.  But that's fine; the
      parens serve as a pun reminding the user that a pair is just a binary
      record with anonymous fields.

  - The dependent pair operators `,>` and `&>` are little-used as of this
    writing, so we arbitrarily dump them next to their non-dependent pair
    variants `,` and `&`, discussed below.

  - The double colon `::` type-annotates an arbitrary expression without
    otherwise changing its meaning.  Since it can go anywhere, we make it looser
    than all expression operators, except `|>` and `$`.  The exception supports
    the common concept that `$` breaks up formulas completely (by being the
    loosest expression-like operator).
    
  - We make backquoted functions and user-defined operators bind tightly by
    default, but for no particularly good reason.  They are currently rare in
    Dex, so it doesn't really matter.

6. Next, we have the special snowflakes that interact with almost nothing

  - Function composition `>>>` and `<<<` are logically the same precedence, but
    we don't want them to chain with each other, because that's just confusing,
    so we arbitrarily make `>>>` tighter than `<<<`.  They should be tighter
    than `$` and `|>` and looser than juxtaposition but don't interact with
    anything else; so we arbitrarily make them loose.

  - The same logic applies to the isomorphism composition operators `&>>` and
    `<<&`.  We arbitrarily make them slightly looser than the function versions.

  - The monoid combine operator `<>` can technically act like `*`, `+`, `&&`,
    `||`, `>>>`, or `<<<` depending on the monoid, but we assume that in
    practice people will only use it on other data types.  We make it tighter
    than comparison because the same data type could have an ordering, and
    looser than arthimetic arbitrarily.

  - Pointer offset `+>>` should be looser than arithmetic, since the latter can
    compute the offset, but we make it tighter than everything else.

7. Dex also has a class of "operators" whose groups are not expressions, but
   which have precedence so they can be treated uniformly by the operator
   precedence stage of parsing.
   
  - Equals `=` is used to separate the binder from the body in a `let` or a
    `def`, and as the label separator for record and variant data.  In both
    capacities, it's reasonable to make it an operator that's looser than
    everything except the separators `&`, `,`, `|`, and `?`.  Notably, `=` is
    looser than `:`, `$`, and `|>`, which moderately often interact with it.

  - Colon `:` is used in several places as "the object on the left as the type
    on the right".  It also serves as a label separator for record and variant
    types.  For all of these, it's reasonable to make it very loose.  But it is
    tighter than `=`, because it can be used to type-annotated the binder being
    assigned.

  - Ampersand `&` and pipe `|` separate fields of record and variant types,
    respectively.  They should be looser than `:`.

  - Comma `,` and pipe `|` separate fields of records and variant data,
    respectively.  For this use case, they should be looser than `=`.

  - Comma `,` is also used to separate fields in tuple constructors, def class
    argument lists, and in effect rows.  In all three cases, it's already
    externally grouped, so can be very low precedence.

  - Pipe `|` should be looser than comma `,`, because `|` is used to separate
    the remainder of an effect row.

  - Question mark `?` separates fields in labeled rows.  It should be looser
    than `:`, but tighter than `,` and `|`.

  - Ellipsis `...` marks remainder groups in almost all of the above.  We make
    it a unary prefix operator that's tighter than the separators comma `,`,
    ampersand `&`, pipe `|`, and question mark `?`, but looser than expressions.

8. We arbitrarily make user-defined operators tight, but looser than unary `-`
   and `+`, because the latter are often part of numeric literals.

