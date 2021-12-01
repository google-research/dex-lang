# DexCall.jl

DexCall provides a mechanism for calling dex-lang code from JuliaLang.
Three main mechanism are provided for this: `evaluate`, `DexModule` and the `dex_func` string macro.
Several helper methods are also provided: `dexize`, `juliaize` and `NativeFunction`.

## `evaluate`: just run a single Dex expression.
`evaluate` takes in a Dex expression as a string and runs it, returning a `Atom` (see below).
It is often useful to use it with [`raw`-string literals](https://docs.julialang.org/en/v1/manual/strings/#man-raw-string-literals), to take care of the escaping

```julia
julia> evaluate(raw"sum $ for i. exp [log 2.0, log 4.0].i")
"6."
```

## `DexModule` run a whole bunch of Dex code defining a module.
Similar to `evaluate`, `DexModule` takes a string full of Dex code and runs it.
However, DexModule is a bit more powerful.
It allowed you to run multiple expressions, and returns a namespaced module object that you can query to get variables out from.


```julia
julia> m = DexModule(raw"""
       x = 42
       y = for i:(Fin 3). IToF x
       z = sum y

       def addTwo (n: Int) ?-> (x: (Fin n)=>Float) : (Fin n)=>Float = 
           for i. x.i + 2.0
       """)
DexModule(Ptr{DexCall.HsContext} @0x0000000000000031)
```

You can then query things from it by name, each of which is returns as an `Atom`
```julia

julia> m.x
"42"

julia> m.y
"[42., 42., 42.]"

julia> m.z
"126."

julia> m.addTwo
"\\n:Int32 ?->\n  \\x:((Fin n) => Float32).\n    for i:(Fin n).\n       tmp:((Add Float32) ?=> Float32 -> Float32 -> Float32) = (+) Float32\n       tmp1:(Float32 -> Float32 -> Float32) = tmp instance1\n       tmp2:Float32 = x i\n       tmp3:(Float32 -> Float32) = tmp1 tmp2\n      tmp3 2."
```

If the variable defines is a function you can even call it, though you need to passin `Atom`s:
```julia
julia> m.addTwo(m.y)
"[44., 44., 44.]"
```

## Atoms: `dexize`, `juliaize`, `NativeFunction`

`evaluate` and the contents of a `DexModule` are returned as `Atom`s.
These can be displayed, but not much else.

```julia
julia> typeof(m.x)
Atom

julia> typeof(m.addTwo)
Atom
```

To convert scalar `Atom`s into julia typed scalars used `juliaize`.
```julia
julia> juliaize(m.x)
42

julia> typeof(juliaize(m.x))
Int32
```

It is not presently possible to `juliaize`/`dexize` arrays (but you can use them / get them as the input/output of `NativeFunction`s, see below).

You can also use [`convert`](https://docs.julialang.org/en/v1/manual/conversion-and-promotion/#Conversion) to convert between `Atom`sand Julia objects.
When converting to a Julia typeit will make the minimal change from the Dex type to get to the type you requested.
```julia
julia> typeof(convert(Integer, m.x))
Int32

julia> typeof(convert(Int64, m.x))
Int64

julia> convert(Atom, 1.5)
"1.5"

julia> convert(Number, convert(Atom, 1.5))
1.5
```

To convert function `Atom`s into something you can execute as if it was a regular julia function use `NativeFunction`.
This will compile it and handing inputs and outputs without needing to del with `Atom`s directly.

```julia
julia> const add_two = NativeFunction(m.addTwo)
(::NativeFunction{Vector{Float32}}) (generic function with 1 method)

julia> add_two([0f0, 10f0, 100f0])
3-element Vector{Float32}:
   2.0
  12.0
 102.0
```

**Performance Note:** at present, when passing multidimensional arrays to or from a `NativeFunction` they are copied.
This is due to Dex using C memory layout, and Julia's default `Array` using Fortran memory layout.
We hope to address this in future versions.

## `dex_func` compile Dex code directly into a function you can call from julia.

The `dex_func` [string macro](https://docs.julialang.org/en/v1/manual/metaprogramming/#Non-Standard-String-Literals) allows you to define a function in Dex that you can then call from julia.
The function type it defines is a `NativeFunction` as described above.
In functionality, `dex_func` is very similar to `NativeFunction ∘ evaluate` except that it does a whole ton of the work at parse time -- including compiling the Dex function.

You can use it to define either named functions.
Both in long form:
```julia
julia> dex_func"""
              def myTranspose (n: Int) ?-> (m: Int) ?->
                              (x : (Fin n)=>(Fin m)=>Float) : (Fin m)=>(Fin n)=>Float =
                  for i j. x.j.i
              """
(::NativeFunction{Matrix{Float32}}) (generic function with 1 method)

julia> myTranspose([1f0 2f0 3f0; 4f0 5f0 6f0])
3×2 Matrix{Float32}:
 1.0  4.0
 2.0  5.0
 3.0  6.0
```

As well as in short-form by assigning a lambda to a variable:
```julia
julia> dex_func"inc = \a:Int. a + 1"
(::NativeFunction{Int32}) (generic function with 1 method)

julia> inc(Int32(9))
10
```

You can also use it to define anonymous functions:

```julia
julia> map(dex_func"\x:Float. pow 2.0 x", [1f0, 2f0,  3f0])
3-element Vector{Float32}:
 2.0
 4.0
 8.0
```

By adding a `c` flag after the string for a named function (in either long or short form), you can make it declared as const.
Which is [a good idea if declaring it at global scope](https://docs.julialang.org/en/v1/manual/performance-tips/#Avoid-global-variables).
For example: `dex_func"inc = \a:Int. a + 1"c`