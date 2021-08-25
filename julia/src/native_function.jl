@doc raw"""
    dex_func"..."
    dex_func"..."c

Compiles a string of dex code which defines a function.
That function can be anonymous, or named.
If named it can either be a lambda that is assigned to a variable, or defined using `def`.

Flags:
 - `c`: for a named function declares it as const


!!! warning
    If the code in the string does anything other than define a single function then the
    behavour of the `dex_func` string macro is undefined. It will probably eventually error.

# Examples
###Long form:
```julia
julia> dex_func\"\"\"
              def myTranspose (n: Int) ?-> (m: Int) ?->
                              (x : (Fin n)=>(Fin m)=>Float) : (Fin m)=>(Fin n)=>Float =
                  for i j. x.j.i
              \"\"\"
(::NativeFunction{Matrix{Float32}}) (generic function with 1 method)

julia> myTranspose([1f0 2f0 3f0; 4f0 5f0 6f0])
3×2 Matrix{Float32}:
 1.0  4.0
 2.0  5.0
 3.0  6.0
```

### Short form
julia> dex_func"inc = \a:Int. a + 1"
(::NativeFunction{Int32}) (generic function with 1 method)

julia> inc(Int32(9))
10
```

### Anonymous
```julia
julia> map(dex_func"\x:Float. pow 2.0 x", [1f0, 2f0,  3f0])
3-element Vector{Float32}:
 2.0
 4.0
 8.0
```
"""
macro dex_func_str(str, flags="")
    # Check if it is named function. Note that we don't need to check if the name is a
    # valid Dex/Julia identifier, the parser of each would/will error if it isn't.
    m = something(
        match(r"^def\s+(.+?)\b", str),  # `def foo`
        match(r"^(.+?)\b\s*=\s*[\\]", str),  # `foo = \x`
        Some(nothing)  # not found by either, so still give nothing.
    )
    if m === nothing  # then this must be an anon function
        NativeFunction(evaluate(str))
    else  # named function
        name = Symbol(only(m.captures))
        mod = DexModule(str)
        atom = getproperty(mod, name)
        native_func = NativeFunction(atom)

        assigment = :($(esc(name)) = $(native_func))
        if 'c' in flags
            assigment = Expr(:const, assigment)
        end
        return assigment
    end
end


"holds information on how to map an argument argment in a signature into a julia type"
struct Binder
    name::Symbol
    type  # Intentionally left unrestricted for now. No restriction seems useful, it is either one of half a dozen scalar types or an ArrayBuilder
    implicit::Bool
end

"Creates an `Array{T,N}``, if all elements of size are present then that array is initialized to hold `size`"
struct ArrayBuilder{T,N}
    size::Vector{Union{Symbol,Int}}
end
ArrayBuilder{T}(size) where T = ArrayBuilder{T,length(size)}(size)



"""
    NativeFunction{R}

Callable Julia wrapper of some native Dex function.
Return type from calling it is is `R`.

Usually constructed using [`@dex_func_str`](@ref),
or via `NativeFunction(atom)` on some [`DexCall.Atom`](@ref).
"""
struct NativeFunction{R} <: Function
    c_func_ptr::Ptr{Nothing}
    argument_signature::Vector{Binder}
    result_signature::Vector{Binder}
end

NativeFunction(atom::Atom, jit=JIT) = NativeFunction(atom.ptr, atom.ctx, jit)
function NativeFunction(atom::Ptr{HsAtom}, ctx=PRELUDE, jit=JIT)
    c_func_ptr = compile(ctx, atom, jit)
    sig_ptr = get_function_signature(c_func_ptr, jit)
    sig_ptr == C_NULL && error("Failed to retrieve the function signature")

    try
        signature = NativeFunctionSignatureJL(sig_ptr)
        result_signature = parse_sig(signature.res)
        R = result_type(result_signature)
        f = NativeFunction{R}(
            c_func_ptr,
            parse_sig(signature.arg),
            result_signature
        )

        # We are attaching this to f.result_signature because only mutable types can have finalizers
        finalizer(f.result_signature) do _
            unload(c_func_ptr, jit)
        end
        return f
    catch
        unload(c_func_ptr, jit)
        rethrow()
    finally
        free_function_signature(sig_ptr)
    end
end

function (f::NativeFunction{R})(args...)::R where R
    named_sizes = Dict{Symbol, Int}()
    num_explict = 0
    c_args = map(f.argument_signature) do binder
        if binder.implicit
            -one(binder.type)  # we will do implicts in a second pass, once named_sizes is filled out
            # Note: because scoping rules are left-to-right if we reversed the list we could do this in a single pass
        else
            num_explict += 1
            to_ctype!(named_sizes, binder.type, args[num_explict])
        end
    end
    num_explict == length(args) || throw(ArgumentError("Wrong number of arguments, expected $num_explict"))

    for (i, binder) in enumerate(f.argument_signature)
        # second pass, filling in implicits from the `named_sizes`
        binder.implicit || continue
        # Make sure it is the right type, just in case dex ever allows e.g Int32 implicts
        c_args[i] = convert(binder.type, named_sizes[binder.name])
    end


    results_ptrs_and_thunks = map(f.result_signature) do builder
        create(builder.type, named_sizes)  
    end

    result_ptrs = first.(results_ptrs_and_thunks)
    result_thunks = Tuple(last.(results_ptrs_and_thunks))

    # No return value, that we care about because it write's its return into  the results_ptrs
    _ccall_dex_func(f.c_func_ptr, c_args..., result_ptrs...)

    if length(result_thunks) === 1
        only(result_thunks)()
    else
        map(t->t(), result_thunks)
    end
end


"""
    _ccall_dex_func(f_ptr, args...)

Use `ccall` to call the dex native function pointed to by `f_ptr`, passing in the given `args`.
The `args` must already be in a C compatible type etc.


!!! warning
    Noone should be expected to follow what this code does.
    Like even people who have been using julia for years shouldn't.
    It's pretty gross.

The sensible version of this code is:
```julia
ccall(f_ptr, Int64, typeof.(args), args...)
```

However, we can not do that directly because `ccall` is not a function but rather a built-in
language intrinsic that is largely resolved at compile time, and that needs the type 
information given to it as literals.
`typeof.(args)` is not a literal which is a problem -- even though it can actually be 
resolved at compile-time -- the information exists.

So we use a generated function in order to get at the information.
Docs on those are at https://docs.julialang.org/en/v1/manual/metaprogramming/#Generated-functions
The short version though is that they take in arguments at compile time and they only get their types,
then they return a AST which is what is run at runtime.
So what we are doing is building the AST that is for the ccall, which has the types all present as literals.

See: https://github.com/JuliaLang/julia/issues/41991
"""
@generated function _ccall_dex_func(f_ptr, args...)
    arg_types = Expr(:tuple, args...)
    return :(ccall(f_ptr, Int64, $arg_types, $(Any[:(args[$i]) for i in 1:length(args)]...)))
end


"""
    to_ctype!(named_sizes::Dict{Symbol, Int}, builder, actual)

Returns a object suitable for passing into Dex's C API, that represents `actual`.
Checks the consistency of `actual` with the `builder`, and with `named_sizes`.
Sizes referred to by name for the first time are added to `named_sizes`, with the `actual` size.
"""
to_ctype!(named_sizes, builder::ArrayBuilder, actual) = to_ctype(named_sizes, builder, collect(actual))
to_ctype!(::Any, ::ArrayBuilder{T}, ::Array{S}) where {S,T} = throw(ArgumentError("Expected eltype $T, got $S."))
to_ctype!(::Any, ::ArrayBuilder{T,N}, ::Array{T,M}) where {T,N,M} = throw(DimensionMismatch("Expected $B, got $M dims."))

function to_ctype!(named_sizes::Dict{Symbol, Int}, builder::ArrayBuilder{T, N}, actual::Array{T, N}) where {T, N}
    combined_size = Tuple(map(builder.size, size(actual)) do size_or_name, actual_size
        # replace all the `nothings` (being the sizes specified not as literals) with the actual size.
        if size_or_name isa Symbol
            #Either record the size, or return the size that is already recorded
            get!(named_sizes, size_or_name, actual_size)
        else
            @assert size_or_name isa Int
            size_or_name
        end
    end)
    size(actual) == combined_size || throw(DimensionMismatch("Expected $(combined_size), got $(actual_size)"))
    return pointer(flip_array_order(actual))  # flip array order to C
end

# scalar types:
to_ctype!(::Any, ::Type{T}, actual::T) where T = actual
to_ctype!(::Any, ::Type{T}, ::S) where {T,S} = throw(ArgumentError("expected $T got $S"))

"Makes for writing into. Returns a pointer, and a thunk that when run gives the instance."
function create(builder::ArrayBuilder{T, N}, named_sizes::Dict{Symbol,Int}) where {T,N}
    size::NTuple{N,Int} = Tuple(size_or_name isa Symbol ? named_sizes[size_or_name] : size_or_name
            for size_or_name in builder.size)
    
    result = Array{T, N}(undef, reverse(size)...)  # reverse size because dex wants C ordered
    return pointer(result), ()->flip_array_order(result)  # flip order back to Fortran
end

# scalar types
function create(::Type{T}, ::Any) where T
    ref = Ref{T}()
    pointer_from_objref(ref), ()->ref[]
end

"converts between C and Fortran order"
flip_array_order(x::Vector) = x
flip_array_order(x::Array) = permutedims(x, ndims(x):-1:1)


"Mirror of NativeFunctionSignature that using julia Strings, rather than CStrings"
struct NativeFunctionSignatureJL
    arg::String
    res::String
    _ccall::String 
end
function NativeFunctionSignatureJL(x::NativeFunctionSignature)
    return NativeFunctionSignatureJL(unsafe_string.((x.arg, x.res, x._ccall))...)
end
function NativeFunctionSignatureJL(ptr::Ptr{NativeFunctionSignature})
    return NativeFunctionSignatureJL(unsafe_load(ptr))
end

"given a Binder for a result_signature returns the julia type that will be returned by the funcion"
result_type(x::Binder) = result_type(x.type)
function result_type(x::Vector{Binder})
    @assert !isempty(x)
    if length(x) == 1
        return result_type(only(x))
    else
        Tuple{result_type.(x)...}  # multiple returns, represented as a Tuple
    end
end
result_type(x::Type) = x
result_type(::ArrayBuilder{T,N}) where {T,N} = Array{T,N}

# CombinedParsers.jl based parser:
function parse_sig(sig)
    @with_names begin
        name = map(Symbol, !re"arg\d+")
        scalar_type = Either{Any}(
            parser("f32"=>Float32),
            parser("f64"=>Float64),
            parser("i32"=>Int32),
            parser("i64"=>Int64),
            parser("i8"=>Int8),
        )
        size_ele = NumericParser(Int) | name
        sizes = join(Repeat(size_ele),",")
        array_type = map(scalar_type * "[" * sizes * "]") do (T, _, sz, _)
            ArrayBuilder{T}(sz)
        end
        type = array_type | scalar_type
        implicit = parser("?"=>true) | false
        arg_sig = map(implicit * name * ":" * type) do (i, n, _ , t)
            Binder(n, t, i)
        end
        arg_sigs = join(Repeat(arg_sig),",")
    end    
    return parse(arg_sigs, sig)
end