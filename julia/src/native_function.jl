macro dex_func_str(str)
    # TODO support functions defined as `foo = \x. 1.0` etc
    m = match(r"^def ([a-zA-Z0-9]+)", str)
    if m === nothing  # then this must be an anon function
        NativeFunction(evaluate(str))
    else  # named function
        name = Symbol(only(m.captures))
        mod = DexModule(str)
        atom = getproperty(mod, name)
        native_func = NativeFunction(atom)

        # TODOL: make this declared as const if a `c` flag is set
        :($(esc(name)) = $(native_func))
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



"Callable Julia wrapper of some native dex function. Returns type is `R`."
struct NativeFunction{R} <: Function
    c_func_ptr::Ptr{Nothing}
    implict_argument_signature::Vector{Binder}
    explicit_argument_signature::Vector{Binder}
    result_signature::Vector{Binder}
end

NativeFunction(atom::Atom, jit=JIT) = NativeFunction(atom.ptr, atom.ctx, jit)
function NativeFunction(atom::Ptr{HsAtom}, ctx=PRELUDE, jit=JIT)
    c_func_ptr = compile(ctx, atom, jit)
    sig_ptr = get_function_signature(c_func_ptr, jit)
    sig_ptr == C_NULL && error("Failed to retrieve the function signature")

    try
        signature = NativeFunctionSignatureJL(sig_ptr)
        argument_signature = parse_sig(signature.arg)
        result_signature = parse_sig(signature.res)
        R = result_type(result_signature)
        f = NativeFunction{R}(
            c_func_ptr,
            filter(x->x.implicit, argument_signature),
            filter(x->!x.implicit, argument_signature),
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
    #== TODO
    func_type = ctypes.CFUNCTYPE(
        ctypes.c_int64,
        *(arg.type.arg_ctype for arg in self.argument_signature),
        *(res.type.ref_ctype for res in self.result_signature))
    self.callable = func_type(ctypes.cast(ptr, ctypes.c_void_p).value)
    ==#
end

function (f::NativeFunction{R})(args...)::R where R
    if length(args) != length(f.explicit_argument_signature)
        throw(ArgumentError("wrong number of inputs, expected: $(length(f.explicit_argument_signature) )"))
    end

    named_sizes = Dict{Symbol, Int}()
    arg_ctypes = map(f.explicit_argument_signature, args) do binder, arg
        to_ctype!(named_sizes, binder.type, arg)
    end

    implict_values = map(f.implict_argument_signature) do binder
        # Right now the Exported API only supports implicts that are sizes
        # and now all of them will have been determined by the preverious `to_ctype!` step
        @assert binder.type == Int32
        named_sizes[binder.name]
    end

    results_ptrs_and_thunks = map(f.result_signature) do builder
        create(builder.type, named_sizes)  
    end

    result_ptrs = first.(results_ptrs_and_thunks)
    result_thunks = Tuple(last.(results_ptrs_and_thunks))

    args = (implict_values..., arg_ctypes..., result_ptrs...)
    # No return value, that we care about because it write's its return into  the results_ptrs
    _ccall_dex_func(f.c_func_ptr, args...)

    if length(result_thunks) === 1
        only(result_thunks)()
    else
        map(t->t(), result_thunks)
    end
end

# Work around needing to have the return types as literals, by defining a generated function that does.
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
result_type(x::Binder) = result_type(x.type)  # don't care about size etc
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
@with_names begin
    name = map(Symbol, !re"arg\d+")
    scalar_type = Either{Any}(Any[
        parser("f32"=>Float32),
        parser("f64"=>Float64),
        parser("i32"=>Int32),
        parser("i64"=>Int64),
        parser("i8"=> Int8),
    ])
    
    size_ele = Numeric(Int) | name
    
    sizes = join(Repeat(size_ele),",")
    
    array_type = map(scalar_type * "[" * sizes * "]") do (T, _, sz, _)
        ArrayBuilder{T}(sz)
    end

    type = Either{Any}(Any[array_type, scalar_type])

    implicit = parser("?"=>true) | false

    arg_sig = map(implicit * name * ":" * type) do (i, n, _ , t)
        Binder(n, t, i)
    end
    arg_sigs = join(Repeat(arg_sig),",")
end

parse_sig(sig) = parse(arg_sigs, sig)