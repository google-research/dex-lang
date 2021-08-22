
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
    argument_signature::Vector{Binder}
    explicit_argument_signature::Vector{Binder}
    result_signature::Vector{Binder}
    ccall_signature::Vector{String}
end

function NativeFunction(atom::HsAtom, ctx=PRELUDE, jit=JIT)
    func_obj_ptr = compile(ctx, atom, jit)
    sig_ptr = get_function_signature(func_obj_ptr, jit)
    sig_ptr == C_NULL && error("Failed to retrieve the function signature")

    try
        signature = NativeFunctionSignatureJL()
        argument_signature = parse_sig(signature.arg)
        result_signature = parse_sig(signature.res)
        R = result_type(result_signature)
        f = NativeFunction{R}(
            argument_signature,
            [arg for arg in argument_signature if !arg.implicit],
            result_signature,
            split(sig._call, ",")
        )
        finalizer(f) do _
            unload(func_obj_ptr, jit)
        end
        return f
    catch
        unload(func_obj_ptr, jit)
        rethrow()
    finally
        api.free_function_signature(sig_ptr)
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
    length(args) == length(f.explicit_argument_signature) || throw(ArgumentError("wrong number of inputs, expected: $(length(f.explicit_argument_signature) )"))

    named_sizes = Dict{Symbol, Int}
    arg_ctypes = map(f.explicit_argument_signature, args) do arg, builder
        to_ctype!(named_sizes, builder, arg)
    end
    #== TODO:
    for binder in self.result_signature:
        value, result_thunk = binder.type.create(name_to_cval)
        name_to_cval[binder.name] = value
        result_thunks.append(result_thunk)
    self.callable(*(name_to_cval[name] for name in self.ccall_signature))
    results = tuple(thunk() for thunk in result_thunks)
    if len(results) == 1:
        return results[0]
    else:
        return results
    ==#
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
    return pointer(actual)
end

# scalar types:
to_ctype!(::Any, ::T, actual::T) where T = actual
to_ctype!(::Any, ::T, ::S) where {T,S} = throw(ArgumentError("expected $T goit $S"))


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
result_type(x::Binder) = x.type  # don't care about size etc
function result_type(x::Vector{Binder})
    @assert !isempty(x)
    if length(x) == 1
        return result_type(only(x))
    else
        Tuple{result_type.(x)...}  # multiple returns, represented as a Tuple
    end
end

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