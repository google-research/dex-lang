const libdex = joinpath(dirname(@__DIR__), "deps", "libDex.so")
isfile(libdex) || error("libDex not found in $libdex. Please run `Pkg.build()`")


struct HsAtom end
struct HsContext end
struct HsJIT end
struct NativeFunctionObj end
struct NativeFunctionSignature
    arg::Cstring
    res::Cstring
    _ccall::Cstring  # can't name this field `ccall` as that is a built-in in julia
end

const NativeFunction = Ptr{NativeFunctionObj}


##########################################################################################
# Global State

# These can only be called once in life-time of program, can not re-init after fini etc
init() = @ccall libdex.dexInit()::Nothing
fini() = @ccall libdex.dexFini()::Nothing

# No reason to call these more than once in life-time of program
create_JIT() = @ccall libdex.dexCreateJIT()::Ptr{HsJIT}
function destroy_JIT(jit)
    NO_FREE[] || @ccall libdex.dexDestroyJIT(jit::Ptr{HsJIT})::Nothing
    return nothing
end

##########################################################################################

struct DexError <: Exception
    msg::String
end
Base.showerror(io::IO, err::DexError) = println(io, "(DexError)\n", err.msg)

get_error_msg() = unsafe_string(@ccall libdex.dexGetError()::Cstring)
throw_from_dex() = throw(DexError(get_error_msg()))


create_context() = @ccall libdex.dexCreateContext()::Ptr{HsContext}
function destroy_context(ctx)
    NO_FREE[] || @ccall libdex.dexDestroyContext(ctx::Ptr{HsContext})::Nothing
    return nothing
end

function context(f)
    ctx = create_context()
    try
        f(ctx)
    finally
        destroy_context(ctx)
    end
end


dex_eval(ctx, str) = @ccall libdex.dexEval(ctx::Ptr{HsContext}, str::Cstring)::Ptr{HsContext}

insert(ctx, str, atm) = @ccall libdex.dexInsert(ctx::Ptr{HsContext}, str::Cstring, atm::Ptr{HsAtom})::Ptr{HsContext}
eval_expr(ctx, str) = @ccall libdex.dexEvalExpr(ctx::Ptr{HsContext}, str::Cstring)::Ptr{HsAtom}
lookup(ctx, str) = @ccall libdex.dexLookup(ctx::Ptr{HsContext}, str::Cstring)::Ptr{HsAtom}

print(atm) = unsafe_string(@ccall libdex.dexPrint(atm::Ptr{HsAtom})::Cstring)
# TODO once have tagged unions working
#to_CAtom = dex_func('dexToCAtom', HsAtomPtr, CAtomPtr, ctypes.c_int)


compile(ctx, atm, jit=JIT) = @ccall libdex.dexCompile(jit::Ptr{HsJIT}, ctx::Ptr{HsContext}, atm::Ptr{HsAtom})::NativeFunction

get_function_signature(f, jit=JIT) = @ccall libdex.dexGetFunctionSignature(jit::Ptr{HsJIT}, f::NativeFunction)::Ptr{NativeFunctionSignature}
free_function_fignature() = @ccall libdex.dexFreeFunctionSignature()::Ptr{NativeFunctionSignature}

