const libdex = joinpath(dirname(@__DIR__), "deps", "libDex.so")
isfile(libdex) || error("libDex not found in $libdex. Please run `make build-ffis`")


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

# These can only be called once in life-time of program, can not re-init after fini etc
init() = @ccall libdex.dexInit()::Nothing
fini() = @ccall libdex.dexFini()::Nothing
function __init__()
    init()
    atexit(fini)
end


get_error() = unsafe_string(@ccall libdex.dexGetError()::Cstring)

create_context() = @ccall libdex.dexCreateContext()::Ptr{HsContext}
destroy_context(ctx) = @ccall libdex.dexDestroyContext(ctx::Ptr{HsContext})::Nothing
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

create_JIT() = @ccall libdex.dexCreateJIT()::Ptr{HsJIT}
destroy_JIT(jit) = @ccall libdex.dexDestroyJIT(jit::Ptr{HsJIT})::Nothing
function jit(f)
    JIT = create_JIT()
    try
        f(JIT)
    finally
        destroy_JIT(JIT)
    end
end

compile(jit, ctx, atm) = @ccall libdex.dexCompile(jit::Ptr{HsJIT}, ctx::Ptr{HsContext}, atm::Ptr{HsAtom})::NativeFunction

get_function_signature(jit, f) = @ccall libdex.dexGetFunctionSignature(jit::Ptr{HsJIT}, f::NativeFunction)::Ptr{NativeFunctionSignature}
free_function_fignature() = @ccall libdex.dexFreeFunctionSignature()::Ptr{NativeFunctionSignature}
