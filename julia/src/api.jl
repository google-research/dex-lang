const libdex = joinpath(dirname(@__DIR__), "deps", "libDex.so")
isfile(libdex) || error("libDex not found in $libdex. Please run `Pkg.build()`")


##########################################################################################
# Global State

# These can only be called once in life-time of program, can not re-init after fini etc
init() = @ccall libdex.dexInit()::Nothing
fini() = @ccall libdex.dexFini()::Nothing

# No reason to call these more than once in life-time of program
create_JIT() = @ccall libdex.dexCreateJIT()::Ptr{HsJIT}
destroy_JIT(jit) = NO_FREE[] || @ccall libdex.dexDestroyJIT(jit::Ptr{HsJIT})::Nothing

##########################################################################################
"An error thrown from with-in Dex"
struct DexError <: Exception
    msg::String
end
function Base.showerror(io::IO, err::DexError)
    if '\n' ∈ err.msg
        # If message is multiline then it may dend on exact alignment
        println(io, "DexError:\n", err.msg)
    else
        # If one line then short enough to happen on same line as everuthing else
        println(io, "DexError: ", err.msg)
    end
end

get_error_msg() = unsafe_string(@ccall libdex.dexGetError()::Cstring)
throw_from_dex() = throw(DexError(get_error_msg()))


create_context() = @ccall libdex.dexCreateContext()::Ptr{HsContext}
destroy_context(ctx) = NO_FREE[] || @ccall libdex.dexDestroyContext(ctx::Ptr{HsContext})::Nothing

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

compile(ctx, atm, jit=JIT) = @ccall libdex.dexCompile(jit::Ptr{HsJIT}, ctx::Ptr{HsContext}, atm::Ptr{HsAtom})::Ptr{NativeFunctionObj}
unload(f, jit=JIT) = NO_FREE[] || @ccall libdex.dexUnload(jit::Ptr{HsJIT}, f::Ptr{NativeFunctionObj})::Nothing

get_function_signature(f, jit=JIT) = @ccall libdex.dexGetFunctionSignature(jit::Ptr{HsJIT}, f::Ptr{NativeFunctionObj})::Ptr{NativeFunctionSignature}
free_function_signature(s) = NO_FREE[] || @ccall libdex.dexFreeFunctionSignature(s::Ptr{NativeFunctionSignature})::Nothing


to_CAtom(src, dest) = @ccall libdex.dexToCAtom(src::Ptr{HsAtom}, dest::Ptr{CAtom})::Int32
from_CAtom(src) = @ccall libdex.dexFromCAtom(src::Ptr{CAtom})::Ptr{HsAtom}