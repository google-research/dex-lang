"A wrapped DexLang value"
struct Atom
    ptr::Ptr{HsAtom}
    ctx::Ptr{HsContext}
end

Base.show(io::IO, atom::Atom) = show(io, print(atom.ptr))


mutable struct DexModule
    # Needs to be mutable struct so can attach finalizer
    ctx::Ptr{HsContext}
end

"For running 1 or more Dex expressions, and keeping the state"
function DexModule(source::AbstractString)
    ctx = dex_eval(PRELUDE, source)
    ctx == C_NULL && throw_from_dex()
    m =  DexModule(ctx)
    finalizer(m) do _m
        destroy_context(getfield(_m, :ctx))
    end
    return m
end

function Base.getproperty(m::DexModule, name::Symbol)
    ctx = getfield(m, :ctx)
    ret = lookup(ctx, string(name))
    ret == C_NULL && throw_from_dex()
    return Atom(ret, ctx)
end

"A friendly function for running Dex code."
function evaluate(str, _module=PRELUDE, env=_module)
    result = eval_expr(env, str)
    result == C_NULL && throw_from_dex()
    return Atom(result, _module)
end