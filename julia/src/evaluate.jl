"""
    Atom
A wrapped DexLang value.
On its own not good for much -- just displays as a string.

However scalar values can be converted to julia objects using [`juliaize`](@ref),
and functions can be made exectuable using [`NativeFunction`](@ref).
"""
struct Atom
    ptr::Ptr{HsAtom}
    ctx::Ptr{HsContext}
end

Base.show(io::IO, atom::Atom) = show(io, print(atom.ptr))

juliaize(x::Atom) = juliaize(x.ptr)

mutable struct DexModule
    # Needs to be mutable struct so can attach finalizer
    ctx::Ptr{HsContext}
end

"""
    DexModule(str)

For running 1 or more Dex expressions, and keeping the state.
You can get them back out of the module using `getproperty`.
They are returned as [`DexCall.Atom`](@ref)s.

# Example:

```julia
julia> m = DexModule(raw"""
       x = 42
       y = 2 * x
       """)
DexModule(Ptr{DexCall.HsContext} @0x0000000000000031)

julia> m.x
"42"

julia> m.y
"84"
```
"""
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

@doc raw"""
    evaluate(str)

A friendly function for running Dex code.
The string `str` must contain a single Dex expression.
Return a [`DexCall.Atom`](@ref)
# Example:
```julia
julia> evaluate(raw"sum $ for i. exp [log 2.0, log 4.0].i")
"6."
```
"""
function evaluate(str, _module=PRELUDE, env=_module)
    result = eval_expr(env, str)
    result == C_NULL && throw_from_dex()
    return Atom(result, _module)
end