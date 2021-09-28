"""
    Atom
A wrapped DexLang value.

Scalar values can be converted to julia objects using [`juliaize`](@ref), or `convert`.
Functions can be called directly, if you pass in atoms,
or they can be compiled and made usable on julia objects by using [`NativeFunction`](@ref).
"""
struct Atom
    ptr::Ptr{HsAtom}
    ctx::Ptr{HsContext}
end

Base.show(io::IO, atom::Atom) = show(io, print(atom.ptr))

"""
    juliaize(x)

Get the corresponding Julia object from some Dex object.
The inverse of [`dexize`](@ref).
"""
juliaize(x::CAtom) = bust_union(x)
juliaize(x::Ptr{HsAtom}) = juliaize(CAtom(x))
juliaize(x::Atom) = juliaize(x.ptr)
Base.convert(::Type{T}, atom::Atom) where {T<:Number} = convert(T, juliaize(atom))

"""
    dexize(x)

Get the corresponding Dex object from some Julia object.
The inverse of [`juliaize`](@ref).
"""
dexize(x) = Atom(from_CAtom(Ref(CAtom(x))), PRELUDE) 
# ^ Always defined in PRELUDE as it could be defined anywhere that has all the bindings,
# but because it has no bindings anywhere will do

Base.convert(::Type{Atom}, atom::Number) = dexize(atom)


function (self::Atom)(args...)
    # TODO: Make those calls more hygenic
    env = self.ctx
    pieces = (self, args...)
    for (i, atom) in enumerate(pieces)
        # NB: Atoms can contain arbitrary references
        if atom.ctx !== PRELUDE && atom.ctx !== self.ctx
            throw(ArgumentError("Mixing atoms coming from different Dex modules is not supported yet!"))
        end
        old_env, env = env, insert(env, "julia_arg$i", atom.ptr)
        destroy_context(old_env)
    end
    return evaluate(join("julia_arg" .* string.(eachindex(pieces)), " "), self.ctx, env)
end

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