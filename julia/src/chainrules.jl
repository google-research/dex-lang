
function ChainRulesCore.frule((_, ẋ), f::Atom, x::Atom)
    ẋ isa Atom || throw(DomainError(ẋ, "Tangent to an Atom must be an Atom"))
    env = f.ctx
    env = insert(env, "f", f.ptr)
    env = insert(env, "dx", ẋ.ptr)
    env = insert(env, "x", x.ptr)

    m = DexModule(raw"""
    (y, pushforward) = linearize f x
    dy = pushforward dx
    """,
    env
    )
    return m.y, m.dy
end

function ChainRulesCore.rrule(f::Atom, x::Atom)
    env = f.ctx
    env = insert(env, "f", f.ptr)
    env = insert(env, "x", x.ptr)

    m = DexModule(raw"""
    (y, pushforward) = linearize f x
    pullback = transposeLinear pushforward
    """,
    env
    )

    # It is important that we close over `m` as otherwise the env may be destroyed by GC
    pullback(x̄::Atom)= (NoTangent(), m.pullback(x̄))
    return m.y, pullback
end

ChainRulesCore.frule((_, ẋ), ::typeof(juliaize), x) = juliaize(x), juliaize(ẋ)
function ChainRulesCore.rrule(::typeof(juliaize), x::Atom)
    env= x.ctx

    # pullback must take a julia typed cotangent and give back a dex typed cotangent
    juliaize_pullback(ȳ) = (NoTangent(), dexize(ȳ, env))
    return juliaize(x), juliaize_pullback
end


ChainRulesCore.frule((_, ẋ), ::typeof(dexize), x) = dexize(x), dexize(ẋ)
function ChainRulesCore.rrule(::typeof(dexize), x)
    # pullback must take a dex typed cotangent and give back a julia typed cotangent
    dexize_pullback(ȳ) = (NoTangent(), juliaize(ȳ))
    return dexize(x), dexize_pullback
end

