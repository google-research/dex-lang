using Pkg: Pkg
Pkg.activate(dirname(@__DIR__))
using Test
using DexCall
using DexCall: Atom, insert

double_dex = evaluate(
    raw"\x:Float. 2.0 * x"
)

function frule_2(darg::Atom, primal_f::Atom, arg::Atom)
    env = primal_f.ctx
    env = insert(env, "primal_f", primal_f.ptr)
    env = insert(env, "darg", darg.ptr)
    env = insert(env, "arg", arg.ptr)

    m = DexModule(raw"""
    (primal_out, pushforward) = linearize primal_f arg
    tangent_out = pushforward darg
    """,
    env
    )
    return m.primal_out, m.tangent_out
end
@test frule_2(evaluate("1.5"), double_dex, evaluate("4.0")) .|> juliaize == (8f0, 3f0)


function rrule_1(primal_f::Atom, arg::Atom)
    env = primal_f.ctx
    env = insert(env, "primal_f", primal_f.ptr)
    env = insert(env, "arg", arg.ptr)

    m = DexModule(raw"""
    (primal_out, pushforward) = linearize primal_f arg
    pullback = transposeLinear pushforward
    """,
    env
    )

    dex_pullback = m.pullback
    function pullback(d_out::Atom)
        return dex_pullback(d_out)
    end
    return m.primal_out, pullback
end

val, pb = rrule_1(double_dex, evaluate("4.0"))
@test juliaize(val) == 8f0

@test juliaize(pb(evaluate("1.5"))) == 3f0