
function ChainRulesCore.frule((_, ẋs...), f_native::NativeFunction{R}, xs...) where R
    f = f_native.atom
    env = f.ctx
    env = insert(env, "f", f.ptr)
    
    primal_binders = f_native.argument_signature
    primal_args_sig = repr_sig(primal_binders)
    primal_args = extract_arg_names(primal_binders)

    tangent_binders = generate_tangent_binders(primal_binders)
    tangent_args_sig = repr_sig(tangent_binders)
    tangent_args = extract_arg_names(tangent_binders)

    primal_res_sig = repr_result_sig(f_native.result_signature)
    dual_res_sig = "($primal_res_sig&$primal_res_sig)"
    m = DexModule("""
    def frule_inner $primal_args_sig->$tangent_args_sig : $dual_res_sig =
        (y, pushforward) = linearize f $primal_args
        dy = pushforward $tangent_args        
        (y, dy)
    """,
    env
    )
    # Convert the Atom into `NativeFunction` so can work with any argument type:
    frule_inner_native = NativeFunction(m.frule_inner)
    return frule_inner_native(xs..., ẋs...)
end

extract_arg_names(binds::Vector{Binder}) = join((bind.name for bind in binds), " ")
"""
Given the `Binder` for the signature of a primal argument/s constructs the matching one 
for the tangent.
For now we only support types with tangent type matcing primal type
"""
function generate_tangent_binders(pbinds::Vector{Binder})
    return [generate_tangent_binder(pbind) for pbind in pbinds if !pbind.implicit]
end
function generate_tangent_binder(pbind::Binder)
    pbind.implicit && throw(DomainError(pbind, "Implict arguments have no tangents"))
    return Binder(Symbol(:d, pbind.name), pbind.type, false)
end

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

