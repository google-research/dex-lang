"A wrapped DexLang value"
struct Atom
    ptr::Ptr{HsAtom}
    _module::Ptr{HsContext}
end

Base.show(io::IO, atom::Atom) = show(io, print(atom.ptr))


"A friendly function for running Dex code."
function evaluate(str, _module=PRELUDE, env=_module)
    result = eval_expr(env, str)
    result == C_NULL && throw_from_dex()
    return Atom(result, _module)
end