module DexCall
    using CombinedParsers
    using CombinedParsers.Regexp

    export throw_from_dex, context, dex_eval, evaluate, DexError, DexModule, julia_type

    include("api_types.jl")
    include("api.jl")
    include("evaluate.jl")
    include("native_function.jl")
    
    # use this to disable free'ing haskell objects after we have closed the RTS
    const NO_FREE = Ref(false)

    function __init__()
        init()
        @eval const JIT = create_JIT()
        atexit() do
            destroy_JIT(JIT)
            NO_FREE[] = true
            fini()
        end
    
        @eval const PRELUDE = create_context()
    end
end
