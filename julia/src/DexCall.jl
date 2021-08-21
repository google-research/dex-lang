module DexCall
    export throw_from_dex, context, dex_eval, evaluate, DexError, DexModule

    include("api.jl")
    include("evaluate.jl")
    
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
