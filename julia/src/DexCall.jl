"Calling Dex from Julia"
module DexCall
    using ChainRulesCore
    using CombinedParsers
    using CombinedParsers.Regexp

    export evaluate, DexError, DexModule, dexize, juliaize, NativeFunction, @dex_func_str

    include("api_types.jl")
    include("api.jl")
    include("evaluate.jl")
    include("native_function.jl")
    include("chainrules.jl")
    
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
