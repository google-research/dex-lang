module DexCall
    export throw_from_dex, context, dex_eval

    include("api.jl")
    function __init__()
        init()
        atexit(fini)
    
        @eval const PRELUDE = create_context()
        atexit(()->destroy_context(PRELUDE))
    
        @eval const JIT = create_JIT()
        atexit(()->destroy_JIT(JIT))
    end

end
