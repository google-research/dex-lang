using Test
using DexCall
using ChainRulesCore
using Zygote  # for integration tests 

@testset "DexCall" begin
    include("api.jl")
    include("evaluate.jl")
    include("native_function.jl")
    include("chainrules.jl")
end