using Test
using DexCall

@testset "DexCall" begin
    include("api.jl")
    include("evaluate.jl")
    include("native_function.jl")
end