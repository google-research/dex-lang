@testset "native_function.jl" begin
    @testset "signature parser" begin
        @testset "$example" for example in (
            "arg0:f32",
            "arg0:f32,arg1:f32",
            "arg0:i64,arg1:i32",
            "arg0:f32[10]",
            "?arg0:i32,arg1:f32[arg0]",
            "arg2:f32[arg0]",
            "?arg0:i32,?arg1:i32,arg2:f32[arg0,arg1]",
            "arg3:f32[arg1,arg0]",
        )
            # This is just a quick check to make sure the parser doesn't error.
            # later integration tests will show it has the right behavour.
            @test DexCall.parse_sig(example) isa Vector{DexCall.Binder}
        end
    end
end