@testset "api.jl" begin
    @testset "basic demo of eval and check errors" begin
        DexCall.context() do ctx
            DexCall.dex_eval(ctx, "1 + 1.0\n")
            error_message = DexCall.get_error_msg()
            @test contains(error_message, r"Type error.*Expected: Int32.*Actual: Float32.*1 \+ 1.0"s)
        end
    end
end