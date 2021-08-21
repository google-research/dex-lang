using Test
using DexCall

@testset "DexCall" begin
    @testset "basic demo of eval and check errors" begin
        context() do ctx
            dex_eval(ctx, "1 + 1.0\n")
            error_message = DexCall.get_error_msg()
            @test contains(error_message, r"Type error.*Expected: Int32.*Actual: Float32.*1 \+ 1.0"s)
        end
    end

    @testset "evaluate" begin
        @test repr(evaluate("1")) == repr("1")
        @test repr(evaluate("[1, 2]")) == repr("[1, 2]")
        @test repr(evaluate("1+3")) == repr("4")
        @test repr(evaluate("for i. [1, 2].i + 1")) == repr("[2, 3]")

        @test_throws DexError evaluate("1 + 2.0")
    end

end