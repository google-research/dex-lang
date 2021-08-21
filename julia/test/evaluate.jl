@testset "evaluate.jl" begin
    @testset "evaluate" begin
        @test repr(evaluate("1")) == repr("1")
        @test repr(evaluate("[1, 2]")) == repr("[1, 2]")
        @test repr(evaluate("1+3")) == repr("4")
        @test repr(evaluate("for i. [1, 2].i + 1")) == repr("[2, 3]")

        @test_throws DexError evaluate("1 + 2.0")
    end

    @testset "DexModule" begin
        m = DexModule("""
        x = 2.5
        y = [2, 3, 4]
        """)
        @test repr(m.x) == repr("2.5")
        @test repr(m.y) == repr("[2, 3, 4]")
    end
end