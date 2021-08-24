@testset "evaluate.jl" begin
    @testset "evaluate erroring" begin
        @test_throws DexError evaluate("1 + 2.0")
    end

    @testset "evaluate  show" begin
        @test repr(evaluate("1")) == repr("1")
        @test repr(evaluate("1.5")) == repr("1.5")
        @test repr(evaluate("[1, 2]")) == repr("[1, 2]")
        @test repr(evaluate("1+3")) == repr("4")
        @test repr(evaluate("for i. [1, 2].i + 1")) == repr("[2, 3]")
 
        # This seems weird: why is it doubly quoted? 😕
        @test repr(evaluate("IToW8 65")) === repr(repr('A'))
    end

    @testset "evaluate juliaize" begin
        @test juliaize(evaluate("1")) === Int32(1)
        @test juliaize(evaluate("1.5")) === 1.5f0

        @test juliaize(evaluate("IToW8 65")) === Int8(65)
    end

    @testset "convert CAtom" begin
        atom = evaluate("1.0")
        @test convert(Number, atom) === 1f0
        @test convert(Real, atom) === 1f0
        @test convert(Float64, atom) === 1.0

        atom = evaluate("2")
        @test convert(Number, atom) === Int32(2)
        @test convert(Real, atom) === Int32(2)
        @test convert(Float64, atom) === 2.0
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
