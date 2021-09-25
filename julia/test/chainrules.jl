const double_dex = evaluate(raw"\x:Float. 2.0 * x")

@testset "frule: dexize, evaluate, juliaize" begin
    a, ȧ = frule((NoTangent(), 10f0), dexize, 1.5f0)
    b, ḃ = frule((NoTangent(), ȧ), double_dex, a)
    c, ċ = frule((NoTangent(), ḃ), juliaize, b)
    @test c === 3.0f0
    @test ċ === 20f0
end

@testset "rrule: dexize, evaluate, juliaize" begin
    x = 1.5f0
    a, a_pb = rrule(dexize, x)
    b, b_pb = rrule(double_dex, a)
    c, c_pb = rrule(juliaize, b)
    
    @test c === 3.0f0
    c̄ = 10f0
    _, b̄ = c_pb(c̄)
    _, ā = b_pb(b̄)
    _, x̄ = a_pb(ā)

    @test x̄ === 20f0
end

@testset "Integration Test: Zygote.jl" begin
    double_via_dex = juliaize ∘ double_dex ∘ dexize
    y, pb= Zygote.pullback(double_via_dex, 1.5f0)
    @test y == 3f0
    @test pb(1f0) == (2f0,)
end