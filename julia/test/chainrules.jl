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


@testset "frule NativeFunction" begin
    dex_func"decimate_dex = \x:Float. x/10.0"
    @test frule((NoTangent(), 50f0), decimate_dex, 150f0) === (15f0, 5f0)

    dex_func"sum3_dex = \x:(Fin 3=>Float). sum x"
    @test frule((NoTangent(), [1f0, 10f0, 100f0]), sum3_dex, [1f0, 2f0, 3f0]) === (6f0, 111f0)

    dex_func"twovec_dex = \x:(Float32). [x,x]"
    twovec_dex(1f2)
    @test frule((NoTangent(), 10f0), twovec_dex, 4f0) == ([4f0, 4f0], [10f0,10f0])

    # With Implicts
    dex_func"def mysum_dex (arg0:Int32)?-> (arg1:Fin arg0 => Float32) : Float32 = sum arg1"
    @test_broken frule((NoTangent(), [1f0, 10f0, 100f0, 1000f0]), mysum_dex, [1f0, 2f0, 3f0, 4f0]) === (10f0, 1111f0)

    # With multiple arguments
    dex_func"add_dex = \x:Float32 y:Float32. x+y"
    @test_broken frule((NoTangent(), 10f0, 100f0), add_dex, 1f0, 2f0)
end