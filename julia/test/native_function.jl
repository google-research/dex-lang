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

    @testset "dex_func anon funcs" begin
        @test dex_func"\x:Float. exp x"(0f0) === 1f0
        @test dex_func"\x:Float. (2.0*x, x)"(1.5f0) === (3f0,  1.5f0)
        @test dex_func"\x:Int64 y:Int. I64ToI x + y"(Int64(1), Int32(2)) === Int32(3)
        @test dex_func"\x:((Fin 3)=>Float). sum x"([1f0, 2f0, 3f0]) === 6f0

        @test dex_func"\x:((Fin 3)=>Float). for i. 2.0 * x.i"([1f0, 2f0, 3f0]) isa Vector{Float32}
        @test dex_func"\x:((Fin 3)=>Float). for i. 2.0 * x.i"([1f0, 2f0, 3f0]) == [2f0, 4f0, 6f0]
    end

    @testset "dex_func named funcs" begin
        dex_func"""
        def myTranspose (n: Int) ?-> (m: Int) ?->
                        (x : (Fin n)=>(Fin m)=>Float) : (Fin m)=>(Fin n)=>Float =
            for i j. x.j.i
        """

        myTranspose([1f0 2f0 3f0; 4f0 5f0 6f0]) isa Matrix{Float32}

        # Broken because elements come out in wrong order.
        # Check C vs Fortran array orders
        @test_broken myTranspose([1f0 2f0 3f0; 4f0 5f0 6f0]) == [1f0 2f0 3f0; 4f0 5f0 6f0]'
    end

    @testset "dex_func errors" begin
        @test_throws ArgumentError dex_func"\x:Float. exp x"(0.0)        
    end

    @testset "NativeFunction directly" begin
        m = DexModule(raw"def addTwo (n: Int) ?-> (x: (Fin n)=>Float) : (Fin n)=>Float = for i. x.i + 2.0")
        add_two = NativeFunction(m.addTwo)
        @test add_two([1f0, 10f0]) == [3f0, 12f0]
    end
end
