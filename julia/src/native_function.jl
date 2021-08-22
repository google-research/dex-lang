"holds information on how to map an argument argment in a signature into a julia type"
struct Binder
    name::String
    type
    implicit::Bool
end

"Creates an `Array{T,N}``, if all elements of size are present then that array is initialized to hold `size`"
struct ArrayBuilder{T,N}
    size::Vector{Union{Nothing,Int}}
end
ArrayBuilder{T}(size) where T = ArrayBuilder{T,length(size)}(size)


# CombinedParsers.jl based parser:
@with_names begin
    name = !re"arg\d+"
    scalar_type = Either{Any}(Any[
        parser("f32"=>Float32),
        parser("f64"=>Float64),
        parser("i32"=>Int32),
        parser("i64"=>Int64),
        parser("i8"=> Int8),
    ])
    
    size_ele = Numeric(Int) | parser(name=>nothing)  # convert names to nothing as we don't use them
    sizes = join(Repeat(size_ele),",")
    array_type = map(scalar_type * "[" * sizes * "]") do (T, _, sz, _)
        ArrayBuilder{T}(sz)
    end

    type = Either{Any}(Any[array_type, scalar_type])
    implicit = parser("?"=>true) | false
    arg_sig = map(implicit * name * ":" * type) do (i, n, _ , t)
        Binder(n, t, i)
    end
    arg_sigs = join(Repeat(arg_sig),",")
end

parse_sig(sig) = parse(arg_sigs, sig)