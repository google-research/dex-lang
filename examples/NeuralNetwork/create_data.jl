using Pkg: Pkg
Pkg.activate(@__DIR__)
using Dates: now
using MLDatasets: FashionMNIST


"""
    dex_repr(x)

Take a value `x` and return a string that is parsable in Dex to give an equivelent value.
"""
dex_repr(x) = repr(x)

# Dex only has one floating point value (Real), and its basically Julia's Float64.
dex_repr(x::Real) = repr(convert(Float64, x))
dex_repr(x::Integer) = repr(x)  # but all out Int types should be right.

# Note for multidimentional Array, we are reversing order of dims, by pealing last off first
# as Dex feels like it is row major, in that most commonly iterated dim should be first
dex_repr(xs::AbstractArray{<:Any, 1}) = "[" * join(dex_repr.(xs), ", ") * "]"
dex_repr(xs::AbstractArray{<:Any, N}) where N = dex_repr(collect(eachslice(xs; dims=N)))

###########################################################

declare_constant(io::IO, name, value) = println(io, name, " = ", dex_repr(value))

const MAX_ITEMS=100

open("data.dx", "w") do fh
    println(fh, "' ## [FashionMNIST](https://github.com/zalandoresearch/fashion-mnist)")
    println(fh, "Data constants generated on ", now(), " by  \n", @__FILE__, "  ")
    println(fh, "Truncated to at most $MAX_ITEMS items in the training or test sets")
    println(fh)
    declare_constant(fh, :traintensor, FashionMNIST.traintensor()[:,:,1:min(MAX_ITEMS, end)])
    declare_constant(fh, :trainlabels, FashionMNIST.trainlabels()[1:min(MAX_ITEMS, end)])
    println(fh)
    declare_constant(fh, :testtensor, FashionMNIST.testtensor()[:,:,1:min(MAX_ITEMS, end)])
    declare_constant(fh, :testlabels, FashionMNIST.testlabels()[1:min(MAX_ITEMS, end)])
    println(fh)
    println(fh, "' ---")
end
