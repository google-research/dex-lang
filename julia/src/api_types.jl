struct HsAtom end
struct HsContext end
struct HsJIT end
struct NativeFunctionObj end
struct NativeFunctionSignature
    arg::Cstring
    res::Cstring
    _ccall::Cstring  # can't name this field `ccall` as that is a built-in in julia
end

struct CRectArray
    data::Ptr{Nothing}
    shape_ptr::Ptr{Int64}
    strides_ptr::Ptr{Int64}
end



"""
    TaggedUnion{Tuple{A, B, ...}}

Represents a tagged union over types `A`, `B` etc.
Must have a first field `tag::UInt64`
and a second field `payload` which must be some isbits type that can hold the largest 
element of the union, which you can (e.g.) declare as a custom `primitive`.
This is required as Julia doens't directly support Unions in the mapping to-from C
so we store the data as arbitary bits then force it to be reinterpretted based on the tag
"""
abstract type TaggedUnion{T<:Tuple} end
function bust_union(x::TaggedUnion{U}) where U
    T = U.parameters[Int(x.tag) + 1]
    return bust_union(force_reinterpret(T, x.payload))
end
bust_union(x) = x  # not a union, leave it alone

"Forces reinterpretting `raw` as a `T`. If sizeof(raw) <: size(T) high bits will be filled with junk."
function force_reinterpret(::Type{T}, raw) where T
    isbits(raw) || throw(ArgumentError("Can only reinterpret from a isbits type"))
    isbitstype(T) || throw(ArgumentError("Can only reinterpret into a isbits type"))
    return unsafe_load(Ptr{T}(Base.pointer_from_objref(Ref(raw))))
end

"Holds data for CLit, big enough to hold the larges of its union members, such as a Float64"
primitive type CLitPayload 64 end
struct CLit <: TaggedUnion{Tuple{Int64, Int32, UInt8, Float64, Float32, UInt32, UInt64}}
    tag::UInt64
    payload::CLitPayload
end
CLit(x) = CLit(CLit_tag(x), force_reinterpret(CLitPayload, x))

CLit_tag(::Int64) = 0x0000_0000_0000_0000
CLit_tag(::Int32) = 0x0000_0000_0000_0001
CLit_tag(::UInt8) = 0x0000_0000_0000_0002
CLit_tag(::Float64) = 0x0000_0000_0000_0003
CLit_tag(::Float32) = 0x0000_0000_0000_0004
CLit_tag(::UInt32) = 0x0000_0000_0000_0005
CLit_tag(::UInt64) = 0x0000_0000_0000_0006

"Holds data for CAtom, big enough to hold the larges of its union members, which is the CRectArray"
primitive type CAtomPayload 3*64 end
struct CAtom <: TaggedUnion{Tuple{CLit, CRectArray}}
    tag::UInt64
    payload::CAtomPayload
end
CAtom(x) = CAtom(0x0000_0000_0000_0000, force_reinterpret(CAtomPayload, CLit(x)))
CAtom(x::AbstractArray) = throw(DomainError(typeof(x), "Arrays not yet supported"))
function CAtom(atm::Ptr{HsAtom})
    result = Ref{CAtom}()
    success = to_CAtom(atm, result)
    iszero(success) && throw_from_dex()
    return result[]
end