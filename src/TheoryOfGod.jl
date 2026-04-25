module TheoryOfGod

const T = Float64

"""
TheoryOfGod

I = [ZERO < ○ < ONE] denotes a unit 1-dim space of information with origin ○ (no information) in its center including the corners ZERO and ONE.
Ω = I^I an ∞-dim normed and smooth vector space.
We have a Preorder 𝕋 on Ω such that ϵᵢ ∈ 𝕋:
* ϵᵢ ⊆ Ω
* ϵ₂ ∈ ϵ₁.ϵ̃ => ϵ₂|ϵ₁ ⊆ ϵ₁ <=> ϵ₂ ⫉ ϵ₁ ⩓ ϵ₂ ∈ ϵ₃.ϵ̃ => ϵ₁ = ϵ₃
* x ∈ Ω: x.ρ = 0 => ϵᵢ.Φ(x) ∈ I is arbitrary, computable and smooth fuzzy existence potential towards ONE=true xor ZERO=false.

ϵ ⊊ Ω defines its existence inside a subset of Ω using an origin (μ), a radius (ρ) and a closed vs. open in each direction (∂) vector. These vectors are finite and all other dimensional coordinates of ϵ are ○.
If we use a horizontal axis for dimension and a vertical axis for coordinate in the dimension, for any ϵ, the chart looks like a stepwise linear function with finite non-zero radius intervals (active dimensions) and zero interval points within the interpolated regions.
Each child ϵ is a subset of its parent in the active dimensions declared by the parent. All siblings are inf-dim disjoint.

god ⊊ God = Ω = I^I = I^(.) = [ZERO < ○ < ONE]^(.)
god observes or creates, God iterates.
"""

abstract type ∀ end
struct ∃{V<:AbstractVector,P<:AbstractVector{Tuple{Bool,Bool}},F,E<:∀} <: ∀
    ϵ̂::E
    d::V
    μ::V
    ρ::V
    ∂::P
    Φ::F
    h::UInt
    function ∃(ϵ̂::∀, d::V, μ::V, ρ::V, ∂::P, Φ::F) where {V<:AbstractVector,P<:AbstractVector{Tuple{Bool,Bool}},F}
        @assert length(d) == length(μ) == length(ρ) == length(∂)
        N = length(d)
        p = sortperm(d)
        ḋ = _permute(d, p)
        μ̇ = _permute(μ, p)
        ρ̇ = _permute(ρ, p)
        ∂̇ = _permute(∂, p)
        for i = 1:N
            @assert zero(T) ≤ ḋ[i] ≤ one(T)
            1 < i && @assert ḋ[i-1] ≠ ḋ[i]
            @assert zero(T) ≤ μ̇[i] - ρ̇[i] ≤ μ̇[i] + ρ̇[i] ≤ one(T)
        end
        μΩ, ρΩ = μρΩ(ϵ̂, μ̇, ρ̇)
        ϕ = Φ̂(Φ̇(Φ), ḋ, μΩ .- ρΩ, μΩ .+ ρΩ)
        @assert Φ̇(Φ)(zeros(T, N)) isa T
        h = hash(ḋ, hash(μ̇, hash(ρ̇, hash(∂̇, hash(ϵ̂)))))
        new{V,P,typeof(ϕ),typeof(ϵ̂)}(ϵ̂, ḋ, μ̇, ρ̇, ∂̇, ϕ, h)
    end
end
Base.hash(ϵ::∃, h::UInt) = hash(ϵ.h, h)
function _permute(v::AbstractVector, p::AbstractVector{<:Integer})
    N = length(v)
    @assert length(p) == N
    vals = ntuple(i -> v[p[i]], N)
    V = typeof(v)
    V(vals...)
end
struct 𝕋 <: ∀
    ϵ̃::Dict{∀,Vector{∃}}
    Ο::Dict{∀,UInt}
    L::ReentrantLock
    s::Ref{UInt}
    function 𝕋()
        ϵ̃ = Dict{∀,Vector{∃}}()
        Ο = Dict{∀,UInt}()
        Ω = new(ϵ̃, Ο, ReentrantLock(), Ref(UInt(1)))
        Ω.ϵ̃[Ω] = ∃[]
        Ω.Ο[Ω] = Ω.s[]
        Ω
    end
end
Base.hash(::𝕋, h::UInt) = hash(:Ω, h)
t(Ο::UInt) = one(T) - one(T) / (one(T) + T(log(Ο)))
t(ϵ::∀, ω::𝕋) = t(ω.Ο[ϵ])
t(ω::𝕋) = t(ω, ω)
const ○ = one(T) / (one(T) + one(T))
const ○̂ = x -> ○

struct Φ̂{D<:AbstractVector,F}
    Φ::F
    d::D
    z::D
    o::D
end
function (ϕ::Φ̂)(x)
    for i = 1:length(ϕ.d)
        ϕ.o[i] == ϕ.z[i] && return ○
        x[i] ≤ ϕ.z[i] && return ○
        ϕ.o[i] ≤ x[i] && return ○
    end
    ẋ = (x .- ϕ.z) ./ (ϕ.o .- ϕ.z)
    ϕ.Φ(ẋ)
end
Φ̇(Φ::Φ̂) = Φ.Φ
Φ̇(Φ) = Φ
function Base.copy!(ϵ::∃, ḋ, μ̇, ρ̇, ω::𝕋)
    ϵ̇ = ∃!(ḋ, μ̇, ρ̇, ϵ.∂, ϵ.Φ, ω)
    for ϵ̃ = ω.ϵ̃[ϵ]
        μ̃ = μ̂̂(μ̇, ρ̇, ϵ̃.μ)
        ρ̃ = ρ̂̂(ρ̇, ϵ̃.ρ)
        copy!(ϵ̃, ḋ, μ̃, ρ̃, ω)
    end
    ϵ̇
end
ρ̂̂(ρ̂, ρ) = T(2) .* ρ̂ .* ρ
μ̂̂(μ̂, ρ̂, μ) = μ̂ .+ ρ̂ .* (T(2) .* μ .- one(T))
ρ̃̃(ρ, ρ̃) = ○ * ρ ./ ρ̃
μ̃̃(μ, ρ, μ̃) = ○ * ((μ .- μ̃) ./ ρ .+ one(T))
function μρΩ(ϵ::∃)
    ϵ.ϵ̂ isa 𝕋 && return ϵ.μ, ϵ.ρ
    μ̂, ρ̂ = μρΩ(ϵ.ϵ̂)
    μ̂̂(μ̂, ρ̂, ϵ.μ), ρ̂̂(ρ̂, ϵ.ρ)
end
μρΩ(::𝕋, μ, ρ) = μ, ρ
function μρΩ(ϵ::∃, μ, ρ)
    μ̇, ρ̇ = μρΩ(ϵ)
    μ̂̂(μ̇, ρ̇, μ), ρ̂̂(ρ̇, ρ)
end
function μρ(ϵd, ϵμ, ϵρ, ϵ∂, d)
    i = searchsortedfirst(ϵd, d)
    i ≤ length(ϵd) && ϵd[i] == d && return ϵμ[i], ϵρ[i], ϵ∂[i]
    ○, zero(T), (true, true)
end
function ⊂(z, o, ∂, ẑ, ô, ∂̂)
    !(z < o || (z == o && ∂[1] && ∂[2])) && return false
    !(ẑ < z || (z == ẑ && (!∂[1] || ∂̂[1]))) && return false
    !(o < ô || (o == ô && (!∂[2] || ∂̂[2]))) && return false
    true
end
function ⫉(ϵd, ϵμ, ϵρ, ϵ∂, ϵ̂d, ϵ̂μ, ϵ̂ρ, ϵ̂∂)
    for (î, d̂) = enumerate(ϵ̂d)
        μ̂ = ϵ̂μ[î]
        ρ̂ = ϵ̂ρ[î]
        μ, ρ, ∂ = μρ(ϵd, ϵμ, ϵρ, ϵ∂, d̂)
        z, o = μ - ρ, μ + ρ
        ẑ, ô = μ̂ - ρ̂, μ̂ + ρ̂
        !⊂(z, o, ∂, ẑ, ô, ϵ̂∂[î]) && return false
    end
    true
end
β(d, μ, ρ, ∂, ω::𝕋) = β(d, μ, ρ, ∂, ω, ω)
function β(d, μ, ρ, ∂, ϵ̂::∀, ω::𝕋)
    ϵ̃ = filter(ϵ -> begin
            ϵμ, ϵρ = μρΩ(ϵ)
            ⫉(d, μ, ρ, ∂, ϵ.d, ϵμ, ϵρ, ϵ.∂)
        end, ω.ϵ̃[ϵ̂])
    isempty(ϵ̃) && return ϵ̂
    β(d, μ, ρ, ∂, only(ϵ̃), ω)
end
function Base.:∩(z₁, o₁, ∂₁, z₂, o₂, ∂₂)
    ż = max(z₁, z₂)
    ȯ = min(o₁, o₂)
    ż < ȯ && return true
    ż ≠ ȯ && return false
    ∂₀₀ = z₂ < z₁ ? ∂₁[1] : (z₁ < z₂ ? ∂₂[1] : ∂₁[1] && ∂₂[1])
    ∂₀₁ = o₁ < o₂ ? ∂₁[2] : (o₂ < o₁ ? ∂₂[2] : ∂₁[2] && ∂₂[2])
    ∂₀₀ && ∂₀₁
end
function Base.:∩(ϵ₁d, ϵ₁μ, ϵ₁ρ, ϵ₁∂, ϵ₂d, ϵ₂μ, ϵ₂ρ, ϵ₂∂, ϵ₂ϵ̂d)
    for d = ϵ₂ϵ̂d
        μ₁, ρ₁, ∂₁ = μρ(ϵ₁d, ϵ₁μ, ϵ₁ρ, ϵ₁∂, d)
        μ₂, ρ₂, ∂₂ = μρ(ϵ₂d, ϵ₂μ, ϵ₂ρ, ϵ₂∂, d)
        z₁, o₁ = μ₁ - ρ₁, μ₁ + ρ₁
        z₂, o₂ = μ₂ - ρ₂, μ₂ + ρ₂
        !∩(z₁, o₁, ∂₁, z₂, o₂, ∂₂) && return false
    end
    true
end
function ∃!(d, μ, ρ, ∂, ϕ, ω::𝕋)
    lock(ω.L)
    ϵ̂ = β(d, μ, ρ, ∂, ω)
    any(ϵ̃ -> begin
            ϵ̃ϵ̂d = ϵ̂ isa ∃ ? ϵ̂.d : unique(sort(d ∪ ϵ̃.d))
            ∩(d, μ, ρ, ∂, ϵ̃.d, ϵ̃.μ, ϵ̃.ρ, ϵ̃.∂, ϵ̃ϵ̂d)
        end, ω.ϵ̃[ϵ̂]) && (unlock(ω.L); throw("An intersecting sibling found."))
    μ̃, ρ̃ = if ϵ̂ === ω
        μ, ρ
    else
        ϵ̂μ, ϵ̂ρ = μρΩ(ϵ̂)
        μ̃̃(ϵ̂μ, ϵ̂ρ, μ), ρ̃̃(ρ, ϵ̂ρ)
    end
    ϵ = ∃(ϵ̂, d, μ̃, ρ̃, ∂, ϕ)
    while Sys.free_memory() < ω.s[] + sizeof(ϵ)
        rm!(ω)
    end
    ω.s[] += sizeof(ϵ)
    ω.Ο[ω] += 1
    ω.Ο[ϵ] = ω.Ο[ω]
    push!(ω.ϵ̃[ϵ̂], ϵ)
    ω.ϵ̃[ϵ] = ∃[]
    unlock(ω.L)
    ϵ
end
function rm!(ω::𝕋, ϵ::∃)
    while !isempty(ω.ϵ̃[ϵ])
        ϵ̃ = first(ω.ϵ̃[ϵ])
        rm!(ω, ϵ̃)
    end
    filter!(ϵ̃ -> ϵ̃ !== ϵ, ω.ϵ̃[ϵ.ϵ̂])
    delete!(ω.ϵ̃, ϵ)
    delete!(ω.Ο, ϵ)
    ω.s[] -= sizeof(ϵ)
end
rm!(ω::𝕋) = rm!(ω, argmin(ϵ -> ω.Ο[ϵ], ω.ϵ̃[ω]))

end
