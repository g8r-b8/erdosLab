# D1 report — recovered excerpt (§0–§1 only)

The full D1 report (scratchpad/R7/D1_weight6/D1_report.md) was lost when the scratchpad was wiped after two kernel
panics (2026-09-25). This is the part the R7 coordinator had read, reproduced from its context. §§2–9 (Theorem F,
Lemma S, Theorem G, Corollary 6.1) survive only as the summary in angle_R7.md §5 and as the scripts
`scripts/r7_D1_{flat_orient,tilt,global_hex,ring}.py`.

## 0. Headline (as written by D1)
An ORIENTATION argument replaces discharging: Σ_𝓡 v = 2E_𝓡, where E_𝓡 = #unit edges with at least one end in 𝓡.
If each edge incident to 𝓡 is owned by one of its 𝓡-ends, and every owned edge at y points into a half-open
half-plane of directions, then each y owns ≤ 3 edges and Σv ≤ 6r. In the flat model with the linear potential
"height" this is exact. Globally, sector frames plus averaging over random cut positions give an error ηn + C_η.
Theorem G (§4): Σ_𝓡 v ≤ 6r + ηn + C_η whenever |t − √3/2| ≥ 2.1·10⁻³.

## 1. Set-up and two exact facts
Notation as in B1/N3: δ = 1, R = Δ₂, t = Δ − Δ₂, K = ∩_{w∈X} D(w,R), D = diametral endpoints, S = points with a
Δ₂-partner, 𝓡 = X∖S, v(y) = deg y + m_y. 𝓡_I := 𝓡∖D, 𝓡_D := 𝓡∩D.

**Fact 1.1 (X ∩ ∂K ⊂ S; 𝓡_I ⊂ int K).** K is a finite intersection of closed discs. If y ∈ X∖D lies on ∂K, then y
is on the boundary circle of some D(w,R) with w ∈ X, so |yw| = Δ₂ and y ∈ S. Hence 𝓡_I = X ∩ int K and
S∖D = X ∩ ∂K.

**Fact 1.2.** Σ_{y∈𝓡} v(y) = (2e(𝓡) + e(𝓡,S)) + e(𝓡,S) = 2E_𝓡. So Σ_𝓡 v ≤ 6r + x ⟺ E_𝓡 ≤ 3r + x/2.

**Fact 1.3.** z ∈ D has a partner x with |zx| = Δ, so every other point of X lies in the open half-plane
{(y − z)·u_z > 0}. Unit neighbours are pairwise ≥ 60° apart, so deg z ≤ 3.

**Ownership.** Each edge incident to 𝓡 is assigned to one of its 𝓡-ends (a spoke y–q with q ∈ S necessarily to y).
E_𝓡 = Σ own(y).

**Lemma O.** If the edges owned by y all point into {ψ ∈ (−90°, 90°]} relative to some unit vector, then
own(y) ≤ 3 (four neighbours pairwise ≥ 60° apart span ≥ 180°).

Coordinator's note for the referee: in a flat triangular-lattice hexagon of side k (a toy, not a valid configuration)
E_𝓡 = 3r + 6k − 3, with the excess coming from the six 60° corners. The global claim therefore relies on K having total
turning 2π spread over arcs of radius R. How the tilted boundary rows behave (Lemma S, κ₁) is exactly what the
referee must check.
