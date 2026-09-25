# Route A report — elementary (Euler-free) approach to `CoreE` (Theorem E′, Erdős #132)

Agent: Route A research agent (2026-09-25). Scripts: `problems/132/scripts/l97A_*.py`.
Status: complete (§§0–6). Proof on paper, exact local checks, float sanity checks, Lean DAG estimate.

## 0. Verdict

**An elementary proof exists, and it is better than E′ in the error term.** It uses no faces, no
Euler formula, no Jordan curve theorem, no winding numbers and no arc length.

**Theorem A (Route A).** Let `X` be finite with minimum distance 1 and `Δ ≤ 1.94Δ₂`. Put
`K = ∩_{w∈X} D(w,Δ₂)` and `depth z = min_w (Δ₂ − |z − w|)`. Let `Y ⊆ X ∩ K`, and let `A ⊆ Y` be
points with `depth = 0` (for example `A = S∖D`). Let `ρ > 0` be real, `h = ρ + ½`,
`Yout = {y ∈ Y : depth y < ρ}` and `H = G[Yout]`. Then

  `Def(H) ≥ 2|A| − 18·(1 + (2/√3)·(h/r*)·diam K)`   if `r* := max_K depth ≥ h`,

and in all cases

  **`Def(H) ≥ 2|A| − E_A(h)`,  with `E_A(h) := 2(1200h + 2)²`** (`≤ 2.9·10⁶ h²` for `h ≥ 1`).

In the main case (`r* ≥ h`) the loss is **linear** in `h`: `18 + 12471h`. The quadratic bound
appears only in the trivial case `r* < h`, where `Def ≥ 0` and a packing bound on `|A|` are used.

- **What the proof uses.** An exact direction-averaging identity for `Def`, and steep-chain
  combinatorics (finite; one simple path per vertex). It also uses three local facts: the
  strict chord inequality, a one-variable trigonometric inequality at each A-point, and one
  global convex-geometry lemma. That lemma says that the turning of the "caps" cut off by
  A-to-A chains has bounded overlap, because every cap is separated from the deep core by a
  segment of length `O(h)`. The only "topology" is the intermediate value theorem on segments
  and on the support-point parametrisation of `∂K`.
- **Hypotheses it drops.** It does not use `ρ ∈ ℕ`, `ρ ≥ 1`, `h < Δ₂/200`, `|A| > 1000h` or
  `Δ₂ ≥ 10⁴`. `Δ ≤ 1.94Δ₂` enters only through the fatness Lemma F.
- **Consequence for `CoreE`.** `CoreE` follows once `Eh` in `E132Main97Defs.lean` is replaced by an
  `O(h²)` polynomial with a larger constant, for example `Eh h := 3·10⁶ h²`. The current
  `Eh = 1764h² + 223h + 4` is **not** reached for small `h`, because the fatness constant 600 and
  the packing bound are generous. The downstream constants (`CE`, and possibly `C97`) must be
  raised accordingly; see §6.
- **Obstructions from angle_R6 §5.5.** The L and M obstructions are consistent with the proof.
  The proof is not a first-layer ledger: the missing ½ per A-point is paid by the directions
  `φ` in which an A-point is exposed but its steep chain is **not** A-to-A. That is a global
  property, controlled by the core.

**Status of the verification.**
- Every step is written out in §3.
- The local lemmas are verified **exactly** (Fractions, angles in rational degrees; 20 679
  configurations, `l97A_local_exact.py`).
- The global steps were sanity-checked with floats on 45 configurations
  (`l97A_check.py`, all assertions pass). The configurations are: rings, ring paths, the
  Eisenstein lattice annuli (up to 3426 points), the angle_R6 L family (k = 1..4), the M pair-gap
  row, and random unit-distance growth in Reuleaux, lens, pentagon and disc ball-polygons with
  A-points at corners and exact unit A–A chords.
- **This proof has not been refereed.**

## 1. Setup and exact identities (steep-chain decomposition)

Notation.
- `S¹` is the circle of directions, with arc-length measure `|·|` (total `2π`).
- `∠(u,v) ∈ [0,π]` is the angular distance.
- `C(φ)` is the **open** arc of length `π/3` centred at `φ` (the open 60° cone around `φ`).
- For a vertex `v` of `H` and a neighbour `n`, `dir(v→n) ∈ S¹` is the direction of `n − v`.

**Lemma 1 (one neighbour per cone).** For every `v` and every `φ`, at most one neighbour of `v` has
its direction in `C(φ)`.

*Proof.* Take neighbours `n₁ ≠ n₂`. Then `|n₁ − n₂| ≥ 1 = |v − nᵢ|`, and the law of cosines gives
`∠(dir n₁, dir n₂) ≥ π/3`. Two points of an open arc of length `π/3` are less than `π/3` apart. ∎

**Exposure sets.** `E_v := {φ : no neighbour direction of v lies in C(φ)}`. Now `φ ∉ E_v` iff
`φ ∈ C(dir(v→n))` for some `n`. By Lemma 1 these arcs are pairwise disjoint, so

  `|E_v| = 2π − deg_H(v)·π/3`,  and  `Def(H) = Σ_v (3 − deg v/2) = (3/2π) Σ_v |E_v|`.   (1.1)

**Steep chains (fixed φ).**
- The *up-neighbour* `u(v)` of `v` is its unique neighbour, if any, with direction in `C(φ)`.
  The *down-neighbour* `d(v)` is its neighbour with direction in `C(−φ)`.
- `n = u(v) ⇔ v = d(n)`, and `⟨u(v) − v, φ⟩ > cos(π/6) > 0`.
- Following `u` from `v` terminates at the *top* `top(v)`: `⟨·,φ⟩` increases strictly and `V(H)`
  is finite.
- The tops are exactly `{v : φ ∈ E_v}`. The fibres of `top` are simple paths
  `bottom = v₀, v₁ = u(v₀), …, v_k = top`, called **chains**; `d(v₀)` does not exist, i.e.
  `−φ ∈ E_{v₀}`.
- `N(φ) := #tops = Σ_v 1[φ ∈ E_v]`, so `∫_{S¹} N = Σ_v |E_v| = (2π/3)·Def(H)`.

(Nothing needs `φ` to be generic: the cones are open, and Lemma 1 holds for every `φ`.)

Definitions for `A`:
- `T(φ) := {a ∈ A : φ ∈ E_a}` (A-tops) and `B(φ) := {a ∈ A : −φ ∈ E_a}` (A-bottoms).
- `M₁(φ)` := the set of tops `t ∈ A` whose chain has at least 2 vertices and a bottom in `A`
  (the "A-to-A chains").

**Lemma 2.** `N(φ) ≥ |T(φ) ∪ B(φ)| − |M₁(φ)|`.

*Proof.* Map `a ∈ T ∪ B` to `top(a)`. The fibre over a top `t` is contained in
`{t, bottom(t)}`. It has two elements only when `t ∈ A` and `bottom(t) ∈ A∖{t}`, that is,
when `t ∈ M₁(φ)`. ∎

Integrating over `φ`, and using `1[a ∈ T ∪ B] = 1[φ ∈ E_a ∪ (−E_a)]`:

  `(2π/3)·Def(H) ≥ Σ_{a∈A} |E_a ∪ (−E_a)| − ∫_{S¹} |M₁(φ)| dφ.`   (1.2)

**Where the ½ per A-point lives.**
- Locally, `|E_a ∪ −E_a| ≥ 4π/3` always; see Lemma 5. The inequality `(3/2π)·(4π/3) = 2` is
  exactly the target.
- The whole difficulty is `∫|M₁|`: directions in which an A-point is exposed **and** its steep
  chain ends at another exposed A-point.
- For a single unit-chord ring (`Def = 2|A|`), `∫|M₁| = 4π` comes from the two side chains per
  direction. It is paid exactly by the curvature slack `Σ_a 2(θ₀(a) − π) = 4π`.
- The proof shows that `∫|M₁|` is always paid by such local slack plus `O(h)`.

## 2. Local lemmas at A-points (exact; `l97A_local_exact.py`)

**Support normals.** For `a ∈ A`, let `N(a) := {ν ∈ S¹ : ⟨k − a, ν⟩ ≤ 0 ∀ k ∈ K}`.
- `N(a)` is nonempty. If `|a − w| = Δ₂`, then `ν_w = (a − w)/Δ₂` satisfies
  `⟨k − a, ν_w⟩ ≤ −|k − a|²/(2Δ₂)`.
- `N(a)` is a closed arc of length `< π`.

**Strict separation.** For `k ∈ K∖{a}` and `ν ∈ N(a)`: `⟨k − a, ν⟩ < 0`.
- The midpoint `m` of `ak` satisfies `|m − w|² = (|a − w|² + |k − w|²)/2 − |a − k|²/4
  ≤ Δ₂² − |a − k|²/4`.
- So `depth(m) > 0`, and a small disc around `m` lies in `K`.
- If `⟨k − a, ν⟩ = 0`, then `m + εν ∈ K` would violate the support inequality.

The same parallelogram argument shows that `K` is strictly convex (used in §3).

**Consequences.**
- All neighbours of `a` lie strictly behind every `ν ∈ N(a)`, i.e. in an open half-plane.
- Hence `d := deg_H(a) ≤ 3`.
- For `d ≥ 2`, the gap between consecutive neighbour directions that contains the closed front
  half-circle (the *outer gap*) has length `θ₀ ≥ π`. Put `s_a := θ₀ − π`. For `d ≤ 1` put
  `s_a := π`.
- Fix `ν ∈ N(a)` and measure neighbour directions `ψ` relative to the inward normal
  `θ_ν := dir(−ν)`. Then every `ψ ∈ (−π/2, π/2)`. Put `ε₁ := min ψ + π/2 > 0` and
  `ε₂ := π/2 − max ψ > 0`. Then **`ε₁ + ε₂ = s_a`** (for `d ≥ 1`).

**Lemma 5.** `|E_a ∪ (−E_a)| ≥ 4π/3 + 2·min(s_a, π/3)`.

*Proof.*
1. `E_a` contains the open arc `O` of length `θ₀ − π/3 = 2π/3 + s_a`, centred at the bisector of the
   outer gap. (For `d = 1`, `O = S¹ ∖ C(dir n)`; for `d = 0`, `E_a = S¹`.)
2. `O` and `−O` are arcs of equal length centred at antipodal points.
3. So `|O ∪ −O| = min(2π, 2|O|) = min(2π, 4π/3 + 2s_a)`. ∎

**Ramp functions.** For `ν ∈ N(a)`:
- `σ_ν(φ) := 2π/3 − ∠(φ, −ν)`;
- `m_ν(φ) := min(max(σ_ν(φ), 0), π/3)`;
- `m̂_a(φ) := sup_{ν ∈ N(a)} m_ν(φ)`;
- `J_a := E_a ∖ (−E_a)`. These are the directions where `a` is a top, not a bottom, of its chain.

**Lemma 6.** `∫_{J_a} m̂_a(φ) dφ ≤ min(s_a, π/3)²`.

*Proof.* Fix `ν`. Write `ψ := φ − θ_ν` (relative angle, in `(−π, π]`).

1. **Where `m_ν > 0`.** `m_ν(φ) > 0 ⇔ |ψ| < 2π/3`.
2. **The plateau `|ψ| ≤ π/3` misses `J_a`.** There the cone `C(−φ)` lies in the open front
   half-plane, so it contains no neighbour. Hence `−φ ∈ E_a`, i.e. `φ ∉ J_a`.
3. **Ramp `ψ ∈ (π/3, 2π/3)`.**
   - `m_ν = 2π/3 − ψ`.
   - `φ ∈ E_a` means no neighbour at relative angle in `(ψ − π/6, π/2)`. That is
     `max ψ_n ≤ ψ − π/6`, i.e. `ψ ≥ 2π/3 − ε₂`.
   - `φ ∉ −E_a` means some neighbour at relative angle in `(−π/2, ψ − 5π/6)`. That is
     `ψ > π/3 + ε₁`.
   - So this ramp is `ψ ∈ (max(π/3 + ε₁, 2π/3 − ε₂), 2π/3)`, of length
     `L₊ = min(ε₂, π/3 − ε₁)₊`, on which `m_ν` decreases linearly from `L₊` to 0.
   - The ramp contributes `L₊²/2`.
4. **Ramp `ψ ∈ (−2π/3, −π/3)`.** Symmetrically it contributes `L₋²/2` with
   `L₋ = min(ε₁, π/3 − ε₂)₊`.
5. **The sup over `ν ∈ N(a)`.**
   - In absolute angles the left end of the `+`-ramp is `max(n_min + 5π/6, n_max + π/6)`. This
     does not depend on `ν`.
   - The ramp value is `θ_ν + 2π/3 − φ`.
   - So `sup_ν` on the `+`-side is the ramp of the single extreme `ν` with the largest `θ_ν`.
     Similarly the `−`-side uses the other extreme.
   - Hence `∫_{J_a} m̂_a ≤ L₊(ν⁺)²/2 + L₋(ν⁻)²/2 ≤ min(s_a, π/3)²`, since `ε₁, ε₂ ≤ s_a`. ∎

**Corollary (★).** `|E_a ∪ −E_a| − (6/π)∫_{J_a} m̂_a ≥ 4π/3`.

*Proof.* Put `x = min(s_a, π/3) ≤ π/3`. Then `(6/π)x² ≤ 2x`. Now combine Lemmas 5 and 6. ∎

**Exact verification.** `l97A_local_exact.py 3 20000` verifies Lemma 5, Lemma 6 and (★) exactly in
rational degrees, with piecewise-linear integrals computed exactly:
- the setting is `d = 0..3`, pairwise separations `≥ 60°`, and normal cones of width 0°–89° with
  every neighbour strictly behind every normal;
- the checks cover a 3° grid and 20 000 random rational configurations;
- all hold, and the minimum slack in (★) is `0.0166` (in units of `π`).

Equality in (★) is approached when `s_a → π/3` and a neighbour tends to the tangent line.

## 3. Proof on paper

### 3.1 The chain inequality (a triangle inequality)

**Lemma 7.** Let `t ∈ M₁(φ)` have bottom `b`. Then:
- (i) `φ ∈ J_t` and `−φ ∈ J_b`;
- (ii) for **any** `ν_t ∈ N(t)` and `ν_b ∈ N(b)`,

  `π/3 ≤ m_{ν_t}(φ) + m_{ν_b}(−φ) + ∠(ν_b, ν_t).`

*Proof.*
1. (i): `t` is a top, and its chain predecessor lies in `C(−φ)`. Symmetrically for `b`.
2. (ii): put `σ_t = 2π/3 − ∠(φ, −ν_t)` and `σ_b = 2π/3 − ∠(−φ, −ν_b) = 2π/3 − ∠(φ, ν_b)`. Then

   `σ_t + σ_b = π/3 + ∠(φ, ν_t) − ∠(φ, ν_b) ≥ π/3 − ∠(ν_t, ν_b)`

   by the triangle inequality on `S¹`.
3. If `σ_t ≥ π/3` or `σ_b ≥ π/3`, the corresponding `m` equals `π/3`. Otherwise `m ≥ σ` for both. ∎

Each `a ∈ A` is the top of at most one chain and the bottom of at most one chain. Hence, for any
choice of normals `ν_t ∈ N(t)` and `ν_{b(t)} ∈ N(b(t))`:

  `|M₁(φ)| ≤ (3/π)[ Σ_{a∈A} 1[φ∈J_a] m̂_a(φ) + Σ_{a∈A} 1[−φ∈J_a] m̂_a(−φ) + Σ_{t∈M₁(φ)} ∠(ν_{b(t)}, ν_t) ].`   (3.1)

### 3.2 The global lemma: caps have bounded overlap (the only place the core is used)

Let `r* := max_K depth`, attained at `o`. Assume `r* ≥ h`, and put `K′ := {depth ≥ h}`
(convex, since depth is concave).

**Lemma G.** For every `φ`, normals `ν_t ∈ N(t)` and `ν_{b(t)} ∈ N(b(t))` can be chosen so that

  `Σ_{t∈M₁(φ)} ∠(ν_{b(t)}, ν_t) ≤ 2π·M`,  where  `M := 1 + (2/√3)·(h/r*)·diam K`.

*Proof.*

**(G1) Core.**
- Every point of an edge of `H` has depth `< ρ + ½ = h`: depth is 1-Lipschitz and every
  vertex has depth `< ρ`. So `K′` misses the drawing of `H`.
- For `z ∈ K`, the point `q(z) := o + (1 − h/r*)(z − o)` has depth `≥ (h/r*)·r* = h` by
  concavity. So `q(z) ∈ K′`, and `|z − q(z)| ≤ (h/r*)·diam K`.

**(G2) Sides of a chain.** Fix a chain `C: b = v₀, …, v_k = t` (`k ≥ 1`, `b, t ∈ ∂K`).
- Coordinates: `y := ⟨·,φ⟩` and `x := ⟨·,φ^⊥⟩`. `C` is the graph `x = c(y)`, `y ∈ [y_b, y_t]`,
  of a piecewise-linear `c`.
- `K ∩ {y} = [l(y), r(y)] × {y}` for `y ∈ [y₋, y₊]`.
- **(S0)** If `t` lies in the relative interior of its horizontal chord, or that chord is a
  single point, then `y_t = y₊`.
  - In the first case every supporting line at `t` contains the chord, so it is horizontal.
    Since `y_b < y_t`, this forces `K ⊂ {y ≤ y_t}`.
  - In the second case `int K ≠ ∅` and convexity force `y_t ∈ {y₋, y₊}`.
  - The same holds for `b` with `y₋`.
- **Side function** on `K ∖ C`:
  - in the strip `y_b ≤ y ≤ y_t`: `side(p) = sign(x_p − c(y_p))`;
  - above the strip: `+1` if `t` is the left end of its chord, `−1` if it is the right end
    (by S0 there are no points above otherwise);
  - below the strip: the same rule with `b`.
- **(S1)** If `side p = −1` and `side q = +1`, then `[p,q]` meets `C`.
  - Inside the strip, apply the IVT to `g = x − c(y)` along the segment.
  - A segment leaving the strip through the level `y_t` crosses it at a point `u` with
    `x_u ≤ x_t` (when `t` is a right end). Either `u = t ∈ C`, or `g(u) < 0`, and the IVT
    continues inside the strip. The same holds at `y_b`.
- **(S2)** `K′` is convex and misses `C` (G1), so by S1 it lies on one side. Reflect `x` so that
  this side is `+1`. The **cap** of `C` is `C ∪ {side = −1}`.

**(G3) The cap contains an arc of normals from `N(t)` to `N(b)`.**
- *Support points.* `z(ν)` is the unique maximiser of `⟨·,ν⟩` on `K` (unique by strict
  convexity). It depends continuously on `ν`.
- *Parametrisation.* Put `ν(α) = cos α·φ^⊥ + sin α·φ`.
  - For `α ∈ [π/2, 3π/2]`, `z(ν(α))` is the **left** end `(l(Y(α)), Y(α))` of its horizontal
    chord.
  - `Y` is continuous and non-increasing. Proof: from `⟨z − z′, ν(α)⟩ ≥ 0 ≥ ⟨z − z′, ν(α′)⟩`
    with `α < α′`, the direction of `z − z′` lies in `[α − π/2, α′ − π/2] ⊂ [0, π]`, so
    `y_z ≥ y_{z′}`.
  - `Y(π/2) = y₊` and `Y(3π/2) = y₋`.
  - The right half is symmetric: `Y_R` is non-decreasing on `[−π/2, π/2]`.
- *The endpoint `α_t`.* If `t` is a left end, the IVT gives `α_t ∈ [π/2, 3π/2]` with `z = t`.
  If `t` is a right end, it gives `α_t ∈ [−π/2, π/2]` with `z = t`.
- *The endpoint `α_b`.* The same for `b`, with `α_b ∈ [π/2, 3π/2]` (left end) or
  `α_b ∈ [3π/2, 5π/2]` (right end).
- *Ordering.* Monotonicity gives `α_t < α_b`. Put `Γ_C := {ν(α) : α ∈ [α_t, α_b]}`. It has
  length `< 2π`, and its endpoints satisfy `ν(α_t) ∈ N(t)` and `ν(α_b) ∈ N(b)`.
- *Claim: `z(ν) ∈ cap(C)` for every `ν ∈ Γ_C`.*
  - On the left half, `z = (l(Y), Y)`. If `Y ∈ [y_b, y_t]`, then `l(Y) ≤ c(Y)`, so `z` is on `C`
    or has side `−1`.
  - `Y > y_t` occurs on `Γ_C` only when `t` is a right end, and then everything above the strip
    has side `−1`. The same holds below the strip.
  - On the right half, `Γ_C` contains only normals whose support points lie above `t` (or below
    `b`), or are `t` (or `b`) themselves. Those sit in the attached region of side `−1`.
- So `∠(ν(α_b), ν(α_t)) ≤ |Γ_C|`.

**(G4) Distinct chains are far apart.**
- (P1) Unit edges do not cross.
- Two unit edges with four distinct endpoints, pairwise `≥ 1` apart, are at distance `≥ √3/2`.
  - The distance of disjoint segments is attained at an endpoint.
  - The distance from a point `P` to a unit segment `QR` with `|PQ|, |PR| ≥ 1` is at least
    `√(1 − ¼)`.

**(G5) Counting.** Fix `ν`. Let `I_ν` be the set of `t ∈ M₁(φ)` with `ν ∈ Γ_{C(t)}`. Put
`z = z(ν)` and `q = q(z) ∈ K′`.
- For `t ∈ I_ν`, either `z ∈ C(t)` or `side(z) = −1 ≠ side(q)`. So `[z,q]` meets `C(t)` (S1).
- Chains are vertex-disjoint, so by G4 the meeting points of distinct chains are `≥ √3/2`
  apart.
- Hence `|I_ν| ≤ 1 + |z − q|/(√3/2) ≤ M`.
- Integrating over `ν`: `Σ_t |Γ_{C(t)}| = ∫_{S¹} |I_ν| dν ≤ 2πM`. ∎

**Lemma F′ (fatness).** If `int K ≠ ∅` (and `Δ ≤ 1.94Δ₂`), then `diam K ≤ 600·r*`.

*Proof.*
1. Lemma F of angle_R6 §5.2 (elementary: chord inequality at the two ends of a minimal-width
   chord) gives `diam K ≤ 100·w₀`, where `w₀` is the minimal width.
2. Let `p, q ∈ K` with `|pq| = D = diam K`.
3. The width across `pq` is `≥ w₀`, so some `s ∈ K` is at distance `≥ w₀/2` from the line `pq`.
4. The triangle `pqs ⊂ K` has all sides `≤ D` and area `≥ Dw₀/4`, so all its heights are
   `≥ w₀/2`.
5. The centroid is at distance `height/3 ≥ w₀/6` from each side, so `depth(centroid) ≥ w₀/6`.
   (`D(g,ϱ) ⊂ K` implies `|g − w| + ϱ ≤ Δ₂` for each `w`.) ∎

### 3.3 Assembly

- **Case `int K = ∅`.** Then `|K| ≤ 1`, so `|A| ≤ 1`.
- **Case `r* < h`.**
  - `diam K ≤ 600r* < 600h`.
  - `A ⊂ K` is 1-separated, so `|A| ≤ (2·diam K + 2)² < (1200h + 2)²` (packing, as
    `card_le_sq_diam`).
  - `Def ≥ 0` then gives `Def ≥ 2|A| − 2(1200h + 2)²`.
- **Case `r* ≥ h`.**
  1. Integrate (3.1) over `φ`, choosing the normals of Lemma G. Substitute `φ → −φ` in the second
     sum; each `m_{ν}` is at most `m̂`. This gives

     `∫|M₁| ≤ (3/π)[2 Σ_a ∫_{J_a} m̂_a + 4π²M].`

  2. With (1.2) and (★):

     `(2π/3)·Def ≥ Σ_a (|E_a ∪ −E_a| − (6/π)∫_{J_a} m̂_a) − 12πM ≥ (4π/3)|A| − 12πM`,

     that is,

     **`Def(H) ≥ 2|A| − 18M ≥ 2|A| − 18 − 12471·h`** (by Lemma F′, `(h/r*)·diam K ≤ 600h`).

Both cases give `Def(H) ≥ 2|A| − 2(1200h + 2)²`. ∎

**Remarks.**
- **Measurability.** Every function of `φ` above is a finite sum of indicators of finite unions
  of arcs, times continuous functions. The repo's `dirMeasure` / `sum_dirMeasure_le` handle
  exactly such integrals.
- **Sharpness.**
  - The single unit ring has `Def = 2|A|`.
  - In the ring, Lemma 7 is tight for the two side chains, `(G5)` has multiplicity 1, and
    `∫|M₁| = 4π` equals the local slack.
  - The loss `18M` is an artefact of the counting, not of the ring.

## 4. Adversarial tests

**Exact tests (`l97A_local_exact.py`, Fractions, angles in rational degrees).** `3 20000` checks
Lemma 5, Lemma 6 and (★) on 20 679 A-point configurations:
- `d = 0..3`, pairwise separations `≥ 60°`;
- normal cones of width `0°..89°`, with every neighbour strictly behind every normal;
- 3° grid plus random rational angles.

All pass. Minimum slack in (★): `0.0166π`. Runtime about 25 s.

**Float sanity tests (`l97A_check.py` with `l97A_configs.py`; tolerance `1e-7`).**

Assertions per configuration:
- (I) the identity `Def = (3/2π)Σ|E_v|`;
- (Pa) the per-A-point inequality `cost_a ≤ s_a`, computed by quadrature with the sup over the
  actual normal cone;
- (C3) Lemma 2 at every sampled `φ`;
- (Cap) for every A-to-A chain: the core is strictly on one side, the cap normals form **one**
  arc, its ends are support normals of `b` and `t`, and Lemma 7 holds;
- (Sep) every chain whose cap contains `ν` meets `[z(ν), q(z(ν))]`, and the count obeys the
  `1 + |z − q|/(√3/2)` bound;
- (Sum) `Σ∠ ≤ 2π·mult`, and the sharp integrated form
  `Def ≥ 2|A| + (3/2π)Σ(s_a − cost_a) − (9/2π²)∫Σ_t∠_t`.

Configurations (45 in the full run, log `scratchpad/l97A_full.log`; all pass):

| family | details | Def − 2A | loss term `(9/2π²)∫Σ∠` |
|---|---|---|---|
| ring24, ring60 | unit-chord rings (tight) | 0 | 6.0 (exact value `18/π·π/3·…`; sampled) |
| ringpath60_k | rings cut into A-paths | 15, 30 | ≤ 3 |
| Mpair (R = 50) | angle_R6 M pair-gap row, 24 chords + apex row | 14 | 0.23 |
| L1..L4 (R = 50) | angle_R6 L family, 4 periods | 7..15 | ≤ 0.23 |
| eis1729 ρ=2,3; eis53599 ρ=2 | Eisenstein lattice annuli, 48/96 lattice points exactly on ∂K, up to 3426 vertices | 462..3006 | ≤ 6.7 |
| reul/lens/pent × 6 seeds | random unit-distance growth, A-points incl. corners | ≥ 99 | ≤ 1.2 |
| reulT/lensT × 6, discT | exact unit A–A chords (A-paths), dense growth, corners | ≥ 68 | ≤ 4.1 |

The largest observed cap multiplicity was 3 (Eisenstein, ρ = 3). No assertion ever failed.

**On the L and M obstructions.**
- These kill *first-layer* ledgers, which charge each A-point locally.
- Here the charge of an A-point depends on whether its steep chain in direction `φ` ends at
  another A-point. That is decided globally.
- The L and M configurations satisfy every step (table), with `Def − 2|A| ≥ 7`.

**What is not machine-tested exactly.** Lemma G (sides, cap arc, separation) involves irrational
geometry (circular arcs). It is checked only in floats. Its proof is written out in §3.2 and uses
only convexity, the IVT, and the monotone support-point parametrisation.

## 5. Lean DAG and line estimate

Route A needs **no plane topology**. The ingredients are:
- finite combinatorics;
- trigonometry on `S¹`;
- integrals over `S¹` (the repo's `dirMeasure` / `sum_dirMeasure_le` / `le_dirMeasure_of_Icc`,
  plus `intervalIntegral` for the ramps);
- convexity of `KBall X` (`normalCone`, `dirVec`, `ang` already exist in `E132MainDefs`);
- the IVT (`intermediate_value_Icc`);
- compactness (support points, minimal width).

```
Dir ──► Chain ──┐
Local ──────────┼──► Core (assembly, integrals) ──► CoreE (with new Eh)
Sides ─► Support ─► Cap ─┘        ▲
Fat ──────────────────────────────┘
```

| node (file) | content | Mathlib / repo infrastructure | est. lines |
|---|---|---|---|
| `Main97Dir` | cones `C(φ)`; Lemma 1 (angle ≥ π/3 between unit neighbours; cf. `card_partners_minDist_le`); `E_v`; `dirMeasure(E_v) = 2π − deg·π/3` (disjoint open arcs); `∫N = (2π/3)Def` | `dirMeasure`, `volume` on `AddCircle`/`Icc 0 2π`, measure of disjoint unions | 300 |
| `Main97Chain` | up/down neighbours; `top` by iteration (`⟨·,φ⟩` strictly increasing, bounded by `|V|` steps); `bottom`; Lemma 2 as a `Finset.card` inequality (fibres of size ≤ 2) | `Finset.card_le_card_of_…`, `Function.iterate` | 350 |
| `Main97Local` | support normals of `KBall`; strict separation (parallelogram); `deg ≤ 3`; outer gap `s_a`; Lemma 5 (two antipodal arcs); Lemma 6 (two ramps, sup over the normal cone, exact piecewise-linear integrals); (★) | `Real.Angle` or explicit angle arithmetic; `intervalIntegral` of piecewise-linear functions | 900–1200 |
| `Main97Sides` | Lemma 7 (triangle inequality on `S¹`); chain as graph `x = c(y)`; horizontal chords `l, r`; S0; side function; S1 (IVT on segments); S2 (convex core on one side) | `intermediate_value_Icc`, `Convex.segment_subset` | 500 |
| `Main97Support` | support point `z(ν)`: existence (compactness), uniqueness (strict convexity), continuity; left and right boundary parametrisation, monotonicity of heights | `IsCompact.exists_isMaxOn`, sequential continuity from uniqueness | 450 |
| `Main97Cap` | G3 (cap arc with endpoints in `N(t)`, `N(b)`; case analysis left/right ends); G4 (P1 non-crossing + `√3/2` segment distance); G5 (points `√3/2`-separated on a segment; `sum_dirMeasure_le`) | repo `le_dirMeasure_of_Icc`, `sum_dirMeasure_le` | 800 |
| `Main97Fat` | Lemma F (minimal width by compactness of `S¹`; the 9 elementary steps); triangle-centroid inradius; concavity of depth, `q(z) ∈ K′`; `r* ≥ diam K/600` | `IsCompact.exists_isMinOn`, `ConvexOn`/`ConcaveOn` for `min` of concave functions | 700 |
| `Main97Core` | assembly: integrate the pointwise inequalities over `φ ∈ [0, 2π]` (finite sums of indicators of arc unions × continuous ramps); both cases; packing via `card_le_sq_diam` | `intervalIntegral.integral_finset_sum`, `integral_mono`, measurability of arcs | 600 |

**Total ≈ 4 600–5 000 lines**, with no new axioms, compared with Route B (≥ 10 k lines for
Euler/Jordan/winding numbers). Hardest nodes: `Main97Local` (angle bookkeeping) and `Main97Cap`
(case analysis of G3).

Cheaper variants:
1. Replace support-point continuity by the explicit structure of `∂K` (finitely many circular
   arcs). This is probably not shorter.
2. Replace the ramp integrals by the cruder pointwise bound `m̂ ≤ π/3` on `J_a`. This **fails**:
   it needs `|J_a| ≤ s_a·…`, which is false (ring points).
3. Replace Lemma F by the kite bound of angle_R6 Step 3. This is not shorter.

**Required change to the Lean statement.** `CoreE` is proved as stated **after** changing
`Eh h := 3 * 10^6 * h^2`. Then in `eprime_arith`:
- `Eh(h) ≤ 1.2·10⁷ n^{2/3}` (using `h < 2n^{1/3}`);
- so `CE := 2·10⁷` suffices;
- `C97 = 10¹¹` still satisfies `3/7·CE ≤ C97/2`.

Alternatively state `CoreE` without the hypotheses `h < Δ₂/200` and `|A| > 1000h`, which Theorem A
does not need.

## 6. Open points / flags

1. **Not refereed.** The steps most in need of a hostile check are:
   - Lemma 6: the claim that the ramp's inner end is `ν`-independent, so the sup over the normal
     cone is attained at an extreme normal;
   - (G3): the case analysis of left/right ends and the attached regions above/below the strip;
   - (S0): the degenerate horizontal chord.
2. **Constants.** They are generous: the fatness constant 600 and the `√3/2` packing on a
   segment.
   - The main case has error `18 + 12471h`, i.e. **linear in h**.
   - The quadratic `E_A(h) = 2(1200h + 2)²` comes only from the trivial case `r* < h`. With the
     perimeter bound `|A| ≤ 4·diam K + 1` it becomes linear too: `E = 12471h + 18` overall.
     That perimeter bound needs a polygon-perimeter lemma, which is not in the repo.
   - Either way the result is `O(h²)`, as `CoreE` requires, once `Eh` is enlarged (§5).
3. **Scope.** Theorem A needs only `Y ⊆ K`, `A ⊆ Y ∩ ∂K` and minimum distance 1. Fatness (Lemma F)
   needs `Δ ≤ 1.94Δ₂`. So Route A also re-proves Theorem E′ for every `Y ⊂ X ∩ K`, with error
   `O(h)` in the core step instead of `O(h²)`.
4. **Downstream (for the paper, not needed for Lean).** With `E = O(h)`, the shell optimisation
   in E′ Step 0 changes. The error is `O(h) + O(n/ρ₀)`, optimised at `ρ₀ ≈ √n`. That is only
   useful if `Δ₂/400 ≥ √n`; otherwise the `Δ₂/400` cap binds. So the rate stays `O(n^{2/3})`
   in general. This point is not examined further.
5. **Compute used.** Single process, under 3 GB; float checks about 2 min; exact checks about
   25 s. No Lean compiles.
