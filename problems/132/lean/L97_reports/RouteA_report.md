# Route A report — elementary (Euler-free) approach to `CoreE` (Theorem E′, Erdős #132)

Agent: Route A research agent (2026-09-25). Scripts: `problems/132/scripts/l97A_*.py`.
Status: sections 0–4 written; §5 (Lean DAG) and §6 (flags) follow.

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
