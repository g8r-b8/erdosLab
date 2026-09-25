import Erdos.E132Main97Defs

/-!
# Erdős Problem 132, Theorem E′ — the topological heart (`CoreE`)

`problems/132/angle_R6.md` §5.2, Steps 2–7 (with Lemma F, P2–P7, Lemma W).

This is the only part of the `τ > 1` theorem that needs plane topology (Euler's formula with
face walks, Jordan non-interlacing, winding numbers, arc length of `∂K`), none of which exists in
Mathlib at this toolchain (see `problems/132/lean/MAIN97_PLAN.md`, STEP 0).  Everything else is
proved from the statement `CoreE` (see `erdos132_main97_of_core`).  Routes for proving it:
A (elementary, Euler-free replacement), B (formalise the minimal polygonal topology),
C (leave `CoreE` as the one labelled open statement).
-/

open Finset Real
open Erdos132Convex (Pt pairDist pairsS multS distSetS)
open scoped Classical

namespace Erdos132Main

/-- **Theorem E′, core** (Steps 2–7 of §5.2): `Def(G[Yout ρ]) ≥ 2|A| − E(ρ + ½)` whenever
`ρ ≥ 1`, `ρ + ½ < Δ₂/200`, `|A| > 1000(ρ + ½)`.

TODO: prove (Route A or B; see MAIN97_PLAN.md and `problems/132/lean/L97_reports/`).
What's missing: plane-graph topology — Euler `V − E + F = 1 + c` with face walks (P2), the
separation bound (P3), Jordan non-interlacing (P6), the winding/degree Lemma W; and the convex
geometry of `∂K` (Lemma F via Steinhagen or a weaker elementary inradius bound, the retraction
`P : ∂K → ∂K′`, collapse arcs, (2.1)–(3.1), the window/laminarity count (6.1)).
Acceptance: no `sorry`, no new axioms.
Depends on: `Aset_subset_Yout`, `one_lt_dist_out_in`, (new topology). Difficulty XL. -/
theorem core : CoreE := by
  sorry

end Erdos132Main
