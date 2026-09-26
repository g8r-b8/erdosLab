import Erdos.E132Main97AAssembly

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

TODO: none here — `core := coreA` (visible-path proof, Route A; `E132Main97A*.lean`).  The
remaining `sorry`s are the A-lemmas (see MAIN97_PLAN.md, "Visible-path DAG").
Acceptance: inherits the A-files.
Depends on: `coreA`. -/
theorem core : CoreE := coreA

end Erdos132Main
