import Erdos.E132Main97Defs

/-!
# Erdős Problem 132, Theorem E′ (outer layer): `Def(G[X ∖ D]) ≥ 2|S ∖ D| − CE·n^{2/3}`

`problems/132/angle_R6.md` §5.2, Step 0 (parameters, fallback F1), Step 1 (shell removal),
Step 7 (assembly of the error terms).  The topological heart (Steps 2–7) is the hypothesis
`hcore : CoreE` (proved, or not, in `E132Main97Core.lean`).

Deviations from the paper:
* fallbacks (F2), (F3) are replaced by the single case `|A| ≤ 1000h` (perimeter-free; `CoreE`
  absorbs the implication `|A| > 1000h ⇒ r_in(K) > h ∧ per K ≥ 100h`);
* (F1) is not needed: `Normal X` has `Δ₂ ≥ 10⁴`, so `ρ₀ ≥ 1`;
* packing `n ≤ (2Δ + 2)²` (grid of cells of side `7/10`) instead of `(2Δ + 1)²`; `CE = 10⁵`.
-/

open Finset Real
open Erdos132Convex (Pt pairDist pairsS multS distSetS)
open scoped Classical

namespace Erdos132Main

noncomputable section

variable {X : Finset Pt}

/-- **Step 1 (shell removal)**: `Def(G[Y]) ≥ Def(G[Yout ρ]) − 3|Yshell ρ|`.

TODO: prove.
What's missing: no unit pair joins `Yout` and `Yin` (`one_lt_dist_out_in`), so
`e(Y) ≤ e(Yout) + e(Yin) + Σ_{y ∈ shell} deg y ≤ e(Yout) + 3|Yin| + 6|shell|`
(`mult_le_add_sum` twice; `defc_nonneg` for `Yin`; degree `≤ 6` from
`card_partners_minDist_le`), and `card_Yset_split`.
Acceptance: no `sorry`.
Depends on: `one_lt_dist_out_in`, `card_Yset_split`, `defc_nonneg`, `mult_le_add_sum`,
`card_partners_minDist_le`. Difficulty M. -/
theorem shell_removal (h1 : minDist X = 1) (ρ : ℝ) :
    defc (Yout X ρ) - 3 * (Yshell X ρ).card ≤ defc (Yset X) := by
  sorry

/-- **Step 0 (pigeonhole)**: among the `ρ₀` disjoint shells `ρ ∈ [ρ₀, 2ρ₀)` one has
`|Yshell ρ| · ρ₀ ≤ n`.

TODO: prove.
What's missing: `disjoint_Yshell`; `Σ_{ρ ∈ [ρ₀, 2ρ₀)} |Yshell ρ| ≤ |X|` (`card_biUnion`,
subsets of `X`); `exists_le_of_sum_le` / min ≤ average on `Finset.Ico ρ₀ (2ρ₀)`.
Acceptance: no `sorry`.
Depends on: `disjoint_Yshell`. Difficulty S–M. -/
theorem shell_pigeonhole (ρ₀ : ℕ) (hρ₀ : 1 ≤ ρ₀) :
    ∃ ρ : ℕ, ρ₀ ≤ ρ ∧ ρ < 2 * ρ₀ ∧ ((Yshell X ρ).card : ℝ) * ρ₀ ≤ X.card := by
  sorry

/-- **Packing**: with `δ = 1`, `n ≤ (2Δ + 2)²`.

TODO: prove.
What's missing: the grid argument of `card_lt_N0` (E132MainDefs) with a general diameter:
`X` lies in an axis-parallel square of side `Δ`; cells of side `7/10` hold `≤ 1` point each;
at most `(⌊Δ/0.7⌋ + 1)² ≤ (2Δ + 2)²` cells.  (Or reuse `card_sep_ball_le` if its bound fits.)
Acceptance: no `sorry`.
Depends on: `card_lt_N0` pattern (`floor_cell_lt`, `close_of_floor_eq`). Difficulty M. -/
theorem card_le_sq_diam (h1 : minDist X = 1) : (X.card : ℝ) ≤ (2 * diam X + 2) ^ 2 := by
  sorry

/-- **Step 7, arithmetic**: the error terms.  With `n ≥ 4`, `Δ₂ ≥ 10⁴`, `n ≤ (4Δ₂)²`,
`ρ₀ = ⌊min(n^{1/3}, Δ₂/400)⌋`, `ρ₀ ≤ ρ < 2ρ₀`, `h = ρ + ½`:
`h < Δ₂/200`, `2000 h ≤ CE n^{2/3}`, and `E(h) + 3n/ρ₀ ≤ CE n^{2/3}`.

TODO: prove.
What's missing: real arithmetic with `rpow`: `h < 2n^{1/3}`, `⌊m⌋ ≥ m/2` for `m ≥ 1`,
`3n/ρ₀ ≤ 6n^{2/3} + 2400 n/Δ₂ ≤ 6n^{2/3} + 9600 √n`, `E(h) ≤ 7506 n^{2/3}`,
`√n ≤ n^{2/3}`, `n^{1/3} ≤ n^{2/3}` (`n ≥ 1`).
Acceptance: no `sorry`.
Depends on: nothing (analysis of `Real.rpow`, `Nat.floor`). Difficulty M. -/
theorem eprime_arith {n D₂ : ℝ} {ρ₀ ρ : ℕ} (hn : 4 ≤ n) (hD : 10 ^ 4 ≤ D₂) (hnD : n ≤ (4 * D₂) ^ 2)
    (hρ₀ : ρ₀ = ⌊min (n ^ (1 / 3 : ℝ)) (D₂ / 400)⌋₊) (h₁ : ρ₀ ≤ ρ) (h₂ : ρ < 2 * ρ₀) :
    1 ≤ ρ₀ ∧ ((ρ : ℝ) + 1 / 2) < D₂ / 200 ∧ 2000 * ((ρ : ℝ) + 1 / 2) ≤ CE * n ^ (2 / 3 : ℝ) ∧
      Eh ((ρ : ℝ) + 1 / 2) + 3 * n / ρ₀ ≤ CE * n ^ (2 / 3 : ℝ) := by
  sorry

/-- **Theorem E′** (applied to `Y = X ∖ D`, §5.1 "Application"), from `CoreE`:
`Def(G[X ∖ D]) ≥ 2|S ∖ D| − CE·n^{2/3}`.

TODO: prove (wiring).
What's missing: `n ≤ (2Δ + 2)² ≤ (4Δ₂)²` (`card_le_sq_diam`, `Normal.nondeg`, `Δ₂ ≥ 10⁴`);
choose `ρ₀`, `ρ` (`shell_pigeonhole`), `eprime_arith`; case `|A| ≤ 1000h`: `defc_nonneg`;
case `|A| > 1000h`: `hcore` + `shell_removal`.
Acceptance: no `sorry` (modulo `hcore`).
Depends on: `card_le_sq_diam`, `shell_pigeonhole`, `eprime_arith`, `shell_removal`,
`defc_nonneg`. Difficulty M. -/
theorem eprime (hcore : CoreE) (hX : Normal X) :
    2 * ((Aset X).card : ℝ) - CE * (X.card : ℝ) ^ (2 / 3 : ℝ) ≤ defc (Yset X) := by
  sorry

end

end Erdos132Main
