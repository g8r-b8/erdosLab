import Erdos.E132Main97AWedge
import Erdos.E132Main97ACount

/-!
# Erdős #132, `CoreE` by the visible path (Route A) — A8: assembly

`L97_reports/RouteA_visiblepath_report.md` §2 Step 8 "Assembly", with the referee's fixes
G1–G4 (`REF_core_report.md` §2.10).  Everything here is proved from the statements of the other
`E132Main97A*` files:

* `cert_of_visPath`: a valid visible path yields a `VPCert` with `cCL = 50h`, `cα = 10 + 100h`;
* `core_Hv`: `Def(H) ≥ 2|A ∩ V(H)| − 3 − (3/2π)(10 + 100h) − 50h`;
* `coreA : CoreE`: isolated vertices of `G[Yout]` contribute `3 ≥ 2` each, Lemma 0 supplies
  `int K′ ≠ ∅`, and `8 + 100h ≤ E(h) = 3·10⁶h²`.
-/

open Finset Real
open Erdos132Convex (Pt pairDist pairsS multS distSetS)
open scoped Classical

namespace Erdos132Main

noncomputable section

variable {X : Finset Pt} {ρ : ℕ}

/-- Removing isolated vertices: `Def(Yout) = Def(H) + 3·#(isolated)` (every unit pair of `Yout` has
both ends in `Hv`).

TODO: prove.
What's missing: `mult (Yout X ρ) 1 = mult (Hv X ρ) 1` (`mult_eq_card`, the unit pairs are the same
finset), `card_sdiff`, `defc`.
Acceptance: no `sorry`.  Depends on: `mult_eq_card`, `mult_mono`. Difficulty S–M. -/
theorem defc_Yout_ge (ρ : ℕ) :
    defc (Hv X ρ) + 3 * ((Yout X ρ \ Hv X ρ).card : ℝ) ≤ defc (Yout X ρ) := by
  sorry

/-- `|A| ≤ |A ∩ Hv| + #(isolated vertices of G[Yout])` (`A ⊆ Yout` for `ρ ≥ 1`).

TODO: prove.
What's missing: `Aset_subset_Yout`, `A ⊆ (A ∩ Hv) ∪ (Yout ∖ Hv)`, `card_union_le`.
Acceptance: no `sorry`.  Depends on: `Aset_subset_Yout`. Difficulty S. -/
theorem card_A_le_split (hρ : 1 ≤ ρ) :
    ((Aset X).card : ℝ) ≤ (Aset X ∩ Hv X ρ).card + (Yout X ρ \ Hv X ρ).card := by
  sorry

/-- **The certificate from the visible path.**

Proved (assembly): the fields are `psi_mem`, `wedge_free`, `wedge_disj`, `half_free`,
`wedge_A_inner`, `wedge_A_end`, `card_end_le`, `sum_alpha_end` + `sum_alpha_le`, `turning_vOcc`,
`count_vOcc`, `cl_bound`.
Acceptance: no `sorry` (modulo dependencies).
Depends on: the lemmas above. Difficulty — (assembly). -/
theorem cert_of_visPath (hC : CoreHyp X (hh ρ)) {P : VisPath} (hP : P.Valid X (hh ρ) (Hv X ρ)) :
    ∃ C : VPCert (Hv X ρ) (Aset X), C.cCL = 50 * hh ρ ∧ C.cα = 10 + 100 * hh ρ := by
  have hα : ∀ a, 0 ≤ alphaA X (hh ρ) a := fun a => InnerProductGeometry.angle_nonneg _ _
  have hsumα : ∑ a ∈ Aset X ∩ Hv X ρ, alphaA X (hh ρ) a ≤ 10 + 100 * hh ρ :=
    (Finset.sum_le_sum_of_subset_of_nonneg inter_subset_left fun a _ _ => hα a).trans
      (sum_alpha_le hC)
  refine ⟨
    { occ := P.vOcc (Hv X ρ)
      J := P.J
      n := P.nP (Hv X ρ)
      φ := phiA X
      α := alphaA X (hh ρ)
      cCL := 50 * hh ρ
      cα := 10 + 100 * hh ρ
      pt_mem := fun o ho => of_decide_eq_true (List.mem_filter.1 ho).2
      ψin_mem := fun o ho => (P.psi_mem (List.mem_filter.1 ho).1).1
      ψout_mem := fun o ho => (P.psi_mem (List.mem_filter.1 ho).1).2
      free := fun o ho q hq hqo => wedge_free hC hP ho hq hqo
      disj := P.wedge_disj hC hP
      half_free := fun a ha _ q hq hqa => half_free hC ha hq hqa
      inner_disj := fun o ho hoA hend => wedge_A_inner hC hP ho hoA hend
      end_ovl := fun o ho hoA hend => wedge_A_end hC hP ho hoA hend
      card_end := P.card_end_le _ _
      sum_α := (P.sum_alpha_end hC hP (Aset X) (alphaA X (hh ρ)) hα).trans hsumα
      turning := P.turning_vOcc hP
      count := P.count_vOcc hP
      cl := cl_bound hC hP }, rfl, rfl⟩

/-- **Core bound for `H`** (report Step 8): `Def(H) ≥ 2|A ∩ V(H)| − 3 − (3/2π)(10 + 100h) − 50h`.

Proved (assembly): `exists_visPath`, `cert_of_visPath`, `defc_ge_of_cert`.
Acceptance: no `sorry` (modulo dependencies).
Depends on: `exists_visPath`, `cert_of_visPath`, `defc_ge_of_cert`, `Hv_spec`.
Difficulty — (assembly). -/
theorem core_Hv (hC : CoreHyp X (hh ρ)) (hV : (Hv X ρ).Nonempty) :
    2 * ((Aset X ∩ Hv X ρ).card : ℝ) - 3 - 3 / (2 * π) * (10 + 100 * hh ρ) - 50 * hh ρ ≤
      defc (Hv X ρ) := by
  obtain ⟨P, hP⟩ := exists_visPath hC hV
  obtain ⟨C, hCL, hCα⟩ := cert_of_visPath hC hP
  have h := defc_ge_of_cert (Hv_spec hC.normal ρ).2.2 C
  rw [hCL, hCα] at h
  exact h

/-- **`CoreE`, by the visible path** (Route A; `L97_reports/RouteA_visiblepath_report.md`,
refereed CORRECT WITH GAPS in `REF_core_report.md` §2, gaps G1–G4 built into the statements).

Proved (assembly): Lemma 0 (`exists_deep`) gives `CoreHyp`; if `H = ∅` then
`Def(Yout) = 3|Yout| ≥ 3|A|`; otherwise `core_Hv`, `defc_Yout_ge`, `card_A_le_split`, and
`3 + (3/2π)(10 + 100h) + 50h ≤ 8 + 100h ≤ 3·10⁶h²` (`π > 3`, `h ≥ 3/2`).
Acceptance: no `sorry` (modulo dependencies).
Depends on: `exists_deep`, `core_Hv`, `defc_Yout_ge`, `card_A_le_split`, `defc_nonneg`, `Hv_spec`.
Difficulty — (assembly). -/
theorem coreA : CoreE := by
  intro X ρ hX hρ hh200 hA
  have hρ1 : (1 : ℝ) ≤ ρ := by exact_mod_cast hρ
  have hge : (3 : ℝ) / 2 ≤ hh ρ := by unfold hh; linarith
  have hA' : 1000 * hh ρ < (Aset X).card := hA
  have hC : CoreHyp X (hh ρ) := ⟨hX, hge, hh200, exists_deep hX hge hA'⟩
  have hY := defc_Yout_ge (X := X) ρ
  have hsplit := card_A_le_split (X := X) hρ
  have hE : 8 + 100 * hh ρ ≤ Eh (hh ρ) := by unfold Eh; nlinarith
  have hπ := Real.pi_gt_three
  have hπ0 := Real.pi_pos
  have hc : 3 / (2 * π) * (10 + 100 * hh ρ) ≤ (10 + 100 * hh ρ) / 2 := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  show 2 * ((Aset X).card : ℝ) - Eh (hh ρ) ≤ defc (Yout X ρ)
  by_cases hV : (Hv X ρ).Nonempty
  · have hcore := core_Hv hC hV
    linarith
  · have hV0 : Hv X ρ = ∅ := Finset.not_nonempty_iff_eq_empty.1 hV
    have h0 : (Aset X ∩ Hv X ρ).card = 0 := by rw [hV0, inter_empty, card_empty]
    have hnn := defc_nonneg hX.minDist_eq (Hv_spec hX ρ).2.1
    rw [h0] at hsplit
    push_cast at hsplit
    linarith

end

end Erdos132Main
