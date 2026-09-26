import Erdos.E132Main97AArcs

/-!
# Erdős #132, `CoreE` by the visible path (Route A) — A2: the abstract certificate

`L97_reports/RouteA_visiblepath_report.md` §2 Steps 5–7 (per-vertex bounds, summation (MI)) and the
assembly `m ≥ n + J ≥ |A| − c`, with the referee's fixes (`L97_reports/REF_core_report.md` §2):

* **G1** (a vertex can be a corner twice, the "dip"): corners are counted as **occurrences** — the
  certificate carries a `List Occ`, several entries may have the same point, and the wedges of
  different occurrences of one point are disjoint (`VPCert.disj`).
* the A-point claims of Step 6 are the fields `half_free`, `inner_disj`, `end_ovl`.

This file is purely combinatorial/angular: a `VPCert V A` packages everything the geometry has to
deliver, and `defc_ge_of_cert` turns it into `Def(G[V]) ≥ 2|A ∩ V| − 3 − (3/2π)cα − cCL`.
The geometric construction of a certificate is `cert_of_visPath` (E132Main97AAssembly).
-/

open Finset Real
open Erdos132Convex (Pt pairDist pairsS multS distSetS)
open scoped Classical

namespace Erdos132Main

open Curve (dirMeasure)

noncomputable section

/-- A corner occurrence of the visible path: its point, the angle `θ` of its normal ray, the
relative angles `ψin, ψout ∈ [0, π]` of the incoming/outgoing path directions (measured
counter-clockwise from the ray direction `dirVec θ`), and whether one side is virtual (an end of a
hit arc). -/
structure Occ where
  pt : Pt
  θ : ℝ
  ψin : ℝ
  ψout : ℝ
  isEnd : Bool

namespace Occ

/-- Turning at the occurrence, `κ = ψout − ψin ∈ [−π, π]`. -/
def κ (o : Occ) : ℝ := o.ψout - o.ψin

/-- The wedge `W`: directions counter-clockwise from `θ + ψout` to `θ + ψin + π`; length
`π − κ`.  It is the `K′`-side of the path at the corner (report Step 4). -/
def wedge (o : Occ) : Set Pt := arcO (o.θ + o.ψout) (o.θ + o.ψin + π)

end Occ

/-- The half-circle of directions `H⁺_a` around the outer disc normal of angle `φ`. -/
def halfArc (φ : ℝ) : Set Pt := arcO (φ - π / 2) (φ + π / 2)

/-- **Visible-path certificate** for the vertex set `V` and the boundary set `A`.

`occ` are the corner occurrences at vertices of `V` (feet removed), `J` the number of escape
intervals, `n` the number of pieces; `φ a` is the angle of an outer disc normal at `a ∈ A`, `α a`
the angle between the ray direction `ν(a)` and that normal; `cCL`, `cα` are the error terms of the
counting lemma (Step 8) and of the collapse correction (Step 7). -/
structure VPCert (V A : Finset Pt) where
  occ : List Occ
  J : ℕ
  n : ℕ
  φ : Pt → ℝ
  α : Pt → ℝ
  cCL : ℝ
  cα : ℝ
  pt_mem : ∀ o ∈ occ, o.pt ∈ V
  ψin_mem : ∀ o ∈ occ, 0 ≤ o.ψin ∧ o.ψin ≤ π
  ψout_mem : ∀ o ∈ occ, 0 ≤ o.ψout ∧ o.ψout ≤ π
  /-- wedge lemma (Step 4): no edge of the vertex points into the wedge -/
  free : ∀ o ∈ occ, ∀ q ∈ V, dist q o.pt = 1 → q - o.pt ∉ o.wedge
  /-- G1: wedges of different occurrences of the same point are disjoint -/
  disj : occ.Pairwise (fun o o' => o.pt = o'.pt → Disjoint o.wedge o'.wedge)
  /-- chord inequality: neighbours of `a ∈ A` lie in the open inner half-plane -/
  half_free : ∀ a ∈ A, a ∈ V → ∀ q ∈ V, dist q a = 1 → q - a ∉ halfArc (φ a)
  /-- Step 6, interior A-corner: `W_a ∩ H⁺_a = ∅` -/
  inner_disj : ∀ o ∈ occ, o.pt ∈ A → o.isEnd = false → Disjoint o.wedge (halfArc (φ o.pt))
  /-- Step 6, A-endpoint: `|W_a ∩ H⁺_a| ≤ π/2 + |α_a|` -/
  end_ovl : ∀ o ∈ occ, o.pt ∈ A → o.isEnd = true →
    dirMeasure (o.wedge ∩ halfArc (φ o.pt)) ≤ π / 2 + α o.pt
  /-- at most two A-ends per escape interval -/
  card_end : (occ.filter (fun o => o.isEnd && decide (o.pt ∈ A))).length ≤ 2 * J
  /-- the collapse correction -/
  sum_α : ((occ.filter (fun o => o.isEnd && decide (o.pt ∈ A))).map (fun o => α o.pt)).sum ≤ cα
  /-- Step 3 (turning identity, feet have `κ ≥ 0`) -/
  turning : (occ.map Occ.κ).sum ≤ 2 * π - π * J
  /-- (V4) with occurrence counting -/
  count : n + J ≤ occ.length
  /-- Step 8 (CL) -/
  cl : ((A ∩ V).card : ℝ) ≤ n + J + cCL

/-- Handshake: `Def(V) = Σ_v (3 − deg_V v / 2)`.

TODO: prove.
What's missing: `defc`, `Erdos132Layer.two_mul_multS` (`2·mult V 1 = esum V 1`), `esum` is the sum
of `(nbr V 1 v).card`; push casts and `Finset.sum_sub_distrib`, `Finset.sum_div`.
Acceptance: no `sorry`.
Depends on: `Erdos132Layer.two_mul_multS`. Difficulty S. -/
theorem defc_eq_sum (V : Finset Pt) :
    defc V = ∑ v ∈ V, (3 - ((Erdos132Layer.nbr V 1 v).card : ℝ) / 2) := by
  sorry

/-- **Per-vertex bound (Steps 5–6).**  For `v ∈ V` with occurrences `O_v`:
`3 − deg v/2 ≥ Σ_{o ∈ O_v} (1 − (3/2π)κ_o) + [v ∈ A]·(1 − (3/2π) Σ_{o ∈ O_v, end} (π/2 + α_v))`.

Why true: apply `card_le_of_free_arcs` to the neighbours of `v` and the free arcs
`{W_o : o ∈ O_v}` (plus `H⁺_v` if `v ∈ A`); by `disj` the wedges are pairwise disjoint and each has
measure `≥ π − κ_o` (`le_dirMeasure_arcO`; `κ_o ∈ [−π, π]` from `ψin_mem`, `ψout_mem`); with
`H⁺_v` (measure `≥ π`) the union loses at most `Σ_o |W_o ∩ H⁺_v|`, which is `0` for non-ends
(`inner_disj`) and `≤ π/2 + α_v` for ends (`end_ovl`) (`dirMeasure_union_ge`).  Then
`3 − deg/2 ≥ (3/2π)μ − k/2`.  (REF_core §2.3: per-occurrence wedges, G1.)

TODO: prove.
What's missing: index the filtered list by `Fin` to apply the Finset lemmas; the arithmetic.
Acceptance: no `sorry`.
Depends on: `card_le_of_free_arcs`, `dirMeasure_union_ge`, `sum_dirMeasure_le_union`,
`le_dirMeasure_arcO`, `measurableSet_arcO`, the fields of `VPCert`. Difficulty M (≈ 150 lines). -/
theorem vertex_bound {V A : Finset Pt} (hV : ∀ v ∈ V, ∀ q ∈ V, v ≠ q → 1 ≤ dist v q)
    (C : VPCert V A) {v : Pt} (hv : v ∈ V) :
    ((C.occ.filter (fun o => decide (o.pt = v))).map (fun o => 1 - 3 / (2 * π) * o.κ)).sum
      + (if v ∈ A then
          1 - 3 / (2 * π) *
            ((C.occ.filter (fun o => decide (o.pt = v) && o.isEnd)).map
              (fun o => π / 2 + C.α o.pt)).sum
        else 0)
      ≤ 3 - ((Erdos132Layer.nbr V 1 v).card : ℝ) / 2 := by
  sorry

/-- **Summation (Step 7, first half).**  Summing `vertex_bound` over `V`:
`Def(V) ≥ |occ| − (3/2π)Σκ + |A ∩ V| − (3/2π)((π/2)·#ends + Σ_ends α)`.

TODO: prove.
What's missing: `defc_eq_sum`; `Σ_{v ∈ V} Σ_{o ∈ occ, o.pt = v} f o = Σ_{o ∈ occ} f o` since all
`o.pt ∈ V` (`pt_mem`; `List.sum_map_filter`-type regrouping, or convert to `Multiset`/`Finset.sum`
over `Fin occ.length` and `Finset.sum_fiberwise`); the `if v ∈ A` terms sum to `|A ∩ V|` minus the
end terms.
Acceptance: no `sorry`.
Depends on: `vertex_bound`, `defc_eq_sum`. Difficulty M (≈ 100 lines). -/
theorem defc_ge_occ {V A : Finset Pt} (hV : ∀ v ∈ V, ∀ q ∈ V, v ≠ q → 1 ≤ dist v q)
    (C : VPCert V A) :
    (C.occ.length : ℝ) - 3 / (2 * π) * (C.occ.map Occ.κ).sum + (A ∩ V).card
      - 3 / (2 * π) *
        (π / 2 * (C.occ.filter (fun o => o.isEnd && decide (o.pt ∈ A))).length
          + ((C.occ.filter (fun o => o.isEnd && decide (o.pt ∈ A))).map (fun o => C.α o.pt)).sum)
      ≤ defc V := by
  sorry

/-- **(MI) + (CL) + (V4): the certificate bound.**
`Def(G[V]) ≥ 2|A ∩ V| − 3 − (3/2π)·cα − cCL`.

Proved (assembly) from `defc_ge_occ` and the fields `turning`, `card_end`, `sum_α`, `count`, `cl`:
`(3/2π)Σκ ≤ 3 − 3J/2`, `(3/2π)(π/2)#ends ≤ 3J/2`, `|occ| ≥ n + J ≥ |A ∩ V| − cCL`.
Acceptance: no `sorry` (modulo dependencies).
Depends on: `defc_ge_occ`. Difficulty — (assembly). -/
theorem defc_ge_of_cert {V A : Finset Pt} (hV : ∀ v ∈ V, ∀ q ∈ V, v ≠ q → 1 ≤ dist v q)
    (C : VPCert V A) :
    2 * ((A ∩ V).card : ℝ) - 3 - 3 / (2 * π) * C.cα - C.cCL ≤ defc V := by
  have hπ := Real.pi_pos
  have hmain := defc_ge_occ hV C
  set E : ℕ := (C.occ.filter (fun o => o.isEnd && decide (o.pt ∈ A))).length with hE
  set Sα : ℝ := ((C.occ.filter (fun o => o.isEnd && decide (o.pt ∈ A))).map
    (fun o => C.α o.pt)).sum with hSα
  set Sκ : ℝ := (C.occ.map Occ.κ).sum with hSκ
  have hc : 0 ≤ 3 / (2 * π) := by positivity
  have h1 : 3 / (2 * π) * Sκ ≤ 3 / (2 * π) * (2 * π - π * C.J) :=
    mul_le_mul_of_nonneg_left C.turning hc
  have e1 : 3 / (2 * π) * (2 * π - π * C.J) = 3 - 3 / 2 * C.J := by
    field_simp
  have hE2 : (E : ℝ) ≤ 2 * C.J := by exact_mod_cast C.card_end
  have h2 : 3 / (2 * π) * (π / 2 * E + Sα) ≤ 3 / (2 * π) * (π / 2 * (2 * C.J) + C.cα) := by
    apply mul_le_mul_of_nonneg_left _ hc
    have := C.sum_α
    nlinarith
  have e2 : 3 / (2 * π) * (π / 2 * (2 * C.J) + C.cα) = 3 / 2 * C.J + 3 / (2 * π) * C.cα := by
    field_simp
  have hcount : ((C.n : ℝ) + C.J) ≤ C.occ.length := by exact_mod_cast C.count
  have hcl := C.cl
  linarith

end

end Erdos132Main
