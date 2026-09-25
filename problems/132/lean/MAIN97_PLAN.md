# Lean plan: 9n/7 + O(n^{2/3}) for τ > 1 (angle_R6 §5.2–5.3, Theorem E′ and corollary; paper v3 §12)

Target (project `Erdos`, Lean v4.35.0-rc2, Mathlib as pinned):

```lean
theorem Erdos132Main.erdos132_main97 :
    ∃ C : ℝ, ∀ X : Finset Pt, 2 ≤ X.card → minDist X < diam X - dist2 X →
      (min (mult X (dist2 X)) (mult X (minDist X)) : ℝ) ≤ 9/7 * X.card + C * (X.card : ℝ) ^ (2/3 : ℝ)
```

**τ adaptation.** `tau X = tgap X − (1 − tgap X²)/(2 dist2 X)` (E132MainDefs) is written for `δ = 1`
and is not scale invariant.  With `δ = 1`, `τ − t = (t² − 1)/(2Δ₂)`, so `τ > 1 ⇔ t > 1`
(`t = tgap = Δ − Δ₂`).  The scale-invariant hypothesis is therefore `δ < Δ − Δ₂`
(`minDist X < tgap X`).  We also give `erdos132_main97_tau` with the literal hypotheses
`minDist X = 1`, `1 < tau X`, and the equivalence lemma `one_lt_tau_iff`.

## STEP 0 — feasibility: what E′ uses, and what Mathlib has

Survey of `.lake/packages/mathlib/Mathlib` (grep, 2026-09-25):

| fact used by E′ (angle_R6 §5.2) | Mathlib | route |
|---|---|---|
| (P1) unit-distance graph is plane straight-line, deg ≤ 6 | deg ≤ 6 already in repo (`card_partners_minDist_le`); non-crossing is elementary | (a) elementary |
| (P2) Euler's formula for plane graphs with face walks | **absent** (no planar graphs, no faces, no rotation systems; `SimpleGraph` has no embedding notion; `Algebra/Homology/EulerCharacteristic` is unrelated) | core — see routes |
| (P3) compact Γ separating convex Q from ∞ has H¹(Γ) ≥ per Q | nearest-point map exists (`exists_norm_eq_iInf_of_complete_convex`, `norm_eq_iInf_iff_real_inner_le_zero`); Hausdorff measure exists; **no perimeter of convex bodies, no separation/Jordan** | core |
| (P4) perimeter monotone, per Q ≤ π diam (Cauchy) | **absent** (`ConvexBody` has no perimeter; `BoundedVariation`/`eVariationOn` could define curve length) | avoided: statement made perimeter-free |
| (P5) Steinhagen w ≤ 3 r_in | **absent** (only `Affine.Simplex.inradius`) | inside core (Lemma F); elementary weaker bound suffices |
| (P6) disjoint paths between interlaced boundary points of a disc meet (Jordan) | **absent** (no Jordan curve theorem, even polygonal) | core |
| (P7) A-points vs perimeter | needs arc length | avoided outside core |
| Lemma W: winding number / degree of P∘γ, lifting | covering maps + path lifting exist (`IsCoveringMap`, `Topology/Homotopy/Lifting.lean` `liftPath`, `monodromy_theorem`, `Topology/Covering/AddCircle.lean`); **no winding number of plane curves**, no degree theory | core |
| arc length on ∂K, retraction P, collapse arcs Z_c | absent (15/11 and 54/37 were formalised *without* arc length, via `dirMeasure`) | core |

**Verdict.** Everything in the corollary (§5.3) and the outer layer of E′ (Step 0 shells, Step 1 shell
removal, fallbacks F1–F3) is elementary and feasible with the existing infrastructure.  The heart of
E′ (Steps 2–7: core K′, retraction, collapse lengths, Euler's formula with face walks, P3, Lemma W,
P6 laminarity) needs plane-graph topology that Mathlib does not have at all.  Formalising it the
paper's way means building polygonal Jordan / Euler-with-faces / winding numbers from scratch:
estimated ≥ 10k lines, far beyond one campaign.  So the plan **isolates the topological heart as one
perimeter-free statement `core`** (below), proves everything else, and investigates `core` by routes.

## Cheapest routes for `core`

- **Route A (elementary replacement; research first).**  Exact local identity, no Euler:
  `Def(G) = Σ_v (3 − deg v / 2) = (3/2π) Σ_v Σ_gaps (θ_g − π/3) = (3/2π) ∫_{S¹} N(φ) dφ`,
  `N(φ) = #{v : no neighbour of v in the open 60° cone around φ}`; also, for every single direction
  `φ`, `Def = Σ_v (3 − up_φ(v))` with `0 ≤ 3 − up_φ(v)`.  A-points have deg ≤ 3 (neighbours in an
  open half-plane) — this gives `Def ≥ (3/2)|A|` locally; the missing `½|A|` is global (angle_R6 §5.5:
  the local gap lemma is false).  Route A looks for a global argument that uses only convexity of K,
  straight unit edges and sweeps/φ-monotone walks (discrete, finite), not faces.  If found, it is
  formalisable with the existing `dirMeasure` machinery.
- **Route B (formalise minimal topology).**  Combinatorial faces via the rotation system of the
  straight-line drawing (orbits of the face permutation on darts), Euler `V − E + F = 1 + c` by a sweep
  induction (add the lexicographically last vertex; it sees only the outer face), turning numbers of
  face walks, winding numbers via `IsCoveringMap`/`liftPath` of `ℝ → AddCircle`, then P3, P6, Lemma W
  in polygonal form.  Scoping + a compiling prototype of the first layer; honest line estimate.
- **Route C (fallback; always available).**  `core` stays a clearly labelled statement:
  `erdos132_main97_of_core : CoreE → …` is proved with no sorry, and the unconditional theorem
  inherits exactly one `sorry` (in `core`).  No axioms are added.

Children: at most **one** at a time (budget instruction from the parent).  Order: Route A research
child first; Route B only if A fails and budget remains.  Reports: `problems/132/lean/L97_reports/`.

## The perimeter-free core statement

Notation (δ = 1, `Normal X`): `D = Dset X`, `Y = X ∖ D ⊆ K` (all distances from a non-D point are
`≤ Δ₂`), `A = S ∖ D = Y ∩ ∂K`, `depth y < ρ ⇔ ∃ w ∈ X, |y − w| > Δ₂ − ρ`,
`Yout ρ = {y ∈ Y : depth y < ρ}`, `Def(Z) = 3|Z| − mult Z 1`, `h = ρ + ½`,
`E(h) = 1764h² + 223h + 4`.

```lean
theorem core (hX : Normal X) {ρ : ℕ} (hρ : 1 ≤ ρ) (hρΔ : (ρ + 1/2 : ℝ) < dist2 X / 200)
    (hA : 1000 * (ρ + 1/2 : ℝ) < (Aset X).card) :
    2 * (Aset X).card - Eh (ρ + 1/2) ≤ defc (Yout X ρ)
```

Why true (from angle_R6 §5.2): |A| > 1000h ≥ 2 gives per K ≥ |A| − 1 > 100h (P7) and, via Lemma F
(`r_in ≥ diam K/300 ≥ per K/(300π)`), r_in(K) > h; so (F2), (F3) do not apply and Steps 2–7 give
`Def(H_out) ≥ 2|A| − E(h)`.  Steps 2–7 use only `h < Δ₂/200`, `h ≥ 3/2`, r_in > h, per K ≥ 100h.

## Files and DAG

| file | contents | status target |
|---|---|---|
| `E132Main97Defs.lean` | `defc`, `Aset`, `Yout`, `Yshell`, `Yin`, `Eh`, `CE`, `C97`, basic lemmas (`Aset_subset_Yout`, depth Lipschitz) | fill |
| `E132Main97DPart.lean` | `degδ_le_three_of_D97` (own copy; Main43's is a sorry), `no_cross` (t > 1 ⇒ no δ-edge D–(X∖D)), `card_tEdges_D_le`, `dpart` (`Def(G[D]) ≥ 2|S∩D| − cBad`) | fill |
| `E132Main97Core.lean` | `core` (topological heart; Route A/B/C) | open |
| `E132Main97Eprime.lean` | `shell_pigeonhole`, `shell_removal`, `card_le_of_small`, `eprime` (`Def(G[X∖D]) ≥ 2|S∖D| − CE n^{2/3}`) | fill |
| `E132Main97.lean` | `one_lt_tau_iff`, `exists_normalize97`, `lp97`, `main97_normalized`, `erdos132_main97`, `erdos132_main97_tau`, `erdos132_main97_of_core` | fill |

```
Main15 (unchanged) ─┬─ Main97Defs ─┬─ Main97DPart ─────────────┐
MainLocal/Regions ──┘              ├─ Main97Core ── Main97Eprime ┴─ Main97
```

Reused unchanged: `exists_normalize` pattern (`diam_smul`, `dist2_smul`, `minDist_smul`, `mult_smul`),
`degenerate`, `card_lt_N0`, `VS`, `mult_minDist_le`, `card_partners_minDist_le`,
`good_subset_T_union_rungs`, `rungs_eq_empty`, `card_bad_le`, `card_good_add_bad`, `T1`,
`two_mul_card_le_of_deg_le`, `mult_le_add_sum`, `dist_le_dist2`, `gap`.

Check one file: `cd Erdos && /Users/wingatejones/Projects/erdosLab/tools/leanslot.sh lake env lean -o .lake/build/lib/lean/Erdos/<F>.olean -i .lake/build/lib/lean/Erdos/<F>.ilean Erdos/<F>.lean`
(DAG order).  Not imported from `Erdos.lean` until sorry-free.
