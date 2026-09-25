# REF_core — hostile referee of `CoreE` and of the visible-path proof (RouteA_visiblepath_report.md)

Referee agent, 2026-09-25. Scripts: `problems/132/scripts/l97R_*.py`. Status: in progress.

## 0. Verdicts (filled at the end)

## 1. Task 1 — the reduction behind `CoreE`

Sources read: angle_R6.md §5 (lines 200–466), MAIN97_PLAN.md, E132Main97Defs.lean (`defc`, `Yset`, `Aset`,
`Yout`, `Eh`, `CoreE`), E132MainDefs.lean (`Normal`, `Sset`, `Dset`, `dist2`, `diam`, `minDist`, `KBall`).

### 1(a) |A| > 1000h ⇒ per K > 100h and r_in(K) > h — CORRECT, but the chain as written is too weak

- |A| > 1000h ≥ 1500 ≥ 2. (P7): the |A| gap arcs of ∂K between cyclically consecutive A-points each have
  length ≥ chord ≥ 1, so in fact **per K ≥ |A| > 1000h** (the paper's |A| ≤ per K + 1 is weaker than needed).
- int K ≠ ∅: two A-points a ≠ b lie in K with |a − b| ≤ Δ₂ < 2Δ₂ (neither is in D), and every disc
  D(w, Δ₂) containing a, b contains the lens of radius Δ₂ on the chord ab, which has interior. So Lemma F applies.
- Lemma F (re-checked, steps 1–9): diam K ≤ 100·w(K); Steinhagen w ≤ 3r_in; Cauchy per K ≤ π diam K. Hence
  r_in ≥ diam K/300 ≥ per K/(300π).
- **Wording error (docstring of `CoreE` and MAIN97_PLAN):** "per K > 100h … ⇒ per K/(300π) > h" is false as a
  chain: per K > 100h gives only r_in > h/(3π) ≈ 0.106h. What is true: per K ≥ |A| > 1000h > 300πh
  (300π < 942.5), so r_in > h. Replace "per K ≥ |A| − 1 > 100h" by "per K ≥ |A| > 1000h > 300πh" in the
  docstring. The mathematics is fine; the stated intermediate bound is not the one that does the work.
- Both fallbacks are excluded: (F2) needs r_in ≤ h, (F3) needs per K < 100h.

### 1(b) Given (a) and h < Δ₂/200, §5.2 Steps 2–7 prove Def(G[Yout ρ]) ≥ 2|A| − E(h) — CORRECT (as refereed)

Steps 2–7 use exactly: δ = 1 on all of X (P1, A-spacing ≥ 1, deg ≤ 6), Δ ≤ 1.94Δ₂ (Step 3 ψ_c bound, Lemma F),
h < Δ₂/200 (Step 3, Step 6 window), h ≥ 3/2 (Step 3 "per K′ > 2"), r_in > h (int K′ ≠ ∅), per K ≥ 100h (Step 3).
None uses ρ ∈ ℕ beyond h = ρ + ½, and none uses t or τ. I re-derived the arithmetic:
- case (i): Σ_{outer}(3 + |w_j|) ≥ |A|, |F₀| ≥ per K′ ≥ per K − 2πh − 21h ≥ |A| − 1 − (21 + 2π)h, total
  2|A| − (21 + 2π)h − 4 (the "−3" of Euler, the "−1" of P7);
- case (ii): 2|A| − 2[2πh + 1/200 + 21h(42h + 5)] = 2|A| − 1764h² − (210 + 4π)h − 1/100;
- tan θ*/θ* ≤ 3.26 with θ* = arcsin(194/199) > 1.343: tan θ* = 194/√1965 = 4.3764 ≤ 3.26·1.343 = 4.3782 (tight
  but true); Σ len Z_c ≤ 3.26·2πh = 20.48h ≤ 21h.
Both cases are ≥ 2|A| − E(h), E(h) = 1764h² + 223h + 4 (223 ≥ 210 + 4π = 222.57; 4 ≥ 1/100).
The topological Steps 4–6 (P2, P3, P6, Lemma W) were refereed twice in their earlier form (REF_E, REF2) and
§5.2 says the consolidated write-up "has not itself been re-refereed"; I found no error in them on this reading,
but I did not re-referee the plane topology in depth (Task 2 bypasses it).

### 1(c) Lean encodings vs paper — CORRECT

- `Yout X ρ = {y ∈ X∖D : ∃ w ∈ X, dist y w > Δ₂ − ρ}`. For y ∈ K, depth(y) = dist(y, ℝ²∖K) =
  min_{w∈X}(Δ₂ − |y − w|) (complement of an intersection is the union of complements). So
  ∃w: |y − w| > Δ₂ − ρ ⇔ min_w(Δ₂ − |y − w|) < ρ ⇔ depth y < ρ. Exact (X ≠ ∅).
- `Yset = X ∖ D ⊆ K`: a non-D point has no partner at distance Δ, so all its distances are ≤ Δ₂ (Δ₂ is the
  largest distance < Δ). Correct for `Normal` (Δ₂ ≥ 10⁴ > 0, so `dist2` is not the junk value 0).
- `Aset = S ∖ D = Y ∩ ∂K`: "⊆": a Δ₂-partner w gives |a − w| = Δ₂, so a ∈ K ∩ C(w, Δ₂) ⊆ ∂K.
  "⊇": if y ∈ Y and |y − w| < Δ₂ for all w, y ∈ int K; so y ∈ ∂K gives some w with |y − w| = Δ₂, and w ≠ y.
- `defc Z = 3|Z| − mult Z 1` = 3|V| − e(G[Z]) because `minDist X = 1`.
- `Normal` supplies δ = 1 (`minDist_eq`), Δ ≤ 1.94Δ₂ (`nondeg`), Δ₂ ≥ 10⁴, n ≥ 4. The remaining facts §5.2 uses
  are derived: int K ≠ ∅ and |A| ≥ 2 from |A| > 1000h; h ≥ 3/2 from ρ ≥ 1; h < Δ₂/200 is a hypothesis.
  "Y ⊆ X ∩ K with min distance 1" holds for Y = X ∖ D. No hypothesis of §5.2 is missing from `CoreE`.
- Note (harmless): Theorem E′ is stated for arbitrary Y ⊆ X ∩ K; `CoreE` fixes Y = X ∖ D and A = S ∖ D, which is
  the only instance used downstream.

### 1(d) Verdict on `CoreE`

**`CoreE` is TRUE as stated, given the refereed §5.2** (and independently given the visible-path proof, §2).
Gaps: none mathematical. One documentation fix: the justification "per K > 100h ⇒ r_in > h" in the `CoreE`
docstring and in MAIN97_PLAN.md must read "per K ≥ |A| > 1000h > 300πh ⇒ r_in ≥ per K/(300π) > h".

## 2. Task 2 — the visible-path proof
### 2.1 Setting and Lemma 0
### 2.2 Step 1 (N1–N6)
### 2.3 Step 2 (visible path, V1–V4, m ≥ n + J)
### 2.4 Step 3 (turning identity)
### 2.5 Step 4 (wedge lemma)
### 2.6 Steps 5–6 (per-vertex)
### 2.7 Steps 7–8 (summation, counting, assembly)
### 2.8 Degenerate cases
### 2.9 Counterexample searches
### 2.10 Verdict, fixes, formalisability

