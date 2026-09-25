# Region II branch report (paper v3): extend Theorem 1(b) to √3/2+3β ≤ τ ≤ 1

**What was drafted.** `paper_v3_regionII_fragment.tex`, a new `\section{...}\label{sec:II}` to go right after §sec:P4.
- New Theorem 1(b) (`thm:IIone`): 21n/16 + C₁ whenever τ ≤ √3/2 − 1/50 or τ ≥ √3/2 + 3/100. C₁ = 2·10³² is unchanged; the Region II part contributes < 2.5·10²⁵. Only Region III remains at 4/3.
- `lem:IIlp`: the linear combination with e(S) ≤ s + ½p + C.
- §sec:IIe (`thm:IIe`: e(S) ≤ s + ½p + C_bad + 87), via `lem:IIrung` (L0), `lem:IIZ`, `lem:IIord`, gaps, `lem:IIarc`, `lem:IIdisj`, `thm:IIBC`, `lem:IIcons`, and the proof of Theorem II.
- §sec:IIw (`thm:IIw`: Σv ≤ 7r + 1.3·10²⁶), via `lem:IIS`, `lem:IIclass`, rules, `lem:IIrecv`, `lem:IIloads`.
- A neutral status paragraph, two remarks, and a list of scripts.
- A header comment lists the edits needed elsewhere, which I did NOT make: intro item (b), abstract, the intro status paragraph, rem:bottleneck(b), rem:N3(b), the first sentence of sec:P4, and app:verification.
- Compile test: the fragment was pasted into a scratch copy of paper.tex before §sec:layers. pdflatex runs with no errors and no undefined references. All labels used either exist in paper.tex or are defined in the fragment.

**Page estimate.** The section runs from p. 38 to p. 46 of the compiled test, about 8.5 pages. It could shrink to about 6 by cutting rem:IIsharp, rem:IIw and the script list.

**Q′.** B2 defines Q′ as "all points of S of Δ₂-degree exactly 1". That is exactly the paper's Q, so |Q′| = p. lem:VSQ applies as stated (μ(Δ₂) ≤ 3s/2 − p/2, no C_V). With 5/8 and 3/8: s-coefficient 21/16, p-coefficient −1/8, r-coefficient 21/16. Checked exactly by hand and by r7_A2_constants.py / r7_refB_margins.py.

**Fixes applied.**
- A2 (referee of B2):
  - F1: the different-Z/same-centre case of arc disjointness now uses 2φ < α₁. I made this exact: sin φ_τ = σ/Δ < 1/(2Δ) because σ < ½ (lem:IIrung(b), lem:IIdisj).
  - F2: a shared endpoint v_B = v_A′ means B = A′, i.e. consecutive gaps (proof of thm:IIe).
  - F3: ORD rungs are monotone radius-graphs, and IVT gives a crossing (lem:IIord). I added the collinear case, which the sources omit.
  - F4: constants 6 and 24, and 2U ≤ p + 34 (lem:IIcons, thm:IIe).
  - F5 (shadow lemma, optional, not second-refereed): not used; mentioned only in rem:IIsharp(b).
  - The B2 flag on Lemma Z at end vertices: the induction never starts at an end vertex other than z; I put a sentence in lem:IIZ.
- REF_B:
  - F1: the direct m ≤ 3 argument (≤ 1 D-neighbour since c ≥ t − 3δ₀/2 > cos 26.38°; ≤ 2 K-neighbours) replaces the fan lemmas (lem:IIS).
  - F2: the simplified m_a ≤ 1 argument (y is a third neighbour of a within 35.98°) (lem:IIrecv(b)).
  - F3: the ψ_K ≈ 90° case occurs for every t, and the F2 argument covers it (sentence in lem:IIrecv(b)).
  - F4: frames. All good′ points involved are within distance 4 ≤ ρ − 1, so (G5) applies. Only directions need a common frame; m and v are frame-free (lem:IIloads).
  - F5: R∩D points never receive (proof of thm:IIw).
  - F6: the referee's own scripts pass (see below).
  - REF_B §0: the reused inputs (sec:structR, lem:frame(G5), lem:DN, lem:fewbad2, lem:flatmodel, and the consequences stated after tab:margins) have no τ-hypothesis in their proofs. I say this explicitly. lem:S3, lem:classP4, lem:recv2, lem:cone, lem:Th and lem:loads are not used.

**Deviations from the sources, and simplifications (not errors).**
- (i) B/REF_B allow "R-points on ∂K" and h = 0. In the paper R∖D ⊆ int K (sec:structR(b)), so h > 0 and that label is vacuous. I dropped it.
- (ii) Pinning (flatmodel(c)) is not used, only H ≥ t − δ₀/2.
- (iii) In the deg-6 case I use the exact fact "c > h ⇒ D-neighbour", so no δ₀ enters the h ≥ ½ step.
- (iv) All angular and depth constants in the fragment were recomputed with mpmath at 40 digits, not transcribed from B: 26.38°, [84.02°, 90.006°], 30.012°, 0.86597, 1.10413, 30.02°, 35.98°, 1.7318, 1.7319, 0.0201, 0.99999, 6.28, 12.57, 0.4441, 0.89602. Several are slightly sharper than B's M-constants; r7_B_margins.py checks B's (more conservative) versions. The ad-hoc check was not saved as a script. A small `r7_II_constants.py` would close this.
- (v) I do not use B2's "C_BC" in the bound on U. The U-bound is 2U ≤ p + 34 directly, and BC contributes only its own +70 + C_bad.

**Steps I could not reconstruct / errors found.** No mathematical error found beyond those the referees already fixed. Every step of both proofs is written out in the fragment from paper lemmas, with no "sketch". Three points deserve a second look:
- (1) lem:IIarc(b) cites lem:rigid "verbatim". Its proof uses only γ_AB ⊆ ∂K, w_{v_A} = w and v_B ∈ X, which I checked.
- (2) The counterclockwise sense of K-row right T-steps on C(w,Δ₂) is taken from lem:rigid's coordinate choice.
- (3) The status paragraph claims "one referee pass each". That is true of the sources, but the fragment's text itself (in particular the new collinear case of ORD and the exact 2φ < α₁ proof) has not been refereed.
- Script problem: `r7_B_classify.py` and `r7_B_rules.py` FAIL in problems/132/scripts (FileNotFoundError). They need `r6_below_classify_B1copy.py` and `r6_below_rule_check_B1copy.py`, which exist only in scratchpad/R7/B_weight7/. Run there, both pass.

**Script results** (`.venv/bin/python`; system python3 lacks mpmath/sympy, so only r7_B_lattice_t1.py runs there, and it passes):
- r7_A2_constants, r7_A2_configs, r7_A2_shadow: ALL PASS (2φ/α₁ < 0.8881; CONS 6, 24; LP; config A realisable with e − s = U − 1, |Q| = 2U).
- r7_B_margins: M1–M11 ALL PASS. r7_B_lattice_t1: 2·10⁴ configs, max final charge exactly 7, 0 anomalies.
- r7_B_classify / r7_B_rules (scratch copies): only A and Dtype, max v 8; 179,629 configs, max final 7.000.
- REF_B scratch scripts: refB_margins ALL PASS; refB_classify only A/D_II; refB_exact 9,506 configs, max final 7, 0 anomalies.

**Recommendation: ADOPT**, with three conditions:
- (a) copy the two helper files and the four r7_refB_*.py scripts into problems/132/scripts and list them in app:verification; (b) make the consequential edits listed in the fragment header (abstract/intro "τ > 1" → "τ ≥ √3/2 + 0.03"; the remarks that say Region II is stuck at 4/3); (c) if time allows, one quick independent read of §sec:IIe as written.

Reasons:
- Both inputs had a hostile referee pass with verdict CORRECT WITH FIXES, and no counterexample in extensive exact and float searches.
- The proofs reuse refereed paper machinery (lem:Bprime, lem:rigid, lem:cyclic, lem:corner, lem:C, the P4 flat model) and add only short new lemmas, with angular margins of ≥ 24° and depth margins of ≥ 0.6.
- Gain: Theorem 1(b) then misses only the narrow Region III band. Cost: 6–9 pages, and part (b) rests partly on single-referee material (§sec:P4 had two passes); the status paragraph says so.
- If the paper should contain only doubly refereed material, keep this as a remark or future-work note and do not adopt.
