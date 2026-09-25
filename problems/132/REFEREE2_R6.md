# Erdős #132, angle R6: second independent referee pass (REFEREE2_R6)

Date: 2026-09-25. Target: `problems/132/angle_R6.md` (commits 9508181, 8ed366d).
Method: one leaf referee for each theorem, run one after another. Each referee formed its verdict **before** reading the first-round report (REF_N3, REF_E, REF_B1) and compared afterwards. The coordinator checked every report against the source and re-ran the key scripts.
Full reports (scratchpad, not in the repo): `scratchpad/R6/REF2/{N3/REPORT.md, E/REPORT_FULL.md, B1/REPORT.md}`, with scripts `ref2_*.py` in the same directories.

| statement | verdict |
|---|---|
| **Theorem N3**: Σ_𝓡 v ≤ 8r + C, hence **L ≤ 4/3** | **CORRECT** (cosmetic issues only) |
| **Theorem E′**: Def(G[X∖D]) ≥ 2\|S∖D\| − O(n^{2/3}), all nondegenerate regimes | **CORRECT WITH GAPS**: the mathematics is correct with the fixes, but no complete corrected written proof exists |
| **τ > 1**: min{μ(Δ₂), μ(δ)} ≤ 9n/7 + O(n^{2/3}) | **CORRECT given E′**, but "sharp" is an overclaim |
| **Theorem P4**: Σ_𝓡 v ≤ 7r + C in Region I and for τ > 1, hence **21n/16 + C** | **CORRECT WITH GAPS** (all fixable, none fatal; the first referee's repairs are sound) |

No fatal error was found in any theorem. No adversarial configuration broke any claim.

---

## 1. Theorem N3 (L ≤ 4/3): CORRECT

**Checked by hand**
- The identity μ(δ) = e(S) + ½Σv.
- The LP. With weights 2/3 and 1/3:
  - μ(Δ₂) ≤ 1.5s − 0.5q;
  - μ(δ) ≤ s + q + 4r;
  - so the s-coefficient is 4/3, the q-coefficient is 0 and the r-coefficient is 4/3, giving 4n/3.
- Lemma T\*:
  - cone arc ≤ 458.4 < 464;
  - fatness margin 1.9628 > 1.94;
  - W < 21.49.
- The Lemma BT count.
- Lemmas F′ and DN, including the sharp form |ψ| < 90° + ε₀ for S-neighbours.
- **Classification is exhaustive.**
  - v ≥ 9 leaves only (6,4), (5,4) and (6,3).
  - m = 4 forces K, D, D, K at ±90° and ±30°.
  - The six (6,3) pair cases reduce to HF1, HF2 and cap.
  - Neighbours in 𝓡∩D are counted in deg and not in m, as they should be.
- **Lemma Pin.**
  - The identity (z−p)·u_p = −t + (d²−t²)/(2R) is correct, with the correct sign.
  - The windows are fan t ∈ [0.746, 0.984] and cap t ∈ [0.441, 0.558]. They are disjoint.
- **Charging.**
  - Receivers lie in U′ ⊂ int K ⊂ 𝓡∖D.
  - Before receiving, v ≤ 7 (fan receivers) and v ≤ 6 (cap receivers). These bounds use only the owner's frame, so receivers are never heavy.
  - Owner uniqueness: |y′ − slot occupant| ≤ 0.22 by hand, and ≤ 0.100 in 50-digit sampling.
  - The HF2–HF2 case works: the two D-vertices coincide to within 0.115, and a D-point has degree ≤ 3.

**Scripts**
- `r6_n3_checks.py`: 36/36 exact assertions pass.
- `r6_n3_search.py`: 29 694 assignments, 0 unclassified. It already builds in the DN and Pin constraints, so it is sanity evidence for the enumeration only.
- `r6_n3_examples.py`: passes.
- The referee's `ref2_adversarial.py` (mpmath, 50 digits) builds exact Pin configurations, with the identity holding to 10⁻⁴⁰; the realised t lie in [0.781, 0.908] (fans) and [0.466, 0.532] (caps). All checks pass; the coordinator re-ran it.
- The ienjoymath ring has max v = 6 on 𝓡 and no heavy points. This is a weak float check.

**Dependency.** The corollary uses e(S) ≤ s + |Q| + C in Regions II and III (angle_R4 §§2–3) as a black box. That input was not re-refereed here.

**Text fixes for angle_R6.md §1–2 (cosmetic)**
1. §2: "34 exact assertions" should be **36**.
2. §1.3 Lemma H, first bullet: replace the garbled "needs c ≤ 0.05 ≥ h + t − ε" with "D at ±90° has c ≤ sin 2.81° < 0.05 but needs c ≥ h + t − ε > 0.82".
3. Lemma T\*: the packing count "28 662" is not reproducible. The correct value is ≈ 28 664 with W < 21.49 (≈ 28 677 with W = 21.5). Only "< 3·10⁴" is used.
4. The F6 list says "all within 3°". This mixes the ε₀ offset (F6, F5) with the 2.81° offset (HF). Harmless.

The first referee (REF_N3) agrees on every point.

---

## 2. Theorem E′ and the τ > 1 bound

### (a) Theorem E′: CORRECT WITH GAPS

The second referee found the same three defects as REF_E, independently, before reading it. REF_E's fixes are both needed and enough.

**However, the fixes were never written into a proof.** angle_R6 §5 says they are "all fixed". But the only full written proof, `scratchpad/R6/B_gap/GAP_report.md` §3, still contains the unfixed text. The coordinator confirmed that line 141 still reads "N ≤ 8.8t + 4" and that line 142 still asserts laminarity for all gap arcs.

| # | severity | location | issue and fix |
|---|---|---|---|
| G1 | gap-fixable | GAP §3 Step 5 | The window U_c leaves out nearby corners. Correct bound: len U_c ≤ Σ_{c′} len Z_{c′} + 2r/(r−h) ≤ 21h + 3, so **N ≤ 21h + 4**. |
| G2 | gap-fixable | GAP §3 Step 5 | "Laminar" is false for all gap arcs, because back gaps of nested components wrap around ∂K. Restrict to arcs with err > 0 (these lie in U_c), and add the fallback "per K ≤ 100h ⇒ trivial". |
| G3 | gap-fixable | GAP §3 Steps 2 and 7 | The ψ bound needs h/r ≤ 0.005, which holds only for n ≳ 10¹⁹. Add a small-n clause (2\|A\| ≤ 2n ≤ C·n^{2/3}), or take ρ₀ = min(n^{1/3}, r/400). |
| G4 | typo | GAP §3 Step 2 | Should read tan(ψ/2) ≤ 3.3·(ψ/2) ≤ 1.63ψ. The total 21h is right. |
| G5 | exposition | not written anywhere in full | The winding/degree lemma for case (ii) needs a written proof. Adopt REF_E's argument. |
| G6 | documentation | angle_R6 §5 | **Write one complete corrected proof of E′** (Steps 1–7 with G1–G5) before relying on it. |

**Verified parts**
- The shell pigeonhole.
- The Euler identity Def = 3 + 3c + Σ_f(|f| − 3).
- Case (i): K′ = ∩D(w, r − h) is convex, len Z_c ≤ 2h·tan(ψ/2), and per K′ = (1 − h/r)(per K − ΣZ).
- Case (ii): the degree-0 lift covers an interval twice.
- Lemma F, re-derived line by line.
- Uniformity. The constants depend only on diam X ≤ 1.94r. Large Δ − Δ₂ never enters, because the "t" of E′ is the shell depth (see I-1).

### (b) τ > 1 ⇒ 9n/7 + O(n^{2/3}): CORRECT given (a)

- **Reduction.** τ − t = (t² − 1)/(2Δ₂), so τ > 1 exactly when t > 1. Then dist(D, K) ≥ t > 1 (Lemma 3.1c), so Def splits exactly into a D-part and a K-part.
- **D-part.** Lemma 3.2(a), the T-edge argument and the DD-lens count use only diametral partners, so they hold on all of D (not only on S∩D). This gives Def(G[D]) ≥ 2|D| − O(1) ≥ 2|S∩D| − O(1).
- **LP.** μ(δ) = 3n − Def ≤ 3n − 2s + O(n^{2/3}), and μ(Δ₂) ≤ 1.5s. The maximum over s of min(1.5s, 3n − 2s) is 9n/7, at s = 6n/7.

**Other issues**
- **I-5 (overclaim).** The table, the §5 title and the commit messages call the τ > 1 result "sharp". The known 9/7 constructions (ienjoymath) have t < 1, which is Region I. The theorem shows that configurations with τ > 1 cannot beat 9/7. It does not show that 9/7 is attained with τ > 1. Replace "sharp" with **"matches the global lower bound 9/7"**. The coordinator agrees.
- **I-1 (notation clash).** In E′, t means the shell depth. Elsewhere in the same file t = Δ − Δ₂. Read literally, "K′ = ∩D(w, r − t)" and "≤ 21t" in §5 would be wrong. Rename the shell depth to h.
- **I-2/3.** u_p, good/bad edges and the DD count are defined only on S∩D (WRITEUP §3, §5.2) but are used on all of D. Add one sentence saying they extend.
- **I-4.** `r6_gap_consistency.py` and `ring16.py` import numpy, which the `.venv` lacks. Run them with the system python3.

**Numerics**
- Lemma F (`ref2_lemmaF.py`, 50 digits): the largest diam/width found is **8.1035**, the lens at d = 1.94r. It matches a closed form and is far below the bound 100.
- Adversarial sweep (`ref2_Eprime_adv.py`, floats, sanity only):
  - shapes: lenses, near-degenerate triangles of centres, and squares of centres;
  - r from 40 to 300, n up to about 2100;
  - result: Def − 2|A| > 0 every time, with a worst surplus of +38 in total.
- `r6_refE_parallel.py` re-run: 897 cases pass at 10⁻²⁵, max ΣZ/h = 16.7 ≤ 21. It tests Steps 1–2 only. The topological Steps 4–6 are not tested.
- ienjoymath's configurations: the K-part surplus is ≥ 0, so E′ is consistent with them.

---

## 3. Theorem P4 (21/16 in Region I and for τ > 1): CORRECT WITH GAPS

**Checked by hand**
- **No fans in Region I.**
  - β = 1/100, so Region I is τ ≤ 0.84603.
  - A fan, or a {K,D,D} point, needs t ≥ √3/2 − O(ε₀) ≈ 0.86602 when ε₀ = 10⁻⁶. The margin is ≈ 0.0199.
  - This needs the small ε₀. It would fail with N3's ε₀ = 1/50.
- **P2 is exhaustive.**
  - v ≥ 8 with m ≤ 3 leaves (6,2), (5,3) and (6,3).
  - The cases reduce to A, A′, B, C_φ, Dtype and cap.
  - Neighbours in 𝓡∩D are handled correctly.
- **Receivers.** Every receiver has m ≤ 1, from the depth table. Forwarding targets sit at depth ≥ 1.769, so they have m = 0 and there are no chains.
- **Loads.** The load is ≤ 1 in bands L, H and T, and in band Th once REF_B1's Lemma Th is used (margin ≈ 0.47).
- **LP.** (5/8)(1.5s) + (3/8)(s + 3.5r) = 21n/16.
- **ienjoymath.** v ≤ 6 on 𝓡, which is consistent.

**Issues**
1. [gap-fixable] B1 P4.3, band Th, case β. The text is muddled, though the conclusion is true. Replace it with REF_B1's Lemma Th, which the second referee re-derived and confirmed.
2. [gap-fixable] B1 P0.1, the T\* fatness step. "W ≤ 7.01 + 28R/Λ" does not give tan φ\* < 10⁻³. Use W ≤ w₀ + 2 tan(θ/2)·L instead; REF_B1's repair is correct.
3. [cosmetic] Numeric slips. All are already listed in angle_R6 §4 and none has any effect.
   - A receivers are at depth √3.
   - B receivers are at depth h_B + √3/2.
   - |β| ≤ 30° in the τ > 1 slice.
   - The operative R₀ is 2Λ/ε₀.
4. [cosmetic] B1's scripts test less than claimed. REF_B1 says the same.
5. **[correction to angle_R6 §4 and REF_B1]** "B's range includes H = √3/2" is **false**.
   - H = √3/2 means y ∈ ∂K.
   - Every point of X on ∂K is at distance Δ₂ from some w ∈ X (K is a finite intersection of disks), so it is in S, not 𝓡.
   - B1's original half-open range [t, √3/2) was right. Harmless.
6. **[correction to angle_R6 §4 and REF_B1]** "Forwarding targets may also receive directly" is **false** in the proper band H: target depth 2·depth(a) ≥ 1.769 exceeds every A, B and Dtype receiver depth. It is true only in the slice t ∈ (1, 1 + 2δ₀], and even there the load is ≤ ½ + ½ = 1. Harmless.

**Numerics**
- The referee wrote its own implementation of the discharging rules (flat model, beam-search growth; float screening only).
- It ran about 4.9·10⁵ configurations: 0 anomalies, max load 1.0, max final charge 7.0.
- REF_B1's exact cap lattice (4·10⁴ configurations, about 10⁵ heavy points) re-ran with max charge 7.0.
- **Limitation:** random growth rarely builds more than 2 heavy points. Dense multi-heavy evidence rests on the cap lattice and on the hand analysis.

---

## 4. Recommended edits to angle_R6.md (not applied here)

1. §5 and §7: write the **complete corrected proof of Theorem E′** (G1–G6), for example as `B_gap/E_prime_full.md`, and cite it. Until then, change "all fixed" to "fixes identified; corrected proof pending".
2. Results table, §5 and §7: replace "sharp" with "matches the global lower bound 9/7" (I-5).
3. §5: rename the shell depth t to h (I-1).
4. §4 "Referee corrections": remove "B's range includes H = √3/2" and qualify "forwarding targets may also receive directly" as true only for t ∈ (1, 1 + 2δ₀].
5. §1–2: the cosmetic fixes in the N3 list above (36 assertions, the Lemma H bullet, 28 664, tolerance wording).
6. §2: note that the numpy scripts need the system python3.

## 5. Bottom line

- **L ≤ 4/3 stands.** It holds conditional only on angle_R4's e(S) ≤ s + |Q| + C in Regions II and III, which was not re-refereed here.
- **21/16 in Region I and for τ > 1 stands.** Its gaps are already repaired by REF_B1.
- **9n/7 + O(n^{2/3}) for τ > 1 is correct.** It should be cited as fully proved only once a single corrected write-up of E′ exists.
