# Erdős #132, angle R3: rare distances in convex position via few-distance stability

(2026-09-23. Continues `angle_B.md`, `angle_B2.md`, `angle_B3.md`. Coordinator plus three sub-routes: cyclotomic hit
bound (`r3_cyc_*`), Fishburn/Altman extraction (`r3_fish_*`), stability/obstruction search (`r3_os_*`).)

Notation: P ⊂ R² is strictly convex, |P| = n, m = ⌊n/2⌋, N = C(n,2), and D = D(P) is the number of distinct distances.
μ(d) is the multiplicity of d. A distance is rare if 1 ≤ μ ≤ n and frequent if μ ≥ n+1. k = #rare, F = #frequent,
D = k + F. The counting lemma (angle_B Lemma 1) gives k ≥ D − m + 1.

## 0. Summary

| # | Statement | Status |
|---|---|---|
| 1 | **Reduction to Erdős–Fishburn's f(n).** k(P) ≥ min(m, f(n)+2). So f(n) → ∞ ⇒ k → ∞. | **proved** (2 lines) |
| 2 | **Reduction to sorted multiplicities.** If r_j(P) ≤ n (the j-th largest multiplicity), then k ≥ m − j + 1. So "r₃⁽ⁿ⁾ ≤ n", an open question of Erdős–Fishburn, would give k ≥ m − 2. | **proved** (trivial) |
| 3 | **Hit Lemma (AE′ made unconditional).** A point u off the circle and ≠ centre is at an R_N-chord distance from at most 21 vertices of R_N, for every N. Beukers–Smyth gives ≤ 23. The exact max for N ≤ 120 is 13. | **proved** (§2.1) |
| 4 | **Theorem AC (almost cocircular).** If all but w points of P lie on one circle and n ≥ 3w, then k(P) ≥ min((n−3w+1)/4, m − w/2 − 20 + 20/(w+1)). So k ≥ (n−3w+1)/4 once n+w ≥ 85. | **proved** (§2) |
| 5 | Consequently B2's Theorem D is unconditional up to S1. **k → ∞ for convex sets ⇐ (COC)**: D ≤ n/2 + K ⇒ all but o(n) points on one circle. | **proved** reduction |
| 6 | Lemma U (up-chain) and a "defect Altman" inequality D ≥ m − 1 − c + s(P) | proved by sub-agent, spot-checked (§3.2) |
| 7 | Lemma PZ: if D ≤ Cn, any degree-≤ d curve without line/circle components holds O(n^{3/4}) points. Of two non-concentric circles, one holds O(n^{3/4}) points. | corollary of Pach–de Zeeuw (§4.2) |
| 8 | No far-from-cocircular family with D − n/2 bounded exists among Reuleaux subdivisions, two-orbit sets R_N ∪ ρR_N, and lattice hulls. D − n/2 grows linearly in all of them. | computational evidence (§4.1) |
| 9 | Conjecture LC: D ≥ (n+w)/2 − 2, where w = n − max #points on a circle. LC ⇒ COC with w ≤ 2K+4 ⇒ k ≥ n/4 − O(K), hence k ≥ c·n. | open; holds on every example |

**Net.** The gap for (b)-convex is now exactly a *cocircular stability* statement (COC / LC / f(n) → ∞).
Everything downstream of cocircularity is proved unconditionally, with a linear bound k ≥ n/4 − O(w). This
includes the old "extended Cap Lemma" gap (AE′), which is now closed. What is still open is "few distances ⇒
almost cocircular" for non-cocircular sets. Kneser does that job on a circle, and there is no analogue off it.

## 1. Reductions

**Prop 1.1.** For n ≥ 7: k(P) ≥ min(m, f(n) + 2). Here f(n) is the function of Erdős–Fishburn, *Intervertex
distances in convex polygons*, DAM 60 (1995), Cor. 1: the largest f such that D ≤ m + f forces all n vertices to
lie on a circle (as n vertices of a regular polygon).

*Proof.*
- If D ≤ m + f(n), then P is cocircular. For p ∈ Γ, the circle C(p, d) meets Γ in ≤ 2 points, so every distance
  graph has maximum degree ≤ 2 and ≤ n edges. Hence k = D ≥ m (Altman).
- Otherwise D ≥ m + f(n) + 1, and the counting lemma gives k ≥ f(n) + 2. ∎

Literature status of f, from the Fishburn sub-route:
- Only f ≥ 0 is known in general (Altman for odd n, Fishburn 1995 for even n).
- f(7) = 1 and f(8) = f(10) = 0. Erdős–Fishburn also give upper bounds of order n/4.
- The nonagon paper (Geom. Dedicata 60 (1996)) gives n = 9. It also introduces h(n), the cocircular-only
  threshold, with h(n) ≤ 3n/4.
- Erdős–Fishburn ask to "determine f" and suggest f(n) ~ n/4. **Nobody has proved f(n) → ∞.**
- Prop 1.1 shows that this open problem of theirs implies #132(b) for convex sets.

**Prop 1.2.** Let r_1 ≥ r_2 ≥ … be the sorted multiplicities. If r_j ≤ n, then F ≤ j − 1 and k = D − F ≥ m − j + 1.

Erdős–Fishburn (same paper, §1) state that it is not known whether r₃⁽ⁿ⁾ > n for some n. A proof that r₃ ≤ n would
give k ≥ m − 2. That route is independent of stability.

## 2. Theorem AC: almost-cocircular convex sets have linearly many rare distances

### 2.1 Hit Lemma

Let Γ be the unit circle, ζ = e^{2πi/N}, and c_j = |1 − ζ^j|. A point u "hits" ζ^a if |u − ζ^a| = c_j for some j.

**Hit Lemma.** If u ∉ Γ and u ≠ 0, then u hits at most h vertices of R_N, with h = 21, uniformly in N.

*Proof (Beukers–Smyth route, h = 23).*
1. Put w = ū and τ = |w|² − 1 ≠ 0. A hit at ζ^a with chord c_j means that (X, Y) = (ζ^a, ζ^{±j}) are torsion
   points of
   f(X,Y) = wX + w̄X⁻¹ − Y − Y⁻¹ − τ.
2. The Newton polygon of f is the diamond conv{(±1,0),(0,±1)}, of area V = 2.
3. f contains no torsion coset {(ζ₁t^p, ζ₂t^q)}. Matching the monomials t^{±p}, t^{±q}, t⁰ forces |p| = |q| = 1
   and wζ₁ = ζ₂^{±1}, hence |w| = 1, which is excluded.
4. For |w| ∉ {0,1}, f is absolutely irreducible (sympy-checked).
5. Beukers–Smyth, *Cyclotomic points on curves* (Number Theory for the Millennium I, 2002), main theorem in §4.1:
   such an f has at most 22·V(f) cyclotomic points, or infinitely many. Infinitely many is excluded by step 3.
6. So there are ≤ 44 torsion points. A non-diametral hit gives 2 of them, and a diametral hit (ζ^j = −1) gives 1.
   Hence ≤ 23 hits. ∎

The sub-agent also gave a self-contained Bernstein–Kushnirenko + Galois-conjugation argument with ≤ 40 torsion
points, i.e. h ≤ 21. Its cases are N odd and 4 | N (N ≡ 2 mod 4 reduces to N/2, since R_N = ±R_{N/2}).
This proof is recorded in the sub-agent report but was not re-derived here. **Everything below is valid with
h = 23 using only the published theorem; the constants quoted use h = 21.**

**Exact computation** (`scripts/r3_cyc_hits.py`):
- Method: every u with ≥ 2 hits is a circle–circle intersection. Candidates are scanned in floating point with
  tolerance 1e-7 (so no hit is missed), and the best ones are confirmed exactly in Q(ζ_N) by arithmetic mod Φ_N.
- Result: for N ≤ 120 the global exact maximum is **13**, at N = 60 and 120 with |u| = golden ratio. Typical
  values are 2–6.
- Floats alone give false positives for N ≥ 65, which is why the exact confirmation is needed.

### 2.2 Theorem AC

**Theorem AC.** Let P be strictly convex, |P| = n, and let Γ be a circle with C = P ∩ Γ, W = P \ C, w = |W|, n ≥ 3w.
Then

  k(P) ≥ min( (n − 3w + 1)/4 , m − w/2 − (h−1) + (h−1)/(w+1) ),  with h = 21.

*Proof.* Let q = n − w = |C| and K′ = (q − 3)/4.

**Case 1: D(C) > q/2 + K′ = (3q − 3)/4.** The counting lemma gives
k ≥ D − m + 1 > (3(n−w) − 3)/4 − n/2 + 1 = (n − 3w + 1)/4.

**Case 2: D(C) ≤ q/2 + K′.**
1. Since q > 4K′ + 2, Lemma K (angle_B2 §5.1, Kneser on R/2πZ) gives C ⊆ V(R_N) with N ≤ q + 2K′ + 1 = (3q−1)/2.
2. *The centre O of Γ is not in P when q ≥ 4.* If O were a vertex, C would lie in a closed semicircle, which
   contains ≤ N/2 + 1 ≤ (3q+3)/4 < q vertices of R_N.
3. Inside C each distance graph has maximum degree ≤ 2, hence ≤ q = n − w edges. So a frequent class whose value is
   a chord of R_N (a "chord class") needs ≥ w + 1 pairs touching W. Each such pair is either a W–C hit or a W–W pair.
4. A frequent class whose value is not an R_N chord has all its pairs touching W. Of those, ≤ 2w are W–C (each
   u ∈ W sees ≤ 2 points of Γ at a given distance), so ≥ n + 1 − 2w are W–W pairs.
5. The hits number ≤ hw in total (Hit Lemma, using u ≠ O), and the W–W pairs number ≤ C(w,2). Therefore
   (w+1)·F_ch + (n+1−2w)·F_nc ≤ hw + C(w,2).
6. Since n + 1 − 2w ≥ w + 1, this gives F ≤ (hw + C(w,2))/(w+1) = w/2 + (h−1) − (h−1)/(w+1).
7. Altman gives D ≥ m, so k = D − F ≥ m − w/2 − (h−1) + (h−1)/(w+1). ∎

**Corollaries.**
- w = O(1) gives k ≥ n/4 − O(1). w = o(n) gives k ≥ (1/4 − o(1))n.
- *B2 Theorem D is unconditional modulo S1 alone*, since AE′ is no longer needed. S1(c) ⇒ k ≥ n/4 − O(c), which is
  far more than k ≥ 3.
- **(COC) ⇒ k → ∞ (indeed k ≥ cn).** Proof: if k ≤ K then D ≤ m + K − 1, then COC gives w = o(n), then Theorem AC
  gives k ≥ n/4 − o(n). This is a contradiction for large n.

**Sanity check.** `scripts/r3_almostcoc_check.py` is floating point only. It adds up to 3 adversarial off-circle
points (circle intersections that maximise hits) to R_N minus holes, N ≤ 60. Slack against the bound was ≥ 24 in
every case.

The bottleneck of Theorem AC is the Kneser threshold, which costs the 3w/4 and the factor 1/4 instead of 1/2. A
Freiman-type 3k−4 statement on T would sharpen it.

## 3. Altman / Fishburn: what a stability proof must do (Fishburn sub-route)

### 3.1 Architecture and break point

- Altman's argument (Lemmas L2/L3 in Fishburn's account; cf. angle_B2 §7) and Fishburn 1995's even-n
  classification are *equality counting*. The pyramid of chords on one side of a diameter has strictly increasing
  row minima (Altman's Lemma 1). D = n/2 then forces every row to be a single value, and constant rows 1–2 force
  a regular arc.
- With slack K, the argument gives no localisation of the ≤ K "extra" values. They can be spread over all rows.
- On a circle, Kneser does the localisation (Lemma K). Off a circle there is no Kneser/Freiman analogue for chord
  lengths.
- **This is the precise break point.**
- The pyramid enumeration (angle_B2 §6) confirms that the ordinal content alone does not localise. Checked
  refutations here: Lemma 1 on the whole polygon without a diameter; monotonicity of row maxima; "chord > larger
  child" (`r3_os_lemmas.py`).

### 3.2 Lemma U (up-chain) and a defect Altman inequality

These were proved by the sub-agent. They were checked numerically (`scripts/r3_fish_upchain.py`, floats) and not
independently re-proved here.

**Lemma U.** Let [a, b] be a run of consecutive vertices with b − a ≤ n − 3 whose exterior angles sum to ≤ π.
Then max(|p_{a−1}p_b|, |p_a p_{b+1}|) > |p_a p_b|.

*Proof idea.* The interior angles θ_a, θ_b of the quadrilateral p_{a−1}p_a p_b p_{b+1} satisfy θ_a + θ_b ≥ π. So one
of them is ≥ π/2, and the opposite side of the corresponding triangle is longer than |p_ap_b|.

**Consequence.** D ≥ τ(c) + #{distinct distances ≤ |c|} for a chord c, where τ(c) is the length of an up-chain
from c. Suppose every run with angle sum > π has ≥ m + 1 − c vertices. Then

  D ≥ m − 1 − c + s(P),  where s(P) = #distinct side lengths.

This is tight on R_n and R_{n+1} − 1.

**Remaining gaps.**
- (G1) Show D ≤ m + K ⇒ c = O(K).
- (G2) Show that "rank windows" (each row confined to few values) force cocircularity.

### 3.3 Literature correction

The subdivided Reuleaux pentagon (n = 10, D = 6), listed as a "new observation" in angle_B2 item 9, is already in
Erdős–Fishburn DAM 60 (1995) §2, Fig. 1, where it shows f(10) = 0.

## 4. Obstruction search (stability sub-route)

### 4.1 Families (`scripts/r3_os_families.py`, `r3_os_conc.py`, `r3_os_search.py`; outputs in scratchpad `r3/os/`)

Families tested that are far from cocircular:
- subdivided Reuleaux (2s+1)-gons with t = 2, 3, ≥ 4 points per arc;
- two rotated orbits R_N ∪ ρR_N, N = 4..40;
- convex hulls of Z² and Eisenstein lattice pieces.

In all of them **D − n/2 grows linearly in n**, and k ≈ D. The only near-tight member is the Reuleaux decagon
(D = n/2 + 1).

Targeted searches over concentric-circle configurations (n = 10..16, D = n/2 + 1, n/2 + 2) found only:
- Reuleaux-10 and Reuleaux-14;
- the two-orbit set with N = 6;
- cocircular sets.

**No obstruction to COC was found.**

### 4.2 Lemma PZ (rigorous, from Pach–de Zeeuw, arXiv 1308.0177)

Pach–de Zeeuw show that s points on an irreducible degree-d curve containing no line or circle determine
Ω_d(s^{4/3}) distances. The same holds for points on two non-concentric circles, or two non-parallel lines (their
Theorem 1.2 / Cor.). Hence:

**Lemma PZ.** If D(P) ≤ Cn, then:
- every such curve contains O_{C,d}(n^{3/4}) points of P;
- of two non-concentric circles, one contains O(n^{3/4}) points of P.

So any *algebraically structured* counterexample to COC with D = O(n) must put all but O(n^{3/4}) points on a
family of **concentric** circles. With Lemma K on each circle, each rich circle is then a subset of a regular
polygon. This is the natural next case: two concentric circles without imposed symmetry, handled by Kneser on each
circle plus the torsion-point machinery for the cross distances.

### 4.3 Other results from this sub-route

- **Lemma CP (cap pairs).** In a one-sided pyramid, a span-j chord (j ≤ r) has rank ≥ j among the values. Hence the
  end caps U_t, W_t (t+1 points each) determine ≤ 2t + e distinct bipartite distances among (t+1)² pairs.
  Status: **proved**.
- **Prop S.** Two-orbit sets have D ≥ 3⌊N/2⌋ − O(1). Status: **sketch only**; one step, general x^a y^b torsion
  cosets, is unchecked.
- **Conjecture LC.** D ≥ (n + w)/2 − 2, where w = n − (max #points of P on one circle). It holds on every example;
  Reuleaux t = 2 comes within 1/2 of it. LC ⇒ (D ≤ m+K ⇒ w ≤ 2K+4) ⇒ Theorem AC gives k ≥ n/4 − O(K), i.e. **k ≥ cn
  for convex sets**.
- **Conjecture SIDE.** D ≤ m + K ⇒ the most frequent side length occurs ≥ n − 2K − 2 times.

## 5. Gap statement

- **Proved unconditionally.** k ≥ min((n−3w+1)/4, n/2 − w/2 − O(1)) for convex sets with all but w points on a
  circle. For w = o(n) this is linear in n.
- **Missing.** A non-cocircular stability theorem: convex, D ≤ n/2 + K ⇒ all but o(n) points on one circle. Any of
  the following would close #132(b) for convex sets:
  - COC;
  - LC;
  - f(n) → ∞ (Erdős–Fishburn);
  - r₃⁽ⁿ⁾ ≤ n (Erdős–Fishburn).
- Even the first open instance, odd n with K = 1 (angle_B2 Prop B), is still open for n ≥ 15.
- **Most promising next step.** Prove Lemma K for **two concentric circles**: C₁ ∪ C₂ with D ≤ (|C₁|+|C₂|)/2 + K.
  By Lemma PZ this is the only structured case left. Then find an extremal / "rank-window" argument for (G1).
