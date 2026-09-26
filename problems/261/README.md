# Erdős Problem #261

Statement (site): (i) infinitely many n with n/2^n = Σ_{i≤t} a_i/2^{a_i}, t ≥ 2, distinct a_i (solved; Cusick,
Borwein–Loring). (ii) Does every n have this property? (OPEN; TUZ20 verified n ≤ 10^4.) (iii) Is there a rational x
with 2^ℵ0 representations x = Σ_{a∈A} a/2^a, A infinite? (OPEN.)

## Window reduction (proved 2026-09-25)
s_a = 2^a·(x − Σ_{b∈A,b<a} b/2^b) ∈ [0, 2a+2]; include a needs s ≥ a, exclude needs s ≤ a+2.
Integer s: every live branch follows one deterministic orbit.
- (iii), dyadic x: v_a = distance of s_a to centre a+1, v_{a+1} = |a − 2v_a|; each v = 0 doubles the live branches;
  none die ⇒ #inf non-cofinite reps = 2^{#zeros}. x = 1: v_1 = 0, 17 zeros up to 10^12 (v_zeros_to_1e12.txt).
- (ii): all a_i > n (n ≥ 3), start a = n+1, s = 2n. Signed d = s − (a+1): d' = 2d − a·sgn(d) (|d| > 1);
  d = 1 → d' = 2 − a; d = 0 → mirror pair (±a). n has the property ⇔ orbit hits d = −1, or hits 0 and later |d| = 1.

## Results
- (ii) holds for all 2 ≤ n ≤ 10^6 (part_ii_sweep_1e6.txt, scripts/ii.c); worst n = 734946 (7,431,262 levels);
  mean ≈ 2n levels. Checks: orbit = brute force for n < 400 (ii_check.py); exact rational rebuild of A for 11 n up
  to 100003 (ii_rebuild.py); independent live-state simulation for n = 3817, 734946 (ii_s.py).
- (iii) weak variant (2 reps): Lean proof Erdos/Erdos/E261.lean; public repo g8r-b8/erdos261-lean;
  FC PR #6605 (duplicates the earlier LLM-audit issue #6538, x = 3/2).
- TUZ20 DOES treat infinite reps (Cor 2.6: infinitely many rationals with ≥3; abstract: a set with ≥9). 2^k reps for
  any finite k are easy via disjoint Borwein–Loring diamonds inside a cofinite set.

## Prior art found 2026-09-26
- TUZ20 Conjecture 3.7 (every solution has a_k ≤ 2(n+k)) is FALSE — but already refuted: KunHcz, Justin Sun Prize
  PR TheJustinSunPrize/awards#85 (16 Sep 2026; n=2, k=185, a_k=392, Lean). Our DP found the identical witness
  (scratchpad cex_search.py: n=2..18 all end at a_k=392). NOT new. TUZ20 Cor 3.6 already gives a 191-term one.
- JSP-000226 (= #261) submissions: #60 (BL family), #85 (above), #268 (Lean, n ≤ 10^4 = TUZ Thm 3.5), #3482
  (Lean registration). None beyond 10^4 ⇒ our n ≤ 10^6 sweep appears new. JSP now only accepts complete solutions.
