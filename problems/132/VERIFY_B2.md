# Erdős #132: adversarial check of angle_B2.md

Date: 2026-09-23. Hand re-derivation of every proved item, plus two exact scripts:
- `scripts/ver_classification_k.py`: exact chord-index profiles (distinct chord indices ⇒ distinct distances,
  since sin is strictly increasing on (0, π/2]).
- `scripts/ver_hexagons.py`: sympy. Strict convexity and multiplicity profiles of Fishburn's three 3-distance
  hexagons. R₇⁻ equality is tested at 80 digits because sympy cannot simplify its trig forms; the exact
  chord-index check in the first script covers R₇⁻ too.
  Run with `uv run --with sympy python ver_hexagons.py`.

## Summary

| Claim | Verdict |
|---|---|
| §1 parity-sharp counting (odd k ≥ K+1, even k ≥ K+2) | VERIFIED. Hand algebra: n = 2m, D = m+1 gives 2mk ≥ 4m+1, so k ≥ 3. Script check for n < 400. |
| Theorem A (even n ≥ 6 ⇒ k ≥ 3; n ≥ 8 and k ≤ 3 ⇒ D = m+1) | VERIFIED, modulo Altman (D ≥ m) and Fishburn 1995 (D = m classification) as black boxes. All D = m extremal sets have k = m (n ≥ 8) or k = 3 (n = 6, all three hexagons checked exactly). |
| Theorem B (convex 9-gons have k ≥ 3) | VERIFIED, modulo Erdős–Fishburn 1996 and "odd n, D = m ⇒ regular". Every 9-subset of R₁₀ and R₁₁ has D = k = 5. R₉ has D = k = 4. |
| Prop B (odd reduction, a + b + Σe = m+2) | VERIFIED. (m−1)(2m+2) + Σe + a + b = m(2m+1) gives exactly m+2. |
| C1 (no star, m ≥ 4) | VERIFIED. Case R₂ₘ ∪ {v}: the Cap Lemma lets only c_{m−1} reach 2m+2 pairs, so F ≤ 1 < m−1. Case R₂ₘ₊₁⁻ ∪ {v}: a frequent chord class needs 3 equidistant concyclic points from v, so v would be the centre. F = 0. Fishburn needs 2m ≥ 8, i.e. m ≥ 4, as stated. |
| C2 (no 2-cover, m ≥ 4) | VERIFIED. Simpler route: every chord c_j, j ≤ m−2, of the base R₂ₘ₋₁ gets at most the pair uv, so it has ≤ 2m < 2m+2 pairs and is rare. But all rare pairs meet {u, v}, which is a contradiction directly. |
| C3 (conditional on AE′(6)) | Arithmetic VERIFIED: 5(m−1) − 3 ≤ 18 ⇒ m ≤ 5.2. The condition is correctly flagged. |
| C4 (diameters near-halving) | NOT re-derived. It rests on the §7 reconstruction of Altman's Cor. (7). The deduction r ∈ {m, m+1} from D ≥ r, D = m+1 and r + r′ = 2m−1 is correct. |
| C5 (no fans) | VERIFIED given C1. A fan puts ≥ m+1 Δ-pairs at A, so a ≥ m+1 and b ≤ 1. |
| Lemma K (Kneser) | VERIFIED. \|A−A\| ≤ 2D+1 (±difference per chord value, plus 0; the antipodal value counts once). Kneser with B = −A. The case split H trivial / t ≥ 2 / t = 1 is correct, with (2t−1)N ≥ (2t−1)q/t ≥ 3q/2. t = 1 gives N ≤ \|A−A\| ≤ q + 2K′ + 1. |
| Theorem D (conditional on S1, AE′) | Steps 3–6 VERIFIED. Step 2 ("the centre is inside conv(C) for large m") is asserted without proof. It holds when C misses ≤ c+2 vertices of R_N with N ≥ 2m+1 > 2(c+2), because then no open half-circle is empty. State it. |
| §9 Reuleaux n = 10, D = 6 | Not re-checked (a numerical observation only; it does not affect any proof). |

No claim was found FALSE.

## Notes and small gaps

1. **Fishburn 1995 statement.** Theorem A uses "even n ≥ 8, D = n/2 ⇒ R_n or R_{n+1}⁻". It is quoted via CDL §2, not
   from the original. Same status as the Vesztergombi citation in REFEREE_A2: check the original before publication.
2. **Cap Lemma scope.** C1 and C2 need the Cap Lemma for a q that may lie *on* the circumcircle (a non-vertex point of
   the circle is still in strictly convex position). angle_B's exact check (a < 600) should say whether it
   included that case. For a proof for all a, angle_B's argument must cover it explicitly.
3. **Strength of the result.** Theorem A (k ≥ 3 for even convex n ≥ 6) follows in five lines from Fishburn plus the
   parity-sharp count. It is a modest but clean improvement on CDL's k ≥ 2 for convex position. Odd n ≥ 11 and
   n = 7 stay open and reduce exactly to Prop B's configuration.
4. **Novelty.** NOVELTY.md (00:14) predates angle_B2 (00:45) and angle_A2, so neither Theorem A (B2) nor the 54/37
   bound (A2) has been through the rule-4 novelty audit yet.
