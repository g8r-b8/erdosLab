# Erdős #132 — Angle D (adversarial / computational)

Code: `scratchpad/p132/angleD/` (own venv `angleD/venv`, numpy+mpmath+sympy).

- `lattice_sa.py`: simulated annealing over subsets of the triangular lattice Z[ω] (Q=a²+ab+b²) or the square lattice Z[i], exact integer squared distances. Objectives:
  `erdos` = M(X) = min over non-diameter distances of μ; `16` = min(μ(Δ₂),μ(δ)); `F` = 3μ(δ)+4μ(Δ₂)−9n; `R` = #{d : 1 ≤ μ(d) ≤ n}.
- `exhaust.py`: exhaustive search over all n-subsets of a radius-2 hexagon (19 points) and a 4×4 grid.
- `cyclo_sa.py`: the same SA over pools in Z[ζ_N] (0, ζ^a, ζ^a+ζ^b, optionally ζ^a+ζ^b+ζ^c), N ∈ {5,7,8,9,10,12,14,16,18}. Squared distances are rounded at 1e-8. These are low-height algebraic numbers, so a spurious coincidence at that precision is very unlikely.
- `ring16.py`: ienjoymath's even-m ring + servers + hexagonal patch (the 9/7 construction), odd-m variants, and single-orbit gadget screening.
- `gadget2.py`: two-round symmetric gadget search on the ring core (orbits of up to 3 candidate points).

## 1. Erdős objective M(X)/n (a counterexample needs M ≥ n+1)

| n | best M found | what achieves it |
|---|---|---|
| 4 | 5 | the rhombus: the only case with M > n |
| 5–18 (every pool) | n | regular n-gon (SA rediscovers R_n in Z[ζ_N] every time) |
| 6 | 6 | regular hexagon (tri lattice, exhaustive) |
| 12 | 12 | regular 12-gon, **and** the 12-point triangular-lattice 5-distance set, spectrum (1:24, 3:15, 4:12, 7:12, 9:3). This is the only non-polygon we found with M = n. |
| lattice n=13…60 | ≈7–12 (ratio 0.54 → 0.18) | lattice pieces are hopeless: the distances near the diameter are always rare |

Exhaustive tri-lattice (19-point pool), n=5..13, M = 4, 6, 6, 7, 7, 9, 10, 12, 7. Square grid: M ≤ 0.8n.
**We found no configuration with M > n for any n ≥ 5.** The regular polygon, where every non-diameter distance has multiplicity exactly n, is the unique maximiser in every pool except at n = 12.

**Counting remark.** A violator has k ≤ n/2 distinct distances, since (k−1)(n+1)+1 ≤ C(n,2) gives k−1 ≤ (n−2)/2. For even n with k = n/2 the equality case forces μ(Δ)=1 and every other class to be exactly n+1. So a violator must be at least as "few-distance" as the regular polygon, and also more uniform. Lattice-type sets have fewer distances but a heavy tail of rare large distances.

**Refined conjecture suggested by the data:** M(X) ≤ n for n ≥ 5, with equality only for R_n and a few sporadic sets (the 12-point lattice set).

### Number of rare distances R(X) (the 2nd question: does R → ∞?)
The Z[ζ12] depth-3 pool gives min R found = 2, 2, 2, 2, 3, 4, 5, 6, 6, 8, 9, 11 for n = 5, 6, 7, 8, 9, 10, 12, 14, 16, 20, 25, 30. That is roughly n/3, and grows. The triangular-lattice SA does better: min R = 2, 2, 2, 3, 3, 3, 3, 3, 3, 5, 6, 7 for n = 5, 6, 7, 8, 9, 10, 12, 14, 16, 20, 25, 30. At n = 16 it is the 4×4 lattice rhombus-hexagon piece, spectrum (1:33, 3:24, 4:18, 7:24, 9:9, 12:6, 13:6), with R = 3. The square lattice gives R = 12 at n = 40. In lattice pieces the rare distances are the O(√n)-scale largest ones, so R grows roughly like √n to n/4 in what we found. That is consistent with R → ∞, but slowly.
Two tight examples (R = 2):
- n = 8, square–triangle tiling patch in Z[ζ12], unit² = 2−√3. Spectrum (0.268:12, 0.536:2, 1:12, 2:2).
  Points: (0,0), (−.866,.5), (−.732,0), (.134,−.5), (−.866,−.5), (−.366,.366), (−.366,−.366), (.134,.5).
- n = 7: the same patch minus one point. Spectrum (10, 2, 8, 1).

## 2. Problem 1.6: min(μ(Δ₂), μ(δ))

Construction values (ring16.py, best m for each n):

| n | min | ratio |
|---|---|---|
| 20 | 21 | 1.05 |
| 30 | 33 | 1.10 |
| 40 | 45 | 1.125 |
| 60 | 71 | 1.18 |
| 100 | 120 | 1.20 |
| 150 | 183 | 1.22 |

The ratio tends to 9/7 ≈ 1.2857, with an O(√n) loss from the patch boundary. The SA over lattice and cyclotomic pools does much worse (≤ 0.93 for n ≥ 14), because Δ₂ needs a near-circular set with rotational structure.

**LP / dual view.** Write A = μ(Δ₂) and B = μ(δ).
- The ring core (m-gon vertices plus m servers, N = 2m points) gives A = 1.5 per point and B = 1 per point.
- A patch point gives (0, 3).
- The optimal mix gives 9/7, with dual weights 4/7 on A and 3/7 on B.
- So a new point, or a k-point gadget, with Δ₂-degree a and δ-degree b beats 9/7 only if **4a + 3b > 9** (or 4A + 3B > 9k for a gadget).

Equivalent clean inequality: **F(X) := μ(δ) + (4/3)μ(Δ₂) ≤ 3n + o(n) ⟹ L ≤ 9/7.** Checks:
- The even-m ring core has F = 3n **exactly**, for every even m ≥ 8 checked (8 through 80).
- The full construction has F = 3n − √(12P).
- The odd-m core has F = 3n − m.
- R_odd has F = 3n − (2/3)n.

**Gadget screening** (ring16.screen_gadgets and gadget2.py): the candidates are all intersections of radius-g and radius-Δ₂ circles around core points, over two rounds, as rotation-symmetric orbits, with combinations of up to 3 orbits.
- Best result for even m: 4a+3b = 6, from inner apexes with (a,b) = (0,2).
- Best result for odd m: 4a+3b = 7, from (a,b) = (1,1).
- **No improving gadget exists.** The ring core is a strict local optimum of F.

**Why (heuristic proof sketch of L = 9/7).**
1. An endpoint x of a Δ₂-edge xy lies on ∂D(y,Δ₂), and that disk contains every point except y's Δ-neighbours. So Δ₂-incident points are "ball-hull extreme". They live on (or o(g)-close to) a closed convex curve Γ. In the construction this is the annulus of width Θ(ε) ≪ g = Θ(√ε).
2. Such points are pairwise ≥ g apart along Γ, so there are c ≤ |Γ|/g of them. Their δ-degree inside the thin annulus is ≤ 2, and A ≤ (3/2)c (Vesztergombi applied to the incident set).
3. δ-edge "loss" = 3n − μ(δ) = 6 + Σ_faces(|f|−3) in the penny graph. The outer face has length ≳ |Γ|/g. The interior of Γ has area ~|Γ|², and filling it needs ~(|Γ|/g)² ≫ n points. So some inner face (or faces) must have total length ≳ |Γ|/g − O(n g/|Γ|)·(…), by an isoperimetric count. Filling a band of width O(g) only shortens it by O(1).
4. So loss ≥ 2c − o(n) ≥ (4/3)A − o(n), which is exactly F ≤ 3n + o(n), and hence min(A,B) ≤ min(1.5c, 3n − 2c) ≤ 9n/7.

Lattice bands attached inside the ring are exactly neutral in this accounting: the value stays 3a/(a−b+3) = 9/7 for every band width. That is why thickening the ring cannot help.
The weak spots are (1), making "thin annulus" rigorous when Δ − Δ₂ ≳ g or when Δ-exceptions are many, and (3), the disconnected / sparse-core cases. This matches ienjoymath's claim that the construction is tight for every Vesztergombi-type LP inequality.

**Result for (a): no improvement over 9/7.** Any improvement needs Δ₂-incident points with δ-loss below 2 per point: 4a+3b > 9 at the margin, or equivalently a Δ₂-rich set that is genuinely 2-dimensional. That seems to contradict the ball-hull extremality in step 1.
